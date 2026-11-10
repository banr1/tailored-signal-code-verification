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
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8c
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: 4-KiB Hook Companion for `Variant8d`

Lifts `Variant8d.lean`'s `AllocContracts`-parameterized theorems to `AllocContracts4K`
inside `CryptoVerification.SpqrV1.States.FromPb.Ext4K`.
-/

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
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

attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  statesFromPb_fnOff
  stubOff_rust_no_alloc_shim
  stubOff_rust_alloc
  stubOff_rust_dealloc
  stubOff_memcpy
  stubOff_handle_error

namespace Ext4K

private theorem v8_local_dealloc_125316
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + (bv% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_dealloc")))
      (rustDeallocSpec A) :=
  sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_dealloc"))) (b := b) (X := Rust.withPanics ext)
      statesFromPb_fnOff stubOff_rust_dealloc (by decide))
    hA.dealloc

theorem v8_cleanup_vec5_10992
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (out ca5 pa5 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10992#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx21_1 : s1.readReg64 .x21 = pa5)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4240#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗
        vecCapPtrDealloc A ca5 pa5 ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ A.pool ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = 0#64 ∧ TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hdealloc := v8_local_dealloc_125316 hA
  simp only [rustDeallocSpec] at hdealloc
  rw [v8_stackAt_encoderFromPb_split_7552 s0.sp]
  states_from_pb_fetches_range b (Rust.withPanics ext) 10992 20
  states_from_pb_fetches_range b (Rust.withPanics ext) 11220 20
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, vecCapPtrDealloc,
    BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  by_cases hca5 : (ca5 == 0#64) = true <;>
    simp only [hca5, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps
    refine EncoderFromPb.align_pre (by simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_
    wp_done
  · wp_steps; wp_apply; wp_steps
    refine EncoderFromPb.align_pre (by rw [hsp1]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_
    wp_done

theorem v8_cleanup_5vecs_10916
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (out ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4 ca5 pa5 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10916#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx21_1 : s1.readReg64 .x21 = pa5)
    (hx22_1 : s1.readReg64 .x22 = ca1) (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx28_1 : s1.readReg64 .x28 = ca2) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4240#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
        (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        vecCapPtrDealloc A ca1 pa1 ∗ vecCapPtrDealloc A ca2 pa2 ∗ vecCapPtrDealloc A ca3 pa3 ∗
        vecCapPtrDealloc A ca4 pa4 ∗ vecCapPtrDealloc A ca5 pa5 ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
          (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
          A.pool ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = 0#64 ∧ TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hdealloc := v8_local_dealloc_125316 hA
  simp only [rustDeallocSpec] at hdealloc
  have h10992 := Ext4K.v8_cleanup_vec5_10992 hA s0
  rw [v8_stackAt_encoderFromPb_split_7552 s0.sp]
  states_from_pb_fetches_range b (Rust.withPanics ext) 10916 76
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, vecCapPtrDealloc,
    BitVec.ofNat_eq_ofNat] at hdealloc h10992 hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  refine EncoderFromPb.seq_clean
    (mid := entry + 10940#64)
    (P_mid :=
      memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
      (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
      (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
      (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
      (if (ca2 == 0#64) = true then emp else A.live pa2 ca2.toNat 1 ∗ memRegion pa2 ca2.toNat) ∗
      (if (ca3 == 0#64) = true then emp else A.live pa3 ca3.toNat 1 ∗ memRegion pa3 ca3.toNat) ∗
      (if (ca4 == 0#64) = true then emp else A.live pa4 ca4.toNat 1 ∗ memRegion pa4 ca4.toNat) ∗
      (if (ca5 == 0#64) = true then emp else A.live pa5 ca5.toNat 1 ∗ memRegion pa5 ca5.toNat) ∗
      A.pool ∗ Rest)
    (Q := fun s2 => s2.sp = s0.sp - 2400#64 ∧ s2.readReg64 .x0 = pa2 ∧ s2.readReg64 .x19 = out ∧
      s2.readReg64 .x21 = pa5 ∧ s2.readReg64 .x26 = ca3 ∧ s2.readReg64 .x28 = ca2 ∧ TraceCalleeSaved s2 s0)
    ?_ ?_
  · by_cases hca1 : (ca1 == 0#64) = true <;>
      simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; refine EncoderFromPb.align_pre (by simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
    · wp_steps; wp_apply; wp_steps
      refine EncoderFromPb.align_pre (by rw [hsp1]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx19_2, hx21_2, hx26_2, hx28_2, htr2⟩
    refine EncoderFromPb.seq_clean
      (mid := entry + 10960#64)
      (P_mid :=
        memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
        (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        (if (ca3 == 0#64) = true then emp else A.live pa3 ca3.toNat 1 ∗ memRegion pa3 ca3.toNat) ∗
        (if (ca4 == 0#64) = true then emp else A.live pa4 ca4.toNat 1 ∗ memRegion pa4 ca4.toNat) ∗
        (if (ca5 == 0#64) = true then emp else A.live pa5 ca5.toNat 1 ∗ memRegion pa5 ca5.toNat) ∗
        A.pool ∗ Rest)
      (Q := fun s3 => s3.sp = s0.sp - 2400#64 ∧ s3.readReg64 .x0 = pa3 ∧ s3.readReg64 .x19 = out ∧
        s3.readReg64 .x21 = pa5 ∧ s3.readReg64 .x26 = ca3 ∧ TraceCalleeSaved s3 s0)
      ?_ ?_
    · by_cases hca2 : (ca2 == 0#64) = true <;>
        simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; refine EncoderFromPb.align_pre (by simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
      · wp_steps; wp_apply; wp_steps
        refine EncoderFromPb.align_pre (by rw [hsp2]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
    · intro s3 hpc3 hrun3 ⟨hsp3, hx0_3, hx19_3, hx21_3, hx26_3, htr3⟩
      refine EncoderFromPb.seq_clean
        (mid := entry + 10980#64)
        (P_mid :=
          memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
          (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
          (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
          (if (ca4 == 0#64) = true then emp else A.live pa4 ca4.toNat 1 ∗ memRegion pa4 ca4.toNat) ∗
          (if (ca5 == 0#64) = true then emp else A.live pa5 ca5.toNat 1 ∗ memRegion pa5 ca5.toNat) ∗
          A.pool ∗ Rest)
        (Q := fun s4 => s4.sp = s0.sp - 2400#64 ∧ s4.readReg64 .x0 = pa4 ∧ s4.readReg64 .x1 = ca4 ∧
          s4.readReg64 .x19 = out ∧ s4.readReg64 .x21 = pa5 ∧ TraceCalleeSaved s4 s0)
        ?_ ?_
      · by_cases hca3 : (ca3 == 0#64) = true <;>
          simp only [hca3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; refine EncoderFromPb.align_pre (by simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
        · wp_steps; wp_apply; wp_steps
          refine EncoderFromPb.align_pre (by rw [hsp3]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
      · intro s4 hpc4 hrun4 ⟨hsp4, hx0_4, hx1_4, hx19_4, hx21_4, htr4⟩
        refine EncoderFromPb.seq_clean
          (mid := entry + 10992#64)
          (P_mid :=
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗
            (if (ca5 == 0#64) = true then emp else A.live pa5 ca5.toNat 1 ∗ memRegion pa5 ca5.toNat) ∗
            A.pool ∗
            ((((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
             (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗
             (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗ Rest))
          (Q := fun s5 => s5.sp = s0.sp - 2400#64 ∧ s5.readReg64 .x19 = out ∧
            s5.readReg64 .x21 = pa5 ∧ TraceCalleeSaved s5 s0)
          ?_ ?_
        · by_cases hca4 : (ca4 == 0#64) = true <;>
            simp only [hca4, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps
            refine EncoderFromPb.align_pre ?_ ?_
            · rw [v8_stackAt_encoderFromPb_split_7552 s0.sp]
              simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)
            · wp_done
          · wp_steps; wp_apply
            refine EncoderFromPb.align_pre ?_ ?_
            · rw [v8_stackAt_encoderFromPb_split_7552 s0.sp, hsp4]
              simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)
            · wp_done
        · intro s5 hpc5 hrun5 ⟨hsp5, hx19_5, hx21_5, htr5⟩
          have h5 := h10992 s5 out ca5 pa5
            ((((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
             (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗
             (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗ Rest)
            hsp0_align hpc5 hrun5 hsp5 hx19_5 hx21_5 htr5
          refine SepWP.mono h5 fun sf Pf _ _ ⟨hPf, hsp_f, hx19_f, hx20_f, htr_f⟩ => ?_
          rw [v8_stackAt_encoderFromPb_split_7552 s0.sp] at hPf
          exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hx19_f, hx20_f, htr_f⟩

end Ext4K

end CryptoVerification.SpqrV1.States.FromPb

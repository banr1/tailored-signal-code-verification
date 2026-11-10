/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6a
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 6 (`HeaderReceived`, `+1464`) — Part B

Early `MsgDecode` error cleanup (`+1520 -> +10324`), `StateDecode` error paths from `+3760`
(`s.uc = none`, `hdr.length ≠ 64`, `auth = none`), and validation step `+3760 -> +3796`.
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

attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  statesFromPb_fnOff
  stubOff_rust_no_alloc_shim
  stubOff_rust_alloc
  stubOff_rust_dealloc
  stubOff_memcpy
  stubOff_memset
  stubOff_handle_error
  fnOff_poly_decoder_from_pb

theorem v6hr_sub_ok_decoder_from_pb
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdec : DecoderFromPbOkExt b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 35448#64)
      (decoderFromPbSpec A) :=
  sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := 35448) (b := b) (X := Rust.withPanics ext)
      statesFromPb_fnOff fnOff_poly_decoder_from_pb (by decide))
    hdec

/-! ## 1. `MsgDecode` Early Error Path (`+1520 -> +10324`) -/

theorem v6hr_stackAt_encoderFromPbStack_to_allocHook (fsp : BitVec 64) :
    stackAt fsp encoderFromPbStack ⊢
      stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056 := by
  have h := ProofLib.stackAt_split_bottom fsp allocHookStack 1056 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

theorem v6hr_stackAt_allocHook_to_encoderFromPbStack (fsp : BitVec 64) :
    stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056 ⊢
      stackAt fsp encoderFromPbStack := by
  have h := ProofLib.stackAt_split_bottom fsp allocHookStack 1056 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

theorem v6hr_dealloc_hdr_1600_to_10324
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (out c0 p0 cd pd ld : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1600#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx9_1 : s1.readReg64 .x9 = p0)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = c0)
    (hx23_1 : s1.readReg64 .x23 = ld)
    (hx28_1 : s1.readReg64 .x28 = cd)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10324#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2168#64) ↦₆₄ pd) ∗
        vecCapPtrDealloc A c0 p0 ∗
        A.pool ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          ((s0.sp - 2168#64) ↦₆₄ pd) ∗
          A.pool ∗
          Rest) ∧
        v6hr_Saved10324Preserved s0 sm (s0.sp - 2400#64) out pd cd 2#64 ∧
        sm.readReg64 .x23 = ld) := by
  by_cases hc0 : (c0 == 0#64) = true
  · dsimp only [vecCapPtrDealloc]
    simp only [hc0, ↓reduceIte, sepConj_emp, emp_sepConj]
    refine EncoderFromPb.seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5588#64)
      (P_mid :=
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2168#64) ↦₆₄ pd) ∗
        A.pool ∗
        Rest)
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = pd ∧
        sm.readReg64 .x23 = ld ∧
        sm.readReg64 .x28 = cd ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · states_from_pb_fetches_range b (Rust.withPanics ext) 1600 8
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx21_2, hx23_2, hx28_2, htr2⟩
      states_from_pb_fetches_range b (Rust.withPanics ext) 5588 8
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc2 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      wp_done
  · have hbeq : (c0 == 0#64) = false := Bool.eq_false_iff.mpr hc0
    dsimp only [vecCapPtrDealloc]
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
      spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
    have hdealloc := v6hr_sub_ok_dealloc_125316 hA
    simp only [rustDeallocSpec] at hdealloc
    refine SepWP.weaken_pre
      (sepConj_mono_left (v6hr_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
    states_from_pb_fetches_range b (Rust.withPanics ext) 1600 32
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_steps
    wp_apply
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have hst := v6hr_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
      have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
      rw [haddr] at hst
      nth_rw 1 [← hsp1] at hst
      refine Entails.trans
        (Entails.of_eq (show _ =
          (stackAt s1.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
          (((s0.sp - 2168#64) ↦₆₄ pd) ∗ A.pool ∗ Rest) by ac_rfl)) ?_
      exact sepConj_mono_left hst
    · wp_done

theorem v6hr_dealloc_auth_1536_to_1600
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (out c0 p0 c1 p1 c2 p2 cd ld : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1536#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx9_1 : s1.readReg64 .x9 = p0)
    (hx14_1 : s1.readReg64 .x14 = p2)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = c0)
    (hx21_1 : s1.readReg64 .x21 = c2)
    (hx23_1 : s1.readReg64 .x23 = ld)
    (hx24_1 : s1.readReg64 .x24 = c1)
    (hx26_1 : s1.readReg64 .x26 = p1)
    (hx28_1 : s1.readReg64 .x28 = cd)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1600#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        vecCapPtrDealloc A c1 p1 ∗
        vecCapPtrDealloc A c2 p2 ∗
        A.pool ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          A.pool ∗
          Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x9 = p0 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = c0 ∧
        sm.readReg64 .x23 = ld ∧
        sm.readReg64 .x28 = cd ∧
        TraceCalleeSaved sm s0) := by
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1572#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      vecCapPtrDealloc A c2 p2 ∗
      A.pool ∗
      Rest)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x9 = p0 ∧
      sm.readReg64 .x14 = p2 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x20 = c0 ∧
      sm.readReg64 .x21 = c2 ∧
      sm.readReg64 .x23 = ld ∧
      sm.readReg64 .x28 = cd ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · by_cases hc1 : (c1 == 0#64) = true
    · dsimp only [vecCapPtrDealloc]
      simp only [hc1, ↓reduceIte, sepConj_emp, emp_sepConj]
      states_from_pb_fetches_range b (Rust.withPanics ext) 1536 4
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      wp_done
    · have hbeq : (c1 == 0#64) = false := Bool.eq_false_iff.mpr hc1
      dsimp only [vecCapPtrDealloc]
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
        spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
      have hdealloc := v6hr_sub_ok_dealloc_125316 hA
      simp only [rustDeallocSpec] at hdealloc
      refine SepWP.weaken_pre
        (sepConj_mono_left (v6hr_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
      states_from_pb_fetches_range b (Rust.withPanics ext) 1536 36
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      wp_apply
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · have hst := v6hr_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
        have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
        rw [haddr] at hst
        nth_rw 1 [← hsp1] at hst
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt s1.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
            ((if (c2 == 0#64) = true then emp else A.live p2 c2.toNat 1 ∗ memRegion p2 c2.toNat) ∗
             A.pool ∗ Rest) by ac_rfl)) ?_
        exact sepConj_mono_left hst
      · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx9_2, hx14_2, hx19_2, hx20_2, hx21_2, hx23_2, hx28_2, htr2⟩
    by_cases hc2 : (c2 == 0#64) = true
    · dsimp only [vecCapPtrDealloc]
      simp only [hc2, ↓reduceIte, sepConj_emp, emp_sepConj]
      states_from_pb_fetches_range b (Rust.withPanics ext) 1572 4
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc2 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      wp_done
    · have hbeq : (c2 == 0#64) = false := Bool.eq_false_iff.mpr hc2
      dsimp only [vecCapPtrDealloc]
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
        spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
      have hdealloc := v6hr_sub_ok_dealloc_125316 hA
      simp only [rustDeallocSpec] at hdealloc
      refine SepWP.weaken_pre
        (sepConj_mono_left (v6hr_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
      states_from_pb_fetches_range b (Rust.withPanics ext) 1572 28
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc hpc2 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      wp_apply
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · have hst := v6hr_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
        have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
        rw [haddr] at hst
        nth_rw 1 [← hsp2] at hst
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt s2.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
            (A.pool ∗ Rest) by ac_rfl)) ?_
        exact sepConj_mono_left hst
      · wp_done

theorem v6hr_err_1520_uc_none_to_10324
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1520#64)
    (hrun1 : s1.status = .Running)
    (hregs1 : v6hr_Regs1508 s0 s1 out noneCap w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w104 d112 d116 w120) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10324#64) s1
      (((s0.sp - 2168#64) ↦₆₄ w96) ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ ((s0.sp - 2168#64) ↦₆₄ w96) ∗ Rest) ∧
        v6hr_Saved10324Preserved s0 sm (s0.sp - 2400#64) out w96 w88 2#64 ∧
        sm.readReg64 .x23 = w104) := by
  rcases hregs1 with ⟨hsp1, hx8_1, hx9_1, hx10_1, hx11_1, hx12_1, hx13_1, hx14_1,
    hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx28_1, htr1⟩
  dsimp only [noneCap] at hx20_1
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4648#64)
    (P_mid := ((s0.sp - 2168#64) ↦₆₄ w96) ∗ Rest)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x23 = w104 ∧
      sm.readReg64 .x28 = w88 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · states_from_pb_fetches_range b (Rust.withPanics ext) 1520 8
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_steps
    wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx23_2, hx28_2, htr2⟩
    states_from_pb_fetches_range b (Rust.withPanics ext) 4648 12
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc2 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_steps
    wp_done

theorem v6hr_err_1520_auth_none_to_10324
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (out c0 p0 w24 w40 w48 w56 w64 w72 w80 w88 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hc0 : c0.toNat < 2 ^ 63)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1520#64)
    (hrun1 : s1.status = .Running)
    (hregs1 : v6hr_Regs1508 s0 s1 out c0 p0 w24 noneCap w40 w48 w56 w64 w72 w80 w88 w104 d112 d116 w120) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10324#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2168#64) ↦₆₄ w96) ∗
        vecCapPtrDealloc A c0 p0 ∗
        A.pool ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          ((s0.sp - 2168#64) ↦₆₄ w96) ∗
          A.pool ∗
          Rest) ∧
        v6hr_Saved10324Preserved s0 sm (s0.sp - 2400#64) out w96 w88 2#64 ∧
        sm.readReg64 .x23 = w104) := by
  rcases hregs1 with ⟨hsp1, hx8_1, hx9_1, hx10_1, hx11_1, hx12_1, hx13_1, hx14_1,
    hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx28_1, htr1⟩
  have hne_c0 := cap_add_one_beq_zero_false hc0
  dsimp only [noneCap] at hx24_1
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1600#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      ((s0.sp - 2168#64) ↦₆₄ w96) ∗
      vecCapPtrDealloc A c0 p0 ∗
      A.pool ∗
      Rest)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x9 = p0 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x20 = c0 ∧
      sm.readReg64 .x23 = w104 ∧
      sm.readReg64 .x28 = w88 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · states_from_pb_fetches_range b (Rust.withPanics ext) 1520 16
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_steps
    wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx9_2, hx19_2, hx20_2, hx23_2, hx28_2, htr2⟩
    exact v6hr_dealloc_hdr_1600_to_10324 hA s0 s2 out c0 p0 w88 w96 w104 Rest
      hsp0_align hpc2 hrun2 hsp2 hx9_2 hx19_2 hx20_2 hx23_2 hx28_2 htr2

theorem v6hr_err_1520_auth_some_to_10324
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (out c0 p0 w24 c1 p1 w48 c2 p2 w72 w80 w88 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hc0 : c0.toNat < 2 ^ 63)
    (hc1 : c1.toNat < 2 ^ 63)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1520#64)
    (hrun1 : s1.status = .Running)
    (hregs1 : v6hr_Regs1508 s0 s1 out c0 p0 w24 c1 p1 w48 c2 p2 w72 w80 w88 w104 d112 d116 w120) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10324#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2168#64) ↦₆₄ w96) ∗
        vecCapPtrDealloc A c0 p0 ∗
        vecCapPtrDealloc A c1 p1 ∗
        vecCapPtrDealloc A c2 p2 ∗
        A.pool ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          ((s0.sp - 2168#64) ↦₆₄ w96) ∗
          A.pool ∗
          Rest) ∧
        v6hr_Saved10324Preserved s0 sm (s0.sp - 2400#64) out w96 w88 2#64 ∧
        sm.readReg64 .x23 = w104) := by
  rcases hregs1 with ⟨hsp1, hx8_1, hx9_1, hx10_1, hx11_1, hx12_1, hx13_1, hx14_1,
    hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx28_1, htr1⟩
  have hne_c0 := cap_add_one_beq_zero_false hc0
  have hne_c1 := cap_add_one_beq_zero_false hc1
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1536#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      vecCapPtrDealloc A c1 p1 ∗
      vecCapPtrDealloc A c2 p2 ∗
      A.pool ∗
      (((s0.sp - 2168#64) ↦₆₄ w96) ∗ vecCapPtrDealloc A c0 p0 ∗ Rest))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x9 = p0 ∧
      sm.readReg64 .x14 = p2 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x20 = c0 ∧
      sm.readReg64 .x21 = c2 ∧
      sm.readReg64 .x23 = w104 ∧
      sm.readReg64 .x24 = c1 ∧
      sm.readReg64 .x26 = p1 ∧
      sm.readReg64 .x28 = w88 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · states_from_pb_fetches_range b (Rust.withPanics ext) 1520 16
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_steps
    refine EncoderFromPb.align_pre (Entails.of_eq (by ac_rfl)) ?_
    wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx9_2, hx14_2, hx19_2, hx20_2, hx21_2, hx23_2, hx24_2, hx26_2, hx28_2, htr2⟩
    refine EncoderFromPb.seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1600#64)
      (P_mid :=
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2168#64) ↦₆₄ w96) ∗
        vecCapPtrDealloc A c0 p0 ∗
        A.pool ∗
        Rest)
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x9 = p0 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = c0 ∧
        sm.readReg64 .x23 = w104 ∧
        sm.readReg64 .x28 = w88 ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · exact SepWP.strengthen_entails_const (Entails.of_eq (by ac_rfl))
        (v6hr_dealloc_auth_1536_to_1600 hA s0 s2 out c0 p0 c1 p1 c2 p2 w88 w104
          (((s0.sp - 2168#64) ↦₆₄ w96) ∗ vecCapPtrDealloc A c0 p0 ∗ Rest)
          hsp0_align hpc2 hrun2 hsp2 hx9_2 hx14_2 hx19_2 hx20_2 hx21_2 hx23_2 hx24_2 hx26_2 hx28_2 htr2)
    · intro s3 hpc3 hrun3 ⟨hsp3, hx9_3, hx19_3, hx20_3, hx23_3, hx28_3, htr3⟩
      exact v6hr_dealloc_hdr_1600_to_10324 hA s0 s3 out c0 p0 w88 w96 w104 Rest
        hsp0_align hpc3 hrun3 hsp3 hx9_3 hx19_3 hx20_3 hx23_3 hx28_3 htr3

/-! ## 2. `StateDecode` Error Paths from `+3760` (`s.uc = none`, `hdr.length ≠ 64`, `auth = none`) -/

theorem v6hr_err_3760_uc_none_to_10316
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 v224 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3760#64)
    (hrun1 : s1.status = .Running)
    (hregs1 : v6hr_Regs1508 s0 s1 out noneCap w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w104 d112 d116 w120) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10316#64) s1
      (((s0.sp - 2176#64) ↦₆₄ v224) ∗
        ((s0.sp - 2168#64) ↦₆₄ w96) ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢ ((s0.sp - 2176#64) ↦₆₄ w120) ∗ ((s0.sp - 2168#64) ↦₆₄ w96) ∗ Rest) ∧
        v6hr_Saved10324Preserved s0 sm (s0.sp - 2400#64) out w96 w88 0#64 ∧
        sm.readReg64 .x23 = w104) := by
  rcases hregs1 with ⟨hsp1, hx8_1, hx9_1, hx10_1, hx11_1, hx12_1, hx13_1, hx14_1,
    hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx28_1, htr1⟩
  dsimp only [noneCap] at hx20_1
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4640#64)
    (P_mid := ((s0.sp - 2176#64) ↦₆₄ w120) ∗ ((s0.sp - 2168#64) ↦₆₄ w96) ∗ Rest)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x23 = w104 ∧
      sm.readReg64 .x28 = w88 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · states_from_pb_fetches_range b (Rust.withPanics ext) 3760 12
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_steps
    wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx23_2, hx28_2, htr2⟩
    refine EncoderFromPb.seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10312#64)
      (P_mid := ((s0.sp - 2176#64) ↦₆₄ w120) ∗ ((s0.sp - 2168#64) ↦₆₄ w96) ∗ Rest)
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = w104 ∧
        sm.readReg64 .x25 = 0#64 ∧
        sm.readReg64 .x28 = w88 ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · states_from_pb_fetches_range b (Rust.withPanics ext) 4640 8
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc2 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      wp_done
    · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx23_3, hx25_3, hx28_3, htr3⟩
      states_from_pb_fetches_range b (Rust.withPanics ext) 10312 4
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc3 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      wp_done

@[simp, arm64_norm, wp_norm]
theorem v6hr_bfm_56_55_low_byte (x : BitVec 64) :
    (((x &&& 72057594037927935#64) <<< 8).extractLsb' 0 8) = 0#8 := by
  bv_kernel

theorem v6hr_dealloc_hdr_4856_to_10316
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (out c0 p0 cd pd ld v144 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4856#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx9_1 : s1.readReg64 .x9 = p0)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = ld)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (hx28_1 : s1.readReg64 .x28 = cd)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10316#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2256#64) ↦₆₄ v144) ∗
        ((s0.sp - 2168#64) ↦₆₄ pd) ∗
        vecCapPtrDealloc A c0 p0 ∗
        A.pool ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          ((s0.sp - 2256#64) ↦₆₄ if (c0 == 0#64) = true then v144 else p0) ∗
          ((s0.sp - 2168#64) ↦₆₄ pd) ∗
          A.pool ∗
          Rest) ∧
        (sm.readReg64 .x25).extractLsb' 0 8 = 0#8 ∧
        v6hr_Saved10324Preserved s0 sm (s0.sp - 2400#64) out pd cd (sm.readReg64 .x25) ∧
        sm.readReg64 .x23 = ld) := by
  by_cases hc0 : (c0 == 0#64) = true
  · dsimp only [vecCapPtrDealloc]
    simp only [hc0, ↓reduceIte, sepConj_emp, emp_sepConj]
    refine EncoderFromPb.seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 6856#64)
      (P_mid :=
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2256#64) ↦₆₄ v144) ∗
        ((s0.sp - 2168#64) ↦₆₄ pd) ∗
        A.pool ∗
        Rest)
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = ld ∧
        sm.readReg64 .x25 = 0#64 ∧
        sm.readReg64 .x28 = cd ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · states_from_pb_fetches_range b (Rust.withPanics ext) 4856 8
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx23_2, hx25_2, hx28_2, htr2⟩
      refine EncoderFromPb.seq_clean
        (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10308#64)
        (P_mid :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          ((s0.sp - 2256#64) ↦₆₄ v144) ∗
          ((s0.sp - 2168#64) ↦₆₄ pd) ∗
          A.pool ∗
          Rest)
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x23 = ld ∧
          sm.readReg64 .x25 = 0#64 ∧
          sm.readReg64 .x28 = cd ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · states_from_pb_fetches_range b (Rust.withPanics ext) 6856 8
        dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc2 ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "<spqr::v1::chunked::states::States>::from_pb" = entry
        examples_hide_fetches
        wp_steps
        wp_done
      · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx23_3, hx25_3, hx28_3, htr3⟩
        states_from_pb_fetches_range b (Rust.withPanics ext) 10308 8
        dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc3 ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "<spqr::v1::chunked::states::States>::from_pb" = entry
        examples_hide_fetches
        wp_steps
        wp_done
  · have hbeq : (c0 == 0#64) = false := Bool.eq_false_iff.mpr hc0
    dsimp only [vecCapPtrDealloc]
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
      spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
    have hdealloc := v6hr_sub_ok_dealloc_125316 hA
    simp only [rustDeallocSpec] at hdealloc
    refine EncoderFromPb.seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9908#64)
      (P_mid :=
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2256#64) ↦₆₄ p0) ∗
        ((s0.sp - 2168#64) ↦₆₄ pd) ∗
        A.live p0 c0.toNat 1 ∗
        memRegion p0 c0.toNat ∗
        A.pool ∗
        Rest)
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x0 = p0 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = c0 ∧
        sm.readReg64 .x23 = ld ∧
        sm.readReg64 .x25 = 0#64 ∧
        sm.readReg64 .x26 = noneCap ∧
        sm.readReg64 .x28 = cd ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · states_from_pb_fetches_range b (Rust.withPanics ext) 4856 28
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx19_2, hx21_2, hx23_2, hx25_2, hx26_2, hx28_2, htr2⟩
      dsimp only [noneCap] at hx26_2
      refine EncoderFromPb.seq_clean
        (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10308#64)
        (P_mid :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          ((s0.sp - 2256#64) ↦₆₄ p0) ∗
          ((s0.sp - 2168#64) ↦₆₄ pd) ∗
          A.pool ∗
          Rest)
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x23 = ld ∧
          sm.readReg64 .x25 = 0#64 ∧
          sm.readReg64 .x28 = cd ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · refine SepWP.weaken_pre
          (sepConj_mono_left (v6hr_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
        states_from_pb_fetches_range b (Rust.withPanics ext) 9908 36
        dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc hpc2 ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "<spqr::v1::chunked::states::States>::from_pb" = entry
        examples_hide_fetches
        wp_steps
        wp_apply
        wp_steps
        refine EncoderFromPb.align_pre ?_ ?_
        · have hst := v6hr_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
          have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
          rw [haddr] at hst
          nth_rw 1 [← hsp2] at hst
          refine Entails.trans
            (Entails.of_eq (show _ =
              (stackAt s2.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
              (((s0.sp - 2256#64) ↦₆₄ p0) ∗ ((s0.sp - 2168#64) ↦₆₄ pd) ∗ A.pool ∗ Rest) by ac_rfl)) ?_
          exact sepConj_mono_left hst
        · wp_done
      · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx23_3, hx25_3, hx28_3, htr3⟩
        states_from_pb_fetches_range b (Rust.withPanics ext) 10308 8
        dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc3 ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "<spqr::v1::chunked::states::States>::from_pb" = entry
        examples_hide_fetches
        wp_steps
        wp_done

theorem v6hr_dealloc_auth_4760_to_4856
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (out c0 p0 c1 p1 c2 p2 cd ld : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4760#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx9_1 : s1.readReg64 .x9 = p0)
    (hx14_1 : s1.readReg64 .x14 = p2)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = c2)
    (hx23_1 : s1.readReg64 .x23 = ld)
    (hx24_1 : s1.readReg64 .x24 = c1)
    (hx26_1 : s1.readReg64 .x26 = p1)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (hx28_1 : s1.readReg64 .x28 = cd)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4856#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        vecCapPtrDealloc A c1 p1 ∗
        vecCapPtrDealloc A c2 p2 ∗
        A.pool ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          A.pool ∗
          Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x9 = p0 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = ld ∧
        sm.readReg64 .x27 = c0 ∧
        sm.readReg64 .x28 = cd ∧
        TraceCalleeSaved sm s0) := by
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4812#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      vecCapPtrDealloc A c2 p2 ∗
      A.pool ∗
      Rest)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x9 = p0 ∧
      sm.readReg64 .x14 = p2 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x21 = c2 ∧
      sm.readReg64 .x23 = ld ∧
      sm.readReg64 .x27 = c0 ∧
      sm.readReg64 .x28 = cd ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · by_cases hc1 : (c1 == 0#64) = true
    · dsimp only [vecCapPtrDealloc]
      simp only [hc1, ↓reduceIte, sepConj_emp, emp_sepConj]
      states_from_pb_fetches_range b (Rust.withPanics ext) 4760 4
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      wp_done
    · have hbeq : (c1 == 0#64) = false := Bool.eq_false_iff.mpr hc1
      dsimp only [vecCapPtrDealloc]
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
        spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
      have hdealloc := v6hr_sub_ok_dealloc_125316 hA
      simp only [rustDeallocSpec] at hdealloc
      refine SepWP.weaken_pre
        (sepConj_mono_left (v6hr_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
      states_from_pb_fetches_range b (Rust.withPanics ext) 4760 52
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      wp_apply
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · have hst := v6hr_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
        have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
        rw [haddr] at hst
        nth_rw 1 [← hsp1] at hst
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt s1.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
            ((if (c2 == 0#64) = true then emp else A.live p2 c2.toNat 1 ∗ memRegion p2 c2.toNat) ∗
             A.pool ∗ Rest) by ac_rfl)) ?_
        exact sepConj_mono_left hst
      · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx9_2, hx14_2, hx19_2, hx21_2, hx23_2, hx27_2, hx28_2, htr2⟩
    by_cases hc2 : (c2 == 0#64) = true
    · dsimp only [vecCapPtrDealloc]
      simp only [hc2, ↓reduceIte, sepConj_emp, emp_sepConj]
      states_from_pb_fetches_range b (Rust.withPanics ext) 4812 4
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc2 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      wp_done
    · have hbeq : (c2 == 0#64) = false := Bool.eq_false_iff.mpr hc2
      dsimp only [vecCapPtrDealloc]
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
        spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
      have hdealloc := v6hr_sub_ok_dealloc_125316 hA
      simp only [rustDeallocSpec] at hdealloc
      refine SepWP.weaken_pre
        (sepConj_mono_left (v6hr_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
      states_from_pb_fetches_range b (Rust.withPanics ext) 4812 44
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc hpc2 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      wp_apply
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · have hst := v6hr_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
        have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
        rw [haddr] at hst
        nth_rw 1 [← hsp2] at hst
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt s2.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
            (A.pool ∗ Rest) by ac_rfl)) ?_
        exact sepConj_mono_left hst
      · wp_done

theorem v6hr_err_3760_auth_none_to_10316
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (out c0 p0 w24 w40 w48 w56 w64 w72 w80 w88 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 v80 v144 v224 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hc0 : c0.toNat < 2 ^ 63)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3760#64)
    (hrun1 : s1.status = .Running)
    (hregs1 : v6hr_Regs1508 s0 s1 out c0 p0 w24 noneCap w40 w48 w56 w64 w72 w80 w88 w104 d112 d116 w120) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10316#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2320#64) ↦₆₄ v80) ∗
        ((s0.sp - 2256#64) ↦₆₄ v144) ∗
        ((s0.sp - 2176#64) ↦₆₄ v224) ∗
        ((s0.sp - 2168#64) ↦₆₄ w96) ∗
        vecCapPtrDealloc A c0 p0 ∗
        A.pool ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          ((s0.sp - 2320#64) ↦₆₄ w24) ∗
          ((s0.sp - 2256#64) ↦₆₄ if (c0 == 0#64) = true then v144 else p0) ∗
          ((s0.sp - 2176#64) ↦₆₄ w120) ∗
          ((s0.sp - 2168#64) ↦₆₄ w96) ∗
          A.pool ∗
          Rest) ∧
        (sm.readReg64 .x25).extractLsb' 0 8 = 0#8 ∧
        v6hr_Saved10324Preserved s0 sm (s0.sp - 2400#64) out w96 w88 (sm.readReg64 .x25) ∧
        sm.readReg64 .x23 = w104) := by
  rcases hregs1 with ⟨hsp1, hx8_1, hx9_1, hx10_1, hx11_1, hx12_1, hx13_1, hx14_1,
    hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx28_1, htr1⟩
  have hne_c0 := cap_add_one_beq_zero_false hc0
  dsimp only [noneCap] at hx24_1
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4856#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      ((s0.sp - 2256#64) ↦₆₄ v144) ∗
      ((s0.sp - 2168#64) ↦₆₄ w96) ∗
      vecCapPtrDealloc A c0 p0 ∗
      A.pool ∗
      (((s0.sp - 2320#64) ↦₆₄ w24) ∗ ((s0.sp - 2176#64) ↦₆₄ w120) ∗ Rest))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x9 = p0 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x23 = w104 ∧
      sm.readReg64 .x27 = c0 ∧
      sm.readReg64 .x28 = w88 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · by_cases hw24 : (w24 == 64#64) = true
    · states_from_pb_fetches_range b (Rust.withPanics ext) 3760 36
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      refine EncoderFromPb.align_pre (Entails.of_eq (by ac_rfl)) ?_
      wp_done
    · refine EncoderFromPb.seq_clean
        (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4752#64)
        (P_mid :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          ((s0.sp - 2256#64) ↦₆₄ v144) ∗
          ((s0.sp - 2168#64) ↦₆₄ w96) ∗
          vecCapPtrDealloc A c0 p0 ∗
          A.pool ∗
          (((s0.sp - 2320#64) ↦₆₄ w24) ∗ ((s0.sp - 2176#64) ↦₆₄ w120) ∗ Rest))
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x9 = p0 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x23 = w104 ∧
          sm.readReg64 .x24 = 0xffffffffffffffff#64 ∧
          sm.readReg64 .x27 = c0 ∧
          sm.readReg64 .x28 = w88 ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · states_from_pb_fetches_range b (Rust.withPanics ext) 3760 28
        dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "<spqr::v1::chunked::states::States>::from_pb" = entry
        examples_hide_fetches
        wp_steps
        refine EncoderFromPb.align_pre (Entails.of_eq (by ac_rfl)) ?_
        wp_done
      · intro s2 hpc2 hrun2 ⟨hsp2, hx9_2, hx19_2, hx23_2, hx24_2, hx27_2, hx28_2, htr2⟩
        states_from_pb_fetches_range b (Rust.withPanics ext) 4752 8
        dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc2 ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "<spqr::v1::chunked::states::States>::from_pb" = entry
        examples_hide_fetches
        wp_steps
        wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx9_2, hx19_2, hx23_2, hx27_2, hx28_2, htr2⟩
    have h4856 := v6hr_dealloc_hdr_4856_to_10316 hA s0 s2 out c0 p0 w88 w96 w104 v144
      (((s0.sp - 2320#64) ↦₆₄ w24) ∗ ((s0.sp - 2176#64) ↦₆₄ w120) ∗ Rest)
      hsp0_align hpc2 hrun2 hsp2 hx9_2 hx19_2 hx23_2 hx27_2 hx28_2 htr2
    refine SepWP.mono h4856 ?_
    intro sm Pm _ _ ⟨hent, hx25, hpres, hx23⟩
    exact ⟨Entails.trans hent (Entails.of_eq (by ac_rfl)), hx25, hpres, hx23⟩

theorem v6hr_err_3760_hdr_ne64_auth_some_to_10316
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (out c0 p0 w24 c1 p1 w48 c2 p2 w72 w80 w88 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 v80 v144 v224 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hc0 : c0.toNat < 2 ^ 63)
    (hc1 : c1.toNat < 2 ^ 63)
    (hw24 : (w24 == 64#64) = false)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3760#64)
    (hrun1 : s1.status = .Running)
    (hregs1 : v6hr_Regs1508 s0 s1 out c0 p0 w24 c1 p1 w48 c2 p2 w72 w80 w88 w104 d112 d116 w120) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10316#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2320#64) ↦₆₄ v80) ∗
        ((s0.sp - 2256#64) ↦₆₄ v144) ∗
        ((s0.sp - 2176#64) ↦₆₄ v224) ∗
        ((s0.sp - 2168#64) ↦₆₄ w96) ∗
        vecCapPtrDealloc A c0 p0 ∗
        vecCapPtrDealloc A c1 p1 ∗
        vecCapPtrDealloc A c2 p2 ∗
        A.pool ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          ((s0.sp - 2320#64) ↦₆₄ w24) ∗
          ((s0.sp - 2256#64) ↦₆₄ if (c0 == 0#64) = true then v144 else p0) ∗
          ((s0.sp - 2176#64) ↦₆₄ w120) ∗
          ((s0.sp - 2168#64) ↦₆₄ w96) ∗
          A.pool ∗
          Rest) ∧
        (sm.readReg64 .x25).extractLsb' 0 8 = 0#8 ∧
        v6hr_Saved10324Preserved s0 sm (s0.sp - 2400#64) out w96 w88 (sm.readReg64 .x25) ∧
        sm.readReg64 .x23 = w104) := by
  rcases hregs1 with ⟨hsp1, hx8_1, hx9_1, hx10_1, hx11_1, hx12_1, hx13_1, hx14_1,
    hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx28_1, htr1⟩
  have hne_c0 := cap_add_one_beq_zero_false hc0
  have hne_c1 := cap_add_one_beq_zero_false hc1
  have hw24_ne : ¬((w24 == 64#64) = true) := by rw [hw24]; decide
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4760#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      vecCapPtrDealloc A c1 p1 ∗
      vecCapPtrDealloc A c2 p2 ∗
      A.pool ∗
      (((s0.sp - 2256#64) ↦₆₄ v144) ∗
       ((s0.sp - 2168#64) ↦₆₄ w96) ∗
       vecCapPtrDealloc A c0 p0 ∗
       ((s0.sp - 2320#64) ↦₆₄ w24) ∗
       ((s0.sp - 2176#64) ↦₆₄ w120) ∗
       Rest))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x9 = p0 ∧
      sm.readReg64 .x14 = p2 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x21 = c2 ∧
      sm.readReg64 .x23 = w104 ∧
      sm.readReg64 .x24 = c1 ∧
      sm.readReg64 .x26 = p1 ∧
      sm.readReg64 .x27 = c0 ∧
      sm.readReg64 .x28 = w88 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · refine EncoderFromPb.seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4752#64)
      (P_mid :=
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        vecCapPtrDealloc A c1 p1 ∗
        vecCapPtrDealloc A c2 p2 ∗
        A.pool ∗
        (((s0.sp - 2256#64) ↦₆₄ v144) ∗
         ((s0.sp - 2168#64) ↦₆₄ w96) ∗
         vecCapPtrDealloc A c0 p0 ∗
         ((s0.sp - 2320#64) ↦₆₄ w24) ∗
         ((s0.sp - 2176#64) ↦₆₄ w120) ∗
         Rest))
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x9 = p0 ∧
        sm.readReg64 .x14 = p2 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = c2 ∧
        sm.readReg64 .x23 = w104 ∧
        sm.readReg64 .x24 = c1 ∧
        sm.readReg64 .x26 = p1 ∧
        sm.readReg64 .x27 = c0 ∧
        sm.readReg64 .x28 = w88 ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · states_from_pb_fetches_range b (Rust.withPanics ext) 3760 28
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      refine EncoderFromPb.align_pre (Entails.of_eq (by ac_rfl)) ?_
      wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx9_2, hx14_2, hx19_2, hx21_2, hx23_2, hx24_2, hx26_2, hx27_2, hx28_2, htr2⟩
      states_from_pb_fetches_range b (Rust.withPanics ext) 4752 8
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc2 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx9_2, hx14_2, hx19_2, hx21_2, hx23_2, hx24_2, hx26_2, hx27_2, hx28_2, htr2⟩
    refine EncoderFromPb.seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4856#64)
      (P_mid :=
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2256#64) ↦₆₄ v144) ∗
        ((s0.sp - 2168#64) ↦₆₄ w96) ∗
        vecCapPtrDealloc A c0 p0 ∗
        A.pool ∗
        (((s0.sp - 2320#64) ↦₆₄ w24) ∗ ((s0.sp - 2176#64) ↦₆₄ w120) ∗ Rest))
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x9 = p0 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = w104 ∧
        sm.readReg64 .x27 = c0 ∧
        sm.readReg64 .x28 = w88 ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · exact SepWP.strengthen_entails_const (Entails.of_eq (by ac_rfl))
        (v6hr_dealloc_auth_4760_to_4856 hA s0 s2 out c0 p0 c1 p1 c2 p2 w88 w104
          (((s0.sp - 2256#64) ↦₆₄ v144) ∗
           ((s0.sp - 2168#64) ↦₆₄ w96) ∗
           vecCapPtrDealloc A c0 p0 ∗
           ((s0.sp - 2320#64) ↦₆₄ w24) ∗
           ((s0.sp - 2176#64) ↦₆₄ w120) ∗
           Rest)
          hsp0_align hpc2 hrun2 hsp2 hx9_2 hx14_2 hx19_2 hx21_2 hx23_2 hx24_2 hx26_2 hx27_2 hx28_2 htr2)
    · intro s3 hpc3 hrun3 ⟨hsp3, hx9_3, hx19_3, hx23_3, hx27_3, hx28_3, htr3⟩
      have h4856 := v6hr_dealloc_hdr_4856_to_10316 hA s0 s3 out c0 p0 w88 w96 w104 v144
        (((s0.sp - 2320#64) ↦₆₄ w24) ∗ ((s0.sp - 2176#64) ↦₆₄ w120) ∗ Rest)
        hsp0_align hpc3 hrun3 hsp3 hx9_3 hx19_3 hx23_3 hx27_3 hx28_3 htr3
      refine SepWP.mono h4856 ?_
      intro sm Pm _ _ ⟨hent, hx25, hpres, hx23⟩
      exact ⟨Entails.trans hent (Entails.of_eq (by ac_rfl)), hx25, hpres, hx23⟩

theorem v6hr_step_3760_to_3796
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out c0 p0 c1 p1 w48 c2 p2 w72 w80 w88 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 v80 v224 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hc0 : c0.toNat < 2 ^ 63)
    (hc1 : c1.toNat < 2 ^ 63)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3760#64)
    (hrun1 : s1.status = .Running)
    (hregs1 : v6hr_Regs1508 s0 s1 out c0 p0 64#64 c1 p1 w48 c2 p2 w72 w80 w88 w104 d112 d116 w120) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3796#64) s1
      (((s0.sp - 2320#64) ↦₆₄ v80) ∗
        ((s0.sp - 2176#64) ↦₆₄ v224) ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          ((s0.sp - 2320#64) ↦₆₄ 64#64) ∗
          ((s0.sp - 2176#64) ↦₆₄ w120) ∗
          Rest) ∧
        v6hr_Regs1508 s0 sm out c0 p0 64#64 c1 p1 w48 c2 p2 w72 w80 w88 w104 d112 d116 w120 ∧
        sm.readReg64 .x27 = c0) := by
  rcases hregs1 with ⟨hsp1, hx8_1, hx9_1, hx10_1, hx11_1, hx12_1, hx13_1, hx14_1,
    hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx28_1, htr1⟩
  have hne_c0 := cap_add_one_beq_zero_false hc0
  have hne_c1 := cap_add_one_beq_zero_false hc1
  states_from_pb_fetches_range b (Rust.withPanics ext) 3760 36
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_steps
  wp_done

end CryptoVerification.SpqrV1.States.FromPb

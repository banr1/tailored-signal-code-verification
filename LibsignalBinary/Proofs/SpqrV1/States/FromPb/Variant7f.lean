/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7e
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7c
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Epilogue
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# SPQR V1 `<States>::from_pb`: Variant 7 (`Ct1Sampled`, niche variant) — Part F

`<Ct1Sent>::from_pb` copy (`+3480 -> +3548`), call (`+3548`), error branch (`+3552 -> +5444`),
`Ok` spill (`+3552 -> +3648`) and `sendingCt1 = none` branch (`+3648 -> +7100`), plus
`<PolyEncoder>::from_pb` copy (`+3652 -> +3716`), call (`+3716`), error branch (`+3720 -> +3732`),
and `Ok` move (`+3720 -> +7260 -> +7348`).
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

/-! ## 1. `<Ct1Sent>::from_pb` Copy (`+3480 -> +3548`) -/

theorem v7_memRegion_240_split_ucCopy (fsp : BitVec 64) :
    memRegion (fsp + 240#64) 128 ⊢
      (∃∗ d0 : BitVec 64, (fsp + 240#64) ↦₆₄ d0) ∗
      (∃∗ b8 : BitVec 8, (fsp + 248#64) ↦₈ b8) ∗
      (∃∗ q9_lo : BitVec 64, (fsp + 249#64) ↦₆₄ q9_lo) ∗
      (∃∗ q9_hi : BitVec 64, (fsp + 257#64) ↦₆₄ q9_hi) ∗
      memRegion (fsp + 265#64) 7 ∗
      (∃∗ d32 : BitVec 64, (fsp + 272#64) ↦₆₄ d32) ∗
      (∃∗ d40 : BitVec 64, (fsp + 280#64) ↦₆₄ d40) ∗
      (∃∗ d48 : BitVec 64, (fsp + 288#64) ↦₆₄ d48) ∗
      (∃∗ d56 : BitVec 64, (fsp + 296#64) ↦₆₄ d56) ∗
      (∃∗ d64 : BitVec 64, (fsp + 304#64) ↦₆₄ d64) ∗
      (∃∗ d72 : BitVec 64, (fsp + 312#64) ↦₆₄ d72) ∗
      (∃∗ d80 : BitVec 64, (fsp + 320#64) ↦₆₄ d80) ∗
      (∃∗ d88 : BitVec 64, (fsp + 328#64) ↦₆₄ d88) ∗
      (∃∗ d96 : BitVec 64, (fsp + 336#64) ↦₆₄ d96) ∗
      (∃∗ d104 : BitVec 64, (fsp + 344#64) ↦₆₄ d104) ∗
      (∃∗ d112 : BitVec 64, (fsp + 352#64) ↦₆₄ d112) ∗
      (∃∗ d120 : BitVec 64, (fsp + 360#64) ↦₆₄ d120) := by
  exact split_top <|
    split_step (mem64_entails _) <|
    split_step (mem8_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (Entails.refl _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    mem64_entails _

theorem v7_ucTailWordsAt_to_step3480
    (a w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 : BitVec 64) :
    v7_ucTailWordsAt a w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 ⊢
      ((a + 8#64) ↦₈ EncoderFromPb.loByte w8) ∗
      ((a + 9#64) ↦ₛ EncoderFromPb.hiBytes7 w8) ∗
      ((a + 16#64) ↦₆₄ w16) ∗
      ((a + 24#64) ↦₆₄ w24) ∗
      ((a + 32#64) ↦₆₄ w32) ∗
      ((a + 40#64) ↦₆₄ w40) ∗
      ((a + 48#64) ↦₆₄ w48) ∗
      ((a + 56#64) ↦₆₄ w56) ∗
      ((a + 64#64) ↦₆₄ w64) ∗
      ((a + 72#64) ↦₆₄ w72) ∗
      ((a + 80#64) ↦₆₄ w80) ∗
      ((a + 88#64) ↦₆₄ w88) ∗
      ((a + 96#64) ↦₆₄ w96) ∗
      ((a + 104#64) ↦₆₄ w104) ∗
      ((a + 112#64) ↦₆₄ w112) ∗
      ((a + 120#64) ↦₆₄ w120) := by
  unfold v7_ucTailWordsAt
  have h8 := pointsTo64_split_1_7 (a + 8#64) w8
  have ha9 : a + 8#64 + 1#64 = a + 9#64 := by bv_omega
  rw [ha9] at h8
  rw [h8]
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 800000 in
/-- Copy `ProtoUnchunkedCt1Sent` (`128`B) from `pbA` (`x27`) to `fsp + 240` (`sp + 0xf0`) at `+3480 -> +3548`
    when `w0.toNat < 2 ^ 63`. -/
theorem v7_copy_uc_3480_to_3548
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out pbA w0 cap_dec x21_val x23_val x25_val : BitVec 64)
    (u : V1State.Unchunked.Ct1Sent) (Frame : SepProp)
    (hw0 : w0.toNat < 2 ^ 63)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3480#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx9_1 : s1.readReg64 .x9 = w0)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = x21_val)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx23_1 : s1.readReg64 .x23 = x23_val)
    (hx25_1 : s1.readReg64 .x25 = x25_val)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3548#64) s1
      ((pbA ↦₆₄ w0) ∗
        v7_optProtoUnchunkedCt1SentTail A pbA w0 (some u) ∗
        memRegion (fsp + 240#64) 128 ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          memRegion pbA 128 ∗
          protoUnchunkedCt1SentAt A (fsp + 240#64) u ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 240#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x23 = x23_val ∧
        sm.readReg64 .x25 = x25_val ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) := by
  have hne := cap_add_one_beq_zero_false hw0
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono (v7_ucTail_unpack A pbA w0 u)
      (sepConj_mono_left (v7_memRegion_240_split_ucCopy fsp)))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro d120
  apply ProofLib.SepWP.exists_left; intro d112
  apply ProofLib.SepWP.exists_left; intro d104
  apply ProofLib.SepWP.exists_left; intro d96
  apply ProofLib.SepWP.exists_left; intro d88
  apply ProofLib.SepWP.exists_left; intro d80
  apply ProofLib.SepWP.exists_left; intro d72
  apply ProofLib.SepWP.exists_left; intro d64
  apply ProofLib.SepWP.exists_left; intro d56
  apply ProofLib.SepWP.exists_left; intro d48
  apply ProofLib.SepWP.exists_left; intro d40
  apply ProofLib.SepWP.exists_left; intro d32
  apply ProofLib.SepWP.exists_left; intro q9_hi
  apply ProofLib.SepWP.exists_left; intro q9_lo
  apply ProofLib.SepWP.exists_left; intro b8
  apply ProofLib.SepWP.exists_left; intro d0
  apply ProofLib.SepWP.exists_left; intro w8
  apply ProofLib.SepWP.exists_left; intro w16
  apply ProofLib.SepWP.exists_left; intro w24
  apply ProofLib.SepWP.exists_left; intro w32
  apply ProofLib.SepWP.exists_left; intro w40
  apply ProofLib.SepWP.exists_left; intro w48
  apply ProofLib.SepWP.exists_left; intro w56
  apply ProofLib.SepWP.exists_left; intro w64
  apply ProofLib.SepWP.exists_left; intro w72
  apply ProofLib.SepWP.exists_left; intro w80
  apply ProofLib.SepWP.exists_left; intro w88
  apply ProofLib.SepWP.exists_left; intro w96
  apply ProofLib.SepWP.exists_left; intro w104
  apply ProofLib.SepWP.exists_left; intro w112
  apply ProofLib.SepWP.exists_left; intro w120
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left
      (v7_ucTailWordsAt_to_step3480 pbA w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120))) ?_
  states_from_pb_fetches_range b (Rust.withPanics ext) 3480 68
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  refine EncoderFromPb.seq_clean (mid := entry + 3536#64)
    (P_mid :=
      (pbA ↦₆₄ w0) ∗
      (((pbA + 8#64) ↦₈ EncoderFromPb.loByte w8) ∗
       ((pbA + 9#64) ↦₆₄ EncoderFromPb.unshiftWord w8 (EncoderFromPb.loByte w16)) ∗
       ((pbA + 17#64) ↦₆₄ EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24)) ∗
       ((pbA + 25#64) ↦ₛ EncoderFromPb.hiBytes7 w24)) ∗
      (((pbA + 32#64) ↦₆₄ w32) ∗
       ((pbA + 40#64) ↦₆₄ w40) ∗
       ((pbA + 48#64) ↦₆₄ w48) ∗
       ((pbA + 56#64) ↦₆₄ w56) ∗
       ((pbA + 64#64) ↦₆₄ w64) ∗
       ((pbA + 72#64) ↦₆₄ w72) ∗
       ((pbA + 80#64) ↦₆₄ w80) ∗
       ((pbA + 88#64) ↦₆₄ w88) ∗
       ((pbA + 96#64) ↦₆₄ w96) ∗
       ((pbA + 104#64) ↦₆₄ w104) ∗
       ((pbA + 112#64) ↦₆₄ w112) ∗
       ((pbA + 120#64) ↦₆₄ w120)) ∗
      v7_ucTailHeap A w0 u w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 ∗
      ((fsp + 240#64) ↦₆₄ w0) ∗
      ((fsp + 248#64) ↦₈ EncoderFromPb.loByte w8) ∗
      ((fsp + 249#64) ↦₆₄ q9_lo) ∗
      ((fsp + 257#64) ↦₆₄ q9_hi) ∗
      memRegion (fsp + 265#64) 7 ∗
      (((fsp + 272#64) ↦₆₄ w32) ∗
       ((fsp + 280#64) ↦₆₄ w40) ∗
       ((fsp + 288#64) ↦₆₄ w48) ∗
       ((fsp + 296#64) ↦₆₄ w56) ∗
       ((fsp + 304#64) ↦₆₄ w64) ∗
       ((fsp + 312#64) ↦₆₄ w72) ∗
       ((fsp + 320#64) ↦₆₄ w80) ∗
       ((fsp + 328#64) ↦₆₄ w88) ∗
       ((fsp + 336#64) ↦₆₄ w96) ∗
       ((fsp + 344#64) ↦₆₄ w104) ∗
       ((fsp + 352#64) ↦₆₄ w112) ∗
       ((fsp + 360#64) ↦₆₄ w120)) ∗
      Frame)
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x0 = fsp + 1888#64 ∧
      sm.readReg64 .x1 = fsp + 240#64 ∧
      sm.readReg64 .x8 = w24 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x21 = x21_val ∧
      sm.readReg64 .x22 = cap_dec ∧
      sm.readReg64 .x23 = x23_val ∧
      sm.readReg64 .x25 = x25_val ∧
      sm.readReg64 .x27 = pbA ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have h8 := (pointsTo64_split_1_7 (pbA + 8#64) w8).symm
      have ha9 : pbA + 8#64 + 1#64 = pbA + 9#64 := by bv_omega
      rw [ha9] at h8
      have htri := v7_triple64_to_byte_qword_tail7 (pbA + 8#64) w8 w16 w24
      simp only [pointsTo128, extractLsb'_0_64_append, extractLsb'_64_64_append,
        BitVec.add_assoc, BitVec.reduceAdd] at htri
      have hpb_mid :
          ((pbA + 8#64) ↦₈ EncoderFromPb.loByte w8) ∗
          ((pbA + 9#64) ↦ₛ EncoderFromPb.hiBytes7 w8) ∗
          ((pbA + 16#64) ↦₆₄ w16) ∗ ((pbA + 24#64) ↦₆₄ w24) =
          ((pbA + 8#64) ↦₈ EncoderFromPb.loByte w8) ∗
          ((pbA + 9#64) ↦₆₄ EncoderFromPb.unshiftWord w8 (EncoderFromPb.loByte w16)) ∗
          ((pbA + 17#64) ↦₆₄ EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24)) ∗
          ((pbA + 25#64) ↦ₛ EncoderFromPb.hiBytes7 w24) := by
        rw [← sepConj_assoc, h8, htri]
        ac_rfl
      refine Entails.trans (Entails.of_eq (show _ =
        (((pbA + 8#64) ↦₈ EncoderFromPb.loByte w8) ∗
         ((pbA + 9#64) ↦ₛ EncoderFromPb.hiBytes7 w8) ∗
         ((pbA + 16#64) ↦₆₄ w16) ∗ ((pbA + 24#64) ↦₆₄ w24)) ∗
        ((pbA ↦₆₄ w0) ∗
         (((pbA + 32#64) ↦₆₄ w32) ∗
          ((pbA + 40#64) ↦₆₄ w40) ∗
          ((pbA + 48#64) ↦₆₄ w48) ∗
          ((pbA + 56#64) ↦₆₄ w56) ∗
          ((pbA + 64#64) ↦₆₄ w64) ∗
          ((pbA + 72#64) ↦₆₄ w72) ∗
          ((pbA + 80#64) ↦₆₄ w80) ∗
          ((pbA + 88#64) ↦₆₄ w88) ∗
          ((pbA + 96#64) ↦₆₄ w96) ∗
          ((pbA + 104#64) ↦₆₄ w104) ∗
          ((pbA + 112#64) ↦₆₄ w112) ∗
          ((pbA + 120#64) ↦₆₄ w120)) ∗
         v7_ucTailHeap A w0 u w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 ∗
         ((fsp + 240#64) ↦₆₄ w0) ∗
         ((fsp + 248#64) ↦₈ EncoderFromPb.loByte w8) ∗
         ((fsp + 249#64) ↦₆₄ q9_lo) ∗
         ((fsp + 257#64) ↦₆₄ q9_hi) ∗
         memRegion (fsp + 265#64) 7 ∗
         (((fsp + 272#64) ↦₆₄ w32) ∗
          ((fsp + 280#64) ↦₆₄ w40) ∗
          ((fsp + 288#64) ↦₆₄ w48) ∗
          ((fsp + 296#64) ↦₆₄ w56) ∗
          ((fsp + 304#64) ↦₆₄ w64) ∗
          ((fsp + 312#64) ↦₆₄ w72) ∗
          ((fsp + 320#64) ↦₆₄ w80) ∗
          ((fsp + 328#64) ↦₆₄ w88) ∗
          ((fsp + 336#64) ↦₆₄ w96) ∗
          ((fsp + 344#64) ↦₆₄ w104) ∗
          ((fsp + 352#64) ↦₆₄ w112) ∗
          ((fsp + 360#64) ↦₆₄ w120)) ∗
         Frame) by ac_rfl)) ?_
      rw [hpb_mid]
      exact Entails.of_eq (by ac_rfl)
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx1_2, hx8_2, hx19_2, hx21_2, hx22_2, hx23_2, hx25_2, hx27_2, htr2⟩
    refine EncoderFromPb.seq_clean (mid := entry + 3544#64)
      (P_mid :=
        (∃∗ u16 : BitVec 64,
          ((fsp + 248#64) ↦₆₄ w8) ∗
          ((fsp + 256#64) ↦₆₄ w16) ∗
          ((fsp + 264#64) ↦₆₄ u16)) ∗
        memRegion pbA 128 ∗
        v7_ucTailHeap A w0 u w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 ∗
        ((fsp + 240#64) ↦₆₄ w0) ∗
        (((fsp + 272#64) ↦₆₄ w32) ∗
         ((fsp + 280#64) ↦₆₄ w40) ∗
         ((fsp + 288#64) ↦₆₄ w48) ∗
         ((fsp + 296#64) ↦₆₄ w56) ∗
         ((fsp + 304#64) ↦₆₄ w64) ∗
         ((fsp + 312#64) ↦₆₄ w72) ∗
         ((fsp + 320#64) ↦₆₄ w80) ∗
         ((fsp + 328#64) ↦₆₄ w88) ∗
         ((fsp + 336#64) ↦₆₄ w96) ∗
         ((fsp + 344#64) ↦₆₄ w104) ∗
         ((fsp + 352#64) ↦₆₄ w112) ∗
         ((fsp + 360#64) ↦₆₄ w120)) ∗
        Frame)
      (Q := fun sm =>
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 240#64 ∧
        sm.readReg64 .x8 = w24 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x23 = x23_val ∧
        sm.readReg64 .x25 = x25_val ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · have htri_pb := (v7_triple64_to_byte_qword_tail7 (pbA + 8#64) w8 w16 w24).symm
        simp only [pointsTo128, extractLsb'_0_64_append, extractLsb'_64_64_append,
          BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at htri_pb
        have hpb_128 :
            (pbA ↦₆₄ w0) ∗
            (((pbA + 8#64) ↦₈ EncoderFromPb.loByte w8) ∗
             ((pbA + 9#64) ↦₆₄ EncoderFromPb.unshiftWord w8 (EncoderFromPb.loByte w16)) ∗
             ((pbA + 17#64) ↦₆₄ EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24)) ∗
             ((pbA + 25#64) ↦ₛ EncoderFromPb.hiBytes7 w24)) ∗
            (((pbA + 32#64) ↦₆₄ w32) ∗
             ((pbA + 40#64) ↦₆₄ w40) ∗
             ((pbA + 48#64) ↦₆₄ w48) ∗
             ((pbA + 56#64) ↦₆₄ w56) ∗
             ((pbA + 64#64) ↦₆₄ w64) ∗
             ((pbA + 72#64) ↦₆₄ w72) ∗
             ((pbA + 80#64) ↦₆₄ w80) ∗
             ((pbA + 88#64) ↦₆₄ w88) ∗
             ((pbA + 96#64) ↦₆₄ w96) ∗
             ((pbA + 104#64) ↦₆₄ w104) ∗
             ((pbA + 112#64) ↦₆₄ w112) ∗
             ((pbA + 120#64) ↦₆₄ w120)) ⊢
            memRegion pbA 128 := by
          rw [htri_pb]
          refine Entails.trans ?_
            (v7_ucWordsAt_entails_128 pbA w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120)
          unfold v7_ucTailWordsAt
          exact Entails.of_eq (by ac_rfl)
        have htri_dst := v7_byte_qword_mem7_to_triple64 (fsp + 248#64) w8 w16 w24
        simp only [pointsTo128, extractLsb'_0_64_append, extractLsb'_64_64_append,
          BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at htri_dst
        refine Entails.trans (Entails.of_eq (show _ =
          (((fsp + 248#64) ↦₈ EncoderFromPb.loByte w8) ∗
           ((fsp + 249#64) ↦₆₄ EncoderFromPb.unshiftWord w8 (EncoderFromPb.loByte w16)) ∗
           ((fsp + 257#64) ↦₆₄ EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24)) ∗
           memRegion (fsp + 265#64) 7) ∗
          ((pbA ↦₆₄ w0) ∗
           (((pbA + 8#64) ↦₈ EncoderFromPb.loByte w8) ∗
            ((pbA + 9#64) ↦₆₄ EncoderFromPb.unshiftWord w8 (EncoderFromPb.loByte w16)) ∗
            ((pbA + 17#64) ↦₆₄ EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24)) ∗
            ((pbA + 25#64) ↦ₛ EncoderFromPb.hiBytes7 w24)) ∗
           (((pbA + 32#64) ↦₆₄ w32) ∗
            ((pbA + 40#64) ↦₆₄ w40) ∗
            ((pbA + 48#64) ↦₆₄ w48) ∗
            ((pbA + 56#64) ↦₆₄ w56) ∗
            ((pbA + 64#64) ↦₆₄ w64) ∗
            ((pbA + 72#64) ↦₆₄ w72) ∗
            ((pbA + 80#64) ↦₆₄ w80) ∗
            ((pbA + 88#64) ↦₆₄ w88) ∗
            ((pbA + 96#64) ↦₆₄ w96) ∗
            ((pbA + 104#64) ↦₆₄ w104) ∗
            ((pbA + 112#64) ↦₆₄ w112) ∗
            ((pbA + 120#64) ↦₆₄ w120))) ∗
          (v7_ucTailHeap A w0 u w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 ∗
           ((fsp + 240#64) ↦₆₄ w0) ∗
           (((fsp + 272#64) ↦₆₄ w32) ∗
            ((fsp + 280#64) ↦₆₄ w40) ∗
            ((fsp + 288#64) ↦₆₄ w48) ∗
            ((fsp + 296#64) ↦₆₄ w56) ∗
            ((fsp + 304#64) ↦₆₄ w64) ∗
            ((fsp + 312#64) ↦₆₄ w72) ∗
            ((fsp + 320#64) ↦₆₄ w80) ∗
            ((fsp + 328#64) ↦₆₄ w88) ∗
            ((fsp + 336#64) ↦₆₄ w96) ∗
            ((fsp + 344#64) ↦₆₄ w104) ∗
            ((fsp + 352#64) ↦₆₄ w112) ∗
            ((fsp + 360#64) ↦₆₄ w120)) ∗
           Frame) by ac_rfl)) ?_
        exact sepConj_mono htri_dst (sepConj_mono_left hpb_128)
      · wp_done
    · intro s3 hpc3 hrun3 ⟨hsp3, hx0_3, hx1_3, hx8_3, hx19_3, hx21_3, hx22_3, hx23_3, hx25_3, hx27_3, htr3⟩
      wp_simp_pre [sepExists_sepConj_left]
      apply ProofLib.SepWP.exists_left; intro u16
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · have hpack := v7_ucAt_pack A (fsp + 240#64) w0 u
          w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120
        unfold v7_ucTailWordsAt at hpack
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpack
        refine Entails.trans (Entails.of_eq (show _ =
          memRegion pbA 128 ∗
          (((fsp + 240#64) ↦₆₄ w0) ∗
           (((fsp + 248#64) ↦₆₄ w8) ∗
            ((fsp + 256#64) ↦₆₄ w16) ∗
            ((fsp + 264#64) ↦₆₄ w24) ∗
            ((fsp + 272#64) ↦₆₄ w32) ∗
            ((fsp + 280#64) ↦₆₄ w40) ∗
            ((fsp + 288#64) ↦₆₄ w48) ∗
            ((fsp + 296#64) ↦₆₄ w56) ∗
            ((fsp + 304#64) ↦₆₄ w64) ∗
            ((fsp + 312#64) ↦₆₄ w72) ∗
            ((fsp + 320#64) ↦₆₄ w80) ∗
            ((fsp + 328#64) ↦₆₄ w88) ∗
            ((fsp + 336#64) ↦₆₄ w96) ∗
            ((fsp + 344#64) ↦₆₄ w104) ∗
            ((fsp + 352#64) ↦₆₄ w112) ∗
            ((fsp + 360#64) ↦₆₄ w120)) ∗
           v7_ucTailHeap A w0 u w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120) ∗
          Frame by ac_rfl)) ?_
        exact sepConj_mono_right (sepConj_mono_left hpack)
      · wp_done

/-! ## 2. `<Ct1Sent>::from_pb` Branch-With-Link (`+3548 -> +15272`) -/

/-- Execute `bl 0x5dc4c` at `+3548` (`0x5ae80 -> 0x5dc4c`, offset `+15272`), setting `x30 = entry + 3552`. -/
theorem v7_bl_ct1_sent_3548_to_15272
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out pbA cap_dec x21_val x23_val x25_val : BitVec 64)
    (P : SepProp)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3548#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx0_1 : s1.readReg64 .x0 = fsp + 1888#64)
    (hx1_1 : s1.readReg64 .x1 = fsp + 240#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = x21_val)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx23_1 : s1.readReg64 .x23 = x23_val)
    (hx25_1 : s1.readReg64 .x25 = x25_val)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 15272#64) s1
      P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 240#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x23 = x23_val ∧
        sm.readReg64 .x25 = x25_val ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3552#64 ∧
        TraceCalleeSaved sm s0) := by
  states_from_pb_fetches_range b (Rust.withPanics ext) 3548 4
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_steps
  wp_done

/-! ## 3. `<Ct1Sent>::from_pb` Error Branch (`+3552 -> +5444 -> +4632`) -/

theorem v7_byte_word_eq_word_byte (a : BitVec 64) (b0 : BitVec 8) (u : BitVec 64) :
    ((a ↦₈ b0) ∗ ((a + 1#64) ↦₆₄ u)) =
      ((a ↦₆₄ ((u <<< 8) ||| b0.zeroExtend 64)) ∗ ((a + 8#64) ↦₈ EncoderFromPb.hiByte u)) := by
  let w : BitVec 64 := (u <<< 8) ||| b0.zeroExtend 64
  have hlo : EncoderFromPb.loByte w = b0 := by
    simp only [EncoderFromPb.loByte, w]
    bv_kernel
  have hun : EncoderFromPb.unshiftWord w (EncoderFromPb.hiByte u) = u := by
    simp only [EncoderFromPb.unshiftWord, EncoderFromPb.hiByte, w]
    bv_kernel
  conv_lhs => rw [← hlo, ← hun]
  rw [ProofLib.pointsTo64_eq_pointsToBytes (a + 1#64),
      ← ProofLib.pointsToBytes_cons,
      EncoderFromPb.loByte_cons_unpack64_unshiftWord w (EncoderFromPb.hiByte u),
      ProofLib.pointsToBytes_append a (unpack64 w) [EncoderFromPb.hiByte u],
      unpack64_length,
      ← ProofLib.pointsTo64_eq_pointsToBytes a w]
  simp only [ProofLib.pointsToBytes_cons, ProofLib.pointsToBytes_nil, sepConj_emp, w]

theorem v7_byte_region119_to_words (a : BitVec 64) (b0 : BitVec 8) :
    (a ↦₈ b0) ∗ memRegion (a + 1#64) 119 ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64,
        ⌜w0.extractLsb' 0 8 = b0⌝ ∗
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗
        memRegion (a + 24#64) 96 := by
  rw [ProofLib.memRegion_split' (b := a + 1#64) (n := 8) (k := 111)
        (b' := a + 9#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (a + 1#64),
      sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro u
  rw [← sepConj_assoc, v7_byte_word_eq_word_byte a b0 u, sepConj_assoc]
  have h112 : ((a + 8#64) ↦₈ EncoderFromPb.hiByte u) ∗ memRegion (a + 9#64) 111 ⊢
      (∃∗ w8 : BitVec 64, (a + 8#64) ↦₆₄ w8) ∗
      (∃∗ w16 : BitVec 64, (a + 16#64) ↦₆₄ w16) ∗
      memRegion (a + 24#64) 96 := by
    have hjoin : ((a + 8#64) ↦₈ EncoderFromPb.hiByte u) ∗ memRegion (a + 9#64) 111 ⊢
        memRegion (a + 8#64) 112 := by
      rw [ProofLib.memRegion_split' (b := a + 8#64) (n := 1) (k := 111)
            (b' := a + 9#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono_left (pointsTo8_entails_memRegion _ _)
    refine Entails.trans hjoin ?_
    rw [ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 104)
          (b' := a + 16#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 96)
          (b' := a + 24#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight (a + 8#64),
        ProofLib.memRegion_eight (a + 16#64)]
    exact Entails.refl _
  refine Entails.trans (sepConj_mono_right h112) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro w16
  apply Entails.sepExists_elim; intro w8
  have hlo : (((u <<< 8) ||| b0.zeroExtend 64).extractLsb' 0 8) = b0 := by bv_kernel
  refine Entails.sepExists_right ((u <<< 8) ||| b0.zeroExtend 64)
    (Entails.sepExists_right w8 (Entails.sepExists_right w16 ?_))
  exact Entails.pure_right hlo (Entails.refl _)

theorem v7_ct1SentResult_err_unpack
    (A : RustAlloc) {F : ShaCompress} (fsp : BitVec 64) (e : StatesError) :
    ct1SentResultAt A (F := F) (fsp + 1888#64) (.error e) ⊢
      ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64, ∃∗ w24 : BitVec 64,
        ⌜w8.extractLsb' 0 8 = 0#8⌝ ∗
        (((fsp + 1888#64) ↦₆₄ noneCap) ∗
         ((fsp + 1896#64) ↦₆₄ w8) ∗
         ((fsp + 1904#64) ↦₆₄ w16) ∗
         ((fsp + 1912#64) ↦₆₄ w24) ∗
         memRegion (fsp + 1920#64) 96) := by
  unfold ct1SentResultAt
  have hbm := v7_byte_region119_to_words (fsp + 1896#64) 0#8
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hbm ⊢
  refine Entails.trans (sepConj_mono_right hbm) ?_
  simp only [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w8
  apply Entails.sepExists_elim; intro w16
  apply Entails.sepExists_elim; intro w24
  refine Entails.sepExists_right w8 (Entails.sepExists_right w16 (Entails.sepExists_right w24 ?_))
  rw [← sepConj_assoc, sepConj_comm ((fsp + 1888#64) ↦₆₄ noneCap), sepConj_assoc]
  apply Entails.pure_left; intro hw8
  exact Entails.pure_right hw8 (Entails.of_eq (by ac_rfl))

theorem v7_1888_words_to_memRegion_128 (fsp w0 w8 w16 w24 : BitVec 64) :
    ((fsp + 1888#64) ↦₆₄ w0) ∗
    ((fsp + 1896#64) ↦₆₄ w8) ∗
    ((fsp + 1904#64) ↦₆₄ w16) ∗
    ((fsp + 1912#64) ↦₆₄ w24) ∗
    memRegion (fsp + 1920#64) 96 ⊢
      memRegion (fsp + 1888#64) 128 := by
  exact collapse_top <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Entails.refl _

/-- Error branch at `+3552 -> +5444 -> +4632` when `<UnchunkedCt1Sent>::from_pb` returns `.error`. -/
theorem v7_uc_err_3552_to_4632
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (out pbA cap_dec : BitVec 64)
    (e : StatesError)
    (optEnc : Option ProtoPolynomialEncoder)
    (optDec : Option ProtoPolynomialDecoder)
    (Frame : SepProp)
    (hcap_dec : v7_optDecoderCapProp cap_dec optDec)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3552#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ct1SentResultAt A (F := F) ((s0.sp - 2400#64) + 1888#64) (.error e) ∗
        optProtoPolynomialEncoderAt A (pbA + 128#64) optEnc ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion ((s0.sp - 2400#64) + 1888#64) 128 ∗
          memRegion (pbA + 128#64) 56 ∗
          memRegion (pbA + 184#64) 40 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        (sm.readReg64 .x28).extractLsb' 0 8 = 0#8 ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hpre :
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ct1SentResultAt A (F := F) ((s0.sp - 2400#64) + 1888#64) (.error e) ∗
        optProtoPolynomialEncoderAt A (pbA + 128#64) optEnc ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
        A.pool ∗ Frame ⊢
      ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64, ∃∗ w24 : BitVec 64,
        ⌜w8.extractLsb' 0 8 = 0#8⌝ ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         ((s0.sp - 2400#64) + 1888#64) ↦₆₄ noneCap ∗
         ((s0.sp - 2400#64) + 1896#64) ↦₆₄ w8 ∗
         ((s0.sp - 2400#64) + 1904#64) ↦₆₄ w16 ∗
         ((s0.sp - 2400#64) + 1912#64) ↦₆₄ w24 ∗
         memRegion ((s0.sp - 2400#64) + 1920#64) 96 ∗
         optProtoPolynomialEncoderAt A (pbA + 128#64) optEnc ∗
         (((pbA + 184#64) ↦₆₄ cap_dec) ∗
          v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
         A.pool ∗ Frame) := by
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_left
        (v7_ct1SentResult_err_unpack A (F := F) (s0.sp - 2400#64) e))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro w8
    apply Entails.sepExists_elim; intro w16
    apply Entails.sepExists_elim; intro w24
    refine Entails.sepExists_right w8 (Entails.sepExists_right w16 (Entails.sepExists_right w24 ?_))
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hpre ?_
  apply ProofLib.SepWP.exists_left; intro w8
  apply ProofLib.SepWP.exists_left; intro w16
  apply ProofLib.SepWP.exists_left; intro w24
  apply ProofLib.SepWP.pure_elim; intro hw8
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5444#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      optProtoPolynomialEncoderAt A (pbA + 128#64) optEnc ∗
      (((pbA + 184#64) ↦₆₄ cap_dec) ∗
       v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
      A.pool ∗
      (memRegion ((s0.sp - 2400#64) + 1888#64) 128 ∗ Frame))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧
      sm.readReg64 .x27 = pbA ∧
      sm.readReg64 .x28 = w8 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · have h1888 : (s0.sp - 2400#64) + 1888#64 = s0.sp - 512#64 := by bv_omega
    have h1896 : (s0.sp - 2400#64) + 1896#64 = s0.sp - 504#64 := by bv_omega
    have h1904 : (s0.sp - 2400#64) + 1904#64 = s0.sp - 496#64 := by bv_omega
    have h1912 : (s0.sp - 2400#64) + 1912#64 = s0.sp - 488#64 := by bv_omega
    have hjoin := v7_1888_words_to_memRegion_128 (s0.sp - 2400#64) noneCap w8 w16 w24
    rw [h1888, h1896, h1904, h1912] at hjoin ⊢
    dsimp only [noneCap] at hjoin ⊢
    states_from_pb_fetches_range b (Rust.withPanics ext) 3552 24
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · refine Entails.trans
        (Entails.of_eq (show _ =
          (((s0.sp - 512#64) ↦₆₄ 18446744073709551615#64) ∗
           ((s0.sp - 504#64) ↦₆₄ w8) ∗
           ((s0.sp - 496#64) ↦₆₄ w16) ∗
           ((s0.sp - 488#64) ↦₆₄ w24) ∗
           memRegion ((s0.sp - 2400#64) + 1920#64) 96) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           optProtoPolynomialEncoderAt A (pbA + 128#64) optEnc ∗
           (((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
           A.pool ∗ Frame) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hjoin) (Entails.of_eq (by ac_rfl))
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx27_2, hx28_2, htr2⟩
    have h5444 := v7_cleanup_5444 hA s0 s2 out pbA cap_dec w8 optEnc optDec
      (memRegion (s0.sp - 512#64) 128 ∗ Frame)
      hcap_dec hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx27_2 hx28_2 htr2
    have h1888 : (s0.sp - 2400#64) + 1888#64 = s0.sp - 512#64 := by bv_omega
    rw [h1888]
    refine SepWP.mono h5444 ?_
    intro sf Pf _ _ ⟨hPf, hsp_f, hx19_f, hx28_f, htr_f⟩
    rw [hx28_f]
    exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hx19_f, hw8, htr_f⟩

/-! ## 4. `<Ct1Sent>::from_pb` `Ok` Unpack/Spill (`+3552 -> +3648`) and `sendingCt1 = none` (`+3648 -> +7100`) -/

theorem v7_vecU8Heap_entails_dealloc (A : RustAlloc) (bs : List (BitVec 8)) (cap ptr len : BitVec 64) :
    v7_vecU8Heap A bs cap ptr len ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ vecCapPtrDealloc A cap ptr := by
  unfold v7_vecU8Heap
  apply Entails.pure_left; intro hp
  exact Entails.pure_right hp.2 (vecU8Payload_entails_dealloc A cap ptr bs)

def v7_ct1SentWordsAt
    (a c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 epoch : BitVec 64) : SepProp :=
  (a ↦₆₄ c1) ∗
  ((a + 8#64) ↦₆₄ p1) ∗
  ((a + 16#64) ↦₆₄ l1) ∗
  ((a + 24#64) ↦₆₄ c2) ∗
  ((a + 32#64) ↦₆₄ p2) ∗
  ((a + 40#64) ↦₆₄ l2) ∗
  ((a + 48#64) ↦₆₄ c3) ∗
  ((a + 56#64) ↦₆₄ p3) ∗
  ((a + 64#64) ↦₆₄ l3) ∗
  ((a + 72#64) ↦₆₄ c4) ∗
  ((a + 80#64) ↦₆₄ p4) ∗
  ((a + 88#64) ↦₆₄ l4) ∗
  ((a + 96#64) ↦₆₄ c5) ∗
  ((a + 104#64) ↦₆₄ p5) ∗
  ((a + 112#64) ↦₆₄ l5) ∗
  ((a + 120#64) ↦₆₄ epoch)

def v7_ct1SentHeap (A : RustAlloc) {F : ShaCompress}
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 : BitVec 64) : SepProp :=
  v7_vecU8Heap A uc.auth.rootKey c1 p1 l1 ∗
  v7_vecU8Heap A uc.auth.macKey c2 p2 l2 ∗
  v7_vecU8Heap A uc.hdr c3 p3 l3 ∗
  v7_vecU8Heap A uc.es c4 p4 l4 ∗
  v7_vecU8Heap A uc.ct1 c5 p5 l5

theorem v7_ct1SentAt_unpack (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) :
    ct1SentAt A (F := F) a uc ⊢
      ∃∗ c1 : BitVec 64, ∃∗ p1 : BitVec 64, ∃∗ l1 : BitVec 64,
      ∃∗ c2 : BitVec 64, ∃∗ p2 : BitVec 64, ∃∗ l2 : BitVec 64,
      ∃∗ c3 : BitVec 64, ∃∗ p3 : BitVec 64, ∃∗ l3 : BitVec 64,
      ∃∗ c4 : BitVec 64, ∃∗ p4 : BitVec 64, ∃∗ l4 : BitVec 64,
      ∃∗ c5 : BitVec 64, ∃∗ p5 : BitVec 64, ∃∗ l5 : BitVec 64,
        ⌜c1.toNat < 2 ^ 63⌝ ∗
        v7_ct1SentWordsAt a c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
        v7_ct1SentHeap A uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 := by
  dsimp only [ct1SentAt, authenticatorAt]
  refine Entails.trans
    (sepConj_mono
      (sepConj_mono (v7_vecU8_unpack A a uc.auth.rootKey)
        (v7_vecU8_unpack A (a + 24#64) uc.auth.macKey))
      (sepConj_mono (v7_vecU8_unpack A (a + 48#64) uc.hdr)
        (sepConj_mono (v7_vecU8_unpack A (a + 72#64) uc.es)
          (sepConj_mono_left (v7_vecU8_unpack A (a + 96#64) uc.ct1))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  apply Entails.sepExists_elim; intro c5
  apply Entails.sepExists_elim; intro p5
  apply Entails.sepExists_elim; intro l5
  apply Entails.sepExists_elim; intro c4
  apply Entails.sepExists_elim; intro p4
  apply Entails.sepExists_elim; intro l4
  apply Entails.sepExists_elim; intro c3
  apply Entails.sepExists_elim; intro p3
  apply Entails.sepExists_elim; intro l3
  apply Entails.sepExists_elim; intro c2
  apply Entails.sepExists_elim; intro p2
  apply Entails.sepExists_elim; intro l2
  apply Entails.sepExists_elim; intro c1
  apply Entails.sepExists_elim; intro p1
  apply Entails.sepExists_elim; intro l1
  refine Entails.sepExists_right c1 (Entails.sepExists_right p1
    (Entails.sepExists_right l1 (Entails.sepExists_right c2
      (Entails.sepExists_right p2 (Entails.sepExists_right l2
        (Entails.sepExists_right c3 (Entails.sepExists_right p3
          (Entails.sepExists_right l3 (Entails.sepExists_right c4
            (Entails.sepExists_right p4 (Entails.sepExists_right l4
              (Entails.sepExists_right c5 (Entails.sepExists_right p5
                (Entails.sepExists_right l5 ?_))))))))))))))
  unfold v7_ct1SentWordsAt v7_ct1SentHeap
  have hc1 : v7_vecU8Heap A uc.auth.rootKey c1 p1 l1 ⊢
      ⌜c1.toNat < 2 ^ 63⌝ ∗ v7_vecU8Heap A uc.auth.rootKey c1 p1 l1 := by
    unfold v7_vecU8Heap
    apply Entails.pure_left; intro hp
    exact Entails.pure_right hp.2 (Entails.pure_right hp (Entails.refl _))
  refine Entails.trans
    (Entails.of_eq (show _ =
      v7_vecU8Heap A uc.auth.rootKey c1 p1 l1 ∗
      (((a ↦₆₄ c1) ∗ ((a + 8#64) ↦₆₄ p1) ∗ ((a + 16#64) ↦₆₄ l1) ∗
        ((a + 24#64) ↦₆₄ c2) ∗ ((a + 32#64) ↦₆₄ p2) ∗ ((a + 40#64) ↦₆₄ l2) ∗
        ((a + 48#64) ↦₆₄ c3) ∗ ((a + 56#64) ↦₆₄ p3) ∗ ((a + 64#64) ↦₆₄ l3) ∗
        ((a + 72#64) ↦₆₄ c4) ∗ ((a + 80#64) ↦₆₄ p4) ∗ ((a + 88#64) ↦₆₄ l4) ∗
        ((a + 96#64) ↦₆₄ c5) ∗ ((a + 104#64) ↦₆₄ p5) ∗ ((a + 112#64) ↦₆₄ l5) ∗
        ((a + 120#64) ↦₆₄ uc.epoch)) ∗
       (v7_vecU8Heap A uc.auth.macKey c2 p2 l2 ∗
        v7_vecU8Heap A uc.hdr c3 p3 l3 ∗
        v7_vecU8Heap A uc.es c4 p4 l4 ∗
        v7_vecU8Heap A uc.ct1 c5 p5 l5)) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left hc1) ?_
  exact Entails.of_eq (by ac_rfl)

theorem v7_ct1SentAt_pack (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 : BitVec 64) :
    v7_ct1SentWordsAt a c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
      v7_ct1SentHeap A uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ⊢
      ct1SentAt A (F := F) a uc := by
  dsimp only [v7_ct1SentWordsAt, v7_ct1SentHeap, ct1SentAt, authenticatorAt]
  have h1 := v7_vecU8_pack A a uc.auth.rootKey c1 p1 l1
  have h2 := v7_vecU8_pack A (a + 24#64) uc.auth.macKey c2 p2 l2
  have h3 := v7_vecU8_pack A (a + 48#64) uc.hdr c3 p3 l3
  have h4 := v7_vecU8_pack A (a + 72#64) uc.es c4 p4 l4
  have h5 := v7_vecU8_pack A (a + 96#64) uc.ct1 c5 p5 l5
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h2 h3 h4 h5
  refine Entails.trans (Entails.of_eq (show _ =
    (((a ↦₆₄ c1) ∗ ((a + 8#64) ↦₆₄ p1) ∗ ((a + 16#64) ↦₆₄ l1)) ∗
     v7_vecU8Heap A uc.auth.rootKey c1 p1 l1) ∗
    ((((a + 24#64) ↦₆₄ c2) ∗ ((a + 32#64) ↦₆₄ p2) ∗ ((a + 40#64) ↦₆₄ l2)) ∗
     v7_vecU8Heap A uc.auth.macKey c2 p2 l2) ∗
    ((((a + 48#64) ↦₆₄ c3) ∗ ((a + 56#64) ↦₆₄ p3) ∗ ((a + 64#64) ↦₆₄ l3)) ∗
     v7_vecU8Heap A uc.hdr c3 p3 l3) ∗
    ((((a + 72#64) ↦₆₄ c4) ∗ ((a + 80#64) ↦₆₄ p4) ∗ ((a + 88#64) ↦₆₄ l4)) ∗
     v7_vecU8Heap A uc.es c4 p4 l4) ∗
    ((((a + 96#64) ↦₆₄ c5) ∗ ((a + 104#64) ↦₆₄ p5) ∗ ((a + 112#64) ↦₆₄ l5)) ∗
     v7_vecU8Heap A uc.ct1 c5 p5 l5) ∗
    ((a + 120#64) ↦₆₄ uc.epoch) by ac_rfl)) ?_
  refine Entails.trans
    (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 (sepConj_mono h4 (sepConj_mono_left h5))))) ?_
  exact Entails.of_eq (by ac_rfl)

theorem v7_ct1SentWordsAt_entails_128
    (a c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 epoch : BitVec 64) :
    v7_ct1SentWordsAt a c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 epoch ⊢
      memRegion a 128 := by
  unfold v7_ct1SentWordsAt
  exact collapse_top <|
    collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Drop.pointsTo64_entails_memRegion _ _

theorem v7_memRegion_128_to_ct1SentWordsAt (a : BitVec 64) :
    memRegion a 128 ⊢
      ∃∗ c1 : BitVec 64, ∃∗ p1 : BitVec 64, ∃∗ l1 : BitVec 64,
      ∃∗ c2 : BitVec 64, ∃∗ p2 : BitVec 64, ∃∗ l2 : BitVec 64,
      ∃∗ c3 : BitVec 64, ∃∗ p3 : BitVec 64, ∃∗ l3 : BitVec 64,
      ∃∗ c4 : BitVec 64, ∃∗ p4 : BitVec 64, ∃∗ l4 : BitVec 64,
      ∃∗ c5 : BitVec 64, ∃∗ p5 : BitVec 64, ∃∗ l5 : BitVec 64,
      ∃∗ epoch : BitVec 64,
        v7_ct1SentWordsAt a c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 epoch := by
  have hsplit : memRegion a 128 ⊢
      (∃∗ c1 : BitVec 64, a ↦₆₄ c1) ∗
      (∃∗ p1 : BitVec 64, (a + 8#64) ↦₆₄ p1) ∗
      (∃∗ l1 : BitVec 64, (a + 16#64) ↦₆₄ l1) ∗
      (∃∗ c2 : BitVec 64, (a + 24#64) ↦₆₄ c2) ∗
      (∃∗ p2 : BitVec 64, (a + 32#64) ↦₆₄ p2) ∗
      (∃∗ l2 : BitVec 64, (a + 40#64) ↦₆₄ l2) ∗
      (∃∗ c3 : BitVec 64, (a + 48#64) ↦₆₄ c3) ∗
      (∃∗ p3 : BitVec 64, (a + 56#64) ↦₆₄ p3) ∗
      (∃∗ l3 : BitVec 64, (a + 64#64) ↦₆₄ l3) ∗
      (∃∗ c4 : BitVec 64, (a + 72#64) ↦₆₄ c4) ∗
      (∃∗ p4 : BitVec 64, (a + 80#64) ↦₆₄ p4) ∗
      (∃∗ l4 : BitVec 64, (a + 88#64) ↦₆₄ l4) ∗
      (∃∗ c5 : BitVec 64, (a + 96#64) ↦₆₄ c5) ∗
      (∃∗ p5 : BitVec 64, (a + 104#64) ↦₆₄ p5) ∗
      (∃∗ l5 : BitVec 64, (a + 112#64) ↦₆₄ l5) ∗
      (∃∗ epoch : BitVec 64, (a + 120#64) ↦₆₄ epoch) := by
    exact split_top <|
      split_step0 (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      mem64_entails _
  refine Entails.trans hsplit ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro epoch
  apply Entails.sepExists_elim; intro l5
  apply Entails.sepExists_elim; intro p5
  apply Entails.sepExists_elim; intro c5
  apply Entails.sepExists_elim; intro l4
  apply Entails.sepExists_elim; intro p4
  apply Entails.sepExists_elim; intro c4
  apply Entails.sepExists_elim; intro l3
  apply Entails.sepExists_elim; intro p3
  apply Entails.sepExists_elim; intro c3
  apply Entails.sepExists_elim; intro l2
  apply Entails.sepExists_elim; intro p2
  apply Entails.sepExists_elim; intro c2
  apply Entails.sepExists_elim; intro l1
  apply Entails.sepExists_elim; intro p1
  apply Entails.sepExists_elim; intro c1
  refine Entails.sepExists_right c1 (Entails.sepExists_right p1
    (Entails.sepExists_right l1 (Entails.sepExists_right c2
      (Entails.sepExists_right p2 (Entails.sepExists_right l2
        (Entails.sepExists_right c3 (Entails.sepExists_right p3
          (Entails.sepExists_right l3 (Entails.sepExists_right c4
            (Entails.sepExists_right p4 (Entails.sepExists_right l4
              (Entails.sepExists_right c5 (Entails.sepExists_right p5
                (Entails.sepExists_right l5 (Entails.sepExists_right epoch ?_)))))))))))))))
  unfold v7_ct1SentWordsAt
  exact Entails.of_eq (by ac_rfl)

theorem v7_ct1SentHeap_entails_dealloc (A : RustAlloc) {F : ShaCompress}
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 : BitVec 64) :
    v7_ct1SentHeap A uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ⊢
      vecCapPtrDealloc A c1 p1 ∗
      vecCapPtrDealloc A c2 p2 ∗
      vecCapPtrDealloc A c3 p3 ∗
      vecCapPtrDealloc A c4 p4 ∗
      vecCapPtrDealloc A c5 p5 := by
  unfold v7_ct1SentHeap
  refine Entails.trans
    (sepConj_mono (v7_vecU8Heap_entails_dealloc A uc.auth.rootKey c1 p1 l1)
      (sepConj_mono (v7_vecU8Heap_entails_dealloc A uc.auth.macKey c2 p2 l2)
        (sepConj_mono (v7_vecU8Heap_entails_dealloc A uc.hdr c3 p3 l3)
          (sepConj_mono (v7_vecU8Heap_entails_dealloc A uc.es c4 p4 l4)
            (v7_vecU8Heap_entails_dealloc A uc.ct1 c5 p5 l5))))) ?_
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜c1.toNat < 2 ^ 63⌝ ∗ ⌜c2.toNat < 2 ^ 63⌝ ∗ ⌜c3.toNat < 2 ^ 63⌝ ∗
    ⌜c4.toNat < 2 ^ 63⌝ ∗ ⌜c5.toNat < 2 ^ 63⌝ ∗
    (vecCapPtrDealloc A c1 p1 ∗
     vecCapPtrDealloc A c2 p2 ∗
     vecCapPtrDealloc A c3 p3 ∗
     vecCapPtrDealloc A c4 p4 ∗
     vecCapPtrDealloc A c5 p5) by ac_rfl)) ?_
  apply Entails.pure_left; intro _
  apply Entails.pure_left; intro _
  apply Entails.pure_left; intro _
  apply Entails.pure_left; intro _
  apply Entails.pure_left; intro _
  exact Entails.refl _

def v7_ct1SentOtherCells
    (fsp c1 p1 l1 c2 l2 l3 l4 l5 epoch : BitVec 64) : SepProp :=
  ((fsp + 1264#64) ↦₆₄ c1) ∗
  ((fsp + 1272#64) ↦₆₄ p1) ∗
  ((fsp + 1280#64) ↦₆₄ l1) ∗
  ((fsp + 1288#64) ↦₆₄ c2) ∗
  ((fsp + 1304#64) ↦₆₄ l2) ∗
  ((fsp + 1328#64) ↦₆₄ l3) ∗
  ((fsp + 1352#64) ↦₆₄ l4) ∗
  ((fsp + 1376#64) ↦₆₄ l5) ∗
  ((fsp + 1384#64) ↦₆₄ epoch)

theorem v7_ct1SentWordsAt_1264_eq_spill_other
    (fsp c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 epoch : BitVec 64) :
    v7_ct1SentWordsAt (fsp + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 epoch =
      v7_ct1SentSpillCells fsp p2 c3 p3 c4 p4 c5 p5 ∗
      v7_ct1SentOtherCells fsp c1 p1 l1 c2 l2 l3 l4 l5 epoch := by
  unfold v7_ct1SentWordsAt v7_ct1SentSpillCells v7_ct1SentOtherCells
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

/-- Spill `Ok(uc)` from `fsp + 1888..2016` to `fsp + 1264..1392` and branch to `+7100`
    when `[pbA + 128] = noneCap` (`s.sendingCt1 = none`). -/
theorem v7_uc_ok_spill_3552_to_7100
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out pbA cap_dec : BitVec 64)
    (c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 epoch : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hc1 : c1.toNat < 2 ^ 63)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3552#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7100#64) s1
      (v7_ct1SentWordsAt (fsp + 1888#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 epoch ∗
        memRegion (fsp + 1264#64) 128 ∗
        ((pbA + 128#64) ↦₆₄ noneCap) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          memRegion (fsp + 1888#64) 128 ∗
          v7_ct1SentWordsAt (fsp + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 epoch ∗
          ((pbA + 128#64) ↦₆₄ noneCap) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x1 = c1 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x24 = c2 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = p1 ∧
        TraceCalleeSaved sm s0) := by
  have hc1_ne := cap_add_one_beq_zero_false hc1
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (v7_memRegion_128_to_ct1SentWordsAt (fsp + 1264#64)))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro d15
  apply ProofLib.SepWP.exists_left; intro d14
  apply ProofLib.SepWP.exists_left; intro d13
  apply ProofLib.SepWP.exists_left; intro d12
  apply ProofLib.SepWP.exists_left; intro d11
  apply ProofLib.SepWP.exists_left; intro d10
  apply ProofLib.SepWP.exists_left; intro d9
  apply ProofLib.SepWP.exists_left; intro d8
  apply ProofLib.SepWP.exists_left; intro d7
  apply ProofLib.SepWP.exists_left; intro d6
  apply ProofLib.SepWP.exists_left; intro d5
  apply ProofLib.SepWP.exists_left; intro d4
  apply ProofLib.SepWP.exists_left; intro d3
  apply ProofLib.SepWP.exists_left; intro d2
  apply ProofLib.SepWP.exists_left; intro d1
  apply ProofLib.SepWP.exists_left; intro d0
  states_from_pb_fetches_range b (Rust.withPanics ext) 3552 100
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, noneCap, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_simp_pre [v7_ct1SentWordsAt, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · have h1888 := v7_ct1SentWordsAt_entails_128 (fsp + 1888#64)
      c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 epoch
    unfold v7_ct1SentWordsAt at h1888 ⊢
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1888 ⊢
    refine Entails.trans (Entails.of_eq (show _ =
      (((fsp + 1888#64) ↦₆₄ c1) ∗ ((fsp + 1896#64) ↦₆₄ p1) ∗ ((fsp + 1904#64) ↦₆₄ l1) ∗
       ((fsp + 1912#64) ↦₆₄ c2) ∗ ((fsp + 1920#64) ↦₆₄ p2) ∗ ((fsp + 1928#64) ↦₆₄ l2) ∗
       ((fsp + 1936#64) ↦₆₄ c3) ∗ ((fsp + 1944#64) ↦₆₄ p3) ∗ ((fsp + 1952#64) ↦₆₄ l3) ∗
       ((fsp + 1960#64) ↦₆₄ c4) ∗ ((fsp + 1968#64) ↦₆₄ p4) ∗ ((fsp + 1976#64) ↦₆₄ l4) ∗
       ((fsp + 1984#64) ↦₆₄ c5) ∗ ((fsp + 1992#64) ↦₆₄ p5) ∗ ((fsp + 2000#64) ↦₆₄ l5) ∗
       ((fsp + 2008#64) ↦₆₄ epoch)) ∗
      (((fsp + 1264#64) ↦₆₄ c1) ∗ ((fsp + 1272#64) ↦₆₄ p1) ∗ ((fsp + 1280#64) ↦₆₄ l1) ∗
       ((fsp + 1288#64) ↦₆₄ c2) ∗ ((fsp + 1296#64) ↦₆₄ p2) ∗ ((fsp + 1304#64) ↦₆₄ l2) ∗
       ((fsp + 1312#64) ↦₆₄ c3) ∗ ((fsp + 1320#64) ↦₆₄ p3) ∗ ((fsp + 1328#64) ↦₆₄ l3) ∗
       ((fsp + 1336#64) ↦₆₄ c4) ∗ ((fsp + 1344#64) ↦₆₄ p4) ∗ ((fsp + 1352#64) ↦₆₄ l4) ∗
       ((fsp + 1360#64) ↦₆₄ c5) ∗ ((fsp + 1368#64) ↦₆₄ p5) ∗ ((fsp + 1376#64) ↦₆₄ l5) ∗
       ((fsp + 1384#64) ↦₆₄ epoch)) ∗
      ((pbA + 128#64) ↦₆₄ 18446744073709551615#64) ∗
      Frame by ac_rfl)) ?_
    exact sepConj_mono_left h1888
  · wp_done

/-- Spill `Ok(uc)` from `fsp + 1888..2016` to `fsp + 1264..1392` and fall through to `+3652`
    when `[pbA + 128] = cap_enc` with `cap_enc.toNat < 2 ^ 63` (`s.sendingCt1 = some enc`). -/
theorem v7_uc_ok_spill_3552_to_3652
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out pbA cap_enc cap_dec x21_val x23_val x25_val : BitVec 64)
    (c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 epoch : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hc1 : c1.toNat < 2 ^ 63)
    (hcap_enc : cap_enc.toNat < 2 ^ 63)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3552#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = x21_val)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx23_1 : s1.readReg64 .x23 = x23_val)
    (hx25_1 : s1.readReg64 .x25 = x25_val)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3652#64) s1
      (v7_ct1SentWordsAt (fsp + 1888#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 epoch ∗
        memRegion (fsp + 1264#64) 128 ∗
        ((pbA + 128#64) ↦₆₄ cap_enc) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          memRegion (fsp + 1888#64) 128 ∗
          v7_ct1SentWordsAt (fsp + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 epoch ∗
          ((pbA + 128#64) ↦₆₄ cap_enc) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x1 = c1 ∧
        sm.readReg64 .x8 = cap_enc ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x23 = x23_val ∧
        sm.readReg64 .x24 = c2 ∧
        sm.readReg64 .x25 = x25_val ∧
        sm.readReg64 .x26 = l1 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = p1 ∧
        TraceCalleeSaved sm s0) := by
  have hc1_ne := cap_add_one_beq_zero_false hc1
  have henc_ne := cap_add_one_beq_zero_false hcap_enc
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (v7_memRegion_128_to_ct1SentWordsAt (fsp + 1264#64)))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro d15
  apply ProofLib.SepWP.exists_left; intro d14
  apply ProofLib.SepWP.exists_left; intro d13
  apply ProofLib.SepWP.exists_left; intro d12
  apply ProofLib.SepWP.exists_left; intro d11
  apply ProofLib.SepWP.exists_left; intro d10
  apply ProofLib.SepWP.exists_left; intro d9
  apply ProofLib.SepWP.exists_left; intro d8
  apply ProofLib.SepWP.exists_left; intro d7
  apply ProofLib.SepWP.exists_left; intro d6
  apply ProofLib.SepWP.exists_left; intro d5
  apply ProofLib.SepWP.exists_left; intro d4
  apply ProofLib.SepWP.exists_left; intro d3
  apply ProofLib.SepWP.exists_left; intro d2
  apply ProofLib.SepWP.exists_left; intro d1
  apply ProofLib.SepWP.exists_left; intro d0
  states_from_pb_fetches_range b (Rust.withPanics ext) 3552 100
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_simp_pre [v7_ct1SentWordsAt, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · have h1888 := v7_ct1SentWordsAt_entails_128 (fsp + 1888#64)
      c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 epoch
    unfold v7_ct1SentWordsAt at h1888 ⊢
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1888 ⊢
    refine Entails.trans (Entails.of_eq (show _ =
      (((fsp + 1888#64) ↦₆₄ c1) ∗ ((fsp + 1896#64) ↦₆₄ p1) ∗ ((fsp + 1904#64) ↦₆₄ l1) ∗
       ((fsp + 1912#64) ↦₆₄ c2) ∗ ((fsp + 1920#64) ↦₆₄ p2) ∗ ((fsp + 1928#64) ↦₆₄ l2) ∗
       ((fsp + 1936#64) ↦₆₄ c3) ∗ ((fsp + 1944#64) ↦₆₄ p3) ∗ ((fsp + 1952#64) ↦₆₄ l3) ∗
       ((fsp + 1960#64) ↦₆₄ c4) ∗ ((fsp + 1968#64) ↦₆₄ p4) ∗ ((fsp + 1976#64) ↦₆₄ l4) ∗
       ((fsp + 1984#64) ↦₆₄ c5) ∗ ((fsp + 1992#64) ↦₆₄ p5) ∗ ((fsp + 2000#64) ↦₆₄ l5) ∗
       ((fsp + 2008#64) ↦₆₄ epoch)) ∗
      (((fsp + 1264#64) ↦₆₄ c1) ∗ ((fsp + 1272#64) ↦₆₄ p1) ∗ ((fsp + 1280#64) ↦₆₄ l1) ∗
       ((fsp + 1288#64) ↦₆₄ c2) ∗ ((fsp + 1296#64) ↦₆₄ p2) ∗ ((fsp + 1304#64) ↦₆₄ l2) ∗
       ((fsp + 1312#64) ↦₆₄ c3) ∗ ((fsp + 1320#64) ↦₆₄ p3) ∗ ((fsp + 1328#64) ↦₆₄ l3) ∗
       ((fsp + 1336#64) ↦₆₄ c4) ∗ ((fsp + 1344#64) ↦₆₄ p4) ∗ ((fsp + 1352#64) ↦₆₄ l4) ∗
       ((fsp + 1360#64) ↦₆₄ c5) ∗ ((fsp + 1368#64) ↦₆₄ p5) ∗ ((fsp + 1376#64) ↦₆₄ l5) ∗
       ((fsp + 1384#64) ↦₆₄ epoch)) ∗
      ((pbA + 128#64) ↦₆₄ cap_enc) ∗
      Frame by ac_rfl)) ?_
    exact sepConj_mono_left h1888
  · wp_done

end CryptoVerification.SpqrV1.States.FromPb

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsa
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 2 (`HeaderSent`, `+508`) — Part B

Stack copy (`+508..+588`), `ptsNeeded == 480` check (`+592`), `Unchunked::EkSent` validation
(`+3348..+3436`), and `Authenticator::from_pb` assembly (`+3436 -> +9032`).
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

/-! ## PB-to-Stack Copy (`+508..+588`) & `pts_needed == 480` Check (`+592..+600`) -/

@[local simp, local arm64_norm, local wp_norm]
theorem v2hs_bv_sub_sub_lit (x : BitVec 64) (a b : Nat) :
    x - BitVec.ofNat 64 a - BitVec.ofNat 64 b = x - BitVec.ofNat 64 (a + b) := by
  bv_omega

attribute [local simp, local arm64_norm, local wp_norm] v2hs_bv_add_add_lit

theorem v2hs_memRegion_2304_split_896_176_1232 (fsp : BitVec 64) :
    memRegion fsp 2304 ⊢
      memRegion fsp 896 ∗
      (∃∗ q0 : BitVec 128, (fsp + 896#64) ↦₁₂₈ q0) ∗
      (∃∗ q1 : BitVec 128, (fsp + 912#64) ↦₁₂₈ q1) ∗
      (∃∗ q2 : BitVec 128, (fsp + 928#64) ↦₁₂₈ q2) ∗
      (∃∗ q3 : BitVec 128, (fsp + 944#64) ↦₁₂₈ q3) ∗
      (∃∗ q4 : BitVec 128, (fsp + 960#64) ↦₁₂₈ q4) ∗
      (∃∗ q5 : BitVec 128, (fsp + 976#64) ↦₁₂₈ q5) ∗
      (∃∗ q6 : BitVec 128, (fsp + 992#64) ↦₁₂₈ q6) ∗
      (∃∗ q7 : BitVec 128, (fsp + 1008#64) ↦₁₂₈ q7) ∗
      (∃∗ q8 : BitVec 128, (fsp + 1024#64) ↦₁₂₈ q8) ∗
      (∃∗ q9 : BitVec 128, (fsp + 1040#64) ↦₁₂₈ q9) ∗
      (∃∗ q10 : BitVec 128, (fsp + 1056#64) ↦₁₂₈ q10) ∗
      memRegion (fsp + 1072#64) 1232 := by
  rw [ProofLib.memRegion_split fsp 896 1408 (by decide),
      ProofLib.memRegion_split' (b := fsp + 896#64) (n := 176) (k := 1232)
        (b' := fsp + 1072#64) rfl (by bv_omega) (by decide)]
  simpa only [arm64_norm, sepConj_assoc] using
    sepConj_mono_right (sepConj_mono_left (v2hs_memRegion_176_to_128 (fsp + 896#64)))

/-- Copy the 176-byte payload `pbA + 8..184` to `fsp + 896..1072` (`+508..+588`),
    setting `x22 := d_w0` and branching to `+3348` if `d_w0 + 1 == 0` (`optDec = none`)
    or falling through to `+592` (`optDec = some _`). -/
theorem v2hs_copy_pb_to_stack_508
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 508#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      (if (d_w0 + 1#64 == 0#64) = true
       then (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3348#64
       else (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 592#64)
      s1
      (memRegion (s0.sp - 2400#64) 2304 ∗
        v2hs_pb128At (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
          w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        Rest)
      (fun s2 P2 =>
        (P2 ⊢
          memRegion (s0.sp - 2400#64) 896 ∗
          v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
          v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64)
            w0 w8 w16 w24 w32 w40 w48 ∗
          v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64)
            d_w0 d_w8 d_w16 d_w24 d_w32 ∗
          memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
          v2hs_pb128At (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
            w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32 ∗
          Rest) ∧
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x21 = s1.readReg64 .x21 ∧
        s2.readReg64 .x27 = pbA ∧
        s2.readReg64 .x22 = d_w0 ∧
        TraceCalleeSaved s2 s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  rw [← v2hs_words_eq_pb128 (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
    w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32]
  refine SepWP.weaken_pre (sepConj_mono_left (v2hs_memRegion_2304_split_896_176_1232 (s0.sp - 2400#64))) ?_
  wp_simp_pre [v2hs_ucWordsAt, v1_optProtoPolyEncoderWordsAt, v2hs_optProtoDecoderWordsAt, pointsTo128,
    arm64_norm, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro q10
  apply ProofLib.SepWP.exists_left; intro q9
  apply ProofLib.SepWP.exists_left; intro q8
  apply ProofLib.SepWP.exists_left; intro q7
  apply ProofLib.SepWP.exists_left; intro q6
  apply ProofLib.SepWP.exists_left; intro q5
  apply ProofLib.SepWP.exists_left; intro q4
  apply ProofLib.SepWP.exists_left; intro q3
  apply ProofLib.SepWP.exists_left; intro q2
  apply ProofLib.SepWP.exists_left; intro q1
  apply ProofLib.SepWP.exists_left; intro q0
  states_from_pb_fetches_range b (Rust.withPanics ext) 508 84
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  by_cases hcmn : (d_w0 + 1#64 == 0#64) = true <;>
    simp only [hcmn, Bool.false_eq_true, ↓reduceIte]
  · wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · dsimp only [v2hs_ucWordsAt, v1_optProtoPolyEncoderWordsAt, v2hs_optProtoDecoderWordsAt]
      simp only [arm64_norm]
      exact Entails.of_eq (by ac_rfl)
    · wp_done
  · wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · dsimp only [v2hs_ucWordsAt, v1_optProtoPolyEncoderWordsAt, v2hs_optProtoDecoderWordsAt]
      simp only [arm64_norm]
      exact Entails.of_eq (by ac_rfl)
    · wp_done

/-- Check `pts_needed == 480` at `+592..+600`: reads 32-bit `d_w24.extractLsb' 0 32` from `[sp, #1056]`,
    branching to `+3348` if equal to `480#32` (`0x1e0#32`) or falling through to `+604`. -/
theorem v2hs_check_ptsNeeded_592
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64)
    (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 592#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d_w0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      (if (d_w24.extractLsb' 0 32 == 480#32) = true
       then (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3348#64
       else (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 604#64)
      s1
      (v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗ Rest) ∧
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x21 = s1.readReg64 .x21 ∧
        s2.readReg64 .x22 = d_w0 ∧
        s2.readReg64 .x27 = s1.readReg64 .x27 ∧
        TraceCalleeSaved s2 s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  wp_simp_pre [v2hs_optProtoDecoderWordsAt, arm64_norm, sepConj_assoc]
  states_from_pb_fetches_range b (Rust.withPanics ext) 592 12
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  by_cases hpts : (d_w24.extractLsb' 0 32 == 480#32) = true <;>
    simp only [hpts, Bool.false_eq_true, ↓reduceIte]
  · wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · dsimp only [v2hs_optProtoDecoderWordsAt]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)
    · wp_done
  · wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · dsimp only [v2hs_optProtoDecoderWordsAt]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)
    · wp_done

/-! ## `Unchunked::EkSent` Validation at `+3348..+3436` -/

/-- When `u8 = noneCap` (`s.uc = none`), `+3348..+3356` jumps to `+4392`. -/
theorem v2hs_uc_none_3348_to_4392
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out d_w0 : BitVec 64)
    (u16 u24 u32 u40 u48 u56 u64 u72 u80 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3348#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d_w0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4392#64) s1
      (v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64)
        noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64)
          noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗ Rest) ∧
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x22 = d_w0 ∧
        TraceCalleeSaved s2 s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  wp_simp_pre [v2hs_ucWordsAt, noneCap, arm64_norm, sepConj_assoc]
  states_from_pb_fetches_range b (Rust.withPanics ext) 3348 12
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · dsimp only [v2hs_ucWordsAt, noneCap]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)
  · wp_done

/-- Stack split of `memRegion fsp 896` into the 8 scratch slots used by Variant 2 (`96, 152, 176, 184, 200, 216, 224, 232`). -/
def v2hs_stack896ScratchRest (fsp : BitVec 64) : SepProp :=
  memRegion fsp 96 ∗ memRegion (fsp + 104#64) 48 ∗ memRegion (fsp + 160#64) 16 ∗
  memRegion (fsp + 192#64) 8 ∗ memRegion (fsp + 208#64) 8

theorem v2hs_memRegion_896_split_scratch (fsp : BitVec 64) :
    memRegion fsp 896 ⊢
      (∃∗ w96 : BitVec 64, (fsp + 96#64) ↦₆₄ w96) ∗
      (∃∗ w152 : BitVec 64, (fsp + 152#64) ↦₆₄ w152) ∗
      (∃∗ w176 : BitVec 64, (fsp + 176#64) ↦₆₄ w176) ∗
      (∃∗ w184 : BitVec 64, (fsp + 184#64) ↦₆₄ w184) ∗
      (∃∗ w200 : BitVec 64, (fsp + 200#64) ↦₆₄ w200) ∗
      (∃∗ w216 : BitVec 64, (fsp + 216#64) ↦₆₄ w216) ∗
      (∃∗ w224 : BitVec 64, (fsp + 224#64) ↦₆₄ w224) ∗
      (∃∗ w232 : BitVec 64, (fsp + 232#64) ↦₆₄ w232) ∗
      memRegion (fsp + 240#64) 656 ∗
      v2hs_stack896ScratchRest fsp := by
  have h :
      memRegion fsp 896 ⊢
        memRegion fsp 96 ∗
        (∃∗ w96 : BitVec 64, (fsp + 96#64) ↦₆₄ w96) ∗
        memRegion (fsp + 104#64) 48 ∗
        (∃∗ w152 : BitVec 64, (fsp + 152#64) ↦₆₄ w152) ∗
        memRegion (fsp + 160#64) 16 ∗
        (∃∗ w176 : BitVec 64, (fsp + 176#64) ↦₆₄ w176) ∗
        (∃∗ w184 : BitVec 64, (fsp + 184#64) ↦₆₄ w184) ∗
        memRegion (fsp + 192#64) 8 ∗
        (∃∗ w200 : BitVec 64, (fsp + 200#64) ↦₆₄ w200) ∗
        memRegion (fsp + 208#64) 8 ∗
        (∃∗ w216 : BitVec 64, (fsp + 216#64) ↦₆₄ w216) ∗
        (∃∗ w224 : BitVec 64, (fsp + 224#64) ↦₆₄ w224) ∗
        (∃∗ w232 : BitVec 64, (fsp + 232#64) ↦₆₄ w232) ∗
        memRegion (fsp + 240#64) 656 :=
    split_top <|
      split_step0 (Entails.refl _) <|
      split_step (mem64_entails _) <|
      split_step (Entails.refl _) <|
      split_step (mem64_entails _) <|
      split_step (Entails.refl _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (Entails.refl _) <|
      split_step (mem64_entails _) <|
      split_step (Entails.refl _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      Entails.refl _
  refine Entails.trans h ?_
  dsimp only [v2hs_stack896ScratchRest]
  exact Entails.of_eq (by ac_rfl)

theorem v2hs_memRegion_896_unsplit_scratch (fsp w96 w152 w216 w224 w232 : BitVec 64) :
    ((fsp + 96#64) ↦₆₄ w96) ∗
      ((fsp + 152#64) ↦₆₄ w152) ∗
      memRegion (fsp + 176#64) 8 ∗
      memRegion (fsp + 184#64) 8 ∗
      memRegion (fsp + 200#64) 8 ∗
      ((fsp + 216#64) ↦₆₄ w216) ∗
      ((fsp + 224#64) ↦₆₄ w224) ∗
      ((fsp + 232#64) ↦₆₄ w232) ∗
      memRegion (fsp + 240#64) 656 ∗
      v2hs_stack896ScratchRest fsp ⊢
      memRegion fsp 896 := by
  dsimp only [v2hs_stack896ScratchRest]
  have hcol :
      memRegion fsp 96 ∗ ((fsp + 96#64) ↦₆₄ w96) ∗ memRegion (fsp + 104#64) 48 ∗
      ((fsp + 152#64) ↦₆₄ w152) ∗ memRegion (fsp + 160#64) 16 ∗ memRegion (fsp + 176#64) 8 ∗
      memRegion (fsp + 184#64) 8 ∗ memRegion (fsp + 192#64) 8 ∗ memRegion (fsp + 200#64) 8 ∗
      memRegion (fsp + 208#64) 8 ∗ ((fsp + 216#64) ↦₆₄ w216) ∗ ((fsp + 224#64) ↦₆₄ w224) ∗
      ((fsp + 232#64) ↦₆₄ w232) ∗ memRegion (fsp + 240#64) 656 ⊢
      memRegion fsp 896 :=
    collapse_top <|
      collapse_step0 (Entails.refl _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      Entails.refl _
  exact Entails.trans (Entails.of_eq (by ac_rfl)) hcol

theorem v2hs_merge_240_656_80_736 (fsp : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 : BitVec 64) :
    memRegion (fsp + 240#64) 656 ∗
      v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ⊢
      memRegion (fsp + 240#64) 736 := by
  rw [ProofLib.memRegion_split' (b := fsp + 240#64) (n := 656) (k := 80)
    (b' := fsp + 896#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right (v2hs_ucWordsAt_entails_80 (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80)

/-- When `u8.toNat < 2 ^ 63` and `(u24 == 2400#64) = false`, `+3348..+3396` stores `[sp + 152] := u8`
and `[sp + 96] := u24` and branches to `+4660`. -/
theorem v2hs_validate_err_dk_3348_to_4660
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out d_w0 : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 w96 w152 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hu8 : u8.toNat < 2 ^ 63)
    (hdk : (u24 == 2400#64) = false)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3348#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d_w0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4660#64) s1
      (((s0.sp - 2400#64 + 96#64) ↦₆₄ w96) ∗
        ((s0.sp - 2400#64 + 152#64) ↦₆₄ w152) ∗
        v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢
          ((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗
          ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
          v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗ Rest) ∧
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x0 = u40 ∧
        s2.readReg64 .x9 = u16 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x22 = d_w0 ∧
        s2.readReg64 .x24 = u56 ∧
        s2.readReg64 .x25 = u64 ∧
        s2.readReg64 .x26 = u32 ∧
        TraceCalleeSaved s2 s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hu8_ne := cap_add_one_beq_zero_false hu8
  wp_simp_pre [v2hs_ucWordsAt, arm64_norm, sepConj_assoc]
  states_from_pb_fetches_range b (Rust.withPanics ext) 3348 52
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · dsimp only [v2hs_ucWordsAt]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)
  · wp_done

/-- When `u8.toNat < 2 ^ 63`, `(u24 == 2400#64) = true`, and `u32 = noneCap` (`st.auth = none`),
`+3348..+3404` branches to `+4720`. -/
theorem v2hs_validate_err_auth_3348_to_4720
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out d_w0 : BitVec 64)
    (u8 u16 u24 u40 u48 u56 u64 u72 u80 w96 w152 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hu8 : u8.toNat < 2 ^ 63)
    (hdk : (u24 == 2400#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3348#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d_w0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4720#64) s1
      (((s0.sp - 2400#64 + 96#64) ↦₆₄ w96) ∗
        ((s0.sp - 2400#64 + 152#64) ↦₆₄ w152) ∗
        v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64)
          u8 u16 u24 noneCap u40 u48 u56 u64 u72 u80 ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢
          ((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗
          ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
          v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64)
            u8 u16 u24 noneCap u40 u48 u56 u64 u72 u80 ∗ Rest) ∧
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x9 = u16 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x22 = d_w0 ∧
        TraceCalleeSaved s2 s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hu8_ne := cap_add_one_beq_zero_false hu8
  wp_simp_pre [v2hs_ucWordsAt, noneCap, arm64_norm, sepConj_assoc]
  states_from_pb_fetches_range b (Rust.withPanics ext) 3348 60
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · dsimp only [v2hs_ucWordsAt, noneCap]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)
  · wp_done

/-- Validation success step (`+3348 -> +3436`): when `u8.toNat < 2 ^ 63`, `(u24 == 2400#64) = true`,
and `u32.toNat < 2 ^ 63`, stores stack slots `96, 152, 176, 200, 216, 224, 232` and collapses
`v2hs_ucWordsAt (fsp + 896#64)` into `memRegion (fsp + 240#64) 736`. -/
theorem v2hs_validate_ok_3348_3436
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out d_w0 : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 : BitVec 64)
    (w96 w152 w176 w200 w216 w224 w232 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hu8 : u8.toNat < 2 ^ 63)
    (hdk : (u24 == 2400#64) = true)
    (hu32 : u32.toNat < 2 ^ 63)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3348#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d_w0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3436#64) s1
      (((s0.sp - 2400#64 + 96#64) ↦₆₄ w96) ∗
        ((s0.sp - 2400#64 + 152#64) ↦₆₄ w152) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ w176) ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ w200) ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ w216) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ w224) ∗
        ((s0.sp - 2400#64 + 232#64) ↦₆₄ w232) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 656 ∗
        v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        Rest)
      (fun s2 P2 =>
        (P2 ⊢
          ((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗
          ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
          ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
          ((s0.sp - 2400#64 + 200#64) ↦₆₄ u48) ∗
          ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
          ((s0.sp - 2400#64 + 224#64) ↦₆₄ u80) ∗
          ((s0.sp - 2400#64 + 232#64) ↦₆₄ u72) ∗
          memRegion (s0.sp - 2400#64 + 240#64) 736 ∗
          Rest) ∧
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x0 = u40 ∧
        s2.readReg64 .x8 = u72 ∧
        s2.readReg64 .x9 = u16 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x20 = u48 ∧
        s2.readReg64 .x21 = s1.readReg64 .x21 ∧
        s2.readReg64 .x22 = d_w0 ∧
        s2.readReg64 .x24 = u56 ∧
        s2.readReg64 .x25 = u64 ∧
        s2.readReg64 .x26 = u32 ∧
        s2.readReg64 .x27 = s1.readReg64 .x27 ∧
        s2.readReg64 .x28 = u80 ∧
        TraceCalleeSaved s2 s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hu8_ne := cap_add_one_beq_zero_false hu8
  have hu32_ne := cap_add_one_beq_zero_false hu32
  have hmerge := v2hs_merge_240_656_80_736 (s0.sp - 2400#64)
    u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
  dsimp only [v2hs_ucWordsAt] at hmerge
  simp only [arm64_norm, sepConj_assoc] at hmerge
  wp_simp_pre [v2hs_ucWordsAt, arm64_norm, sepConj_assoc]
  states_from_pb_fetches_range b (Rust.withPanics ext) 3348 88
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · simp only [arm64_norm]
    refine Entails.trans (Entails.of_eq (show _ =
      (memRegion (s0.sp - 2160#64) 656 ∗
       (((s0.sp - 1504#64) ↦₆₄ u8) ∗
        ((s0.sp - 1496#64) ↦₆₄ u16) ∗
        ((s0.sp - 1488#64) ↦₆₄ u24) ∗
        ((s0.sp - 1480#64) ↦₆₄ u32) ∗
        ((s0.sp - 1472#64) ↦₆₄ u40) ∗
        ((s0.sp - 1464#64) ↦₆₄ u48) ∗
        ((s0.sp - 1456#64) ↦₆₄ u56) ∗
        ((s0.sp - 1448#64) ↦₆₄ u64) ∗
        ((s0.sp - 1440#64) ↦₆₄ u72) ∗
        ((s0.sp - 1432#64) ↦₆₄ u80))) ∗
      (((s0.sp - 2304#64) ↦₆₄ u24) ∗
       ((s0.sp - 2248#64) ↦₆₄ u8) ∗
       ((s0.sp - 2224#64) ↦₆₄ u16) ∗
       ((s0.sp - 2200#64) ↦₆₄ u48) ∗
       ((s0.sp - 2184#64) ↦₆₄ u40) ∗
       ((s0.sp - 2176#64) ↦₆₄ u80) ∗
       ((s0.sp - 2168#64) ↦₆₄ u72) ∗ Rest) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hmerge) (Entails.of_eq (by ac_rfl))
  · wp_done

/-! ## `Authenticator::from_pb` (`+3436 -> +8700 -> +8884 -> +8944`) & `Unchunked::EkSent` Assembly (`+8944 -> +9036/+9152`) -/

theorem v2hs_pull_alloc_pure (P1 P2 R : SepProp) (φ : Prop) :
    P1 ∗ P2 ∗ ⌜φ⌝ ∗ R = ⌜φ⌝ ∗ (P1 ∗ P2 ∗ R) := by ac_rfl

theorem v2hs_vecU8Payload_of_nil (A : RustAlloc) :
    emp ⊢ vecU8Payload A (BitVec.ofNat 64 ([] : List (BitVec 8)).length) 1#64 [] := by
  unfold vecU8Payload
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.zero_mod,
    Nat.le_refl, true_and, ↓reduceIte]
  exact Entails.pure_right ⟨by decide, by decide⟩ (Entails.refl _)

theorem v2hs_vecU8Payload_pos_unpack (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) :
    vecU8Payload A cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 ∧ cap ≠ 0#64⌝ ∗
      (A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  unfold vecU8Payload
  apply Entails.pure_left; intro ⟨hle, hlt, hptr⟩
  have hcap : cap ≠ 0#64 := cap_ne_zero_of_pos hpos hle
  simp only [hcap, ↓reduceIte]
  exact Entails.pure_right ⟨hle, hlt, hptr, hcap⟩ (Entails.refl _)

theorem v2hs_vecU8Payload_pos_dealloc (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hle : bs.length ≤ cap.toNat) (hlt : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0#64) (hcap : cap ≠ 0#64) :
    A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ⊢
    vecCapPtrDealloc A cap ptr := by
  refine Entails.trans ?_ (vecU8Payload_entails_dealloc A cap ptr bs)
  unfold vecU8Payload
  simp only [hcap, ↓reduceIte]
  exact Entails.pure_right ⟨hle, hlt, hptr⟩ (Entails.refl _)

set_option maxHeartbeats 800000 in
/-- `Authenticator::from_pb` segment (`+3436 -> +8700`) in Variant 2:
    allocates and copies `auth.rootKey` into `pa1 = s1.readReg64 .x23` (or `1#64` if empty). -/
theorem v2hs_auth_from_pb_step1_3436_8700
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s0 s : State) (target_pc fsp out d_w0 : BitVec 64)
    (u32 u40 u56 u64 u80 : BitVec 64)
    (auth : ProtoAuthenticator) (Frame R : SepProp)
    (post : State → SepProp → Prop) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3436#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length)
    (hx22 : s.readReg64 .x22 = d_w0)
    (hx24 : s.readReg64 .x24 = u56)
    (hx25 : s.readReg64 .x25 = u64)
    (hx26 : s.readReg64 .x26 = u32)
    (hx28 : s.readReg64 .x28 = u80)
    (htr : TraceCalleeSaved s s0)
    (hnext : ∀ (pa1 : BitVec 64) (s1 : State),
      s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8700#64 →
      s1.status = .Running →
      (s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧
       s1.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length ∧
       s1.readReg64 .x21 = s.readReg64 .x21 ∧
       s1.readReg64 .x22 = d_w0 ∧ s1.readReg64 .x23 = pa1 ∧
       s1.readReg64 .x24 = u56 ∧ s1.readReg64 .x25 = u64 ∧
       s1.readReg64 .x26 = u32 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
       s1.readReg64 .x28 = u80 ∧
       TraceCalleeSaved s1 s0) →
      SepWPp (tripleRatchetProgAtExt b ext) target_pc s1
        (stackAt fsp encoderFromPbStack ∗
         ((fsp + 216#64) ↦₆₄ u40) ∗
         vecCapPtrDealloc A u32 u40 ∗
         vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
         A.pool ∗ Frame)
        post (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) target_pc s
      (stackAt fsp encoderFromPbStack ∗
       ((fsp + 216#64) ↦₆₄ u40) ∗
       vecU8Payload A u32 u40 auth.rootKey ∗
       A.pool ∗ Frame)
      post (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  have hr_cases : auth.rootKey = [] ∨ 0 < auth.rootKey.length := by cases auth.rootKey <;> simp
  rcases hr_cases with hr_nil | hr_pos
  · refine sepWPp_seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8700#64)
      (P_mid := stackAt fsp encoderFromPbStack ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
        vecCapPtrDealloc A u32 u40 ∗
        vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) 1#64 auth.rootKey ∗ A.pool ∗ Frame)
      (Q_regs := fun s1 => s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧
        s1.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x22 = d_w0 ∧ s1.readReg64 .x23 = 1#64 ∧
        s1.readReg64 .x24 = u56 ∧ s1.readReg64 .x25 = u64 ∧
        s1.readReg64 .x26 = u32 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = u80 ∧
        TraceCalleeSaved s1 s0)
      ?_ (hnext 1#64)
    clear hnext; rw [hr_nil] at hx20 ⊢
    states_from_pb_fetches_range b (Rust.withPanics ext) 3436 4
    states_from_pb_fetches_range b (Rust.withPanics ext) 8696 4
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, List.length_nil, BitVec.ofNat_eq_ofNat] at hpc hx20 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches; wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have hd := vecU8Payload_entails_dealloc A u32 u40 []
      have hn := v2hs_vecU8Payload_of_nil A
      dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hn
      refine Entails.trans (Entails.of_eq (show _ =
        vecU8Payload A u32 u40 [] ∗ emp ∗
        stackAt fsp encoderFromPbStack ∗ ((fsp + 216#64) ↦₆₄ u40) ∗ A.pool ∗ Frame by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hd (sepConj_mono_left hn)) (Entails.of_eq (by ac_rfl))
    · wp_done
  · refine SepWPp.weaken_pre (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (v2hs_vecU8Payload_pos_unpack A u32 u40 auth.rootKey hr_pos)))) ?_
    rw [show stackAt fsp encoderFromPbStack ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
          (⌜auth.rootKey.length ≤ u32.toNat ∧ u32.toNat < 2 ^ 63 ∧
            u40 ≠ 0#64 ∧ u32 ≠ 0#64⌝ ∗
           (A.live u40 u32.toNat 1 ∗ (u40 ↦ₛ auth.rootKey) ∗
            memRegion (u40 + BitVec.ofNat 64 auth.rootKey.length) (u32.toNat - auth.rootKey.length))) ∗
          A.pool ∗ Frame =
        ⌜auth.rootKey.length ≤ u32.toNat ∧ u32.toNat < 2 ^ 63 ∧
          u40 ≠ 0#64 ∧ u32 ≠ 0#64⌝ ∗
        (stackAt fsp encoderFromPbStack ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
         A.live u40 u32.toNat 1 ∗ (u40 ↦ₛ auth.rootKey) ∗
         memRegion (u40 + BitVec.ofNat 64 auth.rootKey.length) (u32.toNat - auth.rootKey.length) ∗
         A.pool ∗ Frame) by ac_rfl]
    refine SepWPp.pure_elim fun ⟨hr_le, hr_cap, hptr0, hcap0_ne⟩ => ?_
    have hr_lt63 : auth.rootKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hr_le hr_cap
    have hr_lt64 : auth.rootKey.length < 2 ^ 64 := by omega
    have hr_toNat : (BitVec.ofNat 64 auth.rootKey.length).toNat = auth.rootKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr_lt64]
    have hr_ne0 : (BitVec.ofNat 64 auth.rootKey.length == 0#64) = false := ofNat_beq_zero_false hr_pos hr_lt64
    have hpow1 : ∃ k : Nat, 1 = 2 ^ k := ⟨0, rfl⟩
    have hr_lay3 : auth.rootKey.length + 1 ≤ 2 ^ 63 := hr_lt63
    have h1_toNat : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [stackAt_encoderFromPb_split_allocHook fsp]; wp_simp_pre [sepConj_assoc]
    have hfn : libsignalSessionCode.fnOff statesFromPbName = 0x54cac := statesFromPb_fnOff
    have hshim := hA.shim_ok_at statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_no_alloc_shim_is_unstable_v2")); simp only [sessionShimSpec] at hshim
    have halloc := hA.alloc_ok_at statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_alloc")); simp only [rustAllocSpec] at halloc
    have hmc := hA.session_memcpy_ok_at statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "memcpy")); simp only [sessionMemcpySpec] at hmc
    have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
      (name := statesFromPbName) (k := (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "alloc::raw_vec::handle_error"))) (by rw [hfn, stubOff_handle_error])
    states_from_pb_fetches_range b (Rust.withPanics ext) 3436 44
    states_from_pb_fetches_range b (Rust.withPanics ext) 11608 12
    dsimp only [contractProg, tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hshim halloc hmc hpanic hpc hnext ⊢
    clear hfn hA
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)) = prog
      reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + 3456#64)
    wp_steps; wp_apply; wp_steps; wp_call halloc (auth.rootKey.length, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom0 : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom0, BitVec.ofNat_eq_ofNat, ↓reduceIte]; rw [v2hs_pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + (bv% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "alloc::raw_vec::handle_error"))); wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [statesFromPbOnPanic, sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom0, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
      have hoom0_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom0
      rw [v2hs_pull_alloc_pure]; refine SepWPp.pure_elim fun ⟨_, htr_alloc⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr_alloc]; simp only [wp_norm, arm64_norm, *]
      refine sepWPp_seq_clean (mid := entry + 8700#64)
        (P_mid := stackAt fsp encoderFromPbStack ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
          vecCapPtrDealloc A u32 u40 ∗
          vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) (sf_1.readReg64 Reg.x0) auth.rootKey ∗
          A.pool ∗ Frame)
        (Q_regs := fun s1 => s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧
          s1.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length ∧
          s1.readReg64 .x21 = s.readReg64 .x21 ∧
          s1.readReg64 .x22 = d_w0 ∧ s1.readReg64 .x23 = sf_1.readReg64 Reg.x0 ∧
          s1.readReg64 .x24 = u56 ∧ s1.readReg64 .x25 = u64 ∧
          s1.readReg64 .x26 = u32 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
          s1.readReg64 .x28 = u80 ∧
          TraceCalleeSaved s1 s0)
        ?_ (hnext (sf_1.readReg64 Reg.x0))
      clear hnext
      have hsp_sf1 : sf_1.sp = fsp := by simp only [wp_norm, arm64_norm, *]
      wp_steps; wp_apply; wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [stackAt_encoderFromPb_split_allocHook fsp, hsp_sf1]
        have hd := v2hs_vecU8Payload_pos_dealloc A u32 u40 auth.rootKey hr_le hr_cap hptr0 hcap0_ne
        have hp := vecU8Payload_pos A (sf_1.readReg64 Reg.x0) auth.rootKey hr_pos hr_lt63 hoom0
        simp only [arm64_norm] at hd hp ⊢
        refine Entails.trans (Entails.of_eq (show _ =
          (A.live u40 u32.toNat 1 ∗ (u40 ↦ₛ auth.rootKey) ∗
           memRegion (u40 + BitVec.ofNat 64 auth.rootKey.length) (u32.toNat - auth.rootKey.length)) ∗
          (A.live (sf_1.readReg64 Reg.x0) auth.rootKey.length 1 ∗ (sf_1.readReg64 Reg.x0 ↦ₛ auth.rootKey)) ∗
          memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack ∗
          ((fsp + 216#64) ↦₆₄ u40) ∗ A.pool ∗ Frame by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono hd (sepConj_mono_left hp)) (Entails.of_eq (by ac_rfl))
      · wp_done

set_option maxHeartbeats 800000 in
/-- `Authenticator::from_pb` segment (`+8700 -> +8884`) in Variant 2:
    allocates and copies `auth.macKey` into `pa2` stored at `[fsp + 184]` (or `1#64` if empty). -/
theorem v2hs_auth_from_pb_step2_8700_8884
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s0 s : State) (target_pc fsp out d_w0 pa1 w184 : BitVec 64)
    (u32 u56 u64 u72 : BitVec 64)
    (auth : ProtoAuthenticator) (Frame R : SepProp)
    (post : State → SepProp → Prop) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8700#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length)
    (hx22 : s.readReg64 .x22 = d_w0)
    (hx23 : s.readReg64 .x23 = pa1)
    (hx24 : s.readReg64 .x24 = u56)
    (hx25 : s.readReg64 .x25 = u64)
    (hx26 : s.readReg64 .x26 = u32)
    (hu72 : u72 = BitVec.ofNat 64 auth.macKey.length)
    (htr : TraceCalleeSaved s s0)
    (hnext : ∀ (pa2 : BitVec 64) (s2 : State),
      s2.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8884#64 →
      s2.status = .Running →
      (s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧
       s2.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length ∧
       s2.readReg64 .x21 = s.readReg64 .x21 ∧
       s2.readReg64 .x22 = d_w0 ∧ s2.readReg64 .x23 = pa1 ∧
       s2.readReg64 .x24 = u56 ∧ s2.readReg64 .x25 = u64 ∧
       s2.readReg64 .x26 = u32 ∧ s2.readReg64 .x27 = s.readReg64 .x27 ∧
       TraceCalleeSaved s2 s0) →
      SepWPp (tripleRatchetProgAtExt b ext) target_pc s2
        (stackAt fsp encoderFromPbStack ∗
         ((fsp + 184#64) ↦₆₄ pa2) ∗
         ((fsp + 232#64) ↦₆₄ u72) ∗
         vecCapPtrDealloc A u56 u64 ∗
         vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
         A.pool ∗ Frame)
        post (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) target_pc s
      (stackAt fsp encoderFromPbStack ∗
       ((fsp + 184#64) ↦₆₄ w184) ∗
       ((fsp + 232#64) ↦₆₄ u72) ∗
       vecU8Payload A u56 u64 auth.macKey ∗
       A.pool ∗ Frame)
      post (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  have hm_cases : auth.macKey = [] ∨ 0 < auth.macKey.length := by cases auth.macKey <;> simp
  rcases hm_cases with hm_nil | hm_pos
  · refine sepWPp_seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8884#64)
      (P_mid := stackAt fsp encoderFromPbStack ∗ ((fsp + 184#64) ↦₆₄ 1#64) ∗
        ((fsp + 232#64) ↦₆₄ u72) ∗ vecCapPtrDealloc A u56 u64 ∗
        vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) 1#64 auth.macKey ∗ A.pool ∗ Frame)
      (Q_regs := fun s2 => s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧
        s2.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length ∧
        s2.readReg64 .x21 = s.readReg64 .x21 ∧
        s2.readReg64 .x22 = d_w0 ∧ s2.readReg64 .x23 = pa1 ∧
        s2.readReg64 .x24 = u56 ∧ s2.readReg64 .x25 = u64 ∧
        s2.readReg64 .x26 = u32 ∧ s2.readReg64 .x27 = s.readReg64 .x27 ∧
        TraceCalleeSaved s2 s0)
      ?_ (hnext 1#64)
    clear hnext; subst hu72; rw [hm_nil]
    states_from_pb_fetches_range b (Rust.withPanics ext) 8700 8
    states_from_pb_fetches_range b (Rust.withPanics ext) 8876 8
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, List.length_nil, BitVec.ofNat_eq_ofNat] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches; wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have hd := vecU8Payload_entails_dealloc A u56 u64 []
      have hn := v2hs_vecU8Payload_of_nil A
      dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hn
      refine Entails.trans (Entails.of_eq (show _ =
        vecU8Payload A u56 u64 [] ∗ emp ∗
        stackAt fsp encoderFromPbStack ∗ ((fsp + 184#64) ↦₆₄ 1#64) ∗
        ((fsp + 232#64) ↦₆₄ 0#64) ∗ A.pool ∗ Frame by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hd (sepConj_mono_left hn)) (Entails.of_eq (by ac_rfl))
    · wp_done
  · subst hu72
    refine SepWPp.weaken_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (v2hs_vecU8Payload_pos_unpack A u56 u64 auth.macKey hm_pos))))) ?_
    rw [show stackAt fsp encoderFromPbStack ∗ ((fsp + 184#64) ↦₆₄ w184) ∗
          ((fsp + 232#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
          (⌜auth.macKey.length ≤ u56.toNat ∧ u56.toNat < 2 ^ 63 ∧
            u64 ≠ 0#64 ∧ u56 ≠ 0#64⌝ ∗
           (A.live u64 u56.toNat 1 ∗ (u64 ↦ₛ auth.macKey) ∗
            memRegion (u64 + BitVec.ofNat 64 auth.macKey.length) (u56.toNat - auth.macKey.length))) ∗
          A.pool ∗ Frame =
        ⌜auth.macKey.length ≤ u56.toNat ∧ u56.toNat < 2 ^ 63 ∧
          u64 ≠ 0#64 ∧ u56 ≠ 0#64⌝ ∗
        (stackAt fsp encoderFromPbStack ∗ ((fsp + 184#64) ↦₆₄ w184) ∗
         ((fsp + 232#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
         A.live u64 u56.toNat 1 ∗ (u64 ↦ₛ auth.macKey) ∗
         memRegion (u64 + BitVec.ofNat 64 auth.macKey.length) (u56.toNat - auth.macKey.length) ∗
         A.pool ∗ Frame) by ac_rfl]
    refine SepWPp.pure_elim fun ⟨hm_le, hm_cap, hptr1, hcap1_ne⟩ => ?_
    have hm_lt63 : auth.macKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hm_le hm_cap
    have hm_lt64 : auth.macKey.length < 2 ^ 64 := by omega
    have hm_toNat : (BitVec.ofNat 64 auth.macKey.length).toNat = auth.macKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm_lt64]
    have hm_ne0 : (BitVec.ofNat 64 auth.macKey.length == 0#64) = false := ofNat_beq_zero_false hm_pos hm_lt64
    have hpow1 : ∃ k : Nat, 1 = 2 ^ k := ⟨0, rfl⟩
    have hm_lay3 : auth.macKey.length + 1 ≤ 2 ^ 63 := hm_lt63
    have h1_toNat : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [stackAt_encoderFromPb_split_allocHook fsp]; wp_simp_pre [sepConj_assoc]
    have hfn : libsignalSessionCode.fnOff statesFromPbName = 0x54cac := statesFromPb_fnOff
    have hshim := hA.shim_ok_at statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_no_alloc_shim_is_unstable_v2")); simp only [sessionShimSpec] at hshim
    have halloc := hA.alloc_ok_at statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_alloc")); simp only [rustAllocSpec] at halloc
    have hmc := hA.session_memcpy_ok_at statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "memcpy")); simp only [sessionMemcpySpec] at hmc
    have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
      (name := statesFromPbName) (k := (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "alloc::raw_vec::handle_error"))) (by rw [hfn, stubOff_handle_error])
    states_from_pb_fetches_range b (Rust.withPanics ext) 8700 48
    states_from_pb_fetches_range b (Rust.withPanics ext) 11572 12
    dsimp only [contractProg, tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hshim halloc hmc hpanic hpc hnext ⊢
    clear hfn hA
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)) = prog
      reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + 8724#64)
    wp_steps; wp_apply; wp_steps; wp_call halloc (auth.macKey.length, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom1 : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom1, BitVec.ofNat_eq_ofNat, ↓reduceIte]; rw [v2hs_pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + (bv% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "alloc::raw_vec::handle_error"))); wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [statesFromPbOnPanic, sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom1, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
      have hoom1_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom1
      rw [v2hs_pull_alloc_pure]; refine SepWPp.pure_elim fun ⟨_, htr_alloc⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr_alloc]; simp only [wp_norm, arm64_norm, *]
      refine sepWPp_seq_clean (mid := entry + 8884#64)
        (P_mid := stackAt fsp encoderFromPbStack ∗ ((fsp + 184#64) ↦₆₄ sf_1.readReg64 Reg.x0) ∗
          ((fsp + 232#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
          vecCapPtrDealloc A u56 u64 ∗
          vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) (sf_1.readReg64 Reg.x0) auth.macKey ∗
          A.pool ∗ Frame)
        (Q_regs := fun s2 => s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧
          s2.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length ∧
          s2.readReg64 .x21 = s.readReg64 .x21 ∧
          s2.readReg64 .x22 = d_w0 ∧ s2.readReg64 .x23 = pa1 ∧
          s2.readReg64 .x24 = u56 ∧ s2.readReg64 .x25 = u64 ∧
          s2.readReg64 .x26 = u32 ∧ s2.readReg64 .x27 = s.readReg64 .x27 ∧
          TraceCalleeSaved s2 s0)
        ?_ (hnext (sf_1.readReg64 Reg.x0))
      clear hnext
      have hsp_sf1 : sf_1.sp = fsp := by simp only [wp_norm, arm64_norm, *]
      wp_steps; wp_apply; wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [stackAt_encoderFromPb_split_allocHook fsp, hsp_sf1]
        have hd := v2hs_vecU8Payload_pos_dealloc A u56 u64 auth.macKey hm_le hm_cap hptr1 hcap1_ne
        have hp := vecU8Payload_pos A (sf_1.readReg64 Reg.x0) auth.macKey hm_pos hm_lt63 hoom1
        simp only [arm64_norm] at hd hp ⊢
        refine Entails.trans (Entails.of_eq (show _ =
          (A.live u64 u56.toNat 1 ∗ (u64 ↦ₛ auth.macKey) ∗
           memRegion (u64 + BitVec.ofNat 64 auth.macKey.length) (u56.toNat - auth.macKey.length)) ∗
          (A.live (sf_1.readReg64 Reg.x0) auth.macKey.length 1 ∗ (sf_1.readReg64 Reg.x0 ↦ₛ auth.macKey)) ∗
          memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack ∗
          ((fsp + 184#64) ↦₆₄ sf_1.readReg64 Reg.x0) ∗
          ((fsp + 232#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗ A.pool ∗ Frame by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono hd (sepConj_mono_left hp)) (Entails.of_eq (by ac_rfl))
      · wp_done

/-- `Authenticator::from_pb` segment (`+8884 -> +8944`) in Variant 2:
    deallocates `auth.rootKey` and `auth.macKey` protobuf buffers and loads `x25 = u48`, `x26 = pa1 >>> 8`, `x28 = u80`. -/
theorem v2hs_auth_from_pb_step3_8884_8944
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s0 s : State) (out d_w0 pa1 : BitVec 64)
    (u32 u40 u56 u64 u80 : BitVec 64)
    (auth : ProtoAuthenticator) (Rest : SepProp)
    (hr_lt63 : auth.rootKey.length < 2 ^ 63)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8884#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx22 : s.readReg64 .x22 = d_w0)
    (hx23 : s.readReg64 .x23 = pa1)
    (hx24 : s.readReg64 .x24 = u56)
    (hx25 : s.readReg64 .x25 = u64)
    (hx26 : s.readReg64 .x26 = u32)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8944#64) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u80) ∗
        vecCapPtrDealloc A u32 u40 ∗
        vecCapPtrDealloc A u56 u64 ∗
        A.pool ∗
        Rest)
      (fun s3 P3 =>
        (P3 ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          ((s0.sp - 2400#64 + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
          ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
          ((s0.sp - 2400#64 + 224#64) ↦₆₄ u80) ∗
          A.pool ∗
          Rest) ∧
        s3.sp = s0.sp - 2400#64 ∧
        s3.readReg64 .x19 = out ∧
        s3.readReg64 .x21 = s.readReg64 .x21 ∧
        s3.readReg64 .x22 = d_w0 ∧
        s3.readReg64 .x23 = pa1 ∧
        s3.readReg64 .x25 = BitVec.ofNat 64 auth.rootKey.length ∧
        s3.readReg64 .x26 = pa1 >>> 8 ∧
        s3.readReg64 .x27 = s.readReg64 .x27 ∧
        s3.readReg64 .x28 = u80 ∧
        TraceCalleeSaved s3 s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hr_toNat : (BitVec.ofNat 64 auth.rootKey.length).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hr_lt63
  have hcmn : ¬((BitVec.ofNat 64 auth.rootKey.length + 1#64 == 0#64) = true) :=
    cap_add_one_beq_zero_false hr_toNat
  have hdealloc := v4_sub_ok_dealloc_125316 (b := b) (A := A) (ext := ext) hA
  simp only [rustDeallocSpec] at hdealloc
  rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
  wp_simp_pre [arm64_norm, sepConj_assoc]
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8912#64)
    (P_mid :=
      memRegion (s0.sp - 7552#64) 1056 ∗
      stackAt (s0.sp - 2400#64) allocHookStack ∗
      ((s0.sp - 2200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
      ((s0.sp - 2184#64) ↦₆₄ u40) ∗
      ((s0.sp - 2176#64) ↦₆₄ u80) ∗
      vecCapPtrDealloc A u56 u64 ∗
      A.pool ∗
      Rest)
    (Q := fun s2 =>
      s2.sp = s0.sp - 2400#64 ∧
      s2.readReg64 .x19 = out ∧
      s2.readReg64 .x21 = s.readReg64 .x21 ∧
      s2.readReg64 .x22 = d_w0 ∧
      s2.readReg64 .x23 = pa1 ∧
      s2.readReg64 .x24 = u56 ∧
      s2.readReg64 .x25 = u64 ∧
      s2.readReg64 .x26 = pa1 >>> 8 ∧
      s2.readReg64 .x27 = s.readReg64 .x27 ∧
      s2.readReg64 .x28 = u80 ∧
      TraceCalleeSaved s2 s0)
    ?_ ?_
  · states_from_pb_fetches_range b (Rust.withPanics ext) 8884 28
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, vecCapPtrDealloc,
      BitVec.ofNat_eq_ofNat] at hdealloc hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    by_cases hc_r : (u32 == 0#64) = true <;>
      simp only [hc_r, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; refine EncoderFromPb.align_pre (Entails.of_eq (by ac_rfl)) ?_; wp_done
    · wp_steps; wp_apply; wp_steps
      refine EncoderFromPb.align_pre (by rw [hsp]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, htr2⟩
    states_from_pb_fetches_range b (Rust.withPanics ext) 8912 32
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, vecCapPtrDealloc,
      BitVec.ofNat_eq_ofNat] at hdealloc hpc2 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    by_cases hc_m : (u56 == 0#64) = true <;>
      simp only [hc_m, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)
      · wp_done
    · wp_steps; wp_apply; wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [hsp2]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)
      · wp_done

/-- Ten 64-bit words (`80` bytes) of `Unchunked.SendEk.EkSent` at `a` (`fsp + 1264#64`). -/
def v2hs_ekSentWordsAt (a u48 pa1 u72 pa2 u8 u16 u24 u80 : BitVec 64) : SepProp :=
  (a ↦₆₄ u48) ∗ ((a + 8#64) ↦₆₄ pa1) ∗ ((a + 16#64) ↦₆₄ u48) ∗
  ((a + 24#64) ↦₆₄ u72) ∗ ((a + 32#64) ↦₆₄ pa2) ∗ ((a + 40#64) ↦₆₄ u72) ∗
  ((a + 48#64) ↦₆₄ u8) ∗ ((a + 56#64) ↦₆₄ u16) ∗ ((a + 64#64) ↦₆₄ u24) ∗
  ((a + 72#64) ↦₆₄ u80)

theorem v2hs_reconstruct_pa1 (sp0 pa1 : BitVec 64) :
    ((sp0 - 1128#64) ↦₈ BitVec.zeroExtend 8 pa1) ∗
      ((sp0 - 1127#64) ↦₃₂ BitVec.truncate 32 (pa1 >>> 8)) ∗
      ((sp0 - 1123#64) ↦₁₆ BitVec.truncate 16 (BitVec.truncate 32 (pa1 >>> 40))) ∗
      ((sp0 - 1121#64) ↦₈ BitVec.zeroExtend 8 (pa1 >>> 56)) ⊢
      ((sp0 - 1128#64) ↦₆₄ pa1) := by
  have h0 : BitVec.zeroExtend 8 pa1 = pa1.extractLsb' 0 8 := by bv_kernel
  have h1 : BitVec.truncate 32 (pa1 >>> 8) = pa1.extractLsb' 8 32 := by bv_kernel
  have h2 : BitVec.truncate 16 (BitVec.truncate 32 (pa1 >>> 40)) = pa1.extractLsb' 40 16 := by bv_kernel
  have h3 : BitVec.zeroExtend 8 (pa1 >>> 56) = pa1.extractLsb' 56 8 := by bv_kernel
  have ha1 : sp0 - 1128#64 + 1#64 = sp0 - 1127#64 := by bv_omega
  have ha5 : sp0 - 1128#64 + 5#64 = sp0 - 1123#64 := by bv_omega
  have ha7 : sp0 - 1128#64 + 7#64 = sp0 - 1121#64 := by bv_omega
  rw [h0, h1, h2, h3, ← ha1, ← ha5, ← ha7, ← v10_pointsTo64_split_1_4_2_1 (sp0 - 1128#64) pa1]
  exact Entails.refl _

theorem v2hs_memRegion_1232_split_1264 (fsp : BitVec 64) :
    memRegion (fsp + 1072#64) 1232 ⊢
      memRegion (fsp + 1072#64) 192 ∗
      (∃∗ e0 : BitVec 64, (fsp + 1264#64) ↦₆₄ e0) ∗ (∃∗ e1 : BitVec 64, (fsp + 1272#64) ↦₆₄ e1) ∗
      (∃∗ e2 : BitVec 64, (fsp + 1280#64) ↦₆₄ e2) ∗ (∃∗ e3 : BitVec 64, (fsp + 1288#64) ↦₆₄ e3) ∗
      (∃∗ e4 : BitVec 64, (fsp + 1296#64) ↦₆₄ e4) ∗ (∃∗ e5 : BitVec 64, (fsp + 1304#64) ↦₆₄ e5) ∗
      (∃∗ e6 : BitVec 64, (fsp + 1312#64) ↦₆₄ e6) ∗ (∃∗ e7 : BitVec 64, (fsp + 1320#64) ↦₆₄ e7) ∗
      (∃∗ e8 : BitVec 64, (fsp + 1328#64) ↦₆₄ e8) ∗ (∃∗ e9 : BitVec 64, (fsp + 1336#64) ↦₆₄ e9) ∗
      memRegion (fsp + 1344#64) 960 := by
  have h : ∀ b : BitVec 64, memRegion b 1232 ⊢
      memRegion b 192 ∗ (∃∗ e0 : BitVec 64, (b + 192#64) ↦₆₄ e0) ∗
      (∃∗ e1 : BitVec 64, (b + 200#64) ↦₆₄ e1) ∗ (∃∗ e2 : BitVec 64, (b + 208#64) ↦₆₄ e2) ∗
      (∃∗ e3 : BitVec 64, (b + 216#64) ↦₆₄ e3) ∗ (∃∗ e4 : BitVec 64, (b + 224#64) ↦₆₄ e4) ∗
      (∃∗ e5 : BitVec 64, (b + 232#64) ↦₆₄ e5) ∗ (∃∗ e6 : BitVec 64, (b + 240#64) ↦₆₄ e6) ∗
      (∃∗ e7 : BitVec 64, (b + 248#64) ↦₆₄ e7) ∗ (∃∗ e8 : BitVec 64, (b + 256#64) ↦₆₄ e8) ∗
      (∃∗ e9 : BitVec 64, (b + 264#64) ↦₆₄ e9) ∗ memRegion (b + 272#64) 960 := fun b =>
    split_top <|
      split_step0 (Entails.refl _) <|
      split_step (mem64_entails _) <| split_step (mem64_entails _) <|
      split_step (mem64_entails _) <| split_step (mem64_entails _) <|
      split_step (mem64_entails _) <| split_step (mem64_entails _) <|
      split_step (mem64_entails _) <| split_step (mem64_entails _) <|
      split_step (mem64_entails _) <| split_step (mem64_entails _) <|
      Entails.refl _
  simpa only [v2hs_bv_add_add_lit, BitVec.ofNat_eq_ofNat, sepConj_assoc] using h (fsp + 1072#64)

/-- Assembly of `Unchunked::EkSent` at `fsp + 1264..1344` (`+8944 -> +9036` if `w0 + 1 != 0`,
or `+9152` if `w0 + 1 == 0`). -/
theorem v2hs_assemble_ekSent_8944_9032
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (out d_w0 pa1 pa2 : BitVec 64)
    (u8 u16 u24 u48 u72 u80 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8944#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out) (hx22 : s.readReg64 .x22 = d_w0)
    (hx23 : s.readReg64 .x23 = pa1) (hx25 : s.readReg64 .x25 = u48)
    (hx26 : s.readReg64 .x26 = pa1 >>> 8) (hx28 : s.readReg64 .x28 = u80)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      (if (w0 + 1#64 == 0#64) = true
       then (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9152#64
       else (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9036#64)
      s
      (((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗
        ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        ((s0.sp - 2400#64 + 232#64) ↦₆₄ u72) ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          ((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗
          ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
          ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
          ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
          ((s0.sp - 2400#64 + 232#64) ↦₆₄ u72) ∗
          v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
          memRegion (s0.sp - 2400#64 + 1072#64) 192 ∗
          v2hs_ekSentWordsAt (s0.sp - 2400#64 + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
          memRegion (s0.sp - 2400#64 + 1344#64) 960 ∗
          Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x0 = pa2 ∧
        sm.readReg64 .x8 = w0 ∧
        sm.readReg64 .x9 = u24 ∧
        sm.readReg64 .x10 = (s0.sp - 2400#64) + 1264#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = s.readReg64 .x21 ∧
        sm.readReg64 .x22 = d_w0 ∧
        sm.readReg64 .x23 = pa1 ∧
        sm.readReg64 .x25 = u48 ∧
        sm.readReg64 .x26 = u8 ∧
        sm.readReg64 .x27 = s.readReg64 .x27 ∧
        sm.readReg64 .x28 = u80 ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hpre_split :
      ((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗ ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗ ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        ((s0.sp - 2400#64 + 232#64) ↦₆₄ u72) ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗ Rest ⊢
      (memRegion (s0.sp - 2400#64 + 1072#64) 192 ∗
        (∃∗ e0 : BitVec 64, (s0.sp - 2400#64 + 1264#64) ↦₆₄ e0) ∗
        (∃∗ e1 : BitVec 64, (s0.sp - 2400#64 + 1272#64) ↦₆₄ e1) ∗
        (∃∗ e2 : BitVec 64, (s0.sp - 2400#64 + 1280#64) ↦₆₄ e2) ∗
        (∃∗ e3 : BitVec 64, (s0.sp - 2400#64 + 1288#64) ↦₆₄ e3) ∗
        (∃∗ e4 : BitVec 64, (s0.sp - 2400#64 + 1296#64) ↦₆₄ e4) ∗
        (∃∗ e5 : BitVec 64, (s0.sp - 2400#64 + 1304#64) ↦₆₄ e5) ∗
        (∃∗ e6 : BitVec 64, (s0.sp - 2400#64 + 1312#64) ↦₆₄ e6) ∗
        (∃∗ e7 : BitVec 64, (s0.sp - 2400#64 + 1320#64) ↦₆₄ e7) ∗
        (∃∗ e8 : BitVec 64, (s0.sp - 2400#64 + 1328#64) ↦₆₄ e8) ∗
        (∃∗ e9 : BitVec 64, (s0.sp - 2400#64 + 1336#64) ↦₆₄ e9) ∗
        memRegion (s0.sp - 2400#64 + 1344#64) 960) ∗
      (((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗ ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗ ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        ((s0.sp - 2400#64 + 232#64) ↦₆₄ u72) ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        Rest) := by
    refine Entails.trans (Entails.of_eq (by ac_rfl))
      (sepConj_mono_left (v2hs_memRegion_1232_split_1264 (s0.sp - 2400#64)))
  refine SepWP.weaken_pre hpre_split ?_; clear hpre_split
  wp_simp_pre [v1_optProtoPolyEncoderWordsAt, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro e9
  apply ProofLib.SepWP.exists_left; intro e8
  apply ProofLib.SepWP.exists_left; intro e7
  apply ProofLib.SepWP.exists_left; intro e6
  apply ProofLib.SepWP.exists_left; intro e5
  apply ProofLib.SepWP.exists_left; intro e4
  apply ProofLib.SepWP.exists_left; intro e3
  apply ProofLib.SepWP.exists_left; intro e2
  apply ProofLib.SepWP.exists_left; intro e1
  apply ProofLib.SepWP.exists_left; intro e0
  rw [v10_pointsTo64_split_1_4_2_1 (s0.sp - 2400#64 + 1272#64) e1]
  wp_simp_pre [arm64_norm, sepConj_assoc]
  have hrec := v2hs_reconstruct_pa1 s0.sp pa1
  states_from_pb_fetches_range b (Rust.withPanics ext) 8944 92
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  by_cases hw0 : (w0 + 1#64 == 0#64) = true <;>
    simp only [hw0, Bool.false_eq_true, ↓reduceIte]
  · wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · dsimp only [v1_optProtoPolyEncoderWordsAt, v2hs_ekSentWordsAt]
      simp only [arm64_norm]
      refine Entails.trans (Entails.of_eq (show _ =
        (((s0.sp - 1128#64) ↦₈ BitVec.zeroExtend 8 pa1) ∗
         ((s0.sp - 1127#64) ↦₃₂ BitVec.truncate 32 (pa1 >>> 8)) ∗
         ((s0.sp - 1123#64) ↦₁₆ BitVec.truncate 16 (BitVec.truncate 32 (pa1 >>> 40))) ∗
         ((s0.sp - 1121#64) ↦₈ BitVec.zeroExtend 8 (pa1 >>> 56))) ∗
        (((s0.sp - 2304#64) ↦₆₄ u24) ∗ ((s0.sp - 2248#64) ↦₆₄ u8) ∗
         ((s0.sp - 2224#64) ↦₆₄ u16) ∗ ((s0.sp - 2216#64) ↦₆₄ pa2) ∗
         ((s0.sp - 2168#64) ↦₆₄ u72) ∗ ((s0.sp - 1424#64) ↦₆₄ w0) ∗
         ((s0.sp - 1416#64) ↦₆₄ w8) ∗ ((s0.sp - 1408#64) ↦₆₄ w16) ∗
         ((s0.sp - 1400#64) ↦₆₄ w24) ∗ ((s0.sp - 1392#64) ↦₆₄ w32) ∗
         ((s0.sp - 1384#64) ↦₆₄ w40) ∗ ((s0.sp - 1376#64) ↦₆₄ w48) ∗
         memRegion (s0.sp - 1328#64) 192 ∗ ((s0.sp - 1136#64) ↦₆₄ u48) ∗
         ((s0.sp - 1120#64) ↦₆₄ u48) ∗ ((s0.sp - 1112#64) ↦₆₄ u72) ∗
         ((s0.sp - 1104#64) ↦₆₄ pa2) ∗ ((s0.sp - 1096#64) ↦₆₄ u72) ∗
         ((s0.sp - 1088#64) ↦₆₄ u8) ∗ ((s0.sp - 1080#64) ↦₆₄ u16) ∗
         ((s0.sp - 1072#64) ↦₆₄ u24) ∗ ((s0.sp - 1064#64) ↦₆₄ u80) ∗
         memRegion (s0.sp - 1056#64) 960 ∗ Rest) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hrec) (Entails.of_eq (by ac_rfl))
    · wp_done
  · wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · dsimp only [v1_optProtoPolyEncoderWordsAt, v2hs_ekSentWordsAt]
      simp only [arm64_norm]
      refine Entails.trans (Entails.of_eq (show _ =
        (((s0.sp - 1128#64) ↦₈ BitVec.zeroExtend 8 pa1) ∗
         ((s0.sp - 1127#64) ↦₃₂ BitVec.truncate 32 (pa1 >>> 8)) ∗
         ((s0.sp - 1123#64) ↦₁₆ BitVec.truncate 16 (BitVec.truncate 32 (pa1 >>> 40))) ∗
         ((s0.sp - 1121#64) ↦₈ BitVec.zeroExtend 8 (pa1 >>> 56))) ∗
        (((s0.sp - 2304#64) ↦₆₄ u24) ∗ ((s0.sp - 2248#64) ↦₆₄ u8) ∗
         ((s0.sp - 2224#64) ↦₆₄ u16) ∗ ((s0.sp - 2216#64) ↦₆₄ pa2) ∗
         ((s0.sp - 2168#64) ↦₆₄ u72) ∗ ((s0.sp - 1424#64) ↦₆₄ w0) ∗
         ((s0.sp - 1416#64) ↦₆₄ w8) ∗ ((s0.sp - 1408#64) ↦₆₄ w16) ∗
         ((s0.sp - 1400#64) ↦₆₄ w24) ∗ ((s0.sp - 1392#64) ↦₆₄ w32) ∗
         ((s0.sp - 1384#64) ↦₆₄ w40) ∗ ((s0.sp - 1376#64) ↦₆₄ w48) ∗
         memRegion (s0.sp - 1328#64) 192 ∗ ((s0.sp - 1136#64) ↦₆₄ u48) ∗
         ((s0.sp - 1120#64) ↦₆₄ u48) ∗ ((s0.sp - 1112#64) ↦₆₄ u72) ∗
         ((s0.sp - 1104#64) ↦₆₄ pa2) ∗ ((s0.sp - 1096#64) ↦₆₄ u72) ∗
         ((s0.sp - 1088#64) ↦₆₄ u8) ∗ ((s0.sp - 1080#64) ↦₆₄ u16) ∗
         ((s0.sp - 1072#64) ↦₆₄ u24) ∗ ((s0.sp - 1064#64) ↦₆₄ u80) ∗
         memRegion (s0.sp - 1056#64) 960 ∗ Rest) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hrec) (Entails.of_eq (by ac_rfl))
    · wp_done

end CryptoVerification.SpqrV1.States.FromPb

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2d
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1b
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 1 (`KeysSampled`, `+1104`) — Part E

**Checked by Lean.**

`<PolyEncoder>::from_pb` call (`+4096`), result dispatch (`+4100`), `Ok` staging (`+6568 -> +8180`),
and shared epilogue composition for `InnerState.keysSampled`.
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

attribute [local simp, local arm64_norm, local wp_norm]
  v1_bv_add_add_lit v1_bv_sub_sub_lit

@[local simp, local arm64_norm, local wp_norm]
theorem v1_x25_add_189 (fsp : BitVec 64) :
    (fsp + 1792#64) + 189#64 = fsp + 1981#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v1_x25_add_189_sext (fsp : BitVec 64) :
    (fsp + 1792#64) + (189#64).signExtend 64 = fsp + 1981#64 := by bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v1_x25_add_233 (fsp : BitVec 64) :
    (fsp + 1792#64) + 233#64 = fsp + 2025#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v1_x25_add_233_sext (fsp : BitVec 64) :
    (fsp + 1792#64) + (233#64).signExtend 64 = fsp + 2025#64 := by bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v1_x11_add_185 (fsp : BitVec 64) :
    (fsp + 1792#64) + 185#64 = fsp + 1977#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v1_x11_add_185_sext (fsp : BitVec 64) :
    (fsp + 1792#64) + (185#64).signExtend 64 = fsp + 1977#64 := by bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v1_x11_add_209 (fsp : BitVec 64) :
    (fsp + 1792#64) + 209#64 = fsp + 2001#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v1_x11_add_209_sext (fsp : BitVec 64) :
    (fsp + 1792#64) + (209#64).signExtend 64 = fsp + 2001#64 := by bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v1_x23_add_39 (fsp : BitVec 64) :
    (fsp + 848#64) + 39#64 = fsp + 887#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v1_x23_add_39_sext (fsp : BitVec 64) :
    (fsp + 848#64) + (39#64).signExtend 64 = fsp + 887#64 := by bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v1_x23_add_15 (fsp : BitVec 64) :
    (fsp + 848#64) + 15#64 = fsp + 863#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v1_x23_add_15_sext (fsp : BitVec 64) :
    (fsp + 848#64) + (15#64).signExtend 64 = fsp + 863#64 := by bv_kernel

theorem v1_fsp_880_realign_64_rest (fsp w880 w888 : BitVec 64) (Rest : SepProp) :
    ((fsp + 880#64) ↦₆₄ w880) ∗ ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 w888) ∗ Rest =
      ((fsp + 880#64) ↦ₛ EncoderFromPb.loBytes7 w880) ∗
      ((fsp + 887#64) ↦₆₄ overlapWord7 w880 w888) ∗ Rest := by
  have h := pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (fsp + 880#64) w880 w888
  have ha7 : (fsp + 880#64) + 7#64 = fsp + 887#64 := by bv_omega
  have ha8 : (fsp + 880#64) + 8#64 = fsp + 888#64 := by bv_omega
  rw [ha7, ha8] at h
  rw [← sepConj_assoc, h, sepConj_assoc]

theorem v1_onPanic_shift {s0 sm : State} (htrace : TraceCalleeSaved sm s0)
    (sf : State) {F : SepProp} :
    encoderFromPbOnPanic sm sf ∗ F ⊢
      statesFromPbOnPanic s0 sf := by
  dsimp only [encoderFromPbOnPanic, statesFromPbOnPanic]
  rw [sepConj_assoc]
  apply Entails.pure_left; intro ⟨haf, hpref⟩
  unfold allocFailedIn at haf ⊢
  rw [htrace.1] at haf hpref
  exact Entails.pure_right ⟨haf, hpref⟩ (entails_anyHeap _)

/-- Call `<PolyEncoder>::from_pb` at `+4096` (`bl +28900`), propagating `encoderFromPbOnPanic`
    into `statesFromPbOnPanic s0`. -/
theorem v1_encoder_call_4096
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (henc : EncoderFromPbOkExt b A ext)
    (s0 s : State) (target_pc fsp out pbA u8 u32 u72 : BitVec 64)
    (pbEnc : ProtoPolynomialEncoder) (R Rest : SepProp)
    (post : State → SepProp → Prop)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_len : ∀ bs ∈ pbEnc.pts, bs.length ≤ 2 * 0x0555555555555555)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4096#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = fsp + 1888#64)
    (hx1 : s.readReg64 .x1 = fsp + 896#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = u8)
    (hx22 : s.readReg64 .x22 = u72)
    (hx23 : s.readReg64 .x23 = fsp + 848#64)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64)
    (hx28 : s.readReg64 .x28 = u32)
    (htr : TraceCalleeSaved s s0)
    (hnext : ∀ (s1 : State),
      s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4100#64 →
      s1.status = .Running →
      (s1.sp = fsp ∧
       s1.readReg64 .x19 = out ∧
       s1.readReg64 .x21 = u8 ∧
       s1.readReg64 .x22 = u72 ∧
       s1.readReg64 .x23 = fsp + 848#64 ∧
       s1.readReg64 .x25 = fsp + 1792#64 ∧
       s1.readReg64 .x28 = u32 ∧
       TraceCalleeSaved s1 s0) →
      SepWP (tripleRatchetProgAtExt b ext) target_pc s1
        (stackAt fsp encoderFromPbStack ∗
         resultPolyEncoderFromPbAt A (fsp + 1888#64) (fromPbResult pbEnc) ∗
         memRegion (fsp + 896#64) protoPolynomialEncoderSize ∗
         A.pool ∗
         Rest)
        post) :
    SepWPp (tripleRatchetProgAtExt b ext) target_pc s
      (stackAt fsp encoderFromPbStack ∗
        memRegion (fsp + 1888#64) polyEncoderSize ∗
        protoPolynomialEncoderAt A (fsp + 896#64) pbEnc ∗
        A.pool ∗
        Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  have hsub := v1_encoder_from_pb_ok_at_statesFromPb henc
  refine sepWPp_seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 32996#64)
    (P_mid :=
      (stackAt fsp encoderFromPbStack ∗
       memRegion (fsp + 1888#64) polyEncoderSize ∗
       protoPolynomialEncoderAt A (fsp + 896#64) pbEnc ∗
       A.pool) ∗
      Rest)
    (Q_regs := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4100#64 ∧
      sm.readReg64 .x0 = fsp + 1888#64 ∧
      sm.readReg64 .x1 = fsp + 896#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x21 = u8 ∧
      sm.readReg64 .x22 = u72 ∧
      sm.readReg64 .x23 = fsp + 848#64 ∧
      sm.readReg64 .x25 = fsp + 1792#64 ∧
      sm.readReg64 .x28 = u32 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · states_from_pb_fetches_range b (Rust.withPanics ext) 4096 4
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_steps
    refine EncoderFromPb.align_pre (Entails.of_eq (by ac_rfl)) ?_
    wp_done
  · intro sm hpc_m hrun_m ⟨hsp_m, hlr_m, hx0_m, hx1_m, hx19_m, hx21_m, hx22_m, hx23_m, hx25_m, hx28_m, htr_m⟩
    have hsp_align_m : sm.spAligned = true := by
      unfold State.spAligned
      rw [hsp_m]
      exact hfsp_align
    refine SepWPp.call
      (x := EncoderFromPbGhost.mk (fsp + 1888#64) (fsp + 896#64) pbEnc)
      (F := Rest)
      hsub hpc_m hrun_m hsp_align_m hlr_m
      (fun R' hm => ?_)
      (fun sf code R' _ hm => not_satisfies_false_sepConj hm)
      (hoom := fun sf R' _ hm => False.elim (not_satisfies_false_sepConj hm))
      (fun sf _ hm => Satisfies.mono (sepConj_mono_left (v1_onPanic_shift htr_m sf)) hm)
      (fun sf hpcf hrunf hspf hcsf => ?_)
    · have hpre_ent :
          stackAt fsp encoderFromPbStack ∗
            memRegion (fsp + 1888#64) polyEncoderSize ∗
            protoPolynomialEncoderAt A (fsp + 896#64) pbEnc ∗
            A.pool ⊢
          (encoderFromPbSpec A).pre (EncoderFromPbGhost.mk (fsp + 1888#64) (fsp + 896#64) pbEnc) sm := by
        dsimp only [encoderFromPbSpec]
        rw [hsp_m]
        exact Entails.pure_right ⟨hx0_m, hx1_m, hpts_len⟩ (Entails.of_eq (by ac_rfl))
      rw [sepConj_assoc] at hm
      exact Satisfies.mono (sepConj_mono_left hpre_ent) hm
    · apply SepWPp.of_sepWP_ret
      dsimp only [encoderFromPbSpec]
      rw [hsp_m, sepConj_assoc]
      apply SepWP.pure_elim; intro htr_sf
      refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
        (hnext sf hpcf hrunf ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
      · rw [hspf, hsp_m]
      · rw [hcsf.1, hx19_m]
      · rw [hcsf.2.2.1, hx21_m]
      · rw [hcsf.2.2.2.1, hx22_m]
      · rw [hcsf.2.2.2.2.1, hx23_m]
      · rw [hcsf.2.2.2.2.2.2.1, hx25_m]
      · rw [hcsf.2.2.2.2.2.2.2.2.2.1, hx28_m]
      · exact ⟨htr_sf.trans htr_m.1, hcsf.2.2.2.2.2.2.2.2.2.2.2.trans htr_m.2⟩

/-- At `+4100`, when `fromPbResult pbEnc = .error err` (`[fsp + 1888] = 2#64`),
    sets `x26 = u8` and falls through at `+4112` to `+4116` (`v1_cleanup_enc_err_4116`). -/
theorem v1_encoder_err_4100_4116
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (fsp out u8 u32 u72 : BitVec 64)
    (err : PolynomialError) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4100#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = u8)
    (hx22 : s.readReg64 .x22 = u72)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64)
    (hx28 : s.readReg64 .x28 = u32)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4116#64) s
      (resultPolyEncoderFromPbAt A (fsp + 1888#64) (.error err) ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢ memRegion (fsp + 1888#64) 400 ∗ Rest) ∧
        s1.sp = fsp ∧
        s1.readReg64 .x19 = out ∧
        s1.readReg64 .x22 = u72 ∧
        s1.readReg64 .x25 = fsp + 1792#64 ∧
        s1.readReg64 .x26 = u8 ∧
        s1.readReg64 .x28 = u32 ∧
        TraceCalleeSaved s1 s0) := by
  refine SepWP.weaken_pre
    (sepConj_mono_left (v1_resultPolyEncoder_err_entails_tag_392 A fsp err)) ?_
  wp_simp_pre [sepConj_assoc]
  states_from_pb_fetches_range b (Rust.withPanics ext) 4100 16
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · have hm400 : ((fsp + 1888#64) ↦₆₄ 2#64) ∗ memRegion (fsp + 1896#64) 392 ⊢
        memRegion (fsp + 1888#64) 400 := by
      rw [ProofLib.memRegion_split' (b := fsp + 1888#64) (n := 8) (k := 392)
            (b' := fsp + 1896#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)
    rw [← sepConj_assoc]
    exact sepConj_mono_left hm400
  · wp_done

/-- At `+4100`, when `[fsp + 1888] = tag` with `tag = 0#64 ∨ tag = 1#64`,
    sets `x15 = tag`, `x26 = u8`, and branches at `+4112` (`b.ne +6568`) to `+6568`. -/
theorem v1_encoder_ok_4100_6568
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (fsp out tag u8 u32 u72 : BitVec 64)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (htag : tag = 0#64 ∨ tag = 1#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4100#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = u8)
    (hx22 : s.readReg64 .x22 = u72)
    (hx23 : s.readReg64 .x23 = fsp + 848#64)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64)
    (hx28 : s.readReg64 .x28 = u32)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 6568#64) s
      (((fsp + 1888#64) ↦₆₄ tag) ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢ ((fsp + 1888#64) ↦₆₄ tag) ∗ Rest) ∧
        s1.sp = fsp ∧
        s1.readReg64 .x15 = tag ∧
        s1.readReg64 .x19 = out ∧
        s1.readReg64 .x21 = u8 ∧
        s1.readReg64 .x22 = u72 ∧
        s1.readReg64 .x23 = fsp + 848#64 ∧
        s1.readReg64 .x25 = fsp + 1792#64 ∧
        s1.readReg64 .x26 = u8 ∧
        s1.readReg64 .x28 = u32 ∧
        TraceCalleeSaved s1 s0) := by
  states_from_pb_fetches_range b (Rust.withPanics ext) 4100 16
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  rcases htag with rfl | rfl
  · wp_steps
    refine EncoderFromPb.align_pre (Entails.of_eq (by ac_rfl)) ?_
    wp_done
  · wp_steps
    refine EncoderFromPb.align_pre (Entails.of_eq (by ac_rfl)) ?_
    wp_done

set_option maxHeartbeats 1200000 in
/-- Execution segment `+6568 -> +8180`: copies `<PolyEncoder>::from_pb` `Ok` output from `fsp + 1888..2288`
    and `uc` fields from stack slots into registers and `fsp + 608..895`, then branches to `+8180`. -/
theorem v1_keysSampled_6568_8180
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (fsp out tag pa1 pa2 u8 u16 u32 u40 u72 u96 u104 : BitVec 64)
    (bs : List (BitVec 8)) (hbs : bs.length = 384)
    (hi32 : BitVec 32) (idx : BitVec 32)
    (w160 w208 w224 w832 w864 w880 w888 : BitVec 64) (d172 : BitVec 32)
    (q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 q848 : BitVec 128)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 6568#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx15 : s.readReg64 .x15 = tag)
    (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = u8)
    (hx22 : s.readReg64 .x22 = u72)
    (hx23 : s.readReg64 .x23 = fsp + 848#64)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64)
    (hx26 : s.readReg64 .x26 = u8)
    (hx28 : s.readReg64 .x28 = u32)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8180#64) s
      (((fsp + 64#64) ↦₆₄ u104) ∗
        ((fsp + 160#64) ↦₆₄ w160) ∗
        ((fsp + 172#64) ↦₃₂ d172) ∗
        ((fsp + 176#64) ↦₆₄ u16) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 200#64) ↦₆₄ pa1) ∗
        ((fsp + 208#64) ↦₆₄ w208) ∗
        ((fsp + 216#64) ↦₆₄ u40) ∗
        ((fsp + 224#64) ↦₆₄ w224) ∗
        ((fsp + 232#64) ↦₆₄ u96) ∗
        ((fsp + 608#64) ↦₁₂₈ q608) ∗ ((fsp + 624#64) ↦₁₂₈ q624) ∗
        ((fsp + 640#64) ↦₁₂₈ q640) ∗ ((fsp + 656#64) ↦₁₂₈ q656) ∗
        ((fsp + 672#64) ↦₁₂₈ q672) ∗ ((fsp + 688#64) ↦₁₂₈ q688) ∗
        ((fsp + 704#64) ↦₁₂₈ q704) ∗ ((fsp + 720#64) ↦₁₂₈ q720) ∗
        ((fsp + 736#64) ↦₁₂₈ q736) ∗ ((fsp + 752#64) ↦₁₂₈ q752) ∗
        ((fsp + 768#64) ↦₁₂₈ q768) ∗ ((fsp + 784#64) ↦₁₂₈ q784) ∗
        ((fsp + 800#64) ↦₁₂₈ q800) ∗ ((fsp + 816#64) ↦₁₂₈ q816) ∗
        ((fsp + 832#64) ↦₆₄ w832) ∗
        ((fsp + 848#64) ↦₁₂₈ q848) ∗ ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 w864) ∗
        ((fsp + 880#64) ↦₆₄ w880) ∗ ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 w888) ∗
        ((fsp + 1888#64) ↦₆₄ tag) ∗
        v1_encCellsAt (fsp + 1888#64) bs ∗
        ((fsp + 2280#64) ↦₆₄ (hi32 ++ idx)) ∗
        memRegion (fsp + 2288#64) 16 ∗
        Rest)
      (fun s1 P1 =>
        (P1 ⊢
          ((fsp + 64#64) ↦₆₄ u104) ∗
          ((fsp + 160#64) ↦₆₄ u96) ∗
          ((fsp + 172#64) ↦₃₂ (loByte (v1_wordAt bs 128)).zeroExtend 32) ∗
          ((fsp + 176#64) ↦₆₄ u16) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 200#64) ↦₆₄ pa1) ∗
          ((fsp + 208#64) ↦₆₄ v1_wordAt bs 0) ∗
          ((fsp + 216#64) ↦₆₄ u40) ∗
          ((fsp + 224#64) ↦₆₄ u32) ∗
          ((fsp + 232#64) ↦₆₄ u96) ∗
          ((fsp + 608#64) ↦₁₂₈ v1_quadAt bs 152) ∗ ((fsp + 624#64) ↦₁₂₈ v1_quadAt bs 168) ∗
          ((fsp + 640#64) ↦₁₂₈ v1_quadAt bs 184) ∗ ((fsp + 656#64) ↦₁₂₈ v1_quadAt bs 200) ∗
          ((fsp + 672#64) ↦₁₂₈ v1_quadAt bs 216) ∗ ((fsp + 688#64) ↦₁₂₈ v1_quadAt bs 232) ∗
          ((fsp + 704#64) ↦₁₂₈ v1_quadAt bs 248) ∗ ((fsp + 720#64) ↦₁₂₈ v1_quadAt bs 264) ∗
          ((fsp + 736#64) ↦₁₂₈ v1_quadAt bs 280) ∗ ((fsp + 752#64) ↦₁₂₈ v1_quadAt bs 296) ∗
          ((fsp + 768#64) ↦₁₂₈ v1_quadAt bs 312) ∗ ((fsp + 784#64) ↦₁₂₈ v1_quadAt bs 328) ∗
          ((fsp + 800#64) ↦₁₂₈ v1_quadAt bs 344) ∗ ((fsp + 816#64) ↦₁₂₈ v1_quadAt bs 360) ∗
          ((fsp + 832#64) ↦₆₄ v1_wordAt bs 376) ∗
          ((fsp + 848#64) ↦₁₂₈ v1_midQ128 (v1_wordAt bs 128) (v1_wordAt bs 136) (v1_wordAt bs 144)) ∗
          ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 (v1_wordAt bs 144 >>> 8)) ∗
          ((fsp + 880#64) ↦₆₄ unshiftWord (v1_wordAt bs 104) (loByte (v1_wordAt bs 112))) ∗
          ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 (v1_wordAt bs 112 >>> 8)) ∗
          ((fsp + 1888#64) ↦₁₂₈ (v1_wordAt bs 0 ++ tag)) ∗
          ((fsp + 1904#64) ↦₁₂₈ (v1_wordAt bs 16 ++ v1_wordAt bs 8)) ∗
          ((fsp + 1920#64) ↦₆₄ v1_wordAt bs 24) ∗
          memRegion (fsp + 1928#64) 376 ∗
          Rest) ∧
        s1.sp = fsp ∧
        s1.readReg64 .x6 = fsp + 576#64 ∧
        s1.readReg64 .x19 = out ∧
        s1.readReg64 .x23 = fsp + 848#64 ∧
        s1.readReg64 .x8 = 3#64 ∧
        s1.readReg64 .x15 = tag ∧
        s1.readReg64 .x20 = v1_wordAt bs 8 ∧
        s1.readReg64 .x13 = v1_wordAt bs 16 ∧
        s1.readReg64 .x25 = v1_wordAt bs 24 ∧
        s1.readReg64 .x30 = v1_wordAt bs 32 ∧
        s1.readReg64 .x9 = v1_wordAt bs 40 ∧
        s1.readReg64 .x14 = v1_wordAt bs 48 ∧
        s1.readReg64 .x18 = v1_wordAt bs 56 ∧
        s1.readReg64 .x17 = v1_wordAt bs 64 ∧
        s1.readReg64 .x0 = v1_wordAt bs 72 ∧
        s1.readReg32 .x3 = ((v1_wordAt bs 80).extractLsb' 0 8).zeroExtend 32 ∧
        s1.readReg32 .x27 = (v1_wordAt bs 80).extractLsb' 8 32 ∧
        ((s1.readReg64 .x27 >>> 32).setWidth 32).setWidth 16 = (v1_wordAt bs 80).extractLsb' 40 16 ∧
        ((s1.readReg64 .x27 >>> 48).setWidth 32).setWidth 8 = (v1_wordAt bs 80).extractLsb' 56 8 ∧
        s1.readReg64 .x4 = v1_wordAt bs 88 ∧
        s1.readReg64 .x5 = v1_wordAt bs 96 ∧
        s1.readReg32 .x21 = (loByte (v1_wordAt bs 104)).zeroExtend 32 ∧
        s1.readReg64 .x7 = v1_wordAt bs 120 ∧
        s1.readReg64 .x2 = hi32 ++ idx ∧
        s1.readReg64 .x11 = u72 ∧
        s1.readReg64 .x22 = pa1 ∧
        s1.readReg64 .x24 = u72 ∧
        s1.readReg64 .x10 = pa2 ∧
        s1.readReg64 .x26 = u8 ∧
        s1.readReg64 .x12 = u16 ∧
        s1.readReg64 .x1 = 1152#64 ∧
        s1.readReg64 .x28 = u40 ∧
        s1.readReg64 .x16 = u104 ∧
        TraceCalleeSaved s1 s0) := by
  subst hsp
  unfold v1_encCellsAt
  wp_simp_pre [pointsTo128, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  states_from_pb_fetches_range b (Rust.withPanics ext) 6568 284
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_conv_pre =>
    rw [v1_fsp_1976_split_rest s.sp (v1_wordAt bs 80),
        v1_fsp_2024_realign_rest s.sp (v1_wordAt bs 128) (v1_wordAt bs 136) (v1_wordAt bs 144)]
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_conv_pre =>
    rw [v1_fsp_2000_realign_rest s.sp (v1_wordAt bs 104) (v1_wordAt bs 112),
        v1_fsp_880_realign_64_rest s.sp w880 w888]
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step
  wp_conv_pre =>
    rw [v1_fsp_2024_unrealign_rest s.sp (v1_wordAt bs 128) (v1_wordAt bs 136) (v1_wordAt bs 144),
        v1_fsp_2024_split_1_7_rest s.sp (v1_wordAt bs 128),
        v1_fsp_880_realign_rest s.sp w880 (v1_wordAt bs 112)]
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_conv_pre =>
    rw [v1_fsp_856_realign_rest s.sp
      ((v1_midQ128 (v1_wordAt bs 128) (v1_wordAt bs 136) (v1_wordAt bs 144)).extractLsb' 64 64) w864]
  wp_step
  wp_conv_pre =>
    rw [v1_fsp_856_unrealign_midQ128_rest s.sp
      (v1_wordAt bs 128) (v1_wordAt bs 136) (v1_wordAt bs 144)]
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · rw [v1_fsp_2024_unsplit_1_7_rest s.sp (v1_wordAt bs 128),
        v1_fsp_2000_unrealign_rest s.sp (v1_wordAt bs 104) (v1_wordAt bs 112),
        v1_fsp_1976_unsplit_rest s.sp (v1_wordAt bs 80)]
    have hep1888 := v1_fsp_1888_entails_epilogue s.sp tag (hi32 ++ idx) bs hbs
    dsimp only [v1_encCellsAt] at hep1888
    simp only [pointsTo128_eq_pair64, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hep1888 ⊢
    refine Entails.trans (Entails.of_eq (show _ =
      (((s.sp + 1888#64) ↦₆₄ tag) ∗
       ((s.sp + 1896#64) ↦₆₄ v1_wordAt bs 0) ∗
       ((s.sp + 1904#64) ↦₆₄ v1_wordAt bs 8) ∗
       ((s.sp + 1912#64) ↦₆₄ v1_wordAt bs 16) ∗
       ((s.sp + 1920#64) ↦₆₄ v1_wordAt bs 24) ∗
       ((s.sp + 1928#64) ↦₆₄ v1_wordAt bs 32) ∗
       ((s.sp + 1936#64) ↦₆₄ v1_wordAt bs 40) ∗
       ((s.sp + 1944#64) ↦₆₄ v1_wordAt bs 48) ∗
       ((s.sp + 1952#64) ↦₆₄ v1_wordAt bs 56) ∗
       ((s.sp + 1960#64) ↦₆₄ v1_wordAt bs 64) ∗
       ((s.sp + 1968#64) ↦₆₄ v1_wordAt bs 72) ∗
       ((s.sp + 1976#64) ↦₆₄ v1_wordAt bs 80) ∗
       ((s.sp + 1984#64) ↦₆₄ v1_wordAt bs 88) ∗
       ((s.sp + 1992#64) ↦₆₄ v1_wordAt bs 96) ∗
       ((s.sp + 2000#64) ↦₆₄ v1_wordAt bs 104) ∗
       ((s.sp + 2008#64) ↦₆₄ v1_wordAt bs 112) ∗
       ((s.sp + 2016#64) ↦₆₄ v1_wordAt bs 120) ∗
       ((s.sp + 2024#64) ↦₆₄ v1_wordAt bs 128) ∗
       ((s.sp + 2032#64) ↦₆₄ v1_wordAt bs 136) ∗
       ((s.sp + 2040#64) ↦₆₄ v1_wordAt bs 144) ∗
       ((s.sp + 2048#64) ↦₆₄ (v1_quadAt bs 152).extractLsb' 0 64) ∗
       ((s.sp + 2056#64) ↦₆₄ (v1_quadAt bs 152).extractLsb' 64 64) ∗
       ((s.sp + 2064#64) ↦₆₄ (v1_quadAt bs 168).extractLsb' 0 64) ∗
       ((s.sp + 2072#64) ↦₆₄ (v1_quadAt bs 168).extractLsb' 64 64) ∗
       ((s.sp + 2080#64) ↦₆₄ (v1_quadAt bs 184).extractLsb' 0 64) ∗
       ((s.sp + 2088#64) ↦₆₄ (v1_quadAt bs 184).extractLsb' 64 64) ∗
       ((s.sp + 2096#64) ↦₆₄ (v1_quadAt bs 200).extractLsb' 0 64) ∗
       ((s.sp + 2104#64) ↦₆₄ (v1_quadAt bs 200).extractLsb' 64 64) ∗
       ((s.sp + 2112#64) ↦₆₄ (v1_quadAt bs 216).extractLsb' 0 64) ∗
       ((s.sp + 2120#64) ↦₆₄ (v1_quadAt bs 216).extractLsb' 64 64) ∗
       ((s.sp + 2128#64) ↦₆₄ (v1_quadAt bs 232).extractLsb' 0 64) ∗
       ((s.sp + 2136#64) ↦₆₄ (v1_quadAt bs 232).extractLsb' 64 64) ∗
       ((s.sp + 2144#64) ↦₆₄ (v1_quadAt bs 248).extractLsb' 0 64) ∗
       ((s.sp + 2152#64) ↦₆₄ (v1_quadAt bs 248).extractLsb' 64 64) ∗
       ((s.sp + 2160#64) ↦₆₄ (v1_quadAt bs 264).extractLsb' 0 64) ∗
       ((s.sp + 2168#64) ↦₆₄ (v1_quadAt bs 264).extractLsb' 64 64) ∗
       ((s.sp + 2176#64) ↦₆₄ (v1_quadAt bs 280).extractLsb' 0 64) ∗
       ((s.sp + 2184#64) ↦₆₄ (v1_quadAt bs 280).extractLsb' 64 64) ∗
       ((s.sp + 2192#64) ↦₆₄ (v1_quadAt bs 296).extractLsb' 0 64) ∗
       ((s.sp + 2200#64) ↦₆₄ (v1_quadAt bs 296).extractLsb' 64 64) ∗
       ((s.sp + 2208#64) ↦₆₄ (v1_quadAt bs 312).extractLsb' 0 64) ∗
       ((s.sp + 2216#64) ↦₆₄ (v1_quadAt bs 312).extractLsb' 64 64) ∗
       ((s.sp + 2224#64) ↦₆₄ (v1_quadAt bs 328).extractLsb' 0 64) ∗
       ((s.sp + 2232#64) ↦₆₄ (v1_quadAt bs 328).extractLsb' 64 64) ∗
       ((s.sp + 2240#64) ↦₆₄ (v1_quadAt bs 344).extractLsb' 0 64) ∗
       ((s.sp + 2248#64) ↦₆₄ (v1_quadAt bs 344).extractLsb' 64 64) ∗
       ((s.sp + 2256#64) ↦₆₄ (v1_quadAt bs 360).extractLsb' 0 64) ∗
       ((s.sp + 2264#64) ↦₆₄ (v1_quadAt bs 360).extractLsb' 64 64) ∗
       ((s.sp + 2272#64) ↦₆₄ v1_wordAt bs 376) ∗
       ((s.sp + 2280#64) ↦₆₄ (hi32 ++ idx)) ∗
       memRegion (s.sp + 2288#64) 16) ∗
      (((s.sp + 64#64) ↦₆₄ u104) ∗
       ((s.sp + 160#64) ↦₆₄ u96) ∗
       ((s.sp + 172#64) ↦₃₂ (loByte (v1_wordAt bs 128)).zeroExtend 32) ∗
       ((s.sp + 176#64) ↦₆₄ u16) ∗
       ((s.sp + 184#64) ↦₆₄ pa2) ∗
       ((s.sp + 200#64) ↦₆₄ pa1) ∗
       ((s.sp + 208#64) ↦₆₄ v1_wordAt bs 0) ∗
       ((s.sp + 216#64) ↦₆₄ u40) ∗
       ((s.sp + 224#64) ↦₆₄ u32) ∗
       ((s.sp + 232#64) ↦₆₄ u96) ∗
       ((s.sp + 608#64) ↦₆₄ (v1_quadAt bs 152).extractLsb' 0 64) ∗
       ((s.sp + 616#64) ↦₆₄ (v1_quadAt bs 152).extractLsb' 64 64) ∗
       ((s.sp + 624#64) ↦₆₄ (v1_quadAt bs 168).extractLsb' 0 64) ∗
       ((s.sp + 632#64) ↦₆₄ (v1_quadAt bs 168).extractLsb' 64 64) ∗
       ((s.sp + 640#64) ↦₆₄ (v1_quadAt bs 184).extractLsb' 0 64) ∗
       ((s.sp + 648#64) ↦₆₄ (v1_quadAt bs 184).extractLsb' 64 64) ∗
       ((s.sp + 656#64) ↦₆₄ (v1_quadAt bs 200).extractLsb' 0 64) ∗
       ((s.sp + 664#64) ↦₆₄ (v1_quadAt bs 200).extractLsb' 64 64) ∗
       ((s.sp + 672#64) ↦₆₄ (v1_quadAt bs 216).extractLsb' 0 64) ∗
       ((s.sp + 680#64) ↦₆₄ (v1_quadAt bs 216).extractLsb' 64 64) ∗
       ((s.sp + 688#64) ↦₆₄ (v1_quadAt bs 232).extractLsb' 0 64) ∗
       ((s.sp + 696#64) ↦₆₄ (v1_quadAt bs 232).extractLsb' 64 64) ∗
       ((s.sp + 704#64) ↦₆₄ (v1_quadAt bs 248).extractLsb' 0 64) ∗
       ((s.sp + 712#64) ↦₆₄ (v1_quadAt bs 248).extractLsb' 64 64) ∗
       ((s.sp + 720#64) ↦₆₄ (v1_quadAt bs 264).extractLsb' 0 64) ∗
       ((s.sp + 728#64) ↦₆₄ (v1_quadAt bs 264).extractLsb' 64 64) ∗
       ((s.sp + 736#64) ↦₆₄ (v1_quadAt bs 280).extractLsb' 0 64) ∗
       ((s.sp + 744#64) ↦₆₄ (v1_quadAt bs 280).extractLsb' 64 64) ∗
       ((s.sp + 752#64) ↦₆₄ (v1_quadAt bs 296).extractLsb' 0 64) ∗
       ((s.sp + 760#64) ↦₆₄ (v1_quadAt bs 296).extractLsb' 64 64) ∗
       ((s.sp + 768#64) ↦₆₄ (v1_quadAt bs 312).extractLsb' 0 64) ∗
       ((s.sp + 776#64) ↦₆₄ (v1_quadAt bs 312).extractLsb' 64 64) ∗
       ((s.sp + 784#64) ↦₆₄ (v1_quadAt bs 328).extractLsb' 0 64) ∗
       ((s.sp + 792#64) ↦₆₄ (v1_quadAt bs 328).extractLsb' 64 64) ∗
       ((s.sp + 800#64) ↦₆₄ (v1_quadAt bs 344).extractLsb' 0 64) ∗
       ((s.sp + 808#64) ↦₆₄ (v1_quadAt bs 344).extractLsb' 64 64) ∗
       ((s.sp + 816#64) ↦₆₄ (v1_quadAt bs 360).extractLsb' 0 64) ∗
       ((s.sp + 824#64) ↦₆₄ (v1_quadAt bs 360).extractLsb' 64 64) ∗
       ((s.sp + 832#64) ↦₆₄ v1_wordAt bs 376) ∗
       ((s.sp + 848#64) ↦₆₄ (v1_midQ128 (v1_wordAt bs 128) (v1_wordAt bs 136) (v1_wordAt bs 144)).extractLsb' 0 64) ∗
       ((s.sp + 856#64) ↦₆₄ (v1_midQ128 (v1_wordAt bs 128) (v1_wordAt bs 136) (v1_wordAt bs 144)).extractLsb' 64 64) ∗
       ((s.sp + 864#64) ↦ₛ EncoderFromPb.loBytes7 (v1_wordAt bs 144 >>> 8)) ∗
       ((s.sp + 880#64) ↦₆₄ unshiftWord (v1_wordAt bs 104) (loByte (v1_wordAt bs 112))) ∗
       ((s.sp + 888#64) ↦ₛ EncoderFromPb.loBytes7 (v1_wordAt bs 112 >>> 8)) ∗
       Rest) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hep1888)
      (Entails.of_eq (by simp only [pointsTo128_eq_pair64, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]; ac_rfl))
  · wp_done

theorem v1_memRegion_72_104_split (fsp : BitVec 64) :
    memRegion (fsp + 72#64) 104 ⊢
      memRegion (fsp + 72#64) 20 ∗
      (∃∗ d92 : BitVec 32, (fsp + 92#64) ↦₃₂ d92) ∗
      memRegion (fsp + 96#64) 8 ∗
      (∃∗ w104 : BitVec 64, (fsp + 104#64) ↦₆₄ w104) ∗
      (∃∗ w112 : BitVec 64, (fsp + 112#64) ↦₆₄ w112) ∗
      (∃∗ w120 : BitVec 64, (fsp + 120#64) ↦₆₄ w120) ∗
      memRegion (fsp + 128#64) 32 ∗
      (∃∗ w160 : BitVec 64, (fsp + 160#64) ↦₆₄ w160) ∗
      memRegion (fsp + 168#64) 4 ∗
      (∃∗ d172 : BitVec 32, (fsp + 172#64) ↦₃₂ d172) := by
  exact split_top <|
    split_step (Entails.refl _) <|
    split_step (mem32_entails _) <|
    split_step (Entails.refl _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (Entails.refl _) <|
    split_step (mem64_entails _) <|
    split_step (Entails.refl _) <|
    mem32_entails _

theorem v1_memRegion_240_1648_split (fsp : BitVec 64) :
    memRegion (fsp + 240#64) 1648 ⊢
      (∃∗ bs240 : { l : List (BitVec 8) // l.length = 328 }, (fsp + 240#64) ↦ₛ bs240.val) ∗
      memRegion (fsp + 568#64) 8 ∗
      (∃∗ q576 : BitVec 128, (fsp + 576#64) ↦₁₂₈ q576) ∗
      ((∃∗ w592 : BitVec 64, (fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗ memRegion (fsp + 599#64) 9) ∗
      (∃∗ q608 : BitVec 128, (fsp + 608#64) ↦₁₂₈ q608) ∗
      (∃∗ q624 : BitVec 128, (fsp + 624#64) ↦₁₂₈ q624) ∗
      (∃∗ q640 : BitVec 128, (fsp + 640#64) ↦₁₂₈ q640) ∗
      (∃∗ q656 : BitVec 128, (fsp + 656#64) ↦₁₂₈ q656) ∗
      (∃∗ q672 : BitVec 128, (fsp + 672#64) ↦₁₂₈ q672) ∗
      (∃∗ q688 : BitVec 128, (fsp + 688#64) ↦₁₂₈ q688) ∗
      (∃∗ q704 : BitVec 128, (fsp + 704#64) ↦₁₂₈ q704) ∗
      (∃∗ q720 : BitVec 128, (fsp + 720#64) ↦₁₂₈ q720) ∗
      (∃∗ q736 : BitVec 128, (fsp + 736#64) ↦₁₂₈ q736) ∗
      (∃∗ q752 : BitVec 128, (fsp + 752#64) ↦₁₂₈ q752) ∗
      (∃∗ q768 : BitVec 128, (fsp + 768#64) ↦₁₂₈ q768) ∗
      (∃∗ q784 : BitVec 128, (fsp + 784#64) ↦₁₂₈ q784) ∗
      (∃∗ q800 : BitVec 128, (fsp + 800#64) ↦₁₂₈ q800) ∗
      (∃∗ q816 : BitVec 128, (fsp + 816#64) ↦₁₂₈ q816) ∗
      (∃∗ w832 : BitVec 64, (fsp + 832#64) ↦₆₄ w832) ∗
      memRegion (fsp + 840#64) 8 ∗
      (∃∗ q848 : BitVec 128, (fsp + 848#64) ↦₁₂₈ q848) ∗
      ((∃∗ w864 : BitVec 64, (fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 w864) ∗ memRegion (fsp + 871#64) 9) ∗
      (∃∗ w880 : BitVec 64, (fsp + 880#64) ↦₆₄ w880) ∗
      ((∃∗ w888 : BitVec 64, (fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 w888) ∗ memRegion (fsp + 895#64) 993) := by
  exact split_top <|
    split_step (memRegion_328_entails_bs _) <|
    split_step (Entails.refl _) <|
    split_step (mem128_entails _) <|
    split_step (memRegion_loBytes7_gap_at fsp 592#64 599#64 8) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem64_entails _) <| split_step (Entails.refl _) <|
    split_step (mem128_entails _) <|
    split_step (memRegion_loBytes7_gap_at fsp 864#64 871#64 8) <|
    split_step (mem64_entails _) <|
    memRegion_loBytes7_gap_at fsp 888#64 895#64 992

theorem v1_epilogueStackGaps_pack (fsp u104 u16 pa2 pa1 u40 : BitVec 64) :
    memRegion fsp 64 ∗
      ((fsp + 64#64) ↦₆₄ u104) ∗
      memRegion (fsp + 72#64) 20 ∗
      memRegion (fsp + 96#64) 8 ∗
      memRegion (fsp + 128#64) 32 ∗
      memRegion (fsp + 168#64) 4 ∗
      ((fsp + 176#64) ↦₆₄ u16) ∗
      ((fsp + 184#64) ↦₆₄ pa2) ∗
      ((fsp + 200#64) ↦₆₄ pa1) ∗
      ((fsp + 216#64) ↦₆₄ u40) ∗
      memRegion (fsp + 568#64) 8 ∗
      memRegion (fsp + 599#64) 9 ∗
      memRegion (fsp + 840#64) 8 ∗
      memRegion (fsp + 871#64) 9 ∗
      memRegion (fsp + 895#64) 993 ∗
      memRegion (fsp + 1928#64) 376 ⊢
      epilogueStackGaps fsp := by
  unfold epilogueStackGaps
  have h92 : memRegion fsp 64 ∗ ((fsp + 64#64) ↦₆₄ u104) ∗ memRegion (fsp + 72#64) 20 ⊢
      memRegion fsp 92 :=
    collapse_top <| collapse_step0 (Entails.refl _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _
  have h16 : ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2) ⊢ memRegion (fsp + 176#64) 16 :=
    collapse_top <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      Drop.pointsTo64_entails_memRegion _ _
  have h200 : ((fsp + 200#64) ↦₆₄ pa1) ⊢ memRegion (fsp + 200#64) 8 :=
    Drop.pointsTo64_entails_memRegion _ _
  have h216 : ((fsp + 216#64) ↦₆₄ u40) ⊢ memRegion (fsp + 216#64) 8 :=
    Drop.pointsTo64_entails_memRegion _ _
  refine Entails.trans (Entails.of_eq (show _ =
    (memRegion fsp 64 ∗ ((fsp + 64#64) ↦₆₄ u104) ∗ memRegion (fsp + 72#64) 20) ∗
    memRegion (fsp + 96#64) 8 ∗
    memRegion (fsp + 128#64) 32 ∗
    memRegion (fsp + 168#64) 4 ∗
    (((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2)) ∗
    ((fsp + 200#64) ↦₆₄ pa1) ∗
    ((fsp + 216#64) ↦₆₄ u40) ∗
    memRegion (fsp + 568#64) 8 ∗
    memRegion (fsp + 599#64) 9 ∗
    memRegion (fsp + 840#64) 8 ∗
    memRegion (fsp + 871#64) 9 ∗
    memRegion (fsp + 895#64) 993 ∗
    memRegion (fsp + 1928#64) 376 by ac_rfl)) ?_
  exact sepConj_mono h92 (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono h16 (sepConj_mono h200 (sepConj_mono_left h216))))))

set_option maxHeartbeats 1200000 in
/-- Compose `+6568 -> +8180` with `states_from_pb_epilogue_8180` and `v1_epilogueOutFull_entails_keysSampled`. -/
theorem v1_keysSampled_6568_ret
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s : State) (out tag pa1 pa2 u8 u16 u24 u32 u40 u48 u72 u96 u104 : BitVec 64)
    (bs : List (BitVec 8)) (hbs : bs.length = 384)
    (hi32 : BitVec 32) (enc : PolyEncoder) (P_heap : SepProp)
    (hreloc :
      ((out + 8#64) ↦₆₄ tag) ∗ (((out + 8#64) + 8#64) ↦ₛ bs) ∗
        (((out + 8#64) + 392#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ P_heap ⊢
        polyEncoderAt A (out + 8#64) enc)
    (ek dk rootKey macKey : List (BitVec 8))
    (hek : u24 = BitVec.ofNat 64 ek.length)
    (hdk : u48 = BitVec.ofNat 64 dk.length)
    (hl1 : u72 = BitVec.ofNat 64 rootKey.length)
    (hl2 : u96 = BitVec.ofNat 64 macKey.length)
    (hu24_1152 : u24 = 1152#64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 6568#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 2400#64)
    (hx15 : s.readReg64 .x15 = tag)
    (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = u8)
    (hx22 : s.readReg64 .x22 = u72)
    (hx23 : s.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx25 : s.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64)
    (hx26 : s.readReg64 .x26 = u8)
    (hx28 : s.readReg64 .x28 = u32)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 64 ∗
        ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗
        memRegion (s0.sp - 2400#64 + 72#64) 104 ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ pa1) ∗
        memRegion (s0.sp - 2400#64 + 208#64) 8 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 1648 ∗
        ((s0.sp - 2400#64 + 1888#64) ↦₆₄ tag) ∗
        v1_encCellsAt (s0.sp - 2400#64 + 1888#64) bs ∗
        ((s0.sp - 2400#64 + 2280#64) ↦₆₄ (hi32 ++ enc.idx)) ∗
        memRegion (s0.sp - 2400#64 + 2288#64) 16 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        P_heap ∗
        vecU8Payload A u8 u16 ek ∗
        vecU8Payload A u32 u40 dk ∗
        vecU8Payload A u72 pa1 rootKey ∗
        vecU8Payload A u96 pa2 macKey ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (.ok (.keysSampled
              { uc := { ek := ek, dk := dk,
                        auth := { rootKey := rootKey, macKey := macKey },
                        epoch := u104 },
                sending_hdr := enc })) ∗
          Rest ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono (v1_memRegion_72_104_split (s0.sp - 2400#64))
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono (mem64_entails (s0.sp - 2400#64 + 208#64))
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_left (v1_memRegion_240_1648_split (s0.sp - 2400#64))))))))))))))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine ProofLib.SepWP.exists_left fun w888 => ProofLib.SepWP.exists_left fun w880 =>
    ProofLib.SepWP.exists_left fun w864 => ProofLib.SepWP.exists_left fun q848 =>
    ProofLib.SepWP.exists_left fun w832 => ProofLib.SepWP.exists_left fun q816 =>
    ProofLib.SepWP.exists_left fun q800 => ProofLib.SepWP.exists_left fun q784 =>
    ProofLib.SepWP.exists_left fun q768 => ProofLib.SepWP.exists_left fun q752 =>
    ProofLib.SepWP.exists_left fun q736 => ProofLib.SepWP.exists_left fun q720 =>
    ProofLib.SepWP.exists_left fun q704 => ProofLib.SepWP.exists_left fun q688 =>
    ProofLib.SepWP.exists_left fun q672 => ProofLib.SepWP.exists_left fun q656 =>
    ProofLib.SepWP.exists_left fun q640 => ProofLib.SepWP.exists_left fun q624 =>
    ProofLib.SepWP.exists_left fun q608 => ProofLib.SepWP.exists_left fun w592 =>
    ProofLib.SepWP.exists_left fun q576 => ProofLib.SepWP.exists_left fun bs240 =>
    ProofLib.SepWP.exists_left fun w208 => ProofLib.SepWP.exists_left fun d172 =>
    ProofLib.SepWP.exists_left fun w160 => ProofLib.SepWP.exists_left fun w120 =>
    ProofLib.SepWP.exists_left fun w112 => ProofLib.SepWP.exists_left fun w104 =>
    ProofLib.SepWP.exists_left fun d92 => ?_
  have h6568 := v1_keysSampled_6568_8180 s0 s (s0.sp - 2400#64) out tag pa1 pa2 u8 u16 u32 u40 u72 u96 u104
    bs hbs hi32 enc.idx w160 w208 u32 w832 w864 w880 w888 d172
    q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 q848
    (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion out chunkedStatesSize ∗
      ((s0.sp - 2400#64 + 92#64) ↦₃₂ d92) ∗
      ((s0.sp - 2400#64 + 104#64) ↦₆₄ w104) ∗
      ((s0.sp - 2400#64 + 112#64) ↦₆₄ w112) ∗
      ((s0.sp - 2400#64 + 120#64) ↦₆₄ w120) ∗
      ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗
      ((s0.sp - 2400#64 + 240#64) ↦ₛ bs240.val) ∗
      ((s0.sp - 2400#64 + 576#64) ↦₁₂₈ q576) ∗
      ((s0.sp - 2400#64 + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗
      memRegion (s0.sp - 2400#64) 64 ∗
      memRegion (s0.sp - 2400#64 + 72#64) 20 ∗
      memRegion (s0.sp - 2400#64 + 96#64) 8 ∗
      memRegion (s0.sp - 2400#64 + 128#64) 32 ∗
      memRegion (s0.sp - 2400#64 + 168#64) 4 ∗
      memRegion (s0.sp - 2400#64 + 568#64) 8 ∗
      memRegion (s0.sp - 2400#64 + 599#64) 9 ∗
      memRegion (s0.sp - 2400#64 + 840#64) 8 ∗
      memRegion (s0.sp - 2400#64 + 871#64) 9 ∗
      memRegion (s0.sp - 2400#64 + 895#64) 993 ∗
      statesFromPbSavedCells s0 ∗
      P_heap ∗
      vecU8Payload A u8 u16 ek ∗
      vecU8Payload A u32 u40 dk ∗
      vecU8Payload A u72 pa1 rootKey ∗
      vecU8Payload A u96 pa2 macKey ∗
      Rest)
    hfsp_align hpc hrun hsp hx15 hx19 hx21 hx22 hx23 hx25 hx26 hx28 htr
  refine SepWP.seq (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) h6568) ?_
  intro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, hx6_1, hx19_1, hx23_1, hx8_1, hx15_1, hx20_1, hx13_1,
    hx25_1, hx30_1, hx9_1, hx14_1, hx18_1, hx17_1, hx0_1, hx3_1, hx27_1, hx27_hi16, hx27_hi8,
    hx4_1, hx5_1, hx21_1, hx7_1, hx2_1, hx11_1, hx22_1, hx24_1, hx10_1, hx26_1, hx12_1,
    hx1_1, hx28_1, hx16_1, htr1⟩
  have hgaps := v1_epilogueStackGaps_pack (s0.sp - 2400#64) u104 u16 pa2 pa1 u40
  have hP1' : P1 ⊢
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion out chunkedStatesSize ∗
      epilogueStackSlots (s0.sp - 2400#64)
        d92 ((loByte (v1_wordAt bs 128)).zeroExtend 32)
        w104 w112 w120 u96 u48 (v1_wordAt bs 0) u32 u96 bs240.val
        q576 w592
        (v1_quadAt bs 152) (v1_quadAt bs 168) (v1_quadAt bs 184) (v1_quadAt bs 200)
        (v1_quadAt bs 216) (v1_quadAt bs 232) (v1_quadAt bs 248) (v1_quadAt bs 264)
        (v1_quadAt bs 280) (v1_quadAt bs 296) (v1_quadAt bs 312) (v1_quadAt bs 328)
        (v1_quadAt bs 344) (v1_quadAt bs 360)
        (v1_wordAt bs 376)
        (v1_midQ128 (v1_wordAt bs 128) (v1_wordAt bs 136) (v1_wordAt bs 144))
        (v1_wordAt bs 144 >>> 8)
        (unshiftWord (v1_wordAt bs 104) (loByte (v1_wordAt bs 112)))
        (v1_wordAt bs 112 >>> 8)
        (v1_wordAt bs 0 ++ tag) (v1_wordAt bs 16 ++ v1_wordAt bs 8) (v1_wordAt bs 24) ∗
      epilogueStackGaps (s0.sp - 2400#64) ∗
      statesFromPbSavedCells s0 ∗
      (P_heap ∗
       vecU8Payload A u8 u16 ek ∗
       vecU8Payload A u32 u40 dk ∗
       vecU8Payload A u72 pa1 rootKey ∗
       vecU8Payload A u96 pa2 macKey ∗
       Rest) := by
    refine Entails.trans hP1 ?_
    unfold epilogueStackSlots
    refine Entails.trans (Entails.of_eq (show _ =
      (memRegion (s0.sp - 2400#64) 64 ∗
       ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗
       memRegion (s0.sp - 2400#64 + 72#64) 20 ∗
       memRegion (s0.sp - 2400#64 + 96#64) 8 ∗
       memRegion (s0.sp - 2400#64 + 128#64) 32 ∗
       memRegion (s0.sp - 2400#64 + 168#64) 4 ∗
       ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
       ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
       ((s0.sp - 2400#64 + 200#64) ↦₆₄ pa1) ∗
       ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
       memRegion (s0.sp - 2400#64 + 568#64) 8 ∗
       memRegion (s0.sp - 2400#64 + 599#64) 9 ∗
       memRegion (s0.sp - 2400#64 + 840#64) 8 ∗
       memRegion (s0.sp - 2400#64 + 871#64) 9 ∗
       memRegion (s0.sp - 2400#64 + 895#64) 993 ∗
       memRegion (s0.sp - 2400#64 + 1928#64) 376) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion out chunkedStatesSize ∗
       (((s0.sp - 2400#64 + 92#64) ↦₃₂ d92) ∗
        ((s0.sp - 2400#64 + 104#64) ↦₆₄ w104) ∗
        ((s0.sp - 2400#64 + 112#64) ↦₆₄ w112) ∗
        ((s0.sp - 2400#64 + 120#64) ↦₆₄ w120) ∗
        ((s0.sp - 2400#64 + 160#64) ↦₆₄ u96) ∗
        ((s0.sp - 2400#64 + 172#64) ↦₃₂ (loByte (v1_wordAt bs 128)).zeroExtend 32) ∗
        ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗
        ((s0.sp - 2400#64 + 208#64) ↦₆₄ v1_wordAt bs 0) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
        ((s0.sp - 2400#64 + 240#64) ↦ₛ bs240.val) ∗
        ((s0.sp - 2400#64 + 576#64) ↦₁₂₈ q576) ∗
        ((s0.sp - 2400#64 + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗
        ((s0.sp - 2400#64 + 608#64) ↦₁₂₈ v1_quadAt bs 152) ∗
        ((s0.sp - 2400#64 + 624#64) ↦₁₂₈ v1_quadAt bs 168) ∗
        ((s0.sp - 2400#64 + 640#64) ↦₁₂₈ v1_quadAt bs 184) ∗
        ((s0.sp - 2400#64 + 656#64) ↦₁₂₈ v1_quadAt bs 200) ∗
        ((s0.sp - 2400#64 + 672#64) ↦₁₂₈ v1_quadAt bs 216) ∗
        ((s0.sp - 2400#64 + 688#64) ↦₁₂₈ v1_quadAt bs 232) ∗
        ((s0.sp - 2400#64 + 704#64) ↦₁₂₈ v1_quadAt bs 248) ∗
        ((s0.sp - 2400#64 + 720#64) ↦₁₂₈ v1_quadAt bs 264) ∗
        ((s0.sp - 2400#64 + 736#64) ↦₁₂₈ v1_quadAt bs 280) ∗
        ((s0.sp - 2400#64 + 752#64) ↦₁₂₈ v1_quadAt bs 296) ∗
        ((s0.sp - 2400#64 + 768#64) ↦₁₂₈ v1_quadAt bs 312) ∗
        ((s0.sp - 2400#64 + 784#64) ↦₁₂₈ v1_quadAt bs 328) ∗
        ((s0.sp - 2400#64 + 800#64) ↦₁₂₈ v1_quadAt bs 344) ∗
        ((s0.sp - 2400#64 + 816#64) ↦₁₂₈ v1_quadAt bs 360) ∗
        ((s0.sp - 2400#64 + 832#64) ↦₆₄ v1_wordAt bs 376) ∗
        ((s0.sp - 2400#64 + 848#64) ↦₁₂₈ v1_midQ128 (v1_wordAt bs 128) (v1_wordAt bs 136) (v1_wordAt bs 144)) ∗
        ((s0.sp - 2400#64 + 864#64) ↦ₛ EncoderFromPb.loBytes7 (v1_wordAt bs 144 >>> 8)) ∗
        ((s0.sp - 2400#64 + 880#64) ↦₆₄ unshiftWord (v1_wordAt bs 104) (loByte (v1_wordAt bs 112))) ∗
        ((s0.sp - 2400#64 + 888#64) ↦ₛ EncoderFromPb.loBytes7 (v1_wordAt bs 112 >>> 8)) ∗
        ((s0.sp - 2400#64 + 1888#64) ↦₁₂₈ (v1_wordAt bs 0 ++ tag)) ∗
        ((s0.sp - 2400#64 + 1904#64) ↦₁₂₈ (v1_wordAt bs 16 ++ v1_wordAt bs 8)) ∗
        ((s0.sp - 2400#64 + 1920#64) ↦₆₄ v1_wordAt bs 24)) ∗
       statesFromPbSavedCells s0 ∗
       (P_heap ∗
        vecU8Payload A u8 u16 ek ∗
        vecU8Payload A u32 u40 dk ∗
        vecU8Payload A u72 pa1 rootKey ∗
        vecU8Payload A u96 pa2 macKey ∗
        Rest)) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hgaps) (Entails.of_eq (by ac_rfl))
  have hep := states_from_pb_epilogue_8180 hA s0 s1 out
    d92 ((loByte (v1_wordAt bs 128)).zeroExtend 32)
    w104 w112 w120 u96 u48 (v1_wordAt bs 0) u32 u96 bs240.val bs240.property
    q576 w592
    (v1_quadAt bs 152) (v1_quadAt bs 168) (v1_quadAt bs 184) (v1_quadAt bs 200)
    (v1_quadAt bs 216) (v1_quadAt bs 232) (v1_quadAt bs 248) (v1_quadAt bs 264)
    (v1_quadAt bs 280) (v1_quadAt bs 296) (v1_quadAt bs 312) (v1_quadAt bs 328)
    (v1_quadAt bs 344) (v1_quadAt bs 360)
    (v1_wordAt bs 376)
    (v1_midQ128 (v1_wordAt bs 128) (v1_wordAt bs 136) (v1_wordAt bs 144))
    (v1_wordAt bs 144 >>> 8)
    (unshiftWord (v1_wordAt bs 104) (loByte (v1_wordAt bs 112)))
    (v1_wordAt bs 112 >>> 8)
    (v1_wordAt bs 0 ++ tag) (v1_wordAt bs 16 ++ v1_wordAt bs 8) (v1_wordAt bs 24)
    (P_heap ∗
     vecU8Payload A u8 u16 ek ∗
     vecU8Payload A u32 u40 dk ∗
     vecU8Payload A u72 pa1 rootKey ∗
     vecU8Payload A u96 pa2 macKey ∗
     Rest)
    hsp0_align hpc1 hrun1 hsp1 hx6_1 hx19_1 hx23_1 htr1
  refine SepWP.weaken_pre hP1' (SepWP.mono hep ?_)
  intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
  refine ⟨Entails.trans hPf ?_, hsp_f, hcs_f, htr_f⟩
  rw [hx8_1, hx15_1, hx20_1, hx13_1, hx25_1, hx30_1, hx9_1, hx14_1, hx18_1, hx17_1, hx0_1,
      hx3_1, v1_zext32_setWidth8, hx27_1, hx27_hi16, hx27_hi8, hx4_1, hx5_1,
      hx21_1, v1_zext32_setWidth8, hx7_1, hx2_1, hx11_1, hx22_1, hx24_1, hx10_1,
      hx26_1, hx12_1, hx1_1, ← hu24_1152, hx28_1, hx16_1]
  have hout := v1_epilogueOutFull_entails_keysSampled A (F := F)
    out tag u72 pa1 u96 pa2 u8 u16 u24 u32 u40 u48 u104
    bs hbs hi32 enc P_heap hreloc ek dk rootKey macKey hek hdk hl1 hl2
    w104 w112 w120 (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592)
    bs240.val bs240.property
    (v1_wordAt bs 0 ++ tag) (v1_wordAt bs 16 ++ v1_wordAt bs 8) (v1_wordAt bs 24)
  refine Entails.trans (Entails.of_eq (show _ =
    (epilogueOutFull out
      3#64 tag (v1_wordAt bs 0) (v1_wordAt bs 8)
      (v1_wordAt bs 16) (v1_wordAt bs 24) (v1_wordAt bs 32) (v1_wordAt bs 40)
      (v1_wordAt bs 48) (v1_wordAt bs 56) (v1_wordAt bs 64) (v1_wordAt bs 72)
      ((v1_wordAt bs 80).extractLsb' 0 8) ((v1_wordAt bs 80).extractLsb' 8 32)
      ((v1_wordAt bs 80).extractLsb' 40 16) ((v1_wordAt bs 80).extractLsb' 56 8)
      (v1_wordAt bs 88) (v1_wordAt bs 96) (loByte (v1_wordAt bs 104))
      (unshiftWord (v1_wordAt bs 104) (loByte (v1_wordAt bs 112)))
      (overlapWord7 (unshiftWord (v1_wordAt bs 104) (loByte (v1_wordAt bs 112)))
        (v1_wordAt bs 112 >>> 8))
      (v1_wordAt bs 120)
      (((loByte (v1_wordAt bs 128)).zeroExtend 32).setWidth 8)
      (v1_midQ128 (v1_wordAt bs 128) (v1_wordAt bs 136) (v1_wordAt bs 144))
      (overlapWord7
        ((v1_midQ128 (v1_wordAt bs 128) (v1_wordAt bs 136) (v1_wordAt bs 144)).extractLsb' 64 64)
        (v1_wordAt bs 144 >>> 8))
      (v1_quadAt bs 152) (v1_quadAt bs 168) (v1_quadAt bs 184) (v1_quadAt bs 200)
      (v1_quadAt bs 216) (v1_quadAt bs 232) (v1_quadAt bs 248) (v1_quadAt bs 264)
      (v1_quadAt bs 280) (v1_quadAt bs 296) (v1_quadAt bs 312) (v1_quadAt bs 328)
      (v1_quadAt bs 344) (v1_quadAt bs 360)
      (v1_wordAt bs 376) (hi32 ++ enc.idx)
      u72 pa1 u72 u96 pa2 u96 u8 u16 u24 u32 u40 u48 u104
      w104 w112 w120
      (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592)
      bs240.val (v1_wordAt bs 0 ++ tag) (v1_wordAt bs 16 ++ v1_wordAt bs 8) (v1_wordAt bs 24) ∗
     P_heap ∗
     vecU8Payload A u8 u16 ek ∗
     vecU8Payload A u32 u40 dk ∗
     vecU8Payload A u72 pa1 rootKey ∗
     vecU8Payload A u96 pa2 macKey) ∗
    Rest ∗
    stackAt s0.sp statesFromPbStack by ac_rfl)) ?_
  exact sepConj_mono_left hout

end CryptoVerification.SpqrV1.States.FromPb

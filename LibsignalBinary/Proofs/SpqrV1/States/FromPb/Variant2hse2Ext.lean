/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hse2
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsdExt
import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBase
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hseExt -- shake: keep

/-! # `<spqr::v1::chunked::states::States>::from_pb`: 4-KiB Hook Wrapper for `Variant2hse2` -/

@[expose] public section

set_option autoImplicit false
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
  stubOff_rust_no_alloc_shim
  stubOff_rust_alloc
  stubOff_rust_dealloc
  stubOff_memcpy
  stubOff_memset
  stubOff_handle_error
  fnOff_poly_encoder_from_pb
  fnOff_poly_decoder_from_pb

open CryptoVerification.SpqrV1.Alloc
attribute [local simp, local arm64_norm, local wp_norm] v2hse2_polyEncoderTag_sub_two_beq_zero
attribute [local simp, local arm64_norm, local wp_norm] v2hse2_polyEncoderTag_bne_two
attribute [local simp, local arm64_norm, local wp_norm] v2hse2_x25_add_105_sext
attribute [local simp, local arm64_norm, local wp_norm] v2hse2_x25_add_105
attribute [local simp, local arm64_norm, local wp_norm] v2hse2_fsp_1897_add_8
attribute [local simp, local arm64_norm, local wp_norm] v2hse2_x24_add_32
attribute [local simp, local arm64_norm, local wp_norm] v2hse2_fsp_1392_add_32
attribute [local simp, local arm64_norm, local wp_norm] v2hse2_fsp_240_add_8
attribute [local simp, local arm64_norm, local wp_norm] v2hse2_fsp_add_255_sext
attribute [local simp, local arm64_norm, local wp_norm] v2hse2_fsp_1264_add_137_sext
attribute [local simp, local arm64_norm, local wp_norm] v2hse2_fsp_1264_add_137
attribute [local simp, local arm64_norm, local wp_norm] v2hse2_fsp_1401_add_8
attribute [local simp, local arm64_norm, local wp_norm] v2hse2_zext64_setWidth32_setWidth8
attribute [local simp, local arm64_norm, local wp_norm] v2hse2_zext32_setWidth8
attribute [local simp, local arm64_norm, local wp_norm] v2hse2_zext64_setWidth8

namespace Ext4K

/-- When `<PolyEncoder>::from_pb` returns `.error err` at `fsp + 1888`, steps `+9100 -> +9112`,
deallocates `(ca1, pa1)`, `(ca2, pa2)`, `(ca3, pa3)` via `v2hsd_cleanup_9112_to_9212`, and reaches `+9212`. -/
theorem v2hse2_enc_err_9100_to_9212
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (fsp out d0 ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch : BitVec 64)
    (err : PolynomialError) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9100#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9212#64) s1
      (stackAt fsp encoderFromPbStack ∗
        resultPolyEncoderFromPbAt A (fsp + 1888#64) (.error err) ∗
        ((fsp + 200#64) ↦₆₄ ca1) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        v2hse_unchunkedEkSentWordsAt (fsp + 1264#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch ∗
        vecCapPtrDealloc A ca1 pa1 ∗
        vecCapPtrDealloc A ca2 pa2 ∗
        vecCapPtrDealloc A ca3 pa3 ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1888#64) 400 ∗
          ((fsp + 200#64) ↦₆₄ ca1) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          memRegion (fsp + 1264#64) 80 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        TraceCalleeSaved sm s0) := by
  unfold v2hse_unchunkedEkSentWordsAt
  simp only [v2hse2_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (v2hse2_resultPolyEncoder_err_entails_tag_392 A fsp err))) ?_
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9112#64)
    (P_mid :=
      stackAt fsp encoderFromPbStack ∗
      ((fsp + 200#64) ↦₆₄ ca1) ∗
      ((fsp + 1272#64) ↦₆₄ pa1) ∗
      ((fsp + 184#64) ↦₆₄ pa2) ∗
      ((fsp + 232#64) ↦₆₄ ca2) ∗
      ((fsp + 176#64) ↦₆₄ pa3) ∗
      vecCapPtrDealloc A ca1 pa1 ∗
      vecCapPtrDealloc A ca2 pa2 ∗
      vecCapPtrDealloc A ca3 pa3 ∗
      A.pool ∗
      (memRegion (fsp + 1888#64) 400 ∗
       ((fsp + 1264#64) ↦₆₄ ca1) ∗
       ((fsp + 1280#64) ↦₆₄ la1) ∗
       ((fsp + 1288#64) ↦₆₄ ca2) ∗
       ((fsp + 1296#64) ↦₆₄ pa2) ∗
       ((fsp + 1304#64) ↦₆₄ la2) ∗
       ((fsp + 1312#64) ↦₆₄ ca3) ∗
       ((fsp + 1320#64) ↦₆₄ pa3) ∗
       ((fsp + 1328#64) ↦₆₄ la3) ∗
       ((fsp + 1336#64) ↦₆₄ epoch) ∗
       Frame))
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = d0 ∧
      sm.readReg64 .x26 = ca3 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · states_from_pb_fetches_range b (Rust.withPanics ext) 9100 12
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_simp_pre [sepConj_assoc]
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have h400 := v2hse2_1888_tag_392_to_memRegion_400 fsp 2#64
      refine Entails.trans (Entails.of_eq (show _ =
        (((fsp + 1888#64) ↦₆₄ 2#64) ∗ memRegion (fsp + 1896#64) 392) ∗
        (stackAt fsp encoderFromPbStack ∗
         ((fsp + 200#64) ↦₆₄ ca1) ∗
         ((fsp + 1272#64) ↦₆₄ pa1) ∗
         ((fsp + 184#64) ↦₆₄ pa2) ∗
         ((fsp + 232#64) ↦₆₄ ca2) ∗
         ((fsp + 176#64) ↦₆₄ pa3) ∗
         vecCapPtrDealloc A ca1 pa1 ∗
         vecCapPtrDealloc A ca2 pa2 ∗
         vecCapPtrDealloc A ca3 pa3 ∗
         A.pool ∗
         ((fsp + 1264#64) ↦₆₄ ca1) ∗
         ((fsp + 1280#64) ↦₆₄ la1) ∗
         ((fsp + 1288#64) ↦₆₄ ca2) ∗
         ((fsp + 1296#64) ↦₆₄ pa2) ∗
         ((fsp + 1304#64) ↦₆₄ la2) ∗
         ((fsp + 1312#64) ↦₆₄ ca3) ∗
         ((fsp + 1320#64) ↦₆₄ pa3) ∗
         ((fsp + 1328#64) ↦₆₄ la3) ∗
         ((fsp + 1336#64) ↦₆₄ epoch) ∗ Frame) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left h400) (Entails.of_eq (by ac_rfl))
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx26_2, htr2⟩
    have h9112 := v2hsd_cleanup_9112_to_9212 hA s0 s2 fsp out d0 ca1 pa1 ca2 pa2 ca3 pa3
      (memRegion (fsp + 1888#64) 400 ∗
       ((fsp + 1264#64) ↦₆₄ ca1) ∗
       ((fsp + 1280#64) ↦₆₄ la1) ∗
       ((fsp + 1288#64) ↦₆₄ ca2) ∗
       ((fsp + 1296#64) ↦₆₄ pa2) ∗
       ((fsp + 1304#64) ↦₆₄ la2) ∗
       ((fsp + 1312#64) ↦₆₄ ca3) ∗
       ((fsp + 1320#64) ↦₆₄ pa3) ∗
       ((fsp + 1328#64) ↦₆₄ la3) ∗
       ((fsp + 1336#64) ↦₆₄ epoch) ∗
       Frame)
      hfsp_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx26_2 htr2
    refine SepWP.mono h9112 fun sm Pm _ _ ⟨hPm, hq⟩ => ⟨Entails.trans hPm ?_, hq⟩
    have hm80 := v2hse_unchunkedEkSentWordsAt_entails_80 (fsp + 1264#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch
    unfold v2hse_unchunkedEkSentWordsAt at hm80
    simp only [v2hse2_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at hm80
    refine Entails.trans (Entails.of_eq (show _ =
      (((fsp + 1264#64) ↦₆₄ ca1) ∗
       ((fsp + 1272#64) ↦₆₄ pa1) ∗
       ((fsp + 1280#64) ↦₆₄ la1) ∗
       ((fsp + 1288#64) ↦₆₄ ca2) ∗
       ((fsp + 1296#64) ↦₆₄ pa2) ∗
       ((fsp + 1304#64) ↦₆₄ la2) ∗
       ((fsp + 1312#64) ↦₆₄ ca3) ∗
       ((fsp + 1320#64) ↦₆₄ pa3) ∗
       ((fsp + 1328#64) ↦₆₄ la3) ∗
       ((fsp + 1336#64) ↦₆₄ epoch)) ∗
      (stackAt fsp encoderFromPbStack ∗
       memRegion (fsp + 1888#64) 400 ∗
       ((fsp + 200#64) ↦₆₄ ca1) ∗
       ((fsp + 184#64) ↦₆₄ pa2) ∗
       ((fsp + 232#64) ↦₆₄ ca2) ∗
       ((fsp + 176#64) ↦₆₄ pa3) ∗
       A.pool ∗ Frame) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hm80) (Entails.of_eq (by ac_rfl))

set_option maxHeartbeats 1200000 in
/-- When `<PolyEncoder>::from_pb` returns `.ok enc` at `fsp + 1888`, steps `+9100 -> +9248 -> +9328`,
moving `polyEncoderAt` words from `fsp + 1888..2288` to `fsp + 1392..1792`, storing `v2hse2_polyEncoderTag enc`
to `[sp + 56]`, and setting `pstate = addsPState64 d0 1#64`. -/
theorem v2hse2_enc_ok_move_9100_to_9328
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (fsp out d0 ca3 pbA slot56_old w8 w16 w24 : BitVec 64)
    (tail368 : { l : List (BitVec 8) // l.length = 368 })
    (enc : PolyEncoder) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9100#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx24_1 : s1.readReg64 .x24 = fsp + 1888#64)
    (hx25_1 : s1.readReg64 .x25 = fsp + 1792#64)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9328#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 1888#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
        ((fsp + 1896#64) ↦₆₄ w8) ∗
        ((fsp + 1904#64) ↦₆₄ w16) ∗
        ((fsp + 1912#64) ↦₆₄ w24) ∗
        ((fsp + 1920#64) ↦ₛ tail368.val) ∗
        memRegion (fsp + 1392#64) 400 ∗
        memRegion (fsp + 240#64) 24 ∗
        ((fsp + 56#64) ↦₆₄ slot56_old) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1888#64) 400 ∗
          ((fsp + 1392#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
          ((fsp + 1400#64) ↦₆₄ w8) ∗
          ((fsp + 1408#64) ↦₆₄ w16) ∗
          ((fsp + 1416#64) ↦₆₄ w24) ∗
          ((fsp + 1424#64) ↦ₛ tail368.val) ∗
          memRegion (fsp + 240#64) 24 ∗
          ((fsp + 56#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = (loByte w8).zeroExtend 64 ∧
        sm.readReg64 .x21 = s1.readReg64 .x21 ∧
        sm.readReg64 .x22 = d0 ∧
        sm.readReg64 .x23 = fsp + 1392#64 ∧
        sm.readReg64 .x24 = fsp + 1888#64 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧
        sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = s1.readReg64 .x28 ∧
        sm.pstate = addsPState64 d0 1#64 ∧
        TraceCalleeSaved sm s0) := by
  subst hsp1
  have hmemcpy := hA.session_memcpy_ok_at statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "memcpy"))
  simp only [sessionMemcpySpec, allocHookStack, stackAt] at hmemcpy
  wp_conv_pre =>
    rw [v2hse2_stackAt_encoderFromPbStack_eq_allocHook s1.sp]
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono (v2hse2_memRegion_1392_400_split_32_368 s1.sp)
          (sepConj_mono_left (v2hse2_memRegion_240_24_split s1.sp))))))))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro d16
  apply ProofLib.SepWP.exists_left; intro d8
  apply ProofLib.SepWP.exists_left; intro d0_spill
  apply ProofLib.SepWP.exists_left; intro e24
  apply ProofLib.SepWP.exists_left; intro e16
  apply ProofLib.SepWP.exists_left; intro e8
  apply ProofLib.SepWP.exists_left; intro e0
  states_from_pb_fetches_range b (Rust.withPanics ext) 9100 12
  states_from_pb_fetches_range b (Rust.withPanics ext) 9248 80
  dsimp only [contractProg, tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hmemcpy hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_simp_pre only [v2hse2_fsp1896_to_unaligned16_rest, sepConj_assoc]
  iterate 4 wp_step
  wp_simp_pre only [v2hse2_fsp1896_to_threeWords_rest, sepConj_assoc]
  iterate 2 wp_step
  wp_simp_pre only [v2hse2_fsp1896_split_rest, sepConj_assoc]
  wp_step
  wp_simp_pre only [v2hse2_fsp1896_unsplit_rest, sepConj_assoc]
  iterate 4 wp_step
  wp_simp_pre only [v2hse2_fsp_248_realign_rest, sepConj_assoc]
  iterate 3 wp_step
  have hlen368 : (368 : Nat) = tail368.val.length := tail368.property.symm
  wp_simp_pre [hlen368, sepConj_assoc]
  wp_call hmemcpy (s1.sp + 1424#64, s1.sp + 1920#64, tail368.val)
  wp_step
  wp_simp_pre only [v2hse2_fsp_248_unrealign_w24_rest, sepConj_assoc]
  wp_step
  wp_simp_pre only [v2hse2_fsp1400_to_unaligned16_rest, sepConj_assoc]
  iterate 4 wp_step
  wp_simp_pre only [v2hse2_fsp_248_realign_w24_rest, sepConj_assoc]
  wp_step
  wp_step
  wp_simp_pre only [v2hse2_fsp1400_to_threeWords_mixed_rest, sepConj_assoc]
  wp_step
  wp_simp_pre only [v2hse2_fsp_248_unrealign_w24_rest, sepConj_assoc]
  refine EncoderFromPb.align_pre ?_ ?_
  · have h1888_400 := v2hse2_1888_32_368_entails_memRegion_400 s1.sp (v2hse2_polyEncoderTag enc) w8 w16 w24 tail368
    have h240_24 := v2hse2_240_spill_entails_memRegion_24 s1.sp
      (unshiftWord w8 (loByte w16)) (unshiftWord w16 (loByte w24)) (w24 >>> 8) ((d16 >>> 56).setWidth 8)
    refine Entails.trans (Entails.of_eq (show _ =
      (memRegion (s1.sp - 4096#64) 4096 ∗ memRegion (s1.sp - 5152#64) 1056) ∗
      (((s1.sp + 1888#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
       ((s1.sp + 1896#64) ↦₆₄ w8) ∗ ((s1.sp + 1904#64) ↦₆₄ w16) ∗
       ((s1.sp + 1912#64) ↦₆₄ w24) ∗ ((s1.sp + 1920#64) ↦ₛ tail368.val)) ∗
      ((s1.sp + 1392#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
      ((s1.sp + 1400#64) ↦₆₄ w8) ∗ ((s1.sp + 1408#64) ↦₆₄ w16) ∗
      ((s1.sp + 1416#64) ↦₆₄ w24) ∗ ((s1.sp + 1424#64) ↦ₛ tail368.val) ∗
      (((s1.sp + 240#64) ↦₆₄ unshiftWord w8 (loByte w16)) ∗
       ((s1.sp + 248#64) ↦₆₄ unshiftWord w16 (loByte w24)) ∗
       (((s1.sp + 256#64) ↦ₛ EncoderFromPb.loBytes7 (w24 >>> 8)) ∗
        ((s1.sp + 263#64) ↦₈ (d16 >>> 56).setWidth 8))) ∗
      ((s1.sp + 56#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
      Frame by ac_rfl)) ?_
    rw [← v2hse2_stackAt_encoderFromPbStack_eq_allocHook s1.sp]
    exact sepConj_mono (Entails.refl _) (sepConj_mono h1888_400
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono h240_24 (Entails.refl _))))))))
  · wp_done

end Ext4K

end CryptoVerification.SpqrV1.States.FromPb

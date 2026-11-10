/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7i
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7h
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: 4-KiB Hook Companion for `Variant7i`

Lifts `Variant7i.lean`'s `AllocContracts`-parameterized theorems to `AllocContracts4K`
inside `CryptoVerification.SpqrV1.States.FromPb.Ext4K`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.States.FromPb.Ext4K

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
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.States.FromPb

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
  fnOff_ct1_sent_from_pb
  fnOff_poly_encoder_from_pb
  fnOff_poly_decoder_from_pb

theorem v7_dec_ok_7404_to_7468
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (fsp out pbA c2 l1 w0_dec w8_dec w16_dec w24_dec w120_old w592_old : BitVec 64)
    (d92_old : BitVec 32) (q576_old : BitVec 128)
    (tail368_dec : { l : List (BitVec 8) // l.length = 368 })
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hw0_dec_lt : w0_dec.toNat < 2 ^ 63)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7404#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = fsp + 1392#64)
    (hx22_1 : s1.readReg64 .x22 = fsp + 1888#64)
    (hx23_1 : s1.readReg64 .x23 = fsp + 848#64)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7468#64) s1
      (stackAt fsp allocHookStack ∗
        ((fsp + 92#64) ↦₃₂ d92_old) ∗
        ((fsp + 120#64) ↦₆₄ w120_old) ∗
        ((fsp + 576#64) ↦₁₂₈ q576_old) ∗
        ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592_old) ∗
        memRegion (fsp + 896#64) 368 ∗
        ((fsp + 1888#64) ↦₆₄ w0_dec) ∗
        ((fsp + 1896#64) ↦₆₄ w8_dec) ∗
        ((fsp + 1904#64) ↦₆₄ w16_dec) ∗
        ((fsp + 1912#64) ↦₆₄ w24_dec) ∗
        ((fsp + 1920#64) ↦ₛ tail368_dec.val) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp allocHookStack ∗
          ((fsp + 92#64) ↦₃₂ (loByte w8_dec).zeroExtend 32) ∗
          ((fsp + 120#64) ↦₆₄ w0_dec) ∗
          ((fsp + 576#64) ↦₁₂₈ v7_midQ128 w8_dec w16_dec w24_dec) ∗
          ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 (w24_dec >>> 8)) ∗
          ((fsp + 896#64) ↦ₛ tail368_dec.val) ∗
          memRegion (fsp + 1888#64) 400 ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = fsp + 1392#64 ∧
        sm.readReg64 .x22 = fsp + 1888#64 ∧
        sm.readReg64 .x23 = fsp + 848#64 ∧
        sm.readReg64 .x24 = c2 ∧
        sm.readReg64 .x26 = l1 ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) := by
  subst hsp1
  have hw0_ne := cap_add_one_beq_zero_false hw0_dec_lt
  have hmemcpy := hA.session_memcpy_ok_at statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "memcpy"))
  simp only [sessionMemcpySpec, allocHookStack] at hmemcpy ⊢
  states_from_pb_fetches_range b (Rust.withPanics ext) 7404 64
  dsimp only [contractProg, tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hmemcpy hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_simp_pre [pointsTo128_eq_pair64, v7_fsp_1896_triple_rest, sepConj_assoc]
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_simp_pre only [v7_fsp_1905_realign_rest, sepConj_assoc]
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_simp_pre only [fsp_584_realign_rest, sepConj_assoc]
  wp_step
  wp_step
  have hlen368 : (368 : Nat) = tail368_dec.val.length := tail368_dec.property.symm
  wp_simp_pre only [v7_fsp_584_realign_low7_rest, hlen368, sepConj_assoc]
  wp_call hmemcpy (s1.sp + 896#64, s1.sp + 1920#64, tail368_dec.val)
  wp_simp_pre only [v7_1896_realign_final_rest, sepConj_assoc]
  refine EncoderFromPb.align_pre ?_ ?_
  · have h1888_400 := v7_1888_32_368_entails_memRegion_400 s1.sp w0_dec w8_dec w16_dec w24_dec tail368_dec
    have hq576 :
        ((s1.sp + 576#64) ↦₆₄ unshiftWord w8_dec (loByte w16_dec)) ∗
        ((s1.sp + 584#64) ↦₆₄ unshiftWord w16_dec (loByte w24_dec)) =
        ((s1.sp + 576#64) ↦₁₂₈ v7_midQ128 w8_dec w16_dec w24_dec) := by
      unfold v7_midQ128
      rw [← v7_fsp_576_add_8 s1.sp, EncoderFromPb.pointsTo64_pair_eq_pointsTo128]
    refine Entails.trans (Entails.of_eq (show _ =
      (((s1.sp + 1888#64) ↦₆₄ w0_dec) ∗
       ((s1.sp + 1896#64) ↦₆₄ w8_dec) ∗
       ((s1.sp + 1904#64) ↦₆₄ w16_dec) ∗
       ((s1.sp + 1912#64) ↦₆₄ w24_dec) ∗
       ((s1.sp + 1920#64) ↦ₛ tail368_dec.val)) ∗
      (((s1.sp + 576#64) ↦₆₄ unshiftWord w8_dec (loByte w16_dec)) ∗
       ((s1.sp + 584#64) ↦₆₄ unshiftWord w16_dec (loByte w24_dec))) ∗
      (stackAt s1.sp 4096 ∗
       ((s1.sp + 92#64) ↦₃₂ (loByte w8_dec).zeroExtend 32) ∗
       ((s1.sp + 120#64) ↦₆₄ w0_dec) ∗
       ((s1.sp + 592#64) ↦ₛ EncoderFromPb.loBytes7 (w24_dec >>> 8)) ∗
       ((s1.sp + 896#64) ↦ₛ tail368_dec.val) ∗
       Frame) by ac_rfl)) ?_
    rw [hq576]
    exact Entails.trans (sepConj_mono_left h1888_400) (Entails.of_eq (by ac_rfl))
  · wp_done

theorem v7_dec_ok_7468_to_8180
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s : State) (fsp out tag c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ep : BitVec 64)
    (bs : List (BitVec 8)) (_hbs : bs.length = 384)
    (hi32 idx : BitVec 32)
    (bs328_dec : { l : List (BitVec 8) // l.length = 328 })
    (q328_dec q344_dec : BitVec 128) (w360_dec : BitVec 64)
    (w8_old w32_old w40_old w48_old w56_old w64_old w72_old w80_old w96_old w104_old w112_old
      w128_old w136_old w144_old w152_old w160_old w176_old w184_old w192_old w208_old w216_old
      w224_old w232_old w832_old w864_old w880_old w888_old w1920_old : BitVec 64)
    (d172_old : BitVec 32)
    (q608_old q624_old q640_old q656_old q672_old q688_old q704_old q720_old
      q736_old q752_old q768_old q784_old q800_old q816_old q848_old q1888_old q1904_old : BitVec 128)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7468#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = fsp + 1392#64)
    (hx24 : s.readReg64 .x24 = c2)
    (hx26 : s.readReg64 .x26 = l1)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8180#64) s
      (stackAt fsp allocHookStack ∗
        ((fsp + 8#64) ↦₆₄ w8_old) ∗
        ((fsp + 16#64) ↦₆₄ tag) ∗
        ((fsp + 24#64) ↦₆₄ c1) ∗
        ((fsp + 32#64) ↦₆₄ w32_old) ∗
        ((fsp + 40#64) ↦₆₄ w40_old) ∗
        ((fsp + 48#64) ↦₆₄ w48_old) ∗
        ((fsp + 56#64) ↦₆₄ w56_old) ∗
        ((fsp + 64#64) ↦₆₄ w64_old) ∗
        ((fsp + 72#64) ↦₆₄ w72_old) ∗
        ((fsp + 80#64) ↦₆₄ w80_old) ∗
        ((fsp + 96#64) ↦₆₄ w96_old) ∗
        ((fsp + 104#64) ↦₆₄ w104_old) ∗
        ((fsp + 112#64) ↦₆₄ w112_old) ∗
        ((fsp + 128#64) ↦₆₄ w128_old) ∗
        ((fsp + 136#64) ↦₆₄ w136_old) ∗
        ((fsp + 144#64) ↦₆₄ w144_old) ∗
        ((fsp + 152#64) ↦₆₄ w152_old) ∗
        ((fsp + 160#64) ↦₆₄ w160_old) ∗
        ((fsp + 172#64) ↦₃₂ d172_old) ∗
        ((fsp + 176#64) ↦₆₄ w176_old) ∗
        ((fsp + 184#64) ↦₆₄ w184_old) ∗
        ((fsp + 192#64) ↦₆₄ w192_old) ∗
        ((fsp + 200#64) ↦₆₄ p1) ∗
        ((fsp + 208#64) ↦₆₄ w208_old) ∗
        ((fsp + 216#64) ↦₆₄ w216_old) ∗
        ((fsp + 224#64) ↦₆₄ w224_old) ∗
        ((fsp + 232#64) ↦₆₄ w232_old) ∗
        memRegion (fsp + 240#64) 328 ∗
        ((fsp + 608#64) ↦₁₂₈ q608_old) ∗ ((fsp + 624#64) ↦₁₂₈ q624_old) ∗
        ((fsp + 640#64) ↦₁₂₈ q640_old) ∗ ((fsp + 656#64) ↦₁₂₈ q656_old) ∗
        ((fsp + 672#64) ↦₁₂₈ q672_old) ∗ ((fsp + 688#64) ↦₁₂₈ q688_old) ∗
        ((fsp + 704#64) ↦₁₂₈ q704_old) ∗ ((fsp + 720#64) ↦₁₂₈ q720_old) ∗
        ((fsp + 736#64) ↦₁₂₈ q736_old) ∗ ((fsp + 752#64) ↦₁₂₈ q752_old) ∗
        ((fsp + 768#64) ↦₁₂₈ q768_old) ∗ ((fsp + 784#64) ↦₁₂₈ q784_old) ∗
        ((fsp + 800#64) ↦₁₂₈ q800_old) ∗ ((fsp + 816#64) ↦₁₂₈ q816_old) ∗
        ((fsp + 832#64) ↦₆₄ w832_old) ∗
        ((fsp + 848#64) ↦₁₂₈ q848_old) ∗ ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 w864_old) ∗
        ((fsp + 880#64) ↦₆₄ w880_old) ∗ ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 w888_old) ∗
        ((fsp + 896#64) ↦ₛ bs328_dec.val) ∗
        ((fsp + 1224#64) ↦₁₂₈ q328_dec) ∗
        ((fsp + 1240#64) ↦₁₂₈ q344_dec) ∗
        ((fsp + 1256#64) ↦₆₄ w360_dec) ∗
        v7_ct1SentWordsAt (fsp + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ep ∗
        ((fsp + 1392#64) ↦₆₄ tag) ∗
        v7_encCellsAt (fsp + 1392#64) bs ∗
        ((fsp + 1784#64) ↦₆₄ (hi32 ++ idx)) ∗
        ((fsp + 1888#64) ↦₁₂₈ q1888_old) ∗
        ((fsp + 1904#64) ↦₁₂₈ q1904_old) ∗
        ((fsp + 1920#64) ↦₆₄ w1920_old) ∗
        Rest)
      (fun s1 P1 =>
        (P1 ⊢
          stackAt fsp allocHookStack ∗
          ((fsp + 8#64) ↦₆₄ v7_wordAt bs 128) ∗
          ((fsp + 16#64) ↦₆₄ tag) ∗
          ((fsp + 24#64) ↦₆₄ c1) ∗
          ((fsp + 32#64) ↦₆₄ ((v7_wordAt bs 88).extractLsb' 0 8).zeroExtend 64) ∗
          ((fsp + 40#64) ↦₆₄ v7_wordAt bs 40) ∗
          ((fsp + 48#64) ↦₆₄ v7_wordAt bs 96) ∗
          ((fsp + 56#64) ↦₆₄ v7_wordAt bs 0) ∗
          ((fsp + 64#64) ↦₆₄ p5) ∗
          ((fsp + 72#64) ↦₆₄ v7_wordAt bs 80) ∗
          ((fsp + 80#64) ↦₆₄ v7_wordAt bs 64) ∗
          ((fsp + 96#64) ↦₆₄ c4) ∗
          ((fsp + 104#64) ↦₆₄ l5) ∗
          ((fsp + 112#64) ↦₆₄ ep) ∗
          ((fsp + 128#64) ↦₆₄ v7_wordAt bs 72) ∗
          ((fsp + 136#64) ↦₆₄ v7_wordAt bs 32) ∗
          ((fsp + 144#64) ↦₆₄ v7_wordAt bs 56) ∗
          ((fsp + 152#64) ↦₆₄ v7_wordAt bs 48) ∗
          ((fsp + 160#64) ↦₆₄ c3) ∗
          ((fsp + 172#64) ↦₃₂ (loByte (v7_wordAt bs 136)).zeroExtend 32) ∗
          ((fsp + 176#64) ↦₆₄ l3) ∗
          ((fsp + 184#64) ↦₆₄ l2) ∗
          ((fsp + 192#64) ↦₆₄ c5) ∗
          ((fsp + 200#64) ↦₆₄ p1) ∗
          ((fsp + 208#64) ↦₆₄ v7_wordAt bs 8) ∗
          ((fsp + 216#64) ↦₆₄ v7_wordAt bs 24) ∗
          ((fsp + 224#64) ↦₆₄ p4) ∗
          ((fsp + 232#64) ↦₆₄ p2) ∗
          ((fsp + 240#64) ↦ₛ bs328_dec.val) ∗
          ((fsp + 608#64) ↦₁₂₈ v7_quadAt bs 160) ∗ ((fsp + 624#64) ↦₁₂₈ v7_quadAt bs 176) ∗
          ((fsp + 640#64) ↦₁₂₈ v7_quadAt bs 192) ∗ ((fsp + 656#64) ↦₁₂₈ v7_quadAt bs 208) ∗
          ((fsp + 672#64) ↦₁₂₈ v7_quadAt bs 224) ∗ ((fsp + 688#64) ↦₁₂₈ v7_quadAt bs 240) ∗
          ((fsp + 704#64) ↦₁₂₈ v7_quadAt bs 256) ∗ ((fsp + 720#64) ↦₁₂₈ v7_quadAt bs 272) ∗
          ((fsp + 736#64) ↦₁₂₈ v7_quadAt bs 288) ∗ ((fsp + 752#64) ↦₁₂₈ v7_quadAt bs 304) ∗
          ((fsp + 768#64) ↦₁₂₈ v7_quadAt bs 320) ∗ ((fsp + 784#64) ↦₁₂₈ v7_quadAt bs 336) ∗
          ((fsp + 800#64) ↦₁₂₈ v7_quadAt bs 352) ∗ ((fsp + 816#64) ↦₁₂₈ v7_quadAt bs 368) ∗
          ((fsp + 832#64) ↦₆₄ (hi32 ++ idx)) ∗
          ((fsp + 848#64) ↦₁₂₈ v7_midQ128 (v7_wordAt bs 136) (v7_wordAt bs 144) (v7_wordAt bs 152)) ∗
          ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 (v7_wordAt bs 152 >>> 8)) ∗
          ((fsp + 880#64) ↦₆₄ unshiftWord (v7_wordAt bs 112) (loByte (v7_wordAt bs 120))) ∗
          ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 (v7_wordAt bs 120 >>> 8)) ∗
          ((fsp + 896#64) ↦ₛ bs328_dec.val) ∗
          ((fsp + 1224#64) ↦₁₂₈ q328_dec) ∗
          ((fsp + 1240#64) ↦₁₂₈ q344_dec) ∗
          ((fsp + 1256#64) ↦₆₄ w360_dec) ∗
          v7_ct1SentWordsAt (fsp + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ep ∗
          ((fsp + 1392#64) ↦₆₄ tag) ∗
          v7_encCellsAt (fsp + 1392#64) bs ∗
          ((fsp + 1784#64) ↦₆₄ (hi32 ++ idx)) ∗
          ((fsp + 1888#64) ↦₁₂₈ q328_dec) ∗
          ((fsp + 1904#64) ↦₁₂₈ q344_dec) ∗
          ((fsp + 1920#64) ↦₆₄ w360_dec) ∗
          Rest) ∧
        s1.sp = fsp ∧
        s1.readReg64 .x6 = fsp + 576#64 ∧
        s1.readReg64 .x19 = out ∧
        s1.readReg64 .x23 = fsp + 848#64 ∧
        s1.readReg64 .x8 = tag ∧
        s1.readReg64 .x15 = v7_wordAt bs 0 ∧
        s1.readReg64 .x20 = v7_wordAt bs 16 ∧
        s1.readReg64 .x13 = v7_wordAt bs 24 ∧
        s1.readReg64 .x25 = v7_wordAt bs 32 ∧
        s1.readReg64 .x30 = v7_wordAt bs 40 ∧
        s1.readReg64 .x9 = v7_wordAt bs 48 ∧
        s1.readReg64 .x14 = v7_wordAt bs 56 ∧
        s1.readReg64 .x18 = v7_wordAt bs 64 ∧
        s1.readReg64 .x17 = v7_wordAt bs 72 ∧
        s1.readReg64 .x0 = v7_wordAt bs 80 ∧
        s1.readReg32 .x3 = ((v7_wordAt bs 88).extractLsb' 0 8).zeroExtend 32 ∧
        s1.readReg32 .x27 = (v7_wordAt bs 88).extractLsb' 8 32 ∧
        ((s1.readReg64 .x27 >>> 32).setWidth 32).setWidth 16 = (v7_wordAt bs 88).extractLsb' 40 16 ∧
        ((s1.readReg64 .x27 >>> 48).setWidth 32).setWidth 8 = (v7_wordAt bs 88).extractLsb' 56 8 ∧
        s1.readReg64 .x4 = v7_wordAt bs 96 ∧
        s1.readReg64 .x5 = v7_wordAt bs 104 ∧
        s1.readReg32 .x21 = (loByte (v7_wordAt bs 112)).zeroExtend 32 ∧
        s1.readReg64 .x7 = v7_wordAt bs 128 ∧
        s1.readReg64 .x2 = c1 ∧
        s1.readReg64 .x11 = p1 ∧
        s1.readReg64 .x22 = l1 ∧
        s1.readReg64 .x24 = c2 ∧
        s1.readReg64 .x10 = l2 ∧
        s1.readReg64 .x26 = p3 ∧
        s1.readReg64 .x12 = l3 ∧
        s1.readReg64 .x1 = c4 ∧
        s1.readReg64 .x28 = l4 ∧
        s1.readReg64 .x16 = p5 ∧
        TraceCalleeSaved s1 s0) := by
  subst hsp
  have hmemcpy := hA.session_memcpy_ok_at statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "memcpy"))
  simp only [sessionMemcpySpec, allocHookStack] at hmemcpy ⊢
  unfold v7_encCellsAt v7_ct1SentWordsAt
  wp_simp_pre [pointsTo128, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  states_from_pb_fetches_range b (Rust.withPanics ext) 7468 352
  states_from_pb_fetches_range b (Rust.withPanics ext) 7820 84
  dsimp only [contractProg, tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hmemcpy hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_conv_pre =>
    rw [v7_fsp_1488_split_rest s.sp (v7_wordAt bs 88),
        v7_fsp_1536_realign_rest s.sp (v7_wordAt bs 136) (v7_wordAt bs 144) (v7_wordAt bs 152)]
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_conv_pre =>
    rw [v7_fsp_1512_realign_rest s.sp (v7_wordAt bs 112) (v7_wordAt bs 120)]
  wp_step; wp_step; wp_step; wp_step
  wp_conv_pre =>
    rw [v7_fsp_880_realign_64_rest s.sp (unshiftWord (v7_wordAt bs 112) (loByte (v7_wordAt bs 120))) w888_old,
        v7_fsp_1536_unrealign_rest s.sp (v7_wordAt bs 136) (v7_wordAt bs 144) (v7_wordAt bs 152),
        v7_fsp_1536_split_1_7_rest s.sp (v7_wordAt bs 136)]
  wp_step; wp_step; wp_step; wp_step; wp_step
  wp_conv_pre =>
    rw [v7_fsp_880_unrealign_unshift_rest s.sp (v7_wordAt bs 112) (v7_wordAt bs 120),
        v7_fsp_856_realign_rest s.sp
          ((v7_midQ128 (v7_wordAt bs 136) (v7_wordAt bs 144) (v7_wordAt bs 152)).extractLsb' 64 64) w864_old]
  wp_step
  wp_conv_pre =>
    rw [v7_fsp_856_unrealign_midQ128_rest s.sp
      (v7_wordAt bs 136) (v7_wordAt bs 144) (v7_wordAt bs 152)]
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step
  have hlen328 : (328 : Nat) = bs328_dec.val.length := bs328_dec.property.symm
  wp_simp_pre [hlen328, sepConj_assoc]
  wp_call hmemcpy (s.sp + 240#64, s.sp + 896#64, bs328_dec.val)
  clear hlen328
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · rw [v7_fsp_1536_unsplit_1_7_rest s.sp (v7_wordAt bs 136),
        v7_fsp_1512_unrealign_rest s.sp (v7_wordAt bs 112) (v7_wordAt bs 120),
        v7_fsp_1488_unsplit_rest s.sp (v7_wordAt bs 88)]
    exact Entails.of_eq (by
      dsimp only [BitVec.zeroExtend]
      simp only [pointsTo128_eq_pair64, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      ac_rfl)
  · wp_done

end CryptoVerification.SpqrV1.States.FromPb.Ext4K

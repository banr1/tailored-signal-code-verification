/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2d
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.EpilogueExt
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2e
import ProofLib.SepLogic.WPp

/-! # `<spqr::v1::chunked::states::States>::from_pb`: 4-KiB Hook Wrapper for `Variant2e` -/

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

open CryptoVerification.SpqrV1.Alloc
attribute [local simp, local arm64_norm, local wp_norm] v1_x25_add_189
attribute [local simp, local arm64_norm, local wp_norm] v1_x25_add_189_sext
attribute [local simp, local arm64_norm, local wp_norm] v1_x25_add_233
attribute [local simp, local arm64_norm, local wp_norm] v1_x25_add_233_sext
attribute [local simp, local arm64_norm, local wp_norm] v1_x11_add_185
attribute [local simp, local arm64_norm, local wp_norm] v1_x11_add_185_sext
attribute [local simp, local arm64_norm, local wp_norm] v1_x11_add_209
attribute [local simp, local arm64_norm, local wp_norm] v1_x11_add_209_sext
attribute [local simp, local arm64_norm, local wp_norm] v1_x23_add_39
attribute [local simp, local arm64_norm, local wp_norm] v1_x23_add_39_sext
attribute [local simp, local arm64_norm, local wp_norm] v1_x23_add_15
attribute [local simp, local arm64_norm, local wp_norm] v1_x23_add_15_sext

namespace Ext4K

set_option maxHeartbeats 1200000 in
/-- Compose `+6568 -> +8180` with `states_from_pb_epilogue_8180` and `v1_epilogueOutFull_entails_keysSampled`. -/
theorem v1_keysSampled_6568_ret
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
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

end Ext4K

end CryptoVerification.SpqrV1.States.FromPb

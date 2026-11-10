/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8d
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8a
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10a
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8aExt
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8bExt
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8c
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8dExt
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: 4-KiB Hook Companion for `Variant8`

Lifts `Variant8.lean`'s `AllocContracts`-parameterized theorems to `AllocContracts4K`
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
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

namespace Ext4K

set_option maxHeartbeats 800000 in
theorem v8_stage_11264_to_ret {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext)
    (s0 s : State) (fsp out tag ep pa1 l1 pa2 l2 ca3 pa3 ca4 pa4 ca5 pa5 : BitVec 64) (bs : List (BitVec 8)) (hbs : bs.length = 384) (hi32 : BitVec 32) (enc : PolyEncoder) (P_heap : SepProp) (hreloc :
      ((out + 8#64) ↦₆₄ tag) ∗ (((out + 8#64) + 8#64) ↦ₛ bs) ∗ (((out + 8#64) + 392#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ P_heap ⊢ polyEncoderAt A (out + 8#64) enc) (rootKey macKey es ek ct1 : List (BitVec 8))
    (hl1 : l1 = BitVec.ofNat 64 rootKey.length) (hl2 : l2 = BitVec.ofNat 64 macKey.length) (hes : es.length = 2080) (hek : ek.length = 1152) (hct1 : ct1.length = 960) (Frame : SepProp)
    (halign : (s0.sp &&& 15#64 == 0#64) = true) (hfsp : fsp = s0.sp - 2400#64) (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11264#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx15 : s.readReg64 .x15 = tag) (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = pa5) (hx22 : s.readReg64 .x22 = l1) (hx23 : s.readReg64 .x23 = fsp + 848#64) (hx26 : s.readReg64 .x26 = ca3)
    (hx28 : s.readReg64 .x28 = l2) (htr : TraceCalleeSaved s s0) : SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s ((memRegion (fsp + 72#64) 48 ∗ memRegion (fsp + 160#64) 16 ∗ memRegion (fsp + 192#64) 8 ∗
        memRegion (fsp + 208#64) 8 ∗ memRegion (fsp + 232#64) 8 ∗ memRegion (fsp + 240#64) 1648) ∗ stackAt fsp encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
       memRegion fsp 64 ∗ ((fsp + 64#64) ↦₆₄ ca5) ∗ ((fsp + 120#64) ↦₆₄ ep) ∗ memRegion (fsp + 128#64) 32 ∗ ((fsp + 176#64) ↦₆₄ pa3) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
       ((fsp + 200#64) ↦₆₄ pa1) ∗ ((fsp + 216#64) ↦₆₄ pa4) ∗ ((fsp + 224#64) ↦₆₄ ca4) ∗ ((fsp + 1888#64) ↦₆₄ tag) ∗ v8_encCellsAt (fsp + 1888#64) bs ∗
       ((fsp + 2280#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ memRegion (fsp + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ P_heap ∗ vecU8Payload A l1 pa1 rootKey ∗ vecU8Payload A l2 pa2 macKey ∗
       vecU8Payload A ca3 pa3 es ∗ vecU8Payload A ca4 pa4 ek ∗ vecU8Payload A ca5 pa5 ct1 ∗ Frame) (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.ok (.ekReceivedCt1Sampled { uc := { auth := { rootKey := rootKey, macKey := macKey }, es := es, ek := ek, ct1 := ct1, epoch := ep }, sending_ct1 := enc })) ∗
          stackAt s0.sp statesFromPbStack ∗ Frame) ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := hfsp ▸ sp_sub_2400_align s0.sp halign
  refine SepWP.weaken_pre (sepConj_mono_left (v8_fsp_split_11264_all fsp)) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine ProofLib.SepWP.exists_left fun u887 => ProofLib.SepWP.exists_left fun u880 =>
    ProofLib.SepWP.exists_left fun u864 => ProofLib.SepWP.exists_left fun uq848 =>
    ProofLib.SepWP.exists_left fun u832 => ProofLib.SepWP.exists_left fun uq816 =>
    ProofLib.SepWP.exists_left fun uq800 => ProofLib.SepWP.exists_left fun uq784 =>
    ProofLib.SepWP.exists_left fun uq768 => ProofLib.SepWP.exists_left fun uq752 =>
    ProofLib.SepWP.exists_left fun uq736 => ProofLib.SepWP.exists_left fun uq720 =>
    ProofLib.SepWP.exists_left fun uq704 => ProofLib.SepWP.exists_left fun uq688 =>
    ProofLib.SepWP.exists_left fun uq672 => ProofLib.SepWP.exists_left fun uq656 =>
    ProofLib.SepWP.exists_left fun uq640 => ProofLib.SepWP.exists_left fun uq624 =>
    ProofLib.SepWP.exists_left fun uq608 => ProofLib.SepWP.exists_left fun w592 =>
    ProofLib.SepWP.exists_left fun q576 => ProofLib.SepWP.exists_left fun bs240 =>
    ProofLib.SepWP.exists_left fun u232 => ProofLib.SepWP.exists_left fun u208 =>
    ProofLib.SepWP.exists_left fun w192 => ProofLib.SepWP.exists_left fun d172 =>
    ProofLib.SepWP.exists_left fun u160 => ProofLib.SepWP.exists_left fun w112 =>
    ProofLib.SepWP.exists_left fun w104 => ProofLib.SepWP.exists_left fun d96 =>
    ProofLib.SepWP.exists_left fun d92 => ?_
  have hstep := v8_stage_11264_to_8180 s0 s fsp out tag l1 pa1 l2 pa2 ca3 pa3 pa4 ca5 pa5 (hi32 ++ enc.idx) bs d96 w104 w112 u160 d172 w192 u208 u232
    uq608 uq624 uq640 uq656 uq672 uq688 uq704 uq720 uq736 uq752 uq768 uq784 uq800 uq816 u832 uq848 u864 u880 u887 (stackAt fsp encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
     memRegion fsp 64 ∗ memRegion (fsp + 72#64) 20 ∗ ((fsp + 92#64) ↦₃₂ d92) ∗ memRegion (fsp + 100#64) 4 ∗ ((fsp + 120#64) ↦₆₄ ep) ∗ memRegion (fsp + 128#64) 32 ∗
     memRegion (fsp + 168#64) 4 ∗ ((fsp + 224#64) ↦₆₄ ca4) ∗ ((fsp + 240#64) ↦ₛ bs240.val) ∗ memRegion (fsp + 568#64) 8 ∗ ((fsp + 576#64) ↦₁₂₈ q576) ∗
     ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗ memRegion (fsp + 599#64) 9 ∗ memRegion (fsp + 840#64) 8 ∗ memRegion (fsp + 871#64) 9 ∗ memRegion (fsp + 895#64) 993 ∗
     ((fsp + 1888#64) ↦₆₄ tag) ∗ memRegion (fsp + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ P_heap ∗ vecU8Payload A l1 pa1 rootKey ∗ vecU8Payload A l2 pa2 macKey ∗
     vecU8Payload A ca3 pa3 es ∗ vecU8Payload A ca4 pa4 ek ∗ vecU8Payload A ca5 pa5 ct1 ∗ Frame) hfsp_align hpc hrun hsp hx15 hx19 hx21 hx22 hx23 hx26 hx28 htr
  refine SepWP.weaken_pre ?_ (EncoderFromPb.seq_clean hstep ?_)
  · unfold v8_stagingSlotsPre; exact Entails.of_eq (by ac_rfl)
  intro s2 hpc2 hrun2 ⟨hsp2, hx6_2, hx8_2, hx15_2, hx20_2, hx13_2, hx25_2, hx30_2, hx9_2, hx14_2, hx18_2, hx17_2, hx0_2, hx3_2, hx27_lo_2, hx27_mid_2, hx27_hi_2,
    hx4_2, hx5_2, hx21_2, hx7_2, hx2_2, hx11_2, hx22_2, hx24_2, hx10_2, hx26_2, hx12_2, hx1_2, hx28_2, hx16_2, hx19_2, hx23_2, htr2⟩
  subst hfsp
  have h92 := v8_fsp_64_72_entails_92 (s0.sp - 2400#64) ca5
  have h96 := v8_fsp_96_100_entails_8 (s0.sp - 2400#64) ((loByte (v8_wordAt bs 104)).zeroExtend 32)
  have h176 := v8_fsp_176_184_cells_entails_16 (s0.sp - 2400#64) pa3 pa2
  have h200 := ProofLib.pointsTo64_entails_memRegion ((s0.sp - 2400#64) + 200#64) pa1
  have h216 := ProofLib.pointsTo64_entails_memRegion ((s0.sp - 2400#64) + 216#64) pa4
  have h1888 := v8_fsp_1888_entails_epilogue (s0.sp - 2400#64) tag (hi32 ++ enc.idx) bs hbs
  have hP2_ep : (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗
      v8_stagingSlotsPost (s0.sp - 2400#64) bs pa5 l2 ∗ v8_encCellsAt ((s0.sp - 2400#64) + 1888#64) bs ∗ (((s0.sp - 2400#64) + 2280#64) ↦₆₄ (hi32 ++ enc.idx)) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗ memRegion (s0.sp - 2400#64) 64 ∗ memRegion ((s0.sp - 2400#64) + 72#64) 20 ∗
       (((s0.sp - 2400#64) + 92#64) ↦₃₂ d92) ∗ memRegion ((s0.sp - 2400#64) + 100#64) 4 ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ ep) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗
       memRegion ((s0.sp - 2400#64) + 168#64) 4 ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗ (((s0.sp - 2400#64) + 240#64) ↦ₛ bs240.val) ∗ memRegion ((s0.sp - 2400#64) + 568#64) 8 ∗
       (((s0.sp - 2400#64) + 576#64) ↦₁₂₈ q576) ∗ (((s0.sp - 2400#64) + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗ memRegion ((s0.sp - 2400#64) + 599#64) 9 ∗ memRegion ((s0.sp - 2400#64) + 840#64) 8 ∗
       memRegion ((s0.sp - 2400#64) + 871#64) 9 ∗ memRegion ((s0.sp - 2400#64) + 895#64) 993 ∗ (((s0.sp - 2400#64) + 1888#64) ↦₆₄ tag) ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ P_heap ∗
       vecU8Payload A l1 pa1 rootKey ∗ vecU8Payload A l2 pa2 macKey ∗ vecU8Payload A ca3 pa3 es ∗ vecU8Payload A ca4 pa4 ek ∗ vecU8Payload A ca5 pa5 ct1 ∗ Frame) ⊢
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗ epilogueStackSlots (s0.sp - 2400#64) d92 ((loByte (v8_wordAt bs 128)).zeroExtend 32)
        pa5 960#64 ep l2 1152#64 (v8_wordAt bs 0) ca4 l2 bs240.val q576 w592 (v8_quadAt bs 152) (v8_quadAt bs 168) (v8_quadAt bs 184) (v8_quadAt bs 200)
        (v8_quadAt bs 216) (v8_quadAt bs 232) (v8_quadAt bs 248) (v8_quadAt bs 264) (v8_quadAt bs 280) (v8_quadAt bs 296) (v8_quadAt bs 312) (v8_quadAt bs 328) (v8_quadAt bs 344) (v8_quadAt bs 360) (v8_wordAt bs 376)
        (v8_midQ128 (v8_wordAt bs 128) (v8_wordAt bs 136) (v8_wordAt bs 144)) (v8_wordAt bs 144 >>> 8) (unshiftWord (v8_wordAt bs 104) (loByte (v8_wordAt bs 112))) (v8_wordAt bs 112 >>> 8)
        (v8_wordAt bs 0 ++ tag) (v8_wordAt bs 16 ++ v8_wordAt bs 8) (v8_wordAt bs 24) ∗ epilogueStackGaps (s0.sp - 2400#64) ∗ statesFromPbSavedCells s0 ∗
      (P_heap ∗ vecU8Payload A l1 pa1 rootKey ∗ vecU8Payload A l2 pa2 macKey ∗ vecU8Payload A ca3 pa3 es ∗ vecU8Payload A ca4 pa4 ek ∗ vecU8Payload A ca5 pa5 ct1 ∗ Frame) := by
    unfold v8_stagingSlotsPost epilogueStackSlots epilogueStackGaps
    refine Entails.trans (Entails.of_eq (show _ = (memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 20) ∗
      ((((s0.sp - 2400#64) + 96#64) ↦₃₂ (loByte (v8_wordAt bs 104)).zeroExtend 32) ∗ memRegion ((s0.sp - 2400#64) + 100#64) 4) ∗ ((((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2)) ∗
      (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗ ((((s0.sp - 2400#64) + 1888#64) ↦₆₄ tag) ∗ v8_encCellsAt ((s0.sp - 2400#64) + 1888#64) bs ∗
       (((s0.sp - 2400#64) + 2280#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16) ∗ (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
       (((s0.sp - 2400#64) + 92#64) ↦₃₂ d92) ∗ (((s0.sp - 2400#64) + 104#64) ↦₆₄ pa5) ∗ (((s0.sp - 2400#64) + 112#64) ↦₆₄ 960#64) ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ ep) ∗
       memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ (((s0.sp - 2400#64) + 160#64) ↦₆₄ l2) ∗ memRegion ((s0.sp - 2400#64) + 168#64) 4 ∗ (((s0.sp - 2400#64) + 172#64) ↦₃₂ (loByte (v8_wordAt bs 128)).zeroExtend 32) ∗
       (((s0.sp - 2400#64) + 192#64) ↦₆₄ 1152#64) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ v8_wordAt bs 0) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ l2) ∗
       (((s0.sp - 2400#64) + 240#64) ↦ₛ bs240.val) ∗ memRegion ((s0.sp - 2400#64) + 568#64) 8 ∗ (((s0.sp - 2400#64) + 576#64) ↦₁₂₈ q576) ∗ (((s0.sp - 2400#64) + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗
       memRegion ((s0.sp - 2400#64) + 599#64) 9 ∗ (((s0.sp - 2400#64) + 608#64) ↦₁₂₈ v8_quadAt bs 152) ∗ (((s0.sp - 2400#64) + 624#64) ↦₁₂₈ v8_quadAt bs 168) ∗ (((s0.sp - 2400#64) + 640#64) ↦₁₂₈ v8_quadAt bs 184) ∗
       (((s0.sp - 2400#64) + 656#64) ↦₁₂₈ v8_quadAt bs 200) ∗ (((s0.sp - 2400#64) + 672#64) ↦₁₂₈ v8_quadAt bs 216) ∗ (((s0.sp - 2400#64) + 688#64) ↦₁₂₈ v8_quadAt bs 232) ∗
       (((s0.sp - 2400#64) + 704#64) ↦₁₂₈ v8_quadAt bs 248) ∗ (((s0.sp - 2400#64) + 720#64) ↦₁₂₈ v8_quadAt bs 264) ∗ (((s0.sp - 2400#64) + 736#64) ↦₁₂₈ v8_quadAt bs 280) ∗
       (((s0.sp - 2400#64) + 752#64) ↦₁₂₈ v8_quadAt bs 296) ∗ (((s0.sp - 2400#64) + 768#64) ↦₁₂₈ v8_quadAt bs 312) ∗ (((s0.sp - 2400#64) + 784#64) ↦₁₂₈ v8_quadAt bs 328) ∗
       (((s0.sp - 2400#64) + 800#64) ↦₁₂₈ v8_quadAt bs 344) ∗ (((s0.sp - 2400#64) + 816#64) ↦₁₂₈ v8_quadAt bs 360) ∗ (((s0.sp - 2400#64) + 832#64) ↦₆₄ v8_wordAt bs 376) ∗ memRegion ((s0.sp - 2400#64) + 840#64) 8 ∗
       (((s0.sp - 2400#64) + 848#64) ↦₁₂₈ v8_midQ128 (v8_wordAt bs 128) (v8_wordAt bs 136) (v8_wordAt bs 144)) ∗ (((s0.sp - 2400#64) + 864#64) ↦ₛ EncoderFromPb.loBytes7 (v8_wordAt bs 144 >>> 8)) ∗
       memRegion ((s0.sp - 2400#64) + 871#64) 9 ∗ (((s0.sp - 2400#64) + 880#64) ↦₆₄ unshiftWord (v8_wordAt bs 104) (loByte (v8_wordAt bs 112))) ∗
       (((s0.sp - 2400#64) + 888#64) ↦ₛ EncoderFromPb.loBytes7 (v8_wordAt bs 112 >>> 8)) ∗ memRegion ((s0.sp - 2400#64) + 895#64) 993 ∗ statesFromPbSavedCells s0 ∗ P_heap ∗
       vecU8Payload A l1 pa1 rootKey ∗ vecU8Payload A l2 pa2 macKey ∗ vecU8Payload A ca3 pa3 es ∗ vecU8Payload A ca4 pa4 ek ∗ vecU8Payload A ca5 pa5 ct1 ∗ Frame) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono h92 (sepConj_mono h96 (sepConj_mono h176 (sepConj_mono h200 (sepConj_mono h216 (sepConj_mono_left h1888)))))) ?_
    exact Entails.of_eq (by ac_rfl)
  have hep := Ext4K.states_from_pb_epilogue_8180 hA s0 s2 out d92 ((loByte (v8_wordAt bs 128)).zeroExtend 32) pa5 960#64 ep l2 1152#64 (v8_wordAt bs 0) ca4 l2 bs240.val bs240.property q576 w592
    (v8_quadAt bs 152) (v8_quadAt bs 168) (v8_quadAt bs 184) (v8_quadAt bs 200) (v8_quadAt bs 216) (v8_quadAt bs 232) (v8_quadAt bs 248) (v8_quadAt bs 264)
    (v8_quadAt bs 280) (v8_quadAt bs 296) (v8_quadAt bs 312) (v8_quadAt bs 328) (v8_quadAt bs 344) (v8_quadAt bs 360) (v8_wordAt bs 376) (v8_midQ128 (v8_wordAt bs 128) (v8_wordAt bs 136) (v8_wordAt bs 144))
    (v8_wordAt bs 144 >>> 8) (unshiftWord (v8_wordAt bs 104) (loByte (v8_wordAt bs 112))) (v8_wordAt bs 112 >>> 8) (v8_wordAt bs 0 ++ tag) (v8_wordAt bs 16 ++ v8_wordAt bs 8) (v8_wordAt bs 24)
    (P_heap ∗ vecU8Payload A l1 pa1 rootKey ∗ vecU8Payload A l2 pa2 macKey ∗ vecU8Payload A ca3 pa3 es ∗ vecU8Payload A ca4 pa4 ek ∗ vecU8Payload A ca5 pa5 ct1 ∗ Frame) halign hpc2 hrun2 hsp2 hx6_2 hx19_2 hx23_2 htr2
  rw [hx8_2, hx15_2, hx20_2, hx13_2, hx25_2, hx30_2, hx9_2, hx14_2, hx18_2, hx17_2, hx0_2, hx3_2, hx27_lo_2, hx27_mid_2, hx27_hi_2, hx4_2, hx5_2, hx21_2, hx7_2,
      hx2_2, hx11_2, hx22_2, hx24_2, hx10_2, hx26_2, hx12_2, hx1_2, hx28_2, hx16_2] at hep
  refine SepWP.weaken_pre hP2_ep (SepWP.mono hep ?_)
  intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
  refine ⟨Entails.trans hPf ?_, hsp_f, hcs_f, htr_f⟩
  have hout := v8_epilogueOutFull_entails_ekReceivedCt1Sampled A (F := F) out tag l1 pa1 l2 pa2 ca3 pa3 ca4 pa4 ca5 pa5 ep bs hbs hi32 enc P_heap hreloc rootKey macKey es ek ct1 hl1 hl2 hes hek hct1
    (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592) bs240.val bs240.property (v8_wordAt bs 0 ++ tag) (v8_wordAt bs 16 ++ v8_wordAt bs 8) (v8_wordAt bs 24)
  refine Entails.trans (Entails.of_eq (show _ = (epilogueOutFull out 10#64 tag (v8_wordAt bs 0) (v8_wordAt bs 8) (v8_wordAt bs 16) (v8_wordAt bs 24) (v8_wordAt bs 32) (v8_wordAt bs 40)
      (v8_wordAt bs 48) (v8_wordAt bs 56) (v8_wordAt bs 64) (v8_wordAt bs 72) ((v8_wordAt bs 80).extractLsb' 0 8) ((v8_wordAt bs 80).extractLsb' 8 32)
      ((v8_wordAt bs 80).extractLsb' 40 16) ((v8_wordAt bs 80).extractLsb' 56 8) (v8_wordAt bs 88) (v8_wordAt bs 96) (loByte (v8_wordAt bs 104)) (unshiftWord (v8_wordAt bs 104) (loByte (v8_wordAt bs 112)))
      (overlapWord7 (unshiftWord (v8_wordAt bs 104) (loByte (v8_wordAt bs 112))) (v8_wordAt bs 112 >>> 8)) (v8_wordAt bs 120) (((loByte (v8_wordAt bs 128)).zeroExtend 32).setWidth 8)
      (v8_midQ128 (v8_wordAt bs 128) (v8_wordAt bs 136) (v8_wordAt bs 144)) (overlapWord7 ((v8_midQ128 (v8_wordAt bs 128) (v8_wordAt bs 136) (v8_wordAt bs 144)).extractLsb' 64 64) (v8_wordAt bs 144 >>> 8))
      (v8_quadAt bs 152) (v8_quadAt bs 168) (v8_quadAt bs 184) (v8_quadAt bs 200) (v8_quadAt bs 216) (v8_quadAt bs 232) (v8_quadAt bs 248) (v8_quadAt bs 264)
      (v8_quadAt bs 280) (v8_quadAt bs 296) (v8_quadAt bs 312) (v8_quadAt bs 328) (v8_quadAt bs 344) (v8_quadAt bs 360) (v8_wordAt bs 376) (hi32 ++ enc.idx) l1 pa1 l1 l2 pa2 l2
      ca3 pa3 2080#64 ca4 pa4 1152#64 ca5 pa5 960#64 ep (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592) bs240.val (v8_wordAt bs 0 ++ tag) (v8_wordAt bs 16 ++ v8_wordAt bs 8) (v8_wordAt bs 24) ∗
     P_heap ∗ vecU8Payload A l1 pa1 rootKey ∗ vecU8Payload A l2 pa2 macKey ∗ vecU8Payload A ca3 pa3 es ∗ vecU8Payload A ca4 pa4 ek ∗ vecU8Payload A ca5 pa5 ct1) ∗ stackAt s0.sp statesFromPbStack ∗ Frame by ac_rfl)) ?_
  exact Entails.trans (sepConj_mono_left hout) (Entails.of_eq (by ac_rfl))

set_option maxHeartbeats 800000 in
theorem v8_ekReceivedCt1Sampled_from_10836 {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) (hE : EncoderFromPbOkExt b A ext)
    (s0 s : State) (out pbA : BitVec 64) (u : V1State.Unchunked.Ct1SentEkReceived) (auth : ProtoAuthenticator) (sendingCt1 : Option PolynomialEncoder) (hpts : optEncoderPtsBound sendingCt1)
    (u8 u16 u32 u40 u56 u64 u80 u88 u96 u104 u112 u120 : BitVec 64) (pa1 l1 pa2 l2 : BitVec 64) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64) (hlen : (u.es.length == ENCAPSULATION_STATE_SIZE &&
      u.ct1.length == CIPHERTEXT1_SIZE && u.ek.length == ENCAPSULATION_KEY_SIZE) = true) (hes : u.es.length = 2080) (hek : u.ek.length = 1152) (hct1 : u.ct1.length = 960) (hauth : u.auth = some auth)
    (hl1 : l1 = BitVec.ofNat 64 auth.rootKey.length) (hl2 : l2 = BitVec.ofNat 64 auth.macKey.length) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10836#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64) (hx9 : s.readReg64 .x9 = u64) (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = u64) (hx22 : s.readReg64 .x22 = l1) (hx23 : s.readReg64 .x23 = (s0.sp - 2400#64) + 848#64) (hx26 : s.readReg64 .x26 = u8) (hx27 : s.readReg64 .x27 = pbA)
    (hx28 : s.readReg64 .x28 = l2) (htr : TraceCalleeSaved s s0) : SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗
        memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
        memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗
        memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗ v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
        memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ vecU8Payload A l1 pa1 auth.rootKey ∗ vecU8Payload A l2 pa2 auth.macKey ∗
        vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗
        v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion (pbA + 192#64) 32 ∗
        statesFromPbJumpTableAt b ∗ A.pool) (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.ekReceivedCt1Sampled { uc := some u, sendingCt1 := sendingCt1 }) }) ∗
          memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf) := by
  have hpb_col := v8_pb_uc_enc_entails_224 pbA u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch w0 w8 w16 w24 w32 w40 w48
  cases sendingCt1 with
  | none =>
    rw [v8_states_from_pb_sendingCt1_none_eq u auth hlen hauth]
    simp only [Option.map_none, v1_optProtoPolyEncoderHeap]
    rw [show stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
        (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗ memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗
        v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗ ⌜w0 = noneCap⌝ ∗
        memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        vecU8Payload A l1 pa1 auth.rootKey ∗ vecU8Payload A l2 pa2 auth.macKey ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗
        v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b ∗ A.pool = ⌜w0 = noneCap⌝ ∗ ((vecU8Payload A l1 pa1 auth.rootKey ∗ vecU8Payload A l2 pa2 auth.macKey ∗
        vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1) ∗ ((pbA ↦₆₄ 0x8000000000000008#64) ∗
        v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion (pbA + 192#64) 32) ∗
       v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
       (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
       (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗
       (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗
       memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl]
    refine SepWPp.pure_left fun hw0 => ?_
    apply SepWPp.of_sepWP_ret
    refine SepWP.weaken_pre (sepConj_mono (v8_5vecs_entails_dealloc A l1 pa1 l2 pa2 u8 u16 u32 u40 u56 u64 auth.rootKey auth.macKey u.es u.ek u.ct1) (sepConj_mono_left hpb_col)) ?_
    subst hw0
    have hw_eq : v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) noneCap w8 w16 w24 w32 w40 w48 = (((s0.sp - 2400#64) + 1520#64) ↦₆₄ noneCap) ∗
        ((((s0.sp - 2400#64) + 1520#64 + 8#64) ↦₆₄ w8) ∗ (((s0.sp - 2400#64) + 1520#64 + 16#64) ↦₆₄ w16) ∗ (((s0.sp - 2400#64) + 1520#64 + 24#64) ↦₆₄ w24) ∗ (((s0.sp - 2400#64) + 1520#64 + 32#64) ↦₆₄ w32) ∗
         (((s0.sp - 2400#64) + 1520#64 + 40#64) ↦₆₄ w40) ∗ (((s0.sp - 2400#64) + 1520#64 + 48#64) ↦₆₄ w48)) := rfl
    have hstep1 := v8_check_sendingCt1_10836_none s0 s out u64 l1 l2 u8 (((((s0.sp - 2400#64) + 1520#64 + 8#64) ↦₆₄ w8) ∗ (((s0.sp - 2400#64) + 1520#64 + 16#64) ↦₆₄ w16) ∗
        (((s0.sp - 2400#64) + 1520#64 + 24#64) ↦₆₄ w24) ∗ (((s0.sp - 2400#64) + 1520#64 + 32#64) ↦₆₄ w32) ∗ (((s0.sp - 2400#64) + 1520#64 + 40#64) ↦₆₄ w40) ∗ (((s0.sp - 2400#64) + 1520#64 + 48#64) ↦₆₄ w48)) ∗
       stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ vecCapPtrDealloc A l1 pa1 ∗ vecCapPtrDealloc A l2 pa2 ∗ vecCapPtrDealloc A u8 u16 ∗
       vecCapPtrDealloc A u32 u40 ∗ vecCapPtrDealloc A u56 u64 ∗ A.pool ∗ (memRegion (s0.sp - 2400#64) 64 ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗
        memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
        memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗
        memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)) hsp0_align hpc hrun hsp hx9 hx19 hx21 hx22 hx26 hx28 htr
    refine SepWP.weaken_pre (by rw [hw_eq]; exact Entails.of_eq (by ac_rfl)) (SepWP.seq hstep1 ?_)
    intro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, hx9_2, hx19_2, hx21_2, hx22_2, hx26_2, hx28_2, htr2⟩
    have hstep2 := Ext4K.v8_cleanup_5vecs_11120 hA s0 s2 out l1 pa1 l2 pa2 u8 u16 u32 u40 u56 u64 (v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) noneCap w8 w16 w24 w32 w40 w48 ∗
       memRegion (s0.sp - 2400#64) 64 ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗
       memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
       memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗
       memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b) hsp0_align hpc2 hrun2 hsp2 hx9_2 hx19_2 hx21_2 hx22_2 hx26_2 hx28_2 htr2
    refine SepWP.weaken_pre (Entails.trans hP2 (by rw [hw_eq]; exact Entails.of_eq (by ac_rfl))) (SepWP.seq hstep2 ?_)
    intro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, hx19_3, hx20_3, htr3⟩
    have hcol1 := v8_fsp_collapse_240_to_1888 (s0.sp - 2400#64) noneCap w8 w16 w24 w32 w40 w48
    have hcol2 := v8_fsp_collapse_2304 (s0.sp - 2400#64) u56 u.epoch u16 pa2 pa1 u40 u32
    have hP3' : P3 ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool) := by
      refine Entails.trans hP3 ?_
      refine Entails.trans (Entails.of_eq (show _ = (memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗ memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗
          v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) noneCap w8 w16 w24 w32 w40 w48 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 312) ∗
        (memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
          (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
          (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
          memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
          memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl)) ?_
      refine Entails.trans (sepConj_mono_left hcol1) ?_
      refine Entails.trans (Entails.of_eq (show _ = (memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
          (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
          (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
          memRegion ((s0.sp - 2400#64) + 240#64) 1648 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16) ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hcol2) (Entails.of_eq (by ac_rfl))
    have hx20_byte : (s3.readReg64 .x20).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
      rw [hx20_3]; rfl
    refine SepWP.weaken_pre hP3' (SepWP.mono (v8_err_4240 (A := A) (F := F) s0 s3 out (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool) hsp0_align hpc3 hrun3 hsp3 hx19_3 hx20_byte htr3) ?_)
    intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
    exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩
  | some pbEnc =>
    dsimp only [optEncoderPtsBound] at hpts
    simp only [Option.map_some]
    refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ = v1_optProtoPolyEncoderHeap A (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
         (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
         (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
         (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
         memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗ v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
         memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         vecU8Payload A l1 pa1 auth.rootKey ∗ vecU8Payload A l2 pa2 auth.macKey ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗
         v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
         memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl)) (sepConj_mono (v1_optProtoPolyEncoderHeap_extract_w0 A (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48)
          (sepConj_mono_left (v8_fsp_240_split_56 (s0.sp - 2400#64))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWPp.exists_elim; intro z288; apply SepWPp.exists_elim; intro z280; apply SepWPp.exists_elim; intro z272; apply SepWPp.exists_elim; intro z264; apply SepWPp.exists_elim; intro z256
    apply SepWPp.exists_elim; intro z248; apply SepWPp.exists_elim; intro z240
    refine SepWPp.pure_left fun hw0_lt => ?_
    have hw_fsp : v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 = (((s0.sp - 2400#64) + 1520#64) ↦₆₄ w0) ∗ (((s0.sp - 2400#64) + 1528#64) ↦₆₄ w8) ∗
        ((((s0.sp - 2400#64) + 1520#64 + 16#64) ↦₆₄ w16) ∗ (((s0.sp - 2400#64) + 1520#64 + 24#64) ↦₆₄ w24) ∗ (((s0.sp - 2400#64) + 1520#64 + 32#64) ↦₆₄ w32) ∗ (((s0.sp - 2400#64) + 1520#64 + 40#64) ↦₆₄ w40) ∗
         (((s0.sp - 2400#64) + 1520#64 + 48#64) ↦₆₄ w48)) := by
      dsimp only [v1_optProtoPolyEncoderWordsAt]
      have h1528 : (s0.sp - 2400#64 + 1520#64) + 8#64 = s0.sp - 2400#64 + 1528#64 := by bv_omega
      rw [h1528]
    have hw_pbA : v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 = ((pbA + 136#64) ↦₆₄ w0) ∗ ((pbA + 144#64) ↦₆₄ w8) ∗ ((pbA + 152#64) ↦₆₄ w16) ∗
        ((pbA + 160#64) ↦₆₄ w24) ∗ ((pbA + 168#64) ↦₆₄ w32) ∗ ((pbA + 176#64) ↦₆₄ w40) ∗ ((pbA + 184#64) ↦₆₄ w48) := by
      dsimp only [v1_optProtoPolyEncoderWordsAt]
      simp only [v8_bv_add_add_lit, BitVec.ofNat_eq_ofNat]
    have hcopy := v8_copy_enc_10836_to_10900 s0 s out pbA u64 l1 u8 l2 w0 w8 w16 w24 w32 w40 w48 z240 z248 z256 z264 z272 z280 z288
      ((((s0.sp - 2400#64) + 1520#64 + 16#64) ↦₆₄ w16) ∗ (((s0.sp - 2400#64) + 1520#64 + 24#64) ↦₆₄ w24) ∗ (((s0.sp - 2400#64) + 1520#64 + 32#64) ↦₆₄ w32) ∗ (((s0.sp - 2400#64) + 1520#64 + 40#64) ↦₆₄ w40) ∗
       (((s0.sp - 2400#64) + 1520#64 + 48#64) ↦₆₄ w48) ∗ ((pbA + 136#64) ↦₆₄ w0) ∗ v1_optProtoPolyEncoderHeap A (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48 ∗
       stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
       (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
       (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
       memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ vecU8Payload A l1 pa1 auth.rootKey ∗ vecU8Payload A l2 pa2 auth.macKey ∗
       vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗
       v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b ∗ A.pool)
      hw0_lt hsp0_align hpc hrun hsp hx19 hx21 hx22 hx23 hx26 hx27 hx28 htr
    refine SepWPp.weaken_pre (by rw [hw_fsp, hw_pbA]; exact Entails.of_eq (by ac_rfl)) (v10_sepWPp_seq_clean hcopy ?_)
    intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx1_2, hx19_2, hx21_2, hx22_2, hx23_2, hx26_2, hx27_2, hx28_2, htr2⟩
    have hP2_col : v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 240#64) w0 w8 w16 w24 w32 w40 w48 ∗ (((s0.sp - 2400#64) + 1520#64) ↦₆₄ w0) ∗ (((s0.sp - 2400#64) + 1528#64) ↦₆₄ w8) ∗
        ((pbA + 144#64) ↦₆₄ w8) ∗ ((pbA + 152#64) ↦₆₄ w16) ∗ ((pbA + 160#64) ↦₆₄ w24) ∗ ((pbA + 168#64) ↦₆₄ w32) ∗ ((pbA + 176#64) ↦₆₄ w40) ∗ ((pbA + 184#64) ↦₆₄ w48) ∗
        ((((s0.sp - 2400#64) + 1520#64 + 16#64) ↦₆₄ w16) ∗ (((s0.sp - 2400#64) + 1520#64 + 24#64) ↦₆₄ w24) ∗ (((s0.sp - 2400#64) + 1520#64 + 32#64) ↦₆₄ w32) ∗ (((s0.sp - 2400#64) + 1520#64 + 40#64) ↦₆₄ w40) ∗
         (((s0.sp - 2400#64) + 1520#64 + 48#64) ↦₆₄ w48) ∗ ((pbA + 136#64) ↦₆₄ w0) ∗ v1_optProtoPolyEncoderHeap A (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48 ∗
         stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
         (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
         (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
         (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
         memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ vecU8Payload A l1 pa1 auth.rootKey ∗ vecU8Payload A l2 pa2 auth.macKey ∗
         vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗
         v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b ∗ A.pool) ⊢
        memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 240#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ A.pool ∗
        (memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
         (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
         (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
         (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
         memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗ v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
         memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         vecU8Payload A l1 pa1 auth.rootKey ∗ vecU8Payload A l2 pa2 auth.macKey ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗
         memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b) := by
      refine Entails.trans (Entails.of_eq (show _ = ((pbA ↦₆₄ 0x8000000000000008#64) ∗ v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗
         (((pbA + 136#64) ↦₆₄ w0) ∗ ((pbA + 144#64) ↦₆₄ w8) ∗ ((pbA + 152#64) ↦₆₄ w16) ∗ ((pbA + 160#64) ↦₆₄ w24) ∗ ((pbA + 168#64) ↦₆₄ w32) ∗ ((pbA + 176#64) ↦₆₄ w40) ∗ ((pbA + 184#64) ↦₆₄ w48)) ∗
         memRegion (pbA + 192#64) 32) ∗ ((((s0.sp - 2400#64) + 1520#64) ↦₆₄ w0) ∗ (((s0.sp - 2400#64) + 1528#64) ↦₆₄ w8) ∗
         ((((s0.sp - 2400#64) + 1520#64 + 16#64) ↦₆₄ w16) ∗ (((s0.sp - 2400#64) + 1520#64 + 24#64) ↦₆₄ w24) ∗ (((s0.sp - 2400#64) + 1520#64 + 32#64) ↦₆₄ w32) ∗ (((s0.sp - 2400#64) + 1520#64 + 40#64) ↦₆₄ w40) ∗
          (((s0.sp - 2400#64) + 1520#64 + 48#64) ↦₆₄ w48))) ∗ (memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 240#64) w0 w8 w16 w24 w32 w40 w48 ∗
         v1_optProtoPolyEncoderHeap A (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ A.pool ∗
         memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
         (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
         (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
         (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
         memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         vecU8Payload A l1 pa1 auth.rootKey ∗ vecU8Payload A l2 pa2 auth.macKey ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ statesFromPbJumpTableAt b) by ac_rfl)) ?_
      rw [← hw_pbA, ← hw_fsp]
      exact Entails.trans (sepConj_mono_left hpb_col) (Entails.of_eq (by ac_rfl))
    have hcall := v8_call_encoder_from_pb_10900_to_10904 hE s0 s2 (s0.sp - 2400#64) out u64 l1 u8 pbA l2 pbEnc w0 w8 w16 w24 w32 w40 w48
      (memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
       (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
       (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
       memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗ v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       vecU8Payload A l1 pa1 auth.rootKey ∗ vecU8Payload A l2 pa2 auth.macKey ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗
       memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b) hpts hsp0_align rfl hpc2 hrun2 hsp2 hx0_2 hx1_2 hx19_2 hx21_2 hx22_2 hx23_2 hx26_2 hx27_2 hx28_2 htr2
    refine SepWPp.weaken_pre hP2_col (v8_sepWPp_seq hcall ?_)
    intro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, hx19_3, hx21_3, hx22_3, hx23_3, hx26_3, hx27_3, hx28_3, htr3⟩; apply SepWPp.of_sepWP_ret
    refine SepWP.weaken_pre hP3 ?_
    have hcol_1648 : memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗ memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗ v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion ((s0.sp - 2400#64) + 1576#64) 312 ⊢ memRegion ((s0.sp - 2400#64) + 240#64) 1648 := v8_fsp_collapse_240_to_1888 (s0.sp - 2400#64) w0 w8 w16 w24 w32 w40 w48
    cases henc : fromPbResult (pbToProtoPolyEncoder pbEnc) with
    | error err =>
      rw [v8_states_from_pb_sendingCt1_err_any_eq u auth pbEnc err hlen hauth henc]
      have herr_tag := v8_resultPolyEncoder_err_entails_tag_392 A (s0.sp - 2400#64) err
      have hpre_err : resultPolyEncoderFromPbAt A ((s0.sp - 2400#64) + 1888#64) (.error err) ∗ memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ A.pool ∗
          (memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
           (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
           (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
           (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
           memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗ v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
           memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
           vecU8Payload A l1 pa1 auth.rootKey ∗ vecU8Payload A l2 pa2 auth.macKey ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗
           memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b) ⊢ (((s0.sp - 2400#64) + 1888#64) ↦₆₄ 2#64) ∗ (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
           (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ vecCapPtrDealloc A l1 pa1 ∗ vecCapPtrDealloc A l2 pa2 ∗ vecCapPtrDealloc A u8 u16 ∗
           vecCapPtrDealloc A u32 u40 ∗ vecCapPtrDealloc A u56 u64 ∗ A.pool ∗ (memRegion (s0.sp - 2400#64) 64 ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗
            memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
            memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 1648 ∗ memRegion ((s0.sp - 2400#64) + 1896#64) 392 ∗
            memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)) := by
        refine Entails.trans (Entails.of_eq (show _ = resultPolyEncoderFromPbAt A ((s0.sp - 2400#64) + 1888#64) (.error err) ∗ (memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗ memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗
           v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 312) ∗ (vecU8Payload A l1 pa1 auth.rootKey ∗ vecU8Payload A l2 pa2 auth.macKey ∗
           vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1) ∗ (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ A.pool ∗
           memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
           (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
           (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
           (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
           memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono herr_tag (sepConj_mono hcol_1648 (sepConj_mono_left (v8_5vecs_entails_dealloc A l1 pa1 l2 pa2 u8 u16 u32 u40 u56 u64 auth.rootKey auth.macKey u.es u.ek u.ct1))))
          (Entails.of_eq (by ac_rfl))
      refine SepWP.weaken_pre hpre_err (SepWP.seq (v8_check_enc_res_10904_err s0 s3 _ hsp0_align hpc3 hrun3 hsp3 htr3) ?_)
      intro s4 P4 hpc4 hrun4 ⟨hP4, hsp4, hx19_4, hx21_4, hx22_4, hx26_4, hx28_4, htr4⟩
      rw [hx19_3] at hx19_4; rw [hx21_3] at hx21_4; rw [hx22_3] at hx22_4
      rw [hx26_3] at hx26_4; rw [hx28_3] at hx28_4
      have hclean := Ext4K.v8_cleanup_5vecs_10916 hA s0 s4 out l1 pa1 l2 pa2 u8 u16 u32 u40 u56 u64 ((((s0.sp - 2400#64) + 1888#64) ↦₆₄ 2#64) ∗
         memRegion (s0.sp - 2400#64) 64 ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗
         memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
         memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 1648 ∗ memRegion ((s0.sp - 2400#64) + 1896#64) 392 ∗
         memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)
        hsp0_align hpc4 hrun4 hsp4 hx19_4 hx21_4 hx22_4 hx26_4 hx28_4 htr4
      refine SepWP.weaken_pre (Entails.trans hP4 (Entails.of_eq (by ac_rfl))) (SepWP.seq hclean ?_)
      intro s5 P5 hpc5 hrun5 ⟨hP5, hsp5, hx19_5, hx20_5, htr5⟩
      have hcol2 := v8_fsp_collapse_2304 (s0.sp - 2400#64) u56 u.epoch u16 pa2 pa1 u40 u32
      have hP5' : P5 ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
          (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool) := by
        refine Entails.trans hP5 ?_
        refine Entails.trans (Entails.of_eq (show _ = ((((s0.sp - 2400#64) + 1888#64) ↦₆₄ 2#64) ∗ memRegion ((s0.sp - 2400#64) + 1896#64) 392) ∗
          (memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
            (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
            (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
            (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
            memRegion ((s0.sp - 2400#64) + 240#64) 1648 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
            memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl)) ?_
        refine Entails.trans (sepConj_mono_left (v8_tag2_392_entails_400 (s0.sp - 2400#64))) ?_
        refine Entails.trans (Entails.of_eq (show _ = (memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
            (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
            (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
            (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
            memRegion ((s0.sp - 2400#64) + 240#64) 1648 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hcol2) (Entails.of_eq (by ac_rfl))
      have hx20_byte : (s5.readReg64 .x20).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
        rw [hx20_5]; rfl
      refine SepWP.weaken_pre hP5' (SepWP.mono (v8_err_4240 (A := A) (F := F) s0 s5 out (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool) hsp0_align hpc5 hrun5 hsp5 hx19_5 hx20_byte htr5) ?_)
      intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
      exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩
    | ok enc =>
      rw [v8_states_from_pb_ok_eq u auth pbEnc enc hlen hauth henc]
      dsimp only [resultPolyEncoderFromPbAt]
      have hrel := v8_polyEncoderAt_relocate A ((s0.sp - 2400#64) + 1888#64) (out + 8#64) enc
      refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ = polyEncoderAt A ((s0.sp - 2400#64) + 1888#64) enc ∗ (memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗ memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗
           v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 312) ∗ (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ A.pool ∗
           memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
           (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
           (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
           (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
           memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ vecU8Payload A l1 pa1 auth.rootKey ∗ vecU8Payload A l2 pa2 auth.macKey ∗
           vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b) by ac_rfl))
          (sepConj_mono hrel (sepConj_mono_left hcol_1648))) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply ProofLib.SepWP.exists_left; intro tag; apply ProofLib.SepWP.exists_left; intro bs; apply ProofLib.SepWP.exists_left; intro hi32; apply ProofLib.SepWP.exists_left; intro P_heap
      apply ProofLib.SepWP.pure_elim; rintro ⟨htag, hreloc⟩
      have hbs_cells := v8_bs384_eq_encCells bs.val bs.property ((s0.sp - 2400#64) + 1888#64)
      have ha2280 : ((s0.sp - 2400#64) + 1888#64) + 392#64 = (s0.sp - 2400#64) + 2280#64 := by bv_omega
      rw [hbs_cells, ha2280]
      refine SepWP.seq (v8_check_enc_res_10904_ok s0 s3 tag htag _ hsp0_align hpc3 hrun3 hsp3 htr3) ?_
      intro s4 P4 hpc4 hrun4 ⟨hP4, hsp4, hx15_4, hx19_4, hx21_4, hx22_4, hx23_4, hx26_4, hx28_4, htr4⟩
      rw [hx19_3] at hx19_4; rw [hx21_3] at hx21_4; rw [hx22_3] at hx22_4
      rw [hx23_3] at hx23_4; rw [hx26_3] at hx26_4; rw [hx28_3] at hx28_4
      have hstage := Ext4K.v8_stage_11264_to_ret (F := F) hA s0 s4 (s0.sp - 2400#64) out tag u.epoch pa1 l1 pa2 l2 u8 u16 u32 u40 u56 u64 bs.val bs.property hi32 enc P_heap hreloc
        auth.rootKey auth.macKey u.es u.ek u.ct1 hl1 hl2 hes hek hct1 (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool)
        hsp0_align rfl hpc4 hrun4 hsp4 hx15_4 hx19_4 hx21_4 hx22_4 hx23_4 hx26_4 hx28_4 htr4
      refine SepWP.weaken_pre (Entails.trans hP4 (Entails.of_eq (by ac_rfl))) (SepWP.mono hstage ?_)
      intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
      exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩

set_option maxHeartbeats 800000 in
theorem v8_ekReceivedCt1Sampled_from_1984 {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) (hE : EncoderFromPbOkExt b A ext)
    (s0 s : State) (out pbA : BitVec 64) (u : V1State.Unchunked.Ct1SentEkReceived) (auth : ProtoAuthenticator) (sendingCt1 : Option PolynomialEncoder) (hpts : optEncoderPtsBound sendingCt1)
    (u8 u16 u32 u40 u56 u64 u80 u88 u104 u112 : BitVec 64) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64) (hlen : (u.es.length == ENCAPSULATION_STATE_SIZE && u.ct1.length == CIPHERTEXT1_SIZE &&
      u.ek.length == ENCAPSULATION_KEY_SIZE) = true) (hes : u.es.length = 2080) (hek : u.ek.length = 1152) (hct1 : u.ct1.length = 960) (hauth : u.auth = some auth) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1984#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64) (hx19 : s.readReg64 .x19 = out) (hx23 : s.readReg64 .x23 = u80)
    (hx26 : s.readReg64 .x26 = u8) (hx27 : s.readReg64 .x27 = pbA) (htr : TraceCalleeSaved s s0) : SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 896 ∗ v8_ucWordsAt ((s0.sp - 2400#64) + 896#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 (BitVec.ofNat 64 auth.rootKey.length) u104 u112
          (BitVec.ofNat 64 auth.macKey.length) u.epoch ∗ memRegion ((s0.sp - 2400#64) + 1024#64) 496 ∗ v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 728 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        vecU8Payload A u80 u88 auth.rootKey ∗ vecU8Payload A u104 u112 auth.macKey ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗
        v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 (BitVec.ofNat 64 auth.rootKey.length) u104 u112 (BitVec.ofNat 64 auth.macKey.length) u.epoch ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b ∗ A.pool) (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.ekReceivedCt1Sampled { uc := some u, sendingCt1 := sendingCt1 }) }) ∗
          memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf) := by
  refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ = vecU8Payload A u80 u88 auth.rootKey ∗ memRegion (s0.sp - 2400#64) 896 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 728 ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ v8_ucWordsAt ((s0.sp - 2400#64) + 896#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 (BitVec.ofNat 64 auth.rootKey.length) u104 u112
         (BitVec.ofNat 64 auth.macKey.length) u.epoch ∗ memRegion ((s0.sp - 2400#64) + 1024#64) 496 ∗ v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ vecU8Payload A u104 u112 auth.macKey ∗
       vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗ v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88
         (BitVec.ofNat 64 auth.rootKey.length) u104 u112 (BitVec.ofNat 64 auth.macKey.length) u.epoch ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl)) (sepConj_mono (vecU8Payload_extract_len_lt63 A u80 u88 auth.rootKey) (sepConj_mono (v8_fsp_896_split_1984 (s0.sp - 2400#64))
          (sepConj_mono_left (v8_fsp_1576_split_728 (s0.sp - 2400#64)))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro v224; apply SepWPp.exists_elim; intro v216; apply SepWPp.exists_elim; intro v200; apply SepWPp.exists_elim; intro v184; apply SepWPp.exists_elim; intro v176
  apply SepWPp.exists_elim; intro v120; apply SepWPp.exists_elim; intro v64
  refine SepWPp.pure_left fun hr_lt63 => ?_
  have hl1_lt : (BitVec.ofNat 64 auth.rootKey.length).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hr_lt63
  have hclone1 := Ext4K.v8_clone_rootKey_1984_to_10680 hA s0 s out pbA u8 u80 u88 u.epoch v120 v200 auth.rootKey (((s0.sp - 2400#64 + 896#64) ↦₆₄ u8) ∗ ((s0.sp - 2400#64 + 904#64) ↦₆₄ u16) ∗
     ((s0.sp - 2400#64 + 912#64) ↦₆₄ 2080#64) ∗ ((s0.sp - 2400#64 + 920#64) ↦₆₄ u32) ∗ ((s0.sp - 2400#64 + 928#64) ↦₆₄ u40) ∗ ((s0.sp - 2400#64 + 936#64) ↦₆₄ 1152#64) ∗
     ((s0.sp - 2400#64 + 944#64) ↦₆₄ u56) ∗ ((s0.sp - 2400#64 + 952#64) ↦₆₄ u64) ∗ ((s0.sp - 2400#64 + 960#64) ↦₆₄ 960#64) ∗ ((s0.sp - 2400#64 + 968#64) ↦₆₄ u80) ∗
     ((s0.sp - 2400#64 + 992#64) ↦₆₄ u104) ∗ ((s0.sp - 2400#64 + 1000#64) ↦₆₄ u112) ∗ ((s0.sp - 2400#64 + 1008#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
     memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ v64) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗
     memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ v176) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
     memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ v216) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ v224) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
     memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗ memRegion ((s0.sp - 2400#64) + 296#64) 600 ∗ memRegion ((s0.sp - 2400#64) + 1024#64) 496 ∗
     v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗ v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
     memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗ vecU8Payload A u104 u112 auth.macKey ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗
     v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 (BitVec.ofNat 64 auth.rootKey.length) u104 u112 (BitVec.ofNat 64 auth.macKey.length) u.epoch ∗
     v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b) hsp0_align hpc hrun hsp hx19 hx23 hx26 hx27 htr
  refine SepWPp.weaken_pre (by rw [v8_ucWordsAt_896_eq]; exact Entails.of_eq (by ac_rfl)) (v8_sepWPp_seq hclone1 ?_)
  intro s2 P2 hpc2 hrun2 ⟨pa1, hP2, hsp2, hx19_2, hx22_2, hx23_2, hx24_2, hx26_2, hx27_2, htr2⟩
  have hclone2 := Ext4K.v8_clone_macKey_10680_to_10740 hA s0 s2 out pbA u8 (BitVec.ofNat 64 auth.rootKey.length) u80 u88 u104 u112 v184 auth.macKey
    ((((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ (((s0.sp - 2400#64) + 976#64) ↦₆₄ u88) ∗ (((s0.sp - 2400#64) + 984#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
     (((s0.sp - 2400#64) + 1016#64) ↦₆₄ u.epoch) ∗ vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗ vecCapPtrDealloc A u80 u88 ∗
     ((s0.sp - 2400#64 + 896#64) ↦₆₄ u8) ∗ ((s0.sp - 2400#64 + 904#64) ↦₆₄ u16) ∗ ((s0.sp - 2400#64 + 912#64) ↦₆₄ 2080#64) ∗ ((s0.sp - 2400#64 + 920#64) ↦₆₄ u32) ∗
     ((s0.sp - 2400#64 + 928#64) ↦₆₄ u40) ∗ ((s0.sp - 2400#64 + 936#64) ↦₆₄ 1152#64) ∗ ((s0.sp - 2400#64 + 944#64) ↦₆₄ u56) ∗ ((s0.sp - 2400#64 + 952#64) ↦₆₄ u64) ∗
     ((s0.sp - 2400#64 + 960#64) ↦₆₄ 960#64) ∗ ((s0.sp - 2400#64 + 968#64) ↦₆₄ u80) ∗ ((s0.sp - 2400#64 + 992#64) ↦₆₄ u104) ∗ memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ v64) ∗
     memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ v176) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
     memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ v216) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ v224) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
     memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗ memRegion ((s0.sp - 2400#64) + 296#64) 600 ∗ memRegion ((s0.sp - 2400#64) + 1024#64) 496 ∗
     v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗ v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
     memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
     vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗ v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88
       (BitVec.ofNat 64 auth.rootKey.length) u104 u112 (BitVec.ofNat 64 auth.macKey.length) u.epoch ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
     memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b) hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx23_2 hx24_2 hx26_2 hx27_2 htr2
  refine SepWPp.weaken_pre (Entails.trans hP2 (Entails.of_eq (by ac_rfl))) (v8_sepWPp_seq hclone2 ?_)
  intro s3 P3 hpc3 hrun3 ⟨pa2, hP3, hsp3, hx19_3, hx20_3, hx22_3, hx23_3, hx24_3, hx26_3, hx27_3, hx28_3, htr3⟩
  have hdealloc := Ext4K.v8_dealloc_old_auth_10740_to_10836 hA s0 s3 out pbA u8 u16 u32 u40 u56 u64 u80 u88 u104 u112 (BitVec.ofNat 64 auth.rootKey.length) (BitVec.ofNat 64 auth.macKey.length) v64 v176 v216 v224
    ((((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 1000#64) ↦₆₄ u112) ∗ (((s0.sp - 2400#64) + 1008#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
     vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ (((s0.sp - 2400#64) + 976#64) ↦₆₄ u88) ∗
     (((s0.sp - 2400#64) + 984#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗ (((s0.sp - 2400#64) + 1016#64) ↦₆₄ u.epoch) ∗ vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
     ((s0.sp - 2400#64 + 896#64) ↦₆₄ u8) ∗ ((s0.sp - 2400#64 + 912#64) ↦₆₄ 2080#64) ∗ ((s0.sp - 2400#64 + 936#64) ↦₆₄ 1152#64) ∗ ((s0.sp - 2400#64 + 960#64) ↦₆₄ 960#64) ∗ ((s0.sp - 2400#64 + 968#64) ↦₆₄ u80) ∗
     memRegion (s0.sp - 2400#64) 64 ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
     memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗
     memRegion ((s0.sp - 2400#64) + 296#64) 600 ∗ memRegion ((s0.sp - 2400#64) + 1024#64) 496 ∗ v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
     v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
     memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗
     (pbA ↦₆₄ 0x8000000000000008#64) ∗ v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 (BitVec.ofNat 64 auth.rootKey.length) u104 u112 (BitVec.ofNat 64 auth.macKey.length) u.epoch ∗
     v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b)
    hl1_lt hsp0_align hpc3 hrun3 hsp3 hx19_3 hx20_3 hx22_3 hx23_3 hx24_3 hx26_3 hx27_3 hx28_3 htr3
  refine SepWPp.weaken_pre (Entails.trans hP3 (Entails.of_eq (by ac_rfl))) (v10_sepWPp_seq_clean hdealloc ?_)
  intro s4 hpc4 hrun4 ⟨hsp4, hx9_4, hx19_4, hx21_4, hx22_4, hx23_4, hx26_4, hx27_4, hx28_4, htr4⟩
  have hcol_1224 := v8_fsp_296_to_1520_collapse (s0.sp - 2400#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 (BitVec.ofNat 64 auth.rootKey.length) u104 u112 (BitVec.ofNat 64 auth.macKey.length) u.epoch
  rw [v8_ucWordsAt_896_eq] at hcol_1224
  refine SepWPp.weaken_pre ?_ (Ext4K.v8_ekReceivedCt1Sampled_from_10836 (F := F) hA hE s0 s4 out pbA u auth sendingCt1 hpts u8 u16 u32 u40 u56 u64 u80 u88 (BitVec.ofNat 64 auth.rootKey.length) u104 u112
      (BitVec.ofNat 64 auth.macKey.length) pa1 (BitVec.ofNat 64 auth.rootKey.length) pa2 (BitVec.ofNat 64 auth.macKey.length) w0 w8 w16 w24 w32 w40 w48
      hlen hes hek hct1 hauth rfl rfl hsp0_align hpc4 hrun4 hsp4 hx9_4 hx19_4 hx21_4 hx22_4 hx23_4 hx26_4 hx27_4 hx28_4 htr4)
  exact Entails.trans (Entails.of_eq (show _ = (memRegion ((s0.sp - 2400#64) + 296#64) 600 ∗ (((s0.sp - 2400#64 + 896#64) ↦₆₄ u8) ∗ ((s0.sp - 2400#64 + 904#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 912#64) ↦₆₄ 2080#64) ∗ ((s0.sp - 2400#64 + 920#64) ↦₆₄ u32) ∗ ((s0.sp - 2400#64 + 928#64) ↦₆₄ u40) ∗ ((s0.sp - 2400#64 + 936#64) ↦₆₄ 1152#64) ∗
        ((s0.sp - 2400#64 + 944#64) ↦₆₄ u56) ∗ ((s0.sp - 2400#64 + 952#64) ↦₆₄ u64) ∗ ((s0.sp - 2400#64 + 960#64) ↦₆₄ 960#64) ∗ ((s0.sp - 2400#64 + 968#64) ↦₆₄ u80) ∗ ((s0.sp - 2400#64 + 976#64) ↦₆₄ u88) ∗
        ((s0.sp - 2400#64 + 984#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗ ((s0.sp - 2400#64 + 992#64) ↦₆₄ u104) ∗ ((s0.sp - 2400#64 + 1000#64) ↦₆₄ u112) ∗
        ((s0.sp - 2400#64 + 1008#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗ ((s0.sp - 2400#64 + 1016#64) ↦₆₄ u.epoch)) ∗ memRegion ((s0.sp - 2400#64) + 1024#64) 496) ∗ (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗
       memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
       memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗
       (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗
       v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗ v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗ vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
       vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗ v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88
         (BitVec.ofNat 64 auth.rootKey.length) u104 u112 (BitVec.ofNat 64 auth.macKey.length) u.epoch ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl)) (Entails.trans (sepConj_mono_left hcol_1224) (Entails.of_eq (by ac_rfl)))

set_option maxHeartbeats 800000 in
theorem states_from_pb_ekReceivedCt1Sampled_1764 {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) (hE : EncoderFromPbOkExt b A ext)
    (s : V1State.Chunked.EkReceivedCt1Sampled) (hpts : optEncoderPtsBound s.sendingCt1) (s0 s1 : State) (out pbA : BitVec 64) (R : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1764#64) (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64) (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1 (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        optProtoInnerStateAt A pbA (some (.ekReceivedCt1Sampled s)) ∗ statesFromPbJumpTableAt b ∗ A.pool) (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.ekReceivedCt1Sampled s) }) ∗ memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  refine v8_sepWPp_weaken_panic R ?_
  rw [v8_optProtoInnerStateAt_ekReceivedCt1Sampled_eq]
  refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ = optProtoUnchunkedCt1SentEkReceivedAt A (pbA + 8#64) s.uc ∗ optProtoPolynomialEncoderAt A (pbA + 136#64) (s.sendingCt1.map pbToProtoPolyEncoder) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗ memRegion (pbA + 192#64) 32 ∗
       statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl)) (sepConj_mono (v8_optProtoUnchunkedCt1SentEkReceivedAt_unpack A (pbA + 8#64) s.uc) (sepConj_mono_left (v1_optProtoPolyEncoderAt_unpack A (pbA + 136#64)
          (s.sendingCt1.map pbToProtoPolyEncoder))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro w0; apply SepWPp.exists_elim; intro w8; apply SepWPp.exists_elim; intro w16; apply SepWPp.exists_elim; intro w24; apply SepWPp.exists_elim; intro w32; apply SepWPp.exists_elim; intro w40
  apply SepWPp.exists_elim; intro w48; apply SepWPp.exists_elim; intro u8; apply SepWPp.exists_elim; intro u16; apply SepWPp.exists_elim; intro u24; apply SepWPp.exists_elim; intro u32
  apply SepWPp.exists_elim; intro u40; apply SepWPp.exists_elim; intro u48; apply SepWPp.exists_elim; intro u56; apply SepWPp.exists_elim; intro u64
  apply SepWPp.exists_elim; intro u72; apply SepWPp.exists_elim; intro u80; apply SepWPp.exists_elim; intro u88; apply SepWPp.exists_elim; intro u96
  apply SepWPp.exists_elim; intro u104; apply SepWPp.exists_elim; intro u112; apply SepWPp.exists_elim; intro u120; apply SepWPp.exists_elim; intro u128
  cases s with | mk uc sendingCt1 =>
  dsimp only at hpts ⊢
  cases uc with
  | none =>
    rw [v8_states_from_pb_uc_none_eq]
    simp only [v8_optProtoUcHeap, sepConj_assoc]
    rw [show v8_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗ ⌜u8 = noneCap⌝ ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b ∗ A.pool = ⌜u8 = noneCap⌝ ∗
      ((v8_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48) ∗
       stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗ memRegion (pbA + 192#64) 32 ∗
       v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl]
    refine SepWPp.pure_left fun hu8 => ?_
    subst hu8
    rw [v8_uc_and_enc_words_eq_pb128]
    apply SepWPp.of_sepWP_ret
    exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (Ext4K.v8_ekReceivedCt1Sampled_uc_none (F := F) hA s0 s1 out pbA u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
        (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1)
  | some u =>
    simp only [v8_optProtoUcHeap, sepConj_assoc]
    rw [show v8_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗ ⌜u8.toNat < 2 ^ 63 ∧ u24 = BitVec.ofNat 64 u.es.length ∧
          u32.toNat < 2 ^ 63 ∧ u48 = BitVec.ofNat 64 u.ek.length ∧ u56.toNat < 2 ^ 63 ∧ u72 = BitVec.ofNat 64 u.ct1.length ∧ u128 = u.epoch⌝ ∗
        vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ v1_optProtoAuthHeap A u.auth u80 u88 u96 u104 u112 u120 ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗ v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗ memRegion (pbA + 192#64) 32 ∗
        statesFromPbJumpTableAt b ∗ A.pool = ⌜u8.toNat < 2 ^ 63 ∧ u24 = BitVec.ofNat 64 u.es.length ∧ u32.toNat < 2 ^ 63 ∧ u48 = BitVec.ofNat 64 u.ek.length ∧ u56.toNat < 2 ^ 63 ∧ u72 = BitVec.ofNat 64 u.ct1.length ∧
        u128 = u.epoch⌝ ∗ (vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ ((v8_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
         v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48) ∗ memRegion (s0.sp - 2400#64) 2304 ∗ v1_optProtoAuthHeap A u.auth u80 u88 u96 u104 u112 u120 ∗
        v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        (pbA ↦₆₄ 0x8000000000000008#64) ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b ∗ A.pool)) by ac_rfl]
    refine SepWPp.pure_left fun ⟨hu8, hu24, hu32, hu48, hu56, hu72, hu128⟩ => ?_
    rw [v8_uc_and_enc_words_eq_pb128]
    refine SepWPp.weaken_pre (sepConj_mono (vecU8Payload_extract_len_lt63 A u8 u16 u.es) (sepConj_mono (vecU8Payload_extract_len_lt63 A u32 u40 u.ek)
          (sepConj_mono_left (vecU8Payload_extract_len_lt63 A u56 u64 u.ct1)))) ?_
    rw [show (⌜u.es.length < 2 ^ 63⌝ ∗ vecU8Payload A u8 u16 u.es) ∗ (⌜u.ek.length < 2 ^ 63⌝ ∗ vecU8Payload A u32 u40 u.ek) ∗ (⌜u.ct1.length < 2 ^ 63⌝ ∗ vecU8Payload A u56 u64 u.ct1) ∗
        (v8_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 w0 w8 w16 w24 w32 w40 w48 ∗ memRegion (s0.sp - 2400#64) 2304 ∗ v1_optProtoAuthHeap A u.auth u80 u88 u96 u104 u112 u120 ∗
         v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         (pbA ↦₆₄ 0x8000000000000008#64) ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b ∗ A.pool) = ⌜u.es.length < 2 ^ 63⌝ ∗ ⌜u.ek.length < 2 ^ 63⌝ ∗ ⌜u.ct1.length < 2 ^ 63⌝ ∗
      (memRegion (s0.sp - 2400#64) 2304 ∗ v8_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 w0 w8 w16 w24 w32 w40 w48 ∗
       (vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ v1_optProtoAuthHeap A u.auth u80 u88 u96 u104 u112 u120 ∗
        v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        (pbA ↦₆₄ 0x8000000000000008#64) ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b ∗ A.pool)) by ac_rfl]
    refine SepWPp.pure_left fun hes_lt =>
      SepWPp.pure_left fun hek_lt =>
      SepWPp.pure_left fun hct1_lt => ?_
    have hcopy := v8_copy_pb_to_stack_1764 s0 s1 out pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 w0 w8 w16 w24 w32 w40 w48
      (vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ v1_optProtoAuthHeap A u.auth u80 u88 u96 u104 u112 u120 ∗
       v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       (pbA ↦₆₄ 0x8000000000000008#64) ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b ∗ A.pool) hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
    have hu8_ne : (u8 + 1#64 == 0#64) = false := v10_cap_add_one_beq_zero_false hu8
    simp only [hu8_ne, Bool.false_eq_true, ↓reduceIte] at hcopy
    refine v10_sepWPp_seq_clean hcopy ?_
    intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx23_2, hx26_2, hx27_2, htr2⟩
    rw [hx23_1] at hx23_2
    rw [← v8_uc_and_enc_words_eq_pb128]
    cases hlen : (u.es.length == ENCAPSULATION_STATE_SIZE && u.ct1.length == CIPHERTEXT1_SIZE && u.ek.length == ENCAPSULATION_KEY_SIZE) with
    | false =>
      rw [v8_states_from_pb_len_err_eq u sendingCt1 hlen]
      have herr : u24 ≠ 2080#64 ∨ u72 ≠ 960#64 ∨ u48 ≠ 1152#64 := by
        rw [hu24, hu72, hu48]
        exact v8_len_err_of_false u hlen hes_lt hct1_lt hek_lt
      apply SepWPp.of_sepWP_ret
      have hstep := v8_step_1872_to_2100_len_err_x26 s0 s2 out pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 (v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
         memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗
         v1_optProtoAuthHeap A u.auth u80 u88 u96 u104 u112 u120 ∗ v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b ∗ A.pool)
        herr hsp0_align hpc2 hrun2 hsp2 hx19_2 hx23_2 hx26_2 hx27_2 htr2
      refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.seq hstep ?_)
      intro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, hx19_3, hx26_3, htr3⟩
      have hpb_col := v8_pb_uc_enc_entails_224 pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 w0 w8 w16 w24 w32 w40 w48
      have h3v := v8_3vecs_entails_dealloc A u8 u16 u32 u40 u56 u64 u.es u.ek u.ct1
      have hP3' : P3 ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 896 ∗ v8_ucWordsAt (s0.sp - 2400#64 + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
          memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗ v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
          v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
          vecCapPtrDealloc A u8 u16 ∗ vecCapPtrDealloc A u32 u40 ∗ vecCapPtrDealloc A u56 u64 ∗ v1_optProtoAuthHeap A u.auth u80 u88 u96 u104 u112 u120 ∗ A.pool ∗
          (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b) := by
        refine Entails.trans hP3 ?_
        refine Entails.trans (Entails.of_eq (show _ = ((pbA ↦₆₄ 0x8000000000000008#64) ∗ v8_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
           v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion (pbA + 192#64) 32) ∗ (vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 896 ∗ v8_ucWordsAt (s0.sp - 2400#64 + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
           memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗ v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
           v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
           v1_optProtoAuthHeap A u.auth u80 u88 u96 u104 u112 u120 ∗ A.pool ∗ statesFromPbJumpTableAt b) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono hpb_col (sepConj_mono_left h3v)) (Entails.of_eq (by ac_rfl))
      refine SepWP.weaken_pre hP3' (SepWP.mono (Ext4K.v8_drop_uc_and_sendingCt1_2100 (F := F) hA s0 s3 out u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 u.auth
        (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b) hsp0_align hpc3 hrun3 hsp3 hx19_3 hx26_3 htr3) ?_)
      intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
      exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩
    | true =>
      obtain ⟨hes, hct1, hek⟩ := v8_len_ok_of_true u hlen
      have hu24_eq : u24 = 2080#64 := by rw [hu24, hes]
      have hu48_eq : u48 = 1152#64 := by rw [hu48, hek]
      have hu72_eq : u72 = 960#64 := by rw [hu72, hct1]
      subst hu24_eq hu48_eq hu72_eq hu128
      have hstep := v8_step_1872_to_1972_len_ok s0 s2 out pbA u8 u16 u32 u40 u56 u64 u80 u88 u96 u104 u112 u120 u.epoch (v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
         memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗
         v1_optProtoAuthHeap A u.auth u80 u88 u96 u104 u112 u120 ∗ v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b ∗ A.pool)
        hsp0_align hpc2 hrun2 hsp2 hx19_2 hx23_2 hx26_2 hx27_2 htr2
      refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (v10_sepWPp_seq_clean hstep ?_)
      intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx26_3, hx27_3, htr3⟩
      cases hauth : u.auth with
      | none =>
        rw [v8_states_from_pb_auth_none_eq u sendingCt1 hlen hauth]
        dsimp only [v1_optProtoAuthHeap]
        rw [show memRegion (s0.sp - 2400#64) 896 ∗ v8_ucWordsAt (s0.sp - 2400#64 + 896#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗ memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
            v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗ (v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
             memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗
             ⌜u80 = noneCap⌝ ∗ v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b ∗ A.pool) = ⌜u80 = noneCap⌝ ∗
          (v8_ucWordsAt (s0.sp - 2400#64 + 896#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗ ((pbA ↦₆₄ 0x8000000000000008#64) ∗ v8_ucWordsAt (pbA + 8#64)
              u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion (pbA + 192#64) 32) ∗
           stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 896 ∗ memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
           v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗ v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
           memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗
           statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl]
        refine SepWPp.pure_left fun hu80 => ?_
        subst hu80
        apply SepWPp.of_sepWP_ret
        have hpb_col := v8_pb_uc_enc_entails_224 pbA u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 noneCap u88 u96 u104 u112 u120 u.epoch w0 w8 w16 w24 w32 w40 w48
        refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left hpb_col)) ?_
        have hchk := v8_check_auth_1972_none s0 s3 out u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u88 u96 u104 u112 u120 u.epoch (memRegion pbA optProtoInnerStateSize ∗
           stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 896 ∗ memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
           v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗ v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
           memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗
           statesFromPbJumpTableAt b ∗ A.pool) hsp0_align hpc3 hrun3 hsp3 hx19_3 htr3
        refine SepWP.seq hchk ?_
        intro s4 P4 hpc4 hrun4 ⟨hP4, hsp4, hx19_4, htr4⟩
        have hdrop := Ext4K.v8_drop_uc_auth_none_10544 (F := F) hA s0 s4 out u u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u88 u96 u104 u112 u120 (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48
          (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b) hsp0_align hu8 (by rw [hes]; rfl) hu32 (by rw [hek]; rfl) hu56 (by rw [hct1]; rfl) hauth hpc4 hrun4 hsp4 hx19_4 htr4
        refine SepWP.weaken_pre (Entails.trans hP4 (Entails.of_eq (by ac_rfl))) (SepWP.mono hdrop ?_)
        intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
        exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩
      | some auth =>
        dsimp only [v1_optProtoAuthHeap]
        rw [show memRegion (s0.sp - 2400#64) 896 ∗ v8_ucWordsAt (s0.sp - 2400#64 + 896#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗ memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
            v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗ (v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
             memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗
             (⌜u80.toNat < 2 ^ 63 ∧ u96 = BitVec.ofNat 64 auth.rootKey.length ∧ u120 = BitVec.ofNat 64 auth.macKey.length⌝ ∗ vecU8Payload A u80 u88 auth.rootKey ∗ vecU8Payload A u104 u112 auth.macKey) ∗
             v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
             (pbA ↦₆₄ 0x8000000000000008#64) ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b ∗ A.pool) = ⌜u80.toNat < 2 ^ 63 ∧ u96 = BitVec.ofNat 64 auth.rootKey.length ∧
            u120 = BitVec.ofNat 64 auth.macKey.length⌝ ∗ (v8_ucWordsAt (s0.sp - 2400#64 + 896#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗
           (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 896 ∗ memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
            v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗ v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
            memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ vecU8Payload A u80 u88 auth.rootKey ∗ vecU8Payload A u104 u112 auth.macKey ∗
            vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗ v8_ucWordsAt (pbA + 8#64)
              u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
            memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b ∗ A.pool)) by ac_rfl]
        refine SepWPp.pure_left fun ⟨hu80, hu96, hu120⟩ => ?_
        subst hu96 hu120
        have hchk := v8_check_auth_1972_some s0 s3 out pbA u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 (BitVec.ofNat 64 auth.rootKey.length) u104 u112 (BitVec.ofNat 64 auth.macKey.length) u.epoch
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 896 ∗ memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
           v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗ v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
           memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ vecU8Payload A u80 u88 auth.rootKey ∗ vecU8Payload A u104 u112 auth.macKey ∗
           vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗ v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88
             (BitVec.ofNat 64 auth.rootKey.length) u104 u112 (BitVec.ofNat 64 auth.macKey.length) u.epoch ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
           memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b ∗ A.pool) hu80 hsp0_align hpc3 hrun3 hsp3 hx19_3 hx26_3 hx27_3 htr3
        refine v10_sepWPp_seq_clean hchk ?_
        intro s4 hpc4 hrun4 ⟨hsp4, hx19_4, hx23_4, hx26_4, hx27_4, htr4⟩
        exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (Ext4K.v8_ekReceivedCt1Sampled_from_1984 (F := F) hA hE s0 s4 out pbA u auth sendingCt1 hpts u8 u16 u32 u40 u56 u64 u80 u88 u104 u112 w0 w8 w16 w24 w32 w40 w48
            hlen hes hek hct1 hauth hsp0_align hpc4 hrun4 hsp4 hx19_4 hx23_4 hx26_4 hx27_4 htr4)

end Ext4K

end CryptoVerification.SpqrV1.States.FromPb

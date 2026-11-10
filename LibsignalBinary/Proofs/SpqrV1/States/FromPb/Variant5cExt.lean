/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5c
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.EpilogueExt
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5aExt
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-! # `<spqr::v1::chunked::states::States>::from_pb`: 4-KiB Hook Wrapper for `Variant5c` -/

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
  stubOff_handle_error

theorem v5c_dealloc_cloned_auth_6520_to_6500
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (fsp out p1_new p2_new l1 l2 : BitVec 64)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 6520#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = l1)
    (hx27_1 : s1.readReg64 .x27 = p1_new)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 6500#64) s1
      (stackAt fsp allocHookStack ∗
        ((fsp + 136#64) ↦₆₄ p2_new) ∗
        ((fsp + 216#64) ↦₆₄ l2) ∗
        vecCapPtrDealloc A l1 p1_new ∗
        vecCapPtrDealloc A l2 p2_new ∗
        A.pool ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp allocHookStack ∗
          ((fsp + 136#64) ↦₆₄ p2_new) ∗
          ((fsp + 216#64) ↦₆₄ l2) ∗
          A.pool ∗
          Rest) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x27 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  have hdealloc := Ext4K.v5a_sub_ok_dealloc_125316 hA
  simp only [rustDeallocSpec] at hdealloc
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 6540#64)
    (P_mid :=
      stackAt fsp allocHookStack ∗
      ((fsp + 136#64) ↦₆₄ p2_new) ∗
      ((fsp + 216#64) ↦₆₄ l2) ∗
      vecCapPtrDealloc A l2 p2_new ∗
      A.pool ∗
      Rest)
    (Q := fun s2 =>
      s2.sp = fsp ∧
      s2.readReg64 .x19 = out ∧
      TraceCalleeSaved s2 s0)
    ?_ ?_
  · states_from_pb_fetches_range b (Rust.withPanics ext) 6520 20
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, vecCapPtrDealloc,
      BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    by_cases hl1 : (l1 == 0#64) = true <;>
      simp only [hl1, Bool.false_eq_true, ↓reduceIte, emp_sepConj]
    · wp_steps
      wp_done
    · wp_steps; wp_apply
      refine EncoderFromPb.align_pre (by rw [hsp1]; exact Entails.of_eq (by ac_rfl)) ?_
      wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, htr2⟩
    states_from_pb_fetches_range b (Rust.withPanics ext) 6540 28
    states_from_pb_fetches_range b (Rust.withPanics ext) 10484 8
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, vecCapPtrDealloc,
      BitVec.ofNat_eq_ofNat] at hdealloc hpc2 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    by_cases hl2 : (l2 == 0#64) = true <;>
      simp only [hl2, Bool.false_eq_true, ↓reduceIte, emp_sepConj]
    · wp_steps
      wp_done
    · wp_steps; wp_apply; wp_steps
      refine EncoderFromPb.align_pre (by rw [hsp2]; exact Entails.of_eq (by ac_rfl)) ?_
      wp_done

theorem v5c_noHeaderReceived_6132_ok_to_ret
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s : State) (fsp out ep pa1 l1 pa2 l2 w224 w232 w392 : BitVec 64)
    (bs : List (BitVec 8)) (hbs : bs.length = 384)
    (hw0_lt : (v9_wordAt bs 0).toNat < 2 ^ 63)
    (dec : PolyDecoder) (P_heap : SepProp)
    (hreloc :
      ((out + 64#64) ↦ₛ bs) ∗
        (((out + 64#64) + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
        (((out + 64#64) + 392#64) ↦₆₄ w392) ∗ P_heap ⊢
        polyDecoderAt A (out + 64#64) dec)
    (rootKey macKey : List (BitVec 8))
    (hl1 : l1 = BitVec.ofNat 64 rootKey.length)
    (hl2 : l2 = BitVec.ofNat 64 macKey.length)
    (Frame : SepProp)
    (halign : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp : fsp = s0.sp - 2400#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 6132#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = fsp + 1888#64)
    (hx21 : s.readReg64 .x21 = l1)
    (hx27 : s.readReg64 .x27 = pa1)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      ((memRegion fsp 136 ∗
        memRegion (fsp + 144#64) 8 ∗
        memRegion (fsp + 160#64) 48 ∗
        memRegion (fsp + 240#64) 1648) ∗
       stackAt fsp encoderFromPbStack ∗
       memRegion out chunkedStatesSize ∗
       ((fsp + 136#64) ↦₆₄ pa2) ∗
       ((fsp + 152#64) ↦₆₄ ep) ∗
       ((fsp + 208#64) ↦₆₄ pa1) ∗
       ((fsp + 216#64) ↦₆₄ l2) ∗
       ((fsp + 224#64) ↦₆₄ w224) ∗
       ((fsp + 232#64) ↦₆₄ w232) ∗
       v5c_decCellsAt (fsp + 1888#64) bs ∗
       ((fsp + 2272#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
       ((fsp + 2280#64) ↦₆₄ w392) ∗
       memRegion (fsp + 2288#64) 16 ∗
       statesFromPbSavedCells s0 ∗
       P_heap ∗
       vecU8Payload A l1 pa1 rootKey ∗
       vecU8Payload A l2 pa2 macKey ∗
       Frame)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (.ok (.noHeaderReceived
              { uc := { auth := { rootKey := rootKey, macKey := macKey }, epoch := ep },
                receiving_hdr := dec })) ∗
          stackAt s0.sp statesFromPbStack ∗ Frame) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true :=
    hfsp ▸ ProofLib.spAligned_sub s0.sp 2400#64 halign (by decide)
  refine SepWP.weaken_pre (sepConj_mono_left
    (sepConj_mono (v5c_memRegion_136_split fsp)
      (sepConj_mono (Entails.refl _)
        (sepConj_mono (v5c_memRegion_160_48_split fsp)
          (v5c_memRegion_240_1648_split fsp))))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine ProofLib.SepWP.exists_left fun u888 => ProofLib.SepWP.exists_left fun u880 =>
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
    ProofLib.SepWP.exists_left fun w192 => ProofLib.SepWP.exists_left fun d172 =>
    ProofLib.SepWP.exists_left fun u160 => ProofLib.SepWP.exists_left fun w120 =>
    ProofLib.SepWP.exists_left fun w112 => ProofLib.SepWP.exists_left fun w104 =>
    ProofLib.SepWP.exists_left fun d92 => ?_
  have hstep := v5c_step_6132_ok_to_8180 s0 s fsp out pa1 pa2 l1 l2 ep
    (BitVec.ofNat 64 dec.ptsNeeded) w392 bs
    u160 d172 pa1 w232
    uq608 uq624 uq640 uq656 uq672 uq688 uq704 uq720 uq736 uq752 uq768 uq784 uq800 uq816
    u832 uq848 u864 u880 u888
    (stackAt fsp encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
     memRegion fsp 92 ∗ ((fsp + 92#64) ↦₃₂ d92) ∗ memRegion (fsp + 96#64) 8 ∗
     ((fsp + 104#64) ↦₆₄ w104) ∗ ((fsp + 112#64) ↦₆₄ w112) ∗ ((fsp + 120#64) ↦₆₄ w120) ∗
     memRegion (fsp + 128#64) 8 ∗ memRegion (fsp + 144#64) 8 ∗
     memRegion (fsp + 168#64) 4 ∗ memRegion (fsp + 176#64) 16 ∗
     ((fsp + 192#64) ↦₆₄ w192) ∗ memRegion (fsp + 200#64) 8 ∗ ((fsp + 224#64) ↦₆₄ w224) ∗
     ((fsp + 240#64) ↦ₛ bs240.val) ∗ memRegion (fsp + 568#64) 8 ∗ ((fsp + 576#64) ↦₁₂₈ q576) ∗
     ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗ memRegion (fsp + 599#64) 9 ∗
     memRegion (fsp + 840#64) 8 ∗ memRegion (fsp + 871#64) 9 ∗ memRegion (fsp + 895#64) 993 ∗
     memRegion (fsp + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗
     P_heap ∗ vecU8Payload A l1 pa1 rootKey ∗ vecU8Payload A l2 pa2 macKey ∗ Frame)
    hfsp_align hw0_lt hpc hrun hsp hx19 hx20 hx21 hx27 htr
  refine SepWP.weaken_pre ?_ (EncoderFromPb.seq_clean hstep ?_)
  · unfold v5c_stagingSlotsPre
    exact Entails.of_eq (by ac_rfl)
  intro s2 hpc2 hrun2 ⟨hsp2, hx8_2, hx15_2, hx20_2, hx13_2, hx25_2, hx30_2,
    hx9_2, hx14_2, hx18_2, hx17_2, hx0_2, hx3_2, hx27_lo_2, hx27_mid_2, hx27_hi_2,
    hx4_2, hx5_2, hx21_2, hx7_2, hx2_2, hx11_2, hx22_2, hx24_2, hx10_2, hx26_2,
    hx6_2, hx19_2, hx23_2, htr2⟩
  subst hfsp
  have h128 := v5c_fsp_128_entails_32 (s0.sp - 2400#64) pa2 ep
  have h216 := ProofLib.pointsTo64_entails_memRegion ((s0.sp - 2400#64) + 216#64) l2
  have h1888 := v5c_fsp_1888_entails_epilogue (s0.sp - 2400#64)
    (BitVec.ofNat 64 dec.ptsNeeded) w392 bs hbs
  have hep := Ext4K.states_from_pb_epilogue_8180 hA s0 s2 out
    d92 ((EncoderFromPb.loByte (v9_wordAt bs 80)).zeroExtend 32)
    w104 w112 w120 (BitVec.ofNat 64 dec.ptsNeeded) w192 pa1 w224 (v9_wordAt bs 368)
    bs240.val bs240.property
    q576 w592
    (v9_quadAt bs 104) (v9_quadAt bs 120) (v9_quadAt bs 136) (v9_quadAt bs 152)
    (v9_quadAt bs 168) (v9_quadAt bs 184) (v9_quadAt bs 200) (v9_quadAt bs 216)
    (v9_quadAt bs 232) (v9_quadAt bs 248) (v9_quadAt bs 264) (v9_quadAt bs 280)
    (v9_quadAt bs 296) (v9_quadAt bs 312)
    (v9_wordAt bs 328)
    (v9_midQ128 (v9_wordAt bs 80) (v9_wordAt bs 88) (v9_wordAt bs 96))
    (v9_wordAt bs 96 >>> 8)
    (EncoderFromPb.unshiftWord (v9_wordAt bs 56) (EncoderFromPb.loByte (v9_wordAt bs 64)))
    (v9_wordAt bs 64 >>> 8)
    (v9_wordAt bs 8 ++ v9_wordAt bs 0) (v9_wordAt bs 24 ++ v9_wordAt bs 16) (v9_wordAt bs 32)
    (P_heap ∗ vecU8Payload A l1 pa1 rootKey ∗ vecU8Payload A l2 pa2 macKey ∗ Frame)
    halign hpc2 hrun2 hsp2 hx6_2 hx19_2 hx23_2 htr2
  rw [hx8_2, hx15_2, hx20_2, hx13_2, hx25_2, hx30_2, hx9_2, hx14_2, hx18_2, hx17_2,
      hx0_2, hx3_2, hx27_lo_2, hx27_mid_2, hx27_hi_2, hx4_2, hx5_2, hx21_2, hx7_2,
      hx2_2, hx11_2, hx22_2, hx24_2, hx10_2, hx26_2] at hep
  refine SepWP.weaken_pre ?_ (SepWP.mono hep ?_)
  · unfold v5c_stagingSlotsPost epilogueStackSlots epilogueStackGaps
    refine Entails.trans (Entails.of_eq (show _ =
      (memRegion ((s0.sp - 2400#64) + 128#64) 8 ∗ (((s0.sp - 2400#64) + 136#64) ↦₆₄ pa2) ∗
       memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep)) ∗
      (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗
      (v5c_decCellsAt ((s0.sp - 2400#64) + 1888#64) bs ∗
       (((s0.sp - 2400#64) + 2272#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
       (((s0.sp - 2400#64) + 2280#64) ↦₆₄ w392) ∗
       memRegion ((s0.sp - 2400#64) + 2288#64) 16) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
       memRegion (s0.sp - 2400#64) 92 ∗ (((s0.sp - 2400#64) + 92#64) ↦₃₂ d92) ∗
       memRegion ((s0.sp - 2400#64) + 96#64) 8 ∗
       (((s0.sp - 2400#64) + 104#64) ↦₆₄ w104) ∗ (((s0.sp - 2400#64) + 112#64) ↦₆₄ w112) ∗
       (((s0.sp - 2400#64) + 120#64) ↦₆₄ w120) ∗
       (((s0.sp - 2400#64) + 160#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
       memRegion ((s0.sp - 2400#64) + 168#64) 4 ∗
       (((s0.sp - 2400#64) + 172#64) ↦₃₂ (EncoderFromPb.loByte (v9_wordAt bs 80)).zeroExtend 32) ∗
       memRegion ((s0.sp - 2400#64) + 176#64) 16 ∗ (((s0.sp - 2400#64) + 192#64) ↦₆₄ w192) ∗
       memRegion ((s0.sp - 2400#64) + 200#64) 8 ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ pa1) ∗
       (((s0.sp - 2400#64) + 224#64) ↦₆₄ w224) ∗
       (((s0.sp - 2400#64) + 232#64) ↦₆₄ v9_wordAt bs 368) ∗
       (((s0.sp - 2400#64) + 240#64) ↦ₛ bs240.val) ∗
       memRegion ((s0.sp - 2400#64) + 568#64) 8 ∗ (((s0.sp - 2400#64) + 576#64) ↦₁₂₈ q576) ∗
       (((s0.sp - 2400#64) + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗
       memRegion ((s0.sp - 2400#64) + 599#64) 9 ∗
       (((s0.sp - 2400#64) + 608#64) ↦₁₂₈ v9_quadAt bs 104) ∗
       (((s0.sp - 2400#64) + 624#64) ↦₁₂₈ v9_quadAt bs 120) ∗
       (((s0.sp - 2400#64) + 640#64) ↦₁₂₈ v9_quadAt bs 136) ∗
       (((s0.sp - 2400#64) + 656#64) ↦₁₂₈ v9_quadAt bs 152) ∗
       (((s0.sp - 2400#64) + 672#64) ↦₁₂₈ v9_quadAt bs 168) ∗
       (((s0.sp - 2400#64) + 688#64) ↦₁₂₈ v9_quadAt bs 184) ∗
       (((s0.sp - 2400#64) + 704#64) ↦₁₂₈ v9_quadAt bs 200) ∗
       (((s0.sp - 2400#64) + 720#64) ↦₁₂₈ v9_quadAt bs 216) ∗
       (((s0.sp - 2400#64) + 736#64) ↦₁₂₈ v9_quadAt bs 232) ∗
       (((s0.sp - 2400#64) + 752#64) ↦₁₂₈ v9_quadAt bs 248) ∗
       (((s0.sp - 2400#64) + 768#64) ↦₁₂₈ v9_quadAt bs 264) ∗
       (((s0.sp - 2400#64) + 784#64) ↦₁₂₈ v9_quadAt bs 280) ∗
       (((s0.sp - 2400#64) + 800#64) ↦₁₂₈ v9_quadAt bs 296) ∗
       (((s0.sp - 2400#64) + 816#64) ↦₁₂₈ v9_quadAt bs 312) ∗
       (((s0.sp - 2400#64) + 832#64) ↦₆₄ v9_wordAt bs 328) ∗
       memRegion ((s0.sp - 2400#64) + 840#64) 8 ∗
       (((s0.sp - 2400#64) + 848#64) ↦₁₂₈
         v9_midQ128 (v9_wordAt bs 80) (v9_wordAt bs 88) (v9_wordAt bs 96)) ∗
       (((s0.sp - 2400#64) + 864#64) ↦ₛ EncoderFromPb.loBytes7 (v9_wordAt bs 96 >>> 8)) ∗
       memRegion ((s0.sp - 2400#64) + 871#64) 9 ∗
       (((s0.sp - 2400#64) + 880#64) ↦₆₄
         EncoderFromPb.unshiftWord (v9_wordAt bs 56) (EncoderFromPb.loByte (v9_wordAt bs 64))) ∗
       (((s0.sp - 2400#64) + 888#64) ↦ₛ EncoderFromPb.loBytes7 (v9_wordAt bs 64 >>> 8)) ∗
       memRegion ((s0.sp - 2400#64) + 895#64) 993 ∗
       statesFromPbSavedCells s0 ∗ P_heap ∗
       vecU8Payload A l1 pa1 rootKey ∗ vecU8Payload A l2 pa2 macKey ∗ Frame) by ac_rfl)) ?_
    refine Entails.trans
      (sepConj_mono h128 (sepConj_mono h216 (sepConj_mono_left h1888))) ?_
    exact Entails.of_eq (by ac_rfl)
  · intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
    refine ⟨Entails.trans hPf ?_, hsp_f, hcs_f, htr_f⟩
    have hout := v5c_epilogueOutFull_entails_noHeaderReceived A (F := F)
      out l1 pa1 l2 pa2 ep bs hbs w392 dec P_heap hreloc rootKey macKey hl1 hl2
      (s2.readReg64 .x12) (s2.readReg64 .x1) w224 (s2.readReg64 .x28) w192 (s2.readReg64 .x16)
      w104 w112 w120 (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592)
      bs240.val bs240.property
      (v9_wordAt bs 8 ++ v9_wordAt bs 0) (v9_wordAt bs 24 ++ v9_wordAt bs 16) (v9_wordAt bs 32)
    refine Entails.trans (Entails.of_eq (show _ =
      (epilogueOutFull out
        7#64 l1 pa1 l1 l2 pa2 l2 ep
        (v9_wordAt bs 0) (v9_wordAt bs 8) (v9_wordAt bs 16) (v9_wordAt bs 24)
        ((v9_wordAt bs 32).extractLsb' 0 8) ((v9_wordAt bs 32).extractLsb' 8 32)
        ((v9_wordAt bs 32).extractLsb' 40 16) ((v9_wordAt bs 32).extractLsb' 56 8)
        (v9_wordAt bs 40) (v9_wordAt bs 48)
        (EncoderFromPb.loByte (v9_wordAt bs 56))
        (EncoderFromPb.unshiftWord (v9_wordAt bs 56) (EncoderFromPb.loByte (v9_wordAt bs 64)))
        (overlapWord7
          (EncoderFromPb.unshiftWord (v9_wordAt bs 56) (EncoderFromPb.loByte (v9_wordAt bs 64)))
          (v9_wordAt bs 64 >>> 8))
        (v9_wordAt bs 72)
        (((EncoderFromPb.loByte (v9_wordAt bs 80)).zeroExtend 32).setWidth 8)
        (v9_midQ128 (v9_wordAt bs 80) (v9_wordAt bs 88) (v9_wordAt bs 96))
        (overlapWord7
          ((v9_midQ128 (v9_wordAt bs 80) (v9_wordAt bs 88) (v9_wordAt bs 96)).extractLsb' 64 64)
          (v9_wordAt bs 96 >>> 8))
        (v9_quadAt bs 104) (v9_quadAt bs 120) (v9_quadAt bs 136) (v9_quadAt bs 152)
        (v9_quadAt bs 168) (v9_quadAt bs 184) (v9_quadAt bs 200) (v9_quadAt bs 216)
        (v9_quadAt bs 232) (v9_quadAt bs 248) (v9_quadAt bs 264) (v9_quadAt bs 280)
        (v9_quadAt bs 296) (v9_quadAt bs 312)
        (v9_wordAt bs 328) (v9_wordAt bs 336) (v9_wordAt bs 344) (v9_wordAt bs 352)
        (v9_wordAt bs 360) (v9_wordAt bs 368) (v9_wordAt bs 376)
        (BitVec.ofNat 64 dec.ptsNeeded) w392
        (s2.readReg64 .x12) (s2.readReg64 .x1) w224 (s2.readReg64 .x28) w192 (s2.readReg64 .x16)
        w104 w112 w120 (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592)
        bs240.val (v9_wordAt bs 8 ++ v9_wordAt bs 0) (v9_wordAt bs 24 ++ v9_wordAt bs 16) (v9_wordAt bs 32) ∗
       P_heap ∗ vecU8Payload A l1 pa1 rootKey ∗ vecU8Payload A l2 pa2 macKey) ∗
      stackAt s0.sp statesFromPbStack ∗ Frame by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hout) (Entails.of_eq (by ac_rfl))

end CryptoVerification.SpqrV1.States.FromPb.Ext4K

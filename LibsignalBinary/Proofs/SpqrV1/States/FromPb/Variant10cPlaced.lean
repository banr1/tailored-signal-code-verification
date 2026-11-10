/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10c
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch2Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1Placed
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 10 (`Ct2Sampled`, `+1632`) — Part C (`Obj.MultiPlacedLib`)

Relocatable `Obj.MultiPlacedLib` (`[LibsignalPlacement]`) counterparts of the program-dependent
theorems in `Variant10c.lean`:
- `v10_ct2Sent_7904_to_8176_placed`
- `v10_ct2Sent_7904_to_ret_placed`
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification
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
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.CodeLayout
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

section

attribute [local irreducible]
  Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

/-! ## 1. Step `+7904 -> +8176` (`0x5bf84 -> 0x5c094`, 68 instructions) -/

set_option maxHeartbeats 1600000 in
/-- Symbolic execution of `+7904 -> +8176` (`0x5bf84 -> 0x5c094`, 68 instructions). -/
theorem v10_ct2Sent_7904_to_8176_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out tag pa1 pa2 l1 l2 ep w2280 : BitVec 64)
    (bs : List (BitVec 8))
    (u160 : BitVec 64) (d172 : BitVec 32) (u208 u232 : BitVec 64)
    (uq608 uq624 uq640 uq656 uq672 uq688 uq704 uq720 uq736 uq752 uq768 uq784 uq800 uq816 : BitVec 128)
    (u832 : BitVec 64) (uq848 : BitVec 128) (u864 u880 u887 : BitVec 64)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 7904#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx15 : s.readReg64 .x15 = tag)
    (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = pa1)
    (hx26 : s.readReg64 .x26 = l2)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8176#64) s
      (((fsp + 152#64) ↦₆₄ ep) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 200#64) ↦₆₄ l1) ∗
        v10_stagingSlotsPre fsp u160 d172 u208 u232
          uq608 uq624 uq640 uq656 uq672 uq688 uq704 uq720 uq736 uq752 uq768 uq784 uq800 uq816
          u832 uq848 u864 u880 u887 ∗
        v10_encCellsAt (fsp + 1888#64) bs ∗
        ((fsp + 2280#64) ↦₆₄ w2280) ∗
        Rest)
      (fun s2 P2 =>
        (P2 ⊢
          ((fsp + 152#64) ↦₆₄ ep) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 200#64) ↦₆₄ l1) ∗
          v10_stagingSlotsPost fsp bs l2 ∗
          v10_encCellsAt (fsp + 1888#64) bs ∗
          ((fsp + 2280#64) ↦₆₄ w2280) ∗
          Rest) ∧
        s2.sp = fsp ∧
        s2.readReg64 .x8 = 12#64 ∧
        s2.readReg64 .x15 = tag ∧
        s2.readReg64 .x20 = v10_wordAt bs 8 ∧
        s2.readReg64 .x13 = v10_wordAt bs 16 ∧
        s2.readReg64 .x25 = v10_wordAt bs 24 ∧
        s2.readReg64 .x30 = v10_wordAt bs 32 ∧
        s2.readReg64 .x9 = v10_wordAt bs 40 ∧
        s2.readReg64 .x14 = v10_wordAt bs 48 ∧
        s2.readReg64 .x18 = v10_wordAt bs 56 ∧
        s2.readReg64 .x17 = v10_wordAt bs 64 ∧
        s2.readReg64 .x0 = v10_wordAt bs 72 ∧
        (s2.readReg32 .x3).setWidth 8 = (v10_wordAt bs 80).extractLsb' 0 8 ∧
        s2.readReg32 .x27 = (v10_wordAt bs 80).extractLsb' 8 32 ∧
        ((s2.readReg64 .x27 >>> 32).setWidth 32).setWidth 16 = (v10_wordAt bs 80).extractLsb' 40 16 ∧
        ((s2.readReg64 .x27 >>> 48).setWidth 32).setWidth 8 = (v10_wordAt bs 80).extractLsb' 56 8 ∧
        s2.readReg64 .x4 = v10_wordAt bs 88 ∧
        s2.readReg64 .x5 = v10_wordAt bs 96 ∧
        (s2.readReg32 .x21).setWidth 8 = loByte (v10_wordAt bs 104) ∧
        s2.readReg64 .x7 = v10_wordAt bs 120 ∧
        s2.readReg64 .x2 = w2280 ∧
        s2.readReg64 .x11 = l1 ∧
        s2.readReg64 .x22 = pa1 ∧
        s2.readReg64 .x24 = l1 ∧
        s2.readReg64 .x10 = pa2 ∧
        s2.readReg64 .x26 = ep ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x23 = fsp + 848#64 ∧
        TraceCalleeSaved s2 s0) := by
  subst hsp
  unfold v10_stagingSlotsPre v10_stagingSlotsPost v10_encCellsAt
  simp only [pointsTo128, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
  change s.pc = (blkPl_333).base + 7904#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 8176#64) _ _ _
  wp_simp_pre only [v10_fsp_1976_split_rest, v10_fsp_2024_realign_rest, sepConj_assoc]
  iterate 12 wp_step
  wp_simp_pre only [v10_fsp_2000_realign_rest, sepConj_assoc]
  iterate 21 wp_step
  wp_simp_pre only [v10_fsp_2024_unrealign_rest, v10_fsp_2024_split_1_7_rest, sepConj_assoc]
  iterate 6 wp_step
  wp_simp_pre only [v10_fsp_880_realign_rest, sepConj_assoc]
  iterate 26 wp_step
  wp_simp_pre only [v10_fsp_856_realign_rest, sepConj_assoc]
  iterate 3 wp_step
  wp_simp_pre only [v10_fsp_856_unrealign_midQ128_rest, v10_fsp_1976_unsplit_rest,
    v10_fsp_2000_unrealign_rest, v10_fsp_2024_unsplit_1_7_rest, sepConj_assoc]
  wp_done

/-! ## 2. `+7904 -> s0.x30` After `PolyEncoder` Relocation -/

set_option maxHeartbeats 800000 in
theorem v10_ct2Sent_7904_to_ret_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s : State) (fsp out tag ep pa1 l1 pa2 l2 w224 w232 : BitVec 64)
    (bs : List (BitVec 8)) (hbs : bs.length = 384)
    (hi32 : BitVec 32) (enc : PolyEncoder) (P_heap : SepProp)
    (hreloc :
      ((out + 8#64) ↦₆₄ tag) ∗ (((out + 8#64) + 8#64) ↦ₛ bs) ∗
        (((out + 8#64) + 392#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ P_heap ⊢
        polyEncoderAt A (out + 8#64) enc)
    (rootKey macKey : List (BitVec 8))
    (hl1 : l1 = BitVec.ofNat 64 rootKey.length)
    (hl2 : l2 = BitVec.ofNat 64 macKey.length)
    (Frame : SepProp)
    (halign : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp : fsp = s0.sp - 2400#64)
    (hpc : s.pc = lsmpl.base 333 + 7904#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx15 : s.readReg64 .x15 = tag)
    (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = pa1)
    (hx26 : s.readReg64 .x26 = l2)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      ((memRegion fsp 152 ∗
        memRegion (fsp + 160#64) 24 ∗
        memRegion (fsp + 192#64) 8 ∗
        memRegion (fsp + 208#64) 16 ∗
        memRegion (fsp + 240#64) 1648) ∗
       stackAt fsp encoderFromPbStack ∗
       memRegion out chunkedStatesSize ∗
       ((fsp + 152#64) ↦₆₄ ep) ∗
       ((fsp + 184#64) ↦₆₄ pa2) ∗
       ((fsp + 200#64) ↦₆₄ l1) ∗
       ((fsp + 224#64) ↦₆₄ w224) ∗
       ((fsp + 232#64) ↦₆₄ w232) ∗
       ((fsp + 1888#64) ↦₆₄ tag) ∗
       v10_encCellsAt (fsp + 1888#64) bs ∗
       ((fsp + 2280#64) ↦₆₄ (hi32 ++ enc.idx)) ∗
       memRegion (fsp + 2288#64) 16 ∗
       statesFromPbSavedCells s0 ∗
       P_heap ∗
       vecU8Payload A l1 pa1 rootKey ∗
       vecU8Payload A l2 pa2 macKey ∗
       Frame)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (.ok (.ct2Sampled
              { uc := { auth := { rootKey := rootKey, macKey := macKey }, epoch := ep },
                sending_ct2 := enc })) ∗
          stackAt s0.sp statesFromPbStack ∗ Frame) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := hfsp ▸ sp_sub_2400_align s0.sp halign
  refine SepWP.weaken_pre (sepConj_mono_left (v10_fsp_split_7904_all fsp)) ?_
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
    ProofLib.SepWP.exists_left fun u208 => ProofLib.SepWP.exists_left fun w192 =>
    ProofLib.SepWP.exists_left fun d172 => ProofLib.SepWP.exists_left fun u160 =>
    ProofLib.SepWP.exists_left fun w120 => ProofLib.SepWP.exists_left fun w112 =>
    ProofLib.SepWP.exists_left fun w104 => ProofLib.SepWP.exists_left fun d92 => ?_
  have hstep := v10_ct2Sent_7904_to_8176_placed (ext := ext) s0 s fsp out tag pa1 pa2 l1 l2 ep (hi32 ++ enc.idx) bs
    u160 d172 u208 w232
    uq608 uq624 uq640 uq656 uq672 uq688 uq704 uq720 uq736 uq752 uq768 uq784 uq800 uq816
    u832 uq848 u864 u880 u887
    (stackAt fsp encoderFromPbStack ∗
     memRegion out chunkedStatesSize ∗
     memRegion fsp 92 ∗
     ((fsp + 92#64) ↦₃₂ d92) ∗
     memRegion (fsp + 96#64) 8 ∗
     ((fsp + 104#64) ↦₆₄ w104) ∗
     ((fsp + 112#64) ↦₆₄ w112) ∗
     ((fsp + 120#64) ↦₆₄ w120) ∗
     memRegion (fsp + 128#64) 24 ∗
     memRegion (fsp + 168#64) 4 ∗
     memRegion (fsp + 176#64) 8 ∗
     ((fsp + 192#64) ↦₆₄ w192) ∗
     memRegion (fsp + 216#64) 8 ∗
     ((fsp + 224#64) ↦₆₄ w224) ∗
     ((fsp + 240#64) ↦ₛ bs240.val) ∗
     memRegion (fsp + 568#64) 8 ∗
     ((fsp + 576#64) ↦₁₂₈ q576) ∗
     ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗
     memRegion (fsp + 599#64) 9 ∗
     memRegion (fsp + 840#64) 8 ∗
     memRegion (fsp + 871#64) 9 ∗
     memRegion (fsp + 895#64) 993 ∗
     ((fsp + 1888#64) ↦₆₄ tag) ∗
     memRegion (fsp + 2288#64) 16 ∗
     statesFromPbSavedCells s0 ∗
     P_heap ∗
     vecU8Payload A l1 pa1 rootKey ∗
     vecU8Payload A l2 pa2 macKey ∗
     Frame)
    hfsp_align hpc hrun hsp hx15 hx19 hx21 hx26 htr
  refine SepWP.weaken_pre ?_ (EncoderFromPb.seq_clean hstep ?_)
  · unfold v10_stagingSlotsPre
    exact Entails.of_eq (by ac_rfl)
  intro s2 hpc2 hrun2 ⟨hsp2, hx8_2, hx15_2, hx20_2, hx13_2, hx25_2, hx30_2,
    hx9_2, hx14_2, hx18_2, hx17_2, hx0_2, hx3_2, hx27_lo_2, hx27_mid_2, hx27_hi_2,
    hx4_2, hx5_2, hx21_2, hx7_2, hx2_2, hx11_2, hx22_2, hx24_2, hx10_2, hx26_2,
    hx19_2, hx23_2, htr2⟩
  subst hfsp
  have h128 := v10_fsp_128_152_entails_32 (s0.sp - 2400#64) ep
  have h176 := v10_fsp_176_184_entails_16 (s0.sp - 2400#64) pa2
  have h200 := ProofLib.pointsTo64_entails_memRegion ((s0.sp - 2400#64) + 200#64) l1
  have h1888 := v10_fsp_1888_entails_epilogue (s0.sp - 2400#64) tag (hi32 ++ enc.idx) bs hbs
  have hP2_ep :
      (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
      (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
      (((s0.sp - 2400#64) + 200#64) ↦₆₄ l1) ∗
      v10_stagingSlotsPost (s0.sp - 2400#64) bs l2 ∗
      v10_encCellsAt ((s0.sp - 2400#64) + 1888#64) bs ∗
      (((s0.sp - 2400#64) + 2280#64) ↦₆₄ (hi32 ++ enc.idx)) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion out chunkedStatesSize ∗
       memRegion (s0.sp - 2400#64) 92 ∗
       (((s0.sp - 2400#64) + 92#64) ↦₃₂ d92) ∗
       memRegion ((s0.sp - 2400#64) + 96#64) 8 ∗
       (((s0.sp - 2400#64) + 104#64) ↦₆₄ w104) ∗
       (((s0.sp - 2400#64) + 112#64) ↦₆₄ w112) ∗
       (((s0.sp - 2400#64) + 120#64) ↦₆₄ w120) ∗
       memRegion ((s0.sp - 2400#64) + 128#64) 24 ∗
       memRegion ((s0.sp - 2400#64) + 168#64) 4 ∗
       memRegion ((s0.sp - 2400#64) + 176#64) 8 ∗
       (((s0.sp - 2400#64) + 192#64) ↦₆₄ w192) ∗
       memRegion ((s0.sp - 2400#64) + 216#64) 8 ∗
       (((s0.sp - 2400#64) + 224#64) ↦₆₄ w224) ∗
       (((s0.sp - 2400#64) + 240#64) ↦ₛ bs240.val) ∗
       memRegion ((s0.sp - 2400#64) + 568#64) 8 ∗
       (((s0.sp - 2400#64) + 576#64) ↦₁₂₈ q576) ∗
       (((s0.sp - 2400#64) + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗
       memRegion ((s0.sp - 2400#64) + 599#64) 9 ∗
       memRegion ((s0.sp - 2400#64) + 840#64) 8 ∗
       memRegion ((s0.sp - 2400#64) + 871#64) 9 ∗
       memRegion ((s0.sp - 2400#64) + 895#64) 993 ∗
       (((s0.sp - 2400#64) + 1888#64) ↦₆₄ tag) ∗
       memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
       statesFromPbSavedCells s0 ∗
       P_heap ∗
       vecU8Payload A l1 pa1 rootKey ∗
       vecU8Payload A l2 pa2 macKey ∗
       Frame) ⊢
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion out chunkedStatesSize ∗
      epilogueStackSlots (s0.sp - 2400#64)
        d92 ((loByte (v10_wordAt bs 128)).zeroExtend 32)
        w104 w112 w120 l2 w192 (v10_wordAt bs 0) w224 l2 bs240.val
        q576 w592
        (v10_quadAt bs 152) (v10_quadAt bs 168) (v10_quadAt bs 184) (v10_quadAt bs 200)
        (v10_quadAt bs 216) (v10_quadAt bs 232) (v10_quadAt bs 248) (v10_quadAt bs 264)
        (v10_quadAt bs 280) (v10_quadAt bs 296) (v10_quadAt bs 312) (v10_quadAt bs 328)
        (v10_quadAt bs 344) (v10_quadAt bs 360)
        (v10_wordAt bs 376)
        (v10_midQ128 (v10_wordAt bs 128) (v10_wordAt bs 136) (v10_wordAt bs 144))
        (v10_wordAt bs 144 >>> 8)
        (unshiftWord (v10_wordAt bs 104) (loByte (v10_wordAt bs 112)))
        (v10_wordAt bs 112 >>> 8)
        (v10_wordAt bs 0 ++ tag) (v10_wordAt bs 16 ++ v10_wordAt bs 8) (v10_wordAt bs 24) ∗
      epilogueStackGaps (s0.sp - 2400#64) ∗
      statesFromPbSavedCells s0 ∗
      (P_heap ∗ vecU8Payload A l1 pa1 rootKey ∗ vecU8Payload A l2 pa2 macKey ∗ Frame) := by
    unfold v10_stagingSlotsPost epilogueStackSlots epilogueStackGaps
    refine Entails.trans (Entails.of_eq (show _ =
      (memRegion ((s0.sp - 2400#64) + 128#64) 24 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep)) ∗
      (memRegion ((s0.sp - 2400#64) + 176#64) 8 ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2)) ∗
      (((s0.sp - 2400#64) + 200#64) ↦₆₄ l1) ∗
      ((((s0.sp - 2400#64) + 1888#64) ↦₆₄ tag) ∗
       v10_encCellsAt ((s0.sp - 2400#64) + 1888#64) bs ∗
       (((s0.sp - 2400#64) + 2280#64) ↦₆₄ (hi32 ++ enc.idx)) ∗
       memRegion ((s0.sp - 2400#64) + 2288#64) 16) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion out chunkedStatesSize ∗
       memRegion (s0.sp - 2400#64) 92 ∗
       (((s0.sp - 2400#64) + 92#64) ↦₃₂ d92) ∗
       memRegion ((s0.sp - 2400#64) + 96#64) 8 ∗
       (((s0.sp - 2400#64) + 104#64) ↦₆₄ w104) ∗
       (((s0.sp - 2400#64) + 112#64) ↦₆₄ w112) ∗
       (((s0.sp - 2400#64) + 120#64) ↦₆₄ w120) ∗
       (((s0.sp - 2400#64) + 160#64) ↦₆₄ l2) ∗
       memRegion ((s0.sp - 2400#64) + 168#64) 4 ∗
       (((s0.sp - 2400#64) + 172#64) ↦₃₂ (loByte (v10_wordAt bs 128)).zeroExtend 32) ∗
       (((s0.sp - 2400#64) + 192#64) ↦₆₄ w192) ∗
       (((s0.sp - 2400#64) + 208#64) ↦₆₄ v10_wordAt bs 0) ∗
       memRegion ((s0.sp - 2400#64) + 216#64) 8 ∗
       (((s0.sp - 2400#64) + 224#64) ↦₆₄ w224) ∗
       (((s0.sp - 2400#64) + 232#64) ↦₆₄ l2) ∗
       (((s0.sp - 2400#64) + 240#64) ↦ₛ bs240.val) ∗
       memRegion ((s0.sp - 2400#64) + 568#64) 8 ∗
       (((s0.sp - 2400#64) + 576#64) ↦₁₂₈ q576) ∗
       (((s0.sp - 2400#64) + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗
       memRegion ((s0.sp - 2400#64) + 599#64) 9 ∗
       (((s0.sp - 2400#64) + 608#64) ↦₁₂₈ v10_quadAt bs 152) ∗
       (((s0.sp - 2400#64) + 624#64) ↦₁₂₈ v10_quadAt bs 168) ∗
       (((s0.sp - 2400#64) + 640#64) ↦₁₂₈ v10_quadAt bs 184) ∗
       (((s0.sp - 2400#64) + 656#64) ↦₁₂₈ v10_quadAt bs 200) ∗
       (((s0.sp - 2400#64) + 672#64) ↦₁₂₈ v10_quadAt bs 216) ∗
       (((s0.sp - 2400#64) + 688#64) ↦₁₂₈ v10_quadAt bs 232) ∗
       (((s0.sp - 2400#64) + 704#64) ↦₁₂₈ v10_quadAt bs 248) ∗
       (((s0.sp - 2400#64) + 720#64) ↦₁₂₈ v10_quadAt bs 264) ∗
       (((s0.sp - 2400#64) + 736#64) ↦₁₂₈ v10_quadAt bs 280) ∗
       (((s0.sp - 2400#64) + 752#64) ↦₁₂₈ v10_quadAt bs 296) ∗
       (((s0.sp - 2400#64) + 768#64) ↦₁₂₈ v10_quadAt bs 312) ∗
       (((s0.sp - 2400#64) + 784#64) ↦₁₂₈ v10_quadAt bs 328) ∗
       (((s0.sp - 2400#64) + 800#64) ↦₁₂₈ v10_quadAt bs 344) ∗
       (((s0.sp - 2400#64) + 816#64) ↦₁₂₈ v10_quadAt bs 360) ∗
       (((s0.sp - 2400#64) + 832#64) ↦₆₄ v10_wordAt bs 376) ∗
       memRegion ((s0.sp - 2400#64) + 840#64) 8 ∗
       (((s0.sp - 2400#64) + 848#64) ↦₁₂₈
         v10_midQ128 (v10_wordAt bs 128) (v10_wordAt bs 136) (v10_wordAt bs 144)) ∗
       (((s0.sp - 2400#64) + 864#64) ↦ₛ EncoderFromPb.loBytes7 (v10_wordAt bs 144 >>> 8)) ∗
       memRegion ((s0.sp - 2400#64) + 871#64) 9 ∗
       (((s0.sp - 2400#64) + 880#64) ↦₆₄ unshiftWord (v10_wordAt bs 104) (loByte (v10_wordAt bs 112))) ∗
       (((s0.sp - 2400#64) + 888#64) ↦ₛ EncoderFromPb.loBytes7 (v10_wordAt bs 112 >>> 8)) ∗
       memRegion ((s0.sp - 2400#64) + 895#64) 993 ∗
       statesFromPbSavedCells s0 ∗
       P_heap ∗
       vecU8Payload A l1 pa1 rootKey ∗
       vecU8Payload A l2 pa2 macKey ∗
       Frame) by ac_rfl)) ?_
    refine Entails.trans
      (sepConj_mono h128 (sepConj_mono h176 (sepConj_mono h200 (sepConj_mono_left h1888)))) ?_
    exact Entails.of_eq (by ac_rfl)
  have hep := states_from_pb_epilogue_8176_placed hA.memcpy s0 s2 out
    d92 ((loByte (v10_wordAt bs 128)).zeroExtend 32)
    w104 w112 w120 l2 w192 (v10_wordAt bs 0) w224 l2 bs240.val bs240.property
    q576 w592
    (v10_quadAt bs 152) (v10_quadAt bs 168) (v10_quadAt bs 184) (v10_quadAt bs 200)
    (v10_quadAt bs 216) (v10_quadAt bs 232) (v10_quadAt bs 248) (v10_quadAt bs 264)
    (v10_quadAt bs 280) (v10_quadAt bs 296) (v10_quadAt bs 312) (v10_quadAt bs 328)
    (v10_quadAt bs 344) (v10_quadAt bs 360)
    (v10_wordAt bs 376)
    (v10_midQ128 (v10_wordAt bs 128) (v10_wordAt bs 136) (v10_wordAt bs 144))
    (v10_wordAt bs 144 >>> 8)
    (unshiftWord (v10_wordAt bs 104) (loByte (v10_wordAt bs 112)))
    (v10_wordAt bs 112 >>> 8)
    (v10_wordAt bs 0 ++ tag) (v10_wordAt bs 16 ++ v10_wordAt bs 8) (v10_wordAt bs 24)
    (P_heap ∗ vecU8Payload A l1 pa1 rootKey ∗ vecU8Payload A l2 pa2 macKey ∗ Frame)
    halign hpc2 hrun2 hsp2 hx19_2 hx23_2 htr2
  rw [hx8_2, hx15_2, hx20_2, hx13_2, hx25_2, hx30_2, hx9_2, hx14_2, hx18_2, hx17_2,
      hx0_2, hx3_2, hx27_lo_2, hx27_mid_2, hx27_hi_2, hx4_2, hx5_2, hx21_2, hx7_2,
      hx2_2, hx11_2, hx22_2, hx24_2, hx10_2, hx26_2] at hep
  refine SepWP.weaken_pre hP2_ep (SepWP.mono hep ?_)
  intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
  refine ⟨Entails.trans hPf ?_, hsp_f, hcs_f, htr_f⟩
  have hout := v10_epilogueOutFull_entails_ct2Sent A (F := F)
    out tag l1 pa1 l2 pa2 ep bs hbs hi32 enc P_heap hreloc rootKey macKey hl1 hl2
    (s2.readReg64 .x12) (s2.readReg64 .x1) w224 (s2.readReg64 .x28) w192 (s2.readReg64 .x16)
    w104 w112 w120 (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592)
    bs240.val bs240.property
    (v10_wordAt bs 0 ++ tag) (v10_wordAt bs 16 ++ v10_wordAt bs 8) (v10_wordAt bs 24)
  refine Entails.trans (Entails.of_eq (show _ =
    (epilogueOutFull out
      12#64 tag (v10_wordAt bs 0) (v10_wordAt bs 8)
      (v10_wordAt bs 16) (v10_wordAt bs 24) (v10_wordAt bs 32) (v10_wordAt bs 40)
      (v10_wordAt bs 48) (v10_wordAt bs 56) (v10_wordAt bs 64) (v10_wordAt bs 72)
      ((v10_wordAt bs 80).extractLsb' 0 8) ((v10_wordAt bs 80).extractLsb' 8 32)
      ((v10_wordAt bs 80).extractLsb' 40 16) ((v10_wordAt bs 80).extractLsb' 56 8)
      (v10_wordAt bs 88) (v10_wordAt bs 96) (loByte (v10_wordAt bs 104))
      (unshiftWord (v10_wordAt bs 104) (loByte (v10_wordAt bs 112)))
      (overlapWord7 (unshiftWord (v10_wordAt bs 104) (loByte (v10_wordAt bs 112)))
        (v10_wordAt bs 112 >>> 8))
      (v10_wordAt bs 120)
      (((loByte (v10_wordAt bs 128)).zeroExtend 32).setWidth 8)
      (v10_midQ128 (v10_wordAt bs 128) (v10_wordAt bs 136) (v10_wordAt bs 144))
      (overlapWord7
        ((v10_midQ128 (v10_wordAt bs 128) (v10_wordAt bs 136) (v10_wordAt bs 144)).extractLsb' 64 64)
        (v10_wordAt bs 144 >>> 8))
      (v10_quadAt bs 152) (v10_quadAt bs 168) (v10_quadAt bs 184) (v10_quadAt bs 200)
      (v10_quadAt bs 216) (v10_quadAt bs 232) (v10_quadAt bs 248) (v10_quadAt bs 264)
      (v10_quadAt bs 280) (v10_quadAt bs 296) (v10_quadAt bs 312) (v10_quadAt bs 328)
      (v10_quadAt bs 344) (v10_quadAt bs 360)
      (v10_wordAt bs 376) (hi32 ++ enc.idx)
      l1 pa1 l1 l2 pa2 l2 ep
      (s2.readReg64 .x12) (s2.readReg64 .x1) w224 (s2.readReg64 .x28) w192 (s2.readReg64 .x16)
      w104 w112 w120 (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592)
      bs240.val (v10_wordAt bs 0 ++ tag) (v10_wordAt bs 16 ++ v10_wordAt bs 8) (v10_wordAt bs 24) ∗
     P_heap ∗
     vecU8Payload A l1 pa1 rootKey ∗
     vecU8Payload A l2 pa2 macKey) ∗
    stackAt s0.sp statesFromPbStack ∗ Frame by ac_rfl)) ?_
  exact Entails.trans (sepConj_mono_left hout) (Entails.of_eq (by ac_rfl))

end

end LibsignalBinary.Proofs.SpqrV1.States.FromPb

namespace CryptoVerification.SpqrV1.States.FromPb

export LibsignalBinary.Proofs.SpqrV1.States.FromPb (
  v10_ct2Sent_7904_to_8176_placed
  v10_ct2Sent_7904_to_ret_placed
)

end CryptoVerification.SpqrV1.States.FromPb

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.InterpolateFull
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.InterpolateFullExt
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.MainLoop

@[expose] public section

set_option autoImplicit false

/-!
# `<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message`: 4K-Stack Main Loop

**Checked by Lean.**

Lifts the evaluation and interpolation loop (`+548..+1404`) of `decoded_message` to
`AllocContracts4K b A ext` (`decodedMessageLoop_wpp_4k`).
-/

open Arm64 ProofLib
open CryptoVerification.RustHeap (RustAlloc allocFailedIn)
open CryptoVerification.LibsignalSessionRepr (VecPin)
open CryptoVerification.LibsignalSpqrV1 (GF16 Poly PolyDecoder u16ToBeBytes)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetProgAtExt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTableAt)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitAt)
open CryptoVerification.SpqrV1.Alloc (AllocContracts4K)
open CryptoVerification.SpqrV1.Poly (sortedSetPtListPinAt ptSliceAt)
open CryptoVerification.SpqrV1.Poly.AddChunk (PolyDecoderStrictSorted bsearchLoop bsearchLoop_bounds
  ptSliceAt_split_take_drop)
open CryptoVerification.SpqrV1.Poly.ComputeAt (computeAtName computeAtSpec computeAtPure
  computeAtStack)
open CryptoVerification.SpqrV1.Poly.LagrangePrepare (lagrangePrepareStack)
open CryptoVerification.SpqrV1.Poly.LagrangeComplete (lagrangeCompleteName lagrangeCompleteSpec)
open CryptoVerification.SpqrV1.Poly.DecodedMessage (decodedMessageName traceVRegs
  optPolyCacheSlotAt optPolyCacheListAt optPolyCacheListAt_focus optPolyCacheListAt_set
  ptSliceRefAt ptSliceRefListAt ptSliceRefListAt_focus
  sortedSetPtListPinAt_focus sortedSetPtPinAt_eq_slice sortedSetPtPinRest
  polyDecoderStrictSorted_elem_length_le
  collectedSlices decodedMessageLoopTotal decodedMessageLoopTotal_step_found
  decodedMessageLoopTotal_step_not_found necessaryPoints_pos_of_lt lagrangeInterpolateTotal
  interpolateScratchAt stackAt_computeAt_eq_prepare
  decodedMessage_bsearchStep_sepWP decodedMessage_computeAtStep_wpp
  decodedMessage_pushTwoBytes_sepWP)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.InterpolateFullExt (
  lagrangeInterpolate_inlined_wpp_4k)

namespace LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.MainLoopExt

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

/-! ## Full Main Loop (`entry + 548#64` to `entry + 1404#64`) under `AllocContracts4K` -/

/-- Full evaluation/interpolation loop (`entry + 548#64` to `entry + 1404#64`) under
    `AllocContracts4K b A ext`: executes `rem + 1` iterations from `i` to `dec.ptsNeeded`,
    matching `decodedMessageLoopTotal dec (collectedSlices dec 0 16) i (rem + 1) polys out`. -/
theorem decodedMessageLoop_wpp_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (hb : b &&& 0xfff#64 = 0#64)
    (hA : AllocContracts4K b A ext)
    (hcomp : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr lagrangeCompleteName)
      (lagrangeCompleteSpec b))
    (hcomp_at : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr computeAtName)
      (computeAtSpec A b))
    (dec : PolyDecoder) (sp0 pts_base pts_vec_ptr out_ptr : BitVec 64)
    (pins : List VecPin)
    (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (hpts : dec.pts.length = 16) (hpins : pins.length = 16)
    (hsort : PolyDecoderStrictSorted dec)
    (hneed_le : dec.ptsNeeded ≤ 16 * 65536)
    (hall_ge : ∀ k (hk : k < 16), dec.necessaryPoints k ≤ (dec.pts[k]'(by omega)).vec.length)
    (s0 : State) (F R : SepProp) (Q : State → SepProp → Prop) :
    ∀ (rem i : Nat) (polys : List (Option Poly)) (out : List (BitVec 8)) (s : State),
      i + (rem + 1) = dec.ptsNeeded →
      polys.length = 16 →
      out.length = 2 * i →
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 548#64 →
      s.status = .Running →
      s.sp = sp0 - 672#64 →
      traceVRegs s = traceVRegs s0 →
      s.readReg64 .x20 = pts_base →
      s.readReg64 .x22 = BitVec.ofNat 64 i →
      s.readReg64 .x23 = BitVec.ofNat 64 (2 * i) →
      s.readReg64 .x24 = BitVec.ofNat 64 dec.ptsNeeded →
      s.readReg64 .x25 = 24#64 →
      s.readReg64 .x26 = sp0 - 600#64 →
      s.readReg64 .x29 = sp0 - 96#64 →
      (∀ sf : State,
        sf.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 1404#64 →
        sf.status = .Running →
        sf.sp = sp0 - 672#64 →
        traceVRegs sf = traceVRegs s0 →
        sf.readReg64 .x29 = sp0 - 96#64 →
        let (polysFinal, outFinal) :=
          decodedMessageLoopTotal dec (collectedSlices dec 0 16) i (rem + 1) polys out
        SepWPp (tripleRatchetProgAtExt b ext) target_pc sf
          (optPolyCacheListAt A (sp0 - 600#64) polysFinal ∗
            ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
            ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
            ((sp0 - 608#64) ↦₆₄ 16#64) ∗
            ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
            ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
            ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
            ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
            sortedSetPtListPinAt A pts_base pins dec.pts ∗
            (out_ptr ↦ₛ outFinal) ∗
            interpolateScratchAt sp0 ∗
            reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗
            stackAt (sp0 - 672#64) computeAtStack ∗ F)
          Q
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) →
      SepWPp (tripleRatchetProgAtExt b ext) target_pc s
        (optPolyCacheListAt A (sp0 - 600#64) polys ∗
          ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
          ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
          ((sp0 - 608#64) ↦₆₄ 16#64) ∗
          ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
          ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
          ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
          ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
          sortedSetPtListPinAt A pts_base pins dec.pts ∗
          (out_ptr ↦ₛ out) ∗
          memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (dec.ptsNeeded - i)) ∗
          interpolateScratchAt sp0 ∗
          reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗
          stackAt (sp0 - 672#64) computeAtStack ∗ F)
        Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))
  | rem, i, polys, out, s, hsum, hpolys_len, hout_len,
      hpc, hstat, hsp, htr, hx20, hx22, hx23, hx24, hx25, hx26, hx29, hnext => by
    have hi_lt : i < dec.ptsNeeded := by omega
    have hpoly_lt : i % 16 < 16 := Nat.mod_lt i (by decide)
    have hpoly_pts : i % 16 < dec.pts.length := by omega
    have hpoly_pins : i % 16 < pins.length := by omega
    have hpoly_p : i % 16 < polys.length := by omega
    have hnec_pos : 1 ≤ dec.necessaryPoints (i % 16) := necessaryPoints_pos_of_lt dec hi_lt
    have hnec_le_len : dec.necessaryPoints (i % 16) ≤ (dec.pts[i % 16]'hpoly_pts).vec.length :=
      hall_ge (i % 16) hpoly_lt
    have hle_len : (dec.pts[i % 16]'hpoly_pts).vec.length ≤ 65536 :=
      polyDecoderStrictSorted_elem_length_le hsort hpoly_pts
    have hge_len : 1 ≤ (dec.pts[i % 16]'hpoly_pts).vec.length := by omega
    have ⟨_, hb_lt0⟩ := bsearchLoop_bounds (dec.pts[i % 16]'hpoly_pts).vec
      (BitVec.ofNat 16 (i / 16)) 0 (dec.pts[i % 16]'hpoly_pts).vec.length hge_len (by omega)
    have hb_lt : bsearchLoop (dec.pts[i % 16]'hpoly_pts).vec (BitVec.ofNat 16 (i / 16)) 0
        (dec.pts[i % 16]'hpoly_pts).vec.length < (dec.pts[i % 16]'hpoly_pts).vec.length := by
      omega
    cases hfound : ((dec.pts[i % 16]'hpoly_pts).vec[bsearchLoop (dec.pts[i % 16]'hpoly_pts).vec (BitVec.ofNat 16 (i / 16)) 0 (dec.pts[i % 16]'hpoly_pts).vec.length]'hb_lt).x.value == BitVec.ofNat 16 (i / 16)
    · apply SepWPp.of_sepWP (mid := (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 660#64)
      refine SepWP.weaken_pre ?_
        (decodedMessage_bsearchStep_sepWP (A := A) dec sp0 pts_base pins i hpts hpins hi_lt hneed_le hge_len hle_len
          s
          (optPolyCacheListAt A (sp0 - 600#64) polys ∗
            ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
            ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
            ((sp0 - 608#64) ↦₆₄ 16#64) ∗
            ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
            ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
            ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
            (out_ptr ↦ₛ out) ∗
            memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (dec.ptsNeeded - i)) ∗
            interpolateScratchAt sp0 ∗
            reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗
            stackAt (sp0 - 672#64) computeAtStack ∗ F)
          _ hpc hstat hx20 hx22 hx23 hx24 hx25 hx26 hx29 ?_ ?_)
      · sep_frame
      · dsimp only
        intro _ htrue
        rw [hfound] at htrue
        cases htrue
      · dsimp only
        intro _ hnot_found s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx20_1 hx22_1 hx24_1 hx25_1 hx26_1 hx29_1
        apply SepWP.done hpc1 hrun1
        have hstep_pure := decodedMessageLoopTotal_step_not_found dec hpts hsort hpolys_len (rem := rem) (out := out) rfl hb_lt hnot_found
        let ptsSlice := (dec.pts[i % 16]'hpoly_pts).vec.take (dec.necessaryPoints (i % 16))
        let pInterp := (polys[i % 16]'hpoly_p).getD (lagrangeInterpolateTotal ptsSlice)
        let yInterp := computeAtPure pInterp (GF16.new (BitVec.ofNat 16 (i / 16)))
        have hslice_len : ptsSlice.length = dec.necessaryPoints (i % 16) :=
          List.length_take_of_le hnec_le_len
        have hk_pos : 1 ≤ ptsSlice.length := by rw [hslice_len]; exact hnec_pos
        have hk_le : ptsSlice.length ≤ 65536 := by rw [hslice_len]; omega
        have hfocus_pre :
            sortedSetPtListPinAt A pts_base pins dec.pts ∗
              ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
              (optPolyCacheListAt A (sp0 - 600#64) polys ∗
                ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
                ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
                ((sp0 - 608#64) ↦₆₄ 16#64) ∗
                ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
                ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
                ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
                (out_ptr ↦ₛ out) ∗
                memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (dec.ptsNeeded - i)) ∗
                interpolateScratchAt sp0 ∗
                reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗
                stackAt (sp0 - 672#64) computeAtStack ∗ F) ⊢
            optPolyCacheSlotAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16))) (polys[i % 16]'hpoly_p) ∗
              ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
              ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
              ((sp0 - 608#64) ↦₆₄ 16#64) ∗
              ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * (i % 16)))
                (pins[i % 16]'hpoly_pins).ptr ptsSlice.length ∗
              ptSliceAt (pins[i % 16]'hpoly_pins).ptr ptsSlice ∗
              interpolateScratchAt sp0 ∗
              reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗
              stackAt (sp0 - 672#64) lagrangePrepareStack ∗
              (optPolyCacheListAt A (sp0 - 600#64) (polys.take (i % 16)) ∗
                optPolyCacheListAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16 + 1))) (polys.drop (i % 16 + 1)) ∗
                ptSliceRefListAt dec 0 pts_vec_ptr (pins.take (i % 16)) ∗
                ptSliceRefListAt dec (i % 16 + 1) (pts_vec_ptr + BitVec.ofNat 64 (16 * (i % 16 + 1))) (pins.drop (i % 16 + 1)) ∗
                sortedSetPtListPinAt A pts_base (pins.take (i % 16)) (dec.pts.take (i % 16)) ∗
                ((pts_base + BitVec.ofNat 64 (24 * (i % 16))) ↦₆₄ (pins[i % 16]'hpoly_pins).cap) ∗
                ((pts_base + BitVec.ofNat 64 (24 * (i % 16)) + 8#64) ↦₆₄ (pins[i % 16]'hpoly_pins).ptr) ∗
                ((pts_base + BitVec.ofNat 64 (24 * (i % 16)) + 16#64) ↦₆₄
                  BitVec.ofNat 64 (dec.pts[i % 16]'hpoly_pts).vec.length) ∗
                ptSliceAt ((pins[i % 16]'hpoly_pins).ptr + BitVec.ofNat 64 (4 * dec.necessaryPoints (i % 16)))
                  ((dec.pts[i % 16]'hpoly_pts).vec.drop (dec.necessaryPoints (i % 16))) ∗
                sortedSetPtPinRest A (pins[i % 16]'hpoly_pins) (dec.pts[i % 16]'hpoly_pts) ∗
                sortedSetPtListPinAt A (pts_base + BitVec.ofNat 64 (24 * (i % 16 + 1)))
                  (pins.drop (i % 16 + 1)) (dec.pts.drop (i % 16 + 1)) ∗
                ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
                ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
                ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
                (out_ptr ↦ₛ out) ∗
                memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (dec.ptsNeeded - i)) ∗
                memRegion ((sp0 - 672#64) - 4352#64) 48 ∗ F) := by
          rw [optPolyCacheListAt_focus A polys (i % 16) (sp0 - 600#64) hpoly_p,
            ptSliceRefListAt_focus dec pins (i % 16) pts_vec_ptr hpoly_pins,
            sortedSetPtListPinAt_focus A pins dec.pts (i % 16) pts_base (by rw [hpins, hpts]) hpoly_pts,
            sortedSetPtPinAt_eq_slice A (pins[i % 16]'hpoly_pins) (dec.pts[i % 16]'hpoly_pts)
              (pts_base + BitVec.ofNat 64 (24 * (i % 16))),
            ptSliceAt_split_take_drop (dec.pts[i % 16]'hpoly_pts).vec (dec.necessaryPoints (i % 16))
              (pins[i % 16]'hpoly_pins).ptr hnec_le_len,
            stackAt_computeAt_eq_prepare (sp0 - 672#64), hslice_len]
          sep_frame
        refine SepWPp.weaken_pre hfocus_pre
          (lagrangeInterpolate_inlined_wpp_4k hb hA hcomp sp0 pts_vec_ptr (pins[i % 16]'hpoly_pins).ptr
            (BitVec.ofNat 64 dec.ptsNeeded) hsp0 (i % 16) (polys[i % 16]'hpoly_p) ptsSlice
            hpoly_lt hk_pos hk_le s0 s1 _ R Q
            hpc1 hrun1 (by rw [hsp1, hsp]) (by rw [htr1, htr])
            hx0_1 hx24_1 hx25_1 hx26_1 hx29_1 ?_)
        intro s2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx22_2 hx24_2 hx25_2 hx26_2 hx29_2
        have hreasm_mid :
            optPolyCacheSlotAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16))) (some pInterp) ∗
              ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
              ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
              ((sp0 - 608#64) ↦₆₄ 16#64) ∗
              ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * (i % 16)))
                (pins[i % 16]'hpoly_pins).ptr ptsSlice.length ∗
              ptSliceAt (pins[i % 16]'hpoly_pins).ptr ptsSlice ∗
              interpolateScratchAt sp0 ∗
              reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗
              stackAt (sp0 - 672#64) lagrangePrepareStack ∗
              (optPolyCacheListAt A (sp0 - 600#64) (polys.take (i % 16)) ∗
                optPolyCacheListAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16 + 1))) (polys.drop (i % 16 + 1)) ∗
                ptSliceRefListAt dec 0 pts_vec_ptr (pins.take (i % 16)) ∗
                ptSliceRefListAt dec (i % 16 + 1) (pts_vec_ptr + BitVec.ofNat 64 (16 * (i % 16 + 1))) (pins.drop (i % 16 + 1)) ∗
                sortedSetPtListPinAt A pts_base (pins.take (i % 16)) (dec.pts.take (i % 16)) ∗
                ((pts_base + BitVec.ofNat 64 (24 * (i % 16))) ↦₆₄ (pins[i % 16]'hpoly_pins).cap) ∗
                ((pts_base + BitVec.ofNat 64 (24 * (i % 16)) + 8#64) ↦₆₄ (pins[i % 16]'hpoly_pins).ptr) ∗
                ((pts_base + BitVec.ofNat 64 (24 * (i % 16)) + 16#64) ↦₆₄
                  BitVec.ofNat 64 (dec.pts[i % 16]'hpoly_pts).vec.length) ∗
                ptSliceAt ((pins[i % 16]'hpoly_pins).ptr + BitVec.ofNat 64 (4 * dec.necessaryPoints (i % 16)))
                  ((dec.pts[i % 16]'hpoly_pts).vec.drop (dec.necessaryPoints (i % 16))) ∗
                sortedSetPtPinRest A (pins[i % 16]'hpoly_pins) (dec.pts[i % 16]'hpoly_pts) ∗
                sortedSetPtListPinAt A (pts_base + BitVec.ofNat 64 (24 * (i % 16 + 1)))
                  (pins.drop (i % 16 + 1)) (dec.pts.drop (i % 16 + 1)) ∗
                ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
                ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
                ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
                (out_ptr ↦ₛ out) ∗
                memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (dec.ptsNeeded - i)) ∗
                memRegion ((sp0 - 672#64) - 4352#64) 48 ∗ F) ⊢
            optPolyCacheSlotAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16))) (some pInterp) ∗
              ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
              ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
              reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗
              stackAt (sp0 - 672#64) computeAtStack ∗
              (optPolyCacheListAt A (sp0 - 600#64) (polys.take (i % 16)) ∗
                optPolyCacheListAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16 + 1))) (polys.drop (i % 16 + 1)) ∗
                ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
                ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
                ((sp0 - 608#64) ↦₆₄ 16#64) ∗
                ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
                ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
                sortedSetPtListPinAt A pts_base pins dec.pts ∗
                (out_ptr ↦ₛ out) ∗
                memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (dec.ptsNeeded - i)) ∗
                interpolateScratchAt sp0 ∗ F) := by
          rw [ptSliceRefListAt_focus dec pins (i % 16) pts_vec_ptr hpoly_pins,
            sortedSetPtListPinAt_focus A pins dec.pts (i % 16) pts_base (by rw [hpins, hpts]) hpoly_pts,
            sortedSetPtPinAt_eq_slice A (pins[i % 16]'hpoly_pins) (dec.pts[i % 16]'hpoly_pts)
              (pts_base + BitVec.ofNat 64 (24 * (i % 16))),
            ptSliceAt_split_take_drop (dec.pts[i % 16]'hpoly_pts).vec (dec.necessaryPoints (i % 16))
              (pins[i % 16]'hpoly_pins).ptr hnec_le_len,
            stackAt_computeAt_eq_prepare (sp0 - 672#64), hslice_len]
          sep_frame
        refine SepWPp.weaken_pre hreasm_mid
          (decodedMessage_computeAtStep_wpp hcomp_at sp0
            ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16))) hsp0 i dec.ptsNeeded pInterp
            hi_lt hneed_le s0 s2 _ R Q
            hpc2 hrun2 hsp2 htr2 hx19_2 (by rw [hx22_2, hx22_1]) hx29_2 ?_)
        intro s3 hpc3 hrun3 hsp3 htr3 hx19_3 hx21_3 hx20_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx29_3
        apply SepWPp.of_sepWP
          (mid := if i + 1 = dec.ptsNeeded then
            (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 1404#64
          else
            (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 548#64)
        have hset_polys :
            optPolyCacheListAt A (sp0 - 600#64) (polys.take (i % 16)) ∗
              optPolyCacheSlotAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16))) (some pInterp) ∗
              optPolyCacheListAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16 + 1))) (polys.drop (i % 16 + 1)) =
            optPolyCacheListAt A (sp0 - 600#64) (polys.set (i % 16) (some pInterp)) :=
          (optPolyCacheListAt_set A polys (i % 16) (some pInterp) (sp0 - 600#64) hpoly_p).symm
        refine SepWP.weaken_pre ?_
          (decodedMessage_pushTwoBytes_sepWP sp0 out_ptr (BitVec.ofNat 64 (2 * i)) i dec.ptsNeeded out
            yInterp.value hi_lt hneed_le hout_len s3
            (optPolyCacheListAt A (sp0 - 600#64) (polys.set (i % 16) (some pInterp)) ∗
              ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
              ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
              ((sp0 - 608#64) ↦₆₄ 16#64) ∗
              ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
              sortedSetPtListPinAt A pts_base pins dec.pts ∗
              interpolateScratchAt sp0 ∗
              reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗
              stackAt (sp0 - 672#64) computeAtStack ∗ F)
            _ hpc3 hrun3 hx19_3 hx21_3 hx22_3 hx23_3 (by rw [hx24_3, hx24_2]) hx29_3 ?_)
        · rw [← hset_polys]
          sep_frame
        intro s4 hpc4 hrun4 hsp4 htr4 hx20_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx29_4
        apply SepWP.done hpc4 hrun4
        cases rem with
        | zero =>
          have hi1_eq : i + 1 = dec.ptsNeeded := by omega
          simp only [hi1_eq, ↓reduceIte] at hpc4
          have hrem0 : dec.ptsNeeded - (i + 1) = 0 := by omega
          rw [hrem0, Nat.mul_zero, memRegion_zero]
          have hloop0 :
              decodedMessageLoopTotal dec (collectedSlices dec 0 16) i (0 + 1) polys out =
                (polys.set (i % 16) (some pInterp), out ++ u16ToBeBytes yInterp.value) := by
            rw [hstep_pure]; rfl
          rw [hloop0] at hnext
          refine SepWPp.weaken_pre ?_
            (hnext s4 hpc4 hrun4 (by rw [hsp4, hsp3]) (by rw [htr4, htr3]) hx29_4)
          rw [hi1_eq]
          sep_frame
        | succ rem' =>
          have hi1_ne : i + 1 ≠ dec.ptsNeeded := by omega
          simp only [hi1_ne, ↓reduceIte] at hpc4
          refine SepWPp.weaken_pre ?_
            (decodedMessageLoop_wpp_4k hb hA hcomp hcomp_at dec sp0 pts_base pts_vec_ptr out_ptr pins
              hsp0 hpts hpins hsort hneed_le hall_ge s0 F R Q
              rem' (i + 1) (polys.set (i % 16) (some pInterp))
              (out ++ u16ToBeBytes yInterp.value)
              s4 (by omega) (by simp [hpolys_len]) (by simp [hout_len, u16ToBeBytes]; omega)
              hpc4 hrun4 (by rw [hsp4, hsp3]) (by rw [htr4, htr3])
              (by rw [hx20_4, hx20_3, hx20_2, hx20_1]) hx22_4 hx23_4 hx24_4
              (by rw [hx25_4, hx25_3, hx25_2]) (by rw [hx26_4, hx26_3, hx26_2]) hx29_4
              (fun sf hpc_f hrun_f hsp_f htr_f hx29_f => ?_))
          · sep_frame
          · rw [← hstep_pure]
            exact hnext sf hpc_f hrun_f hsp_f htr_f hx29_f
    · apply SepWPp.of_sepWP
        (mid := if i + 1 = dec.ptsNeeded then
          (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 1404#64
        else
          (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 548#64)
      refine SepWP.weaken_pre ?_
        (decodedMessage_bsearchStep_sepWP (A := A) dec sp0 pts_base pins i hpts hpins hi_lt hneed_le hge_len hle_len
          s
          (optPolyCacheListAt A (sp0 - 600#64) polys ∗
            ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
            ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
            ((sp0 - 608#64) ↦₆₄ 16#64) ∗
            ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
            ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
            ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
            (out_ptr ↦ₛ out) ∗
            memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (dec.ptsNeeded - i)) ∗
            interpolateScratchAt sp0 ∗
            reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗
            stackAt (sp0 - 672#64) computeAtStack ∗ F)
          _ hpc hstat hx20 hx22 hx23 hx24 hx25 hx26 hx29 ?_ ?_)
      · sep_frame
      · dsimp only
        intro _ hfound' s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx21_1 hx20_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx29_1
        have hstep_pure := decodedMessageLoopTotal_step_found dec hpts hsort (rem := rem) (polys := polys) (out := out) rfl hb_lt hfound'
        refine SepWP.weaken_pre ?_
          (decodedMessage_pushTwoBytes_sepWP sp0 out_ptr (BitVec.ofNat 64 (2 * i)) i dec.ptsNeeded out
            ((dec.pts[i % 16]'hpoly_pts).vec[bsearchLoop (dec.pts[i % 16]'hpoly_pts).vec (BitVec.ofNat 16 (i / 16)) 0 (dec.pts[i % 16]'hpoly_pts).vec.length]'hb_lt).y.value
            hi_lt hneed_le hout_len s1
            (optPolyCacheListAt A (sp0 - 600#64) polys ∗
              ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
              ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
              ((sp0 - 608#64) ↦₆₄ 16#64) ∗
              ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
              sortedSetPtListPinAt A pts_base pins dec.pts ∗
              interpolateScratchAt sp0 ∗
              reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗
              stackAt (sp0 - 672#64) computeAtStack ∗ F)
            _ hpc1 hrun1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx29_1 ?_)
        · sep_frame
        intro s2 hpc2 hrun2 hsp2 htr2 hx20_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx29_2
        apply SepWP.done hpc2 hrun2
        cases rem with
        | zero =>
          have hi1_eq : i + 1 = dec.ptsNeeded := by omega
          simp only [hi1_eq, ↓reduceIte] at hpc2
          have hrem0 : dec.ptsNeeded - (i + 1) = 0 := by omega
          rw [hrem0, Nat.mul_zero, memRegion_zero]
          have hloop0 :
              decodedMessageLoopTotal dec (collectedSlices dec 0 16) i (0 + 1) polys out =
                (polys, out ++ u16ToBeBytes
                  ((dec.pts[i % 16]'hpoly_pts).vec[bsearchLoop (dec.pts[i % 16]'hpoly_pts).vec (BitVec.ofNat 16 (i / 16)) 0 (dec.pts[i % 16]'hpoly_pts).vec.length]'hb_lt).y.value) := by
            rw [hstep_pure]; rfl
          rw [hloop0] at hnext
          refine SepWPp.weaken_pre ?_
            (hnext s2 hpc2 hrun2 (by rw [hsp2, hsp1, hsp]) (by rw [htr2, htr1, htr]) hx29_2)
          rw [hi1_eq]
          sep_frame
        | succ rem' =>
          have hi1_ne : i + 1 ≠ dec.ptsNeeded := by omega
          simp only [hi1_ne, ↓reduceIte] at hpc2
          refine SepWPp.weaken_pre ?_
            (decodedMessageLoop_wpp_4k hb hA hcomp hcomp_at dec sp0 pts_base pts_vec_ptr out_ptr pins
              hsp0 hpts hpins hsort hneed_le hall_ge s0 F R Q
              rem' (i + 1) polys
              (out ++ u16ToBeBytes
                ((dec.pts[i % 16]'hpoly_pts).vec[bsearchLoop (dec.pts[i % 16]'hpoly_pts).vec (BitVec.ofNat 16 (i / 16)) 0 (dec.pts[i % 16]'hpoly_pts).vec.length]'hb_lt).y.value)
              s2 (by omega) hpolys_len (by simp [hout_len, u16ToBeBytes]; omega)
              hpc2 hrun2 (by rw [hsp2, hsp1, hsp]) (by rw [htr2, htr1, htr])
              (by rw [hx20_2, hx20_1]) hx22_2 hx23_2 hx24_2
              (by rw [hx25_2, hx25_1]) (by rw [hx26_2, hx26_1]) hx29_2
              (fun sf hpc_f hrun_f hsp_f htr_f hx29_f => ?_))
          · sep_frame
          · rw [← hstep_pure]
            exact hnext sf hpc_f hrun_f hsp_f htr_f hx29_f
      · dsimp only
        intro _ hfalse
        rw [hfound] at hfalse
        cases hfalse

end LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.MainLoopExt

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DropEpilogue
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.InterpolateFull
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.Proof
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DropEpiloguePlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.LoopPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.MainLoop
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.MainLoopPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.ProofPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangeComplete.Proof
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Proof
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMessageBridgePlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMsgCl1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlaced
import ProofLib.SepLogic.WPp

/-!
# `<PolyDecoder as Decoder>::decoded_message` (Block `418`, Part 2): Main Loop & Top-Level Proof

Completes the relocatable `[LibsignalPlacement]` proof of `<PolyDecoder as Decoder>::decoded_message`
(Block `418`) under `withLsCodeLoaded lsmpl` and `withLsCodeRoLoaded lsmpl`, discharging cross-block
calls to `computeAt` (Block `371`), `lagrangePrepare` (Block `372`), and `lagrangeComplete` (Block `373`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Poly.DecodedMessage

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Alloc CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Poly.AddChunk CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm
open CryptoVerification.SpqrV1.Poly.ComputeAt
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
  (lagrangePrepareName lagrangePrepare_fnOff LagrangePrepareArgs lagrangePrepareSpec
   lagrangePreparePlacedSpec lagrangePreparePure lagrangePreparePure_length
   lagrangePrepareStack lagrangePrepare_ok lagrangePrepare_placed_ok
   lagrangePrepare_placed_ok_of_hookSat polyOf_eq)
open CryptoVerification.SpqrV1.Poly.LagrangeComplete
open CryptoVerification.SpqrV1.GF.UnacceleratedMul CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.States.Leaves
  (sepWP_seq_lscl of_sepWP_lscl polyDecoderDecodedMessagePlacedSpec
   polyDecoderDecodedMessage_placed_cro_of_decodedMessage
   polyDecodedMessagePlacedOkX_of_decodedMessage)
open CryptoVerification.SpqrV1.States.RecvCt2Chunk (PolyDecodedMessagePlacedOkX)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  AddChunkNorm.sp_setPC_pre AddChunkNorm.sp_setMem_setPC_pre
  AddChunkNorm.readReg64_setPC_pre AddChunkNorm.readReg64_setMem_setPC_pre
  AddChunkNorm.readReg32_setPC_pre AddChunkNorm.readReg32_setMem_setPC_pre
  AddChunkNorm.readReg_setPC_pre AddChunkNorm.readReg_setMem_setPC_pre
  sp96_sub120 sp96_sub112 sp96_sub104
  bv64_and15_ofNat bv64_umaddl24_mod16
  bv64_ofNat_mul2_comm bv64_ofNat_one_add_mul2
  bv64_lsl1_norm_proof

/-! ## 1. Main Loop with `withLsCodeLoaded lsmpl` Callees -/

theorem decodedMessage_computeAtStep_cl_placed_wpp [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (hcomp_at : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 371) (withLsCodeLoaded lsmpl (computeAtPlacedSpec A)))
    (sp0 slot : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (i ptsNeeded : Nat) (p : Poly)
    (hi_lt : i < ptsNeeded) (hneed_le : ptsNeeded ≤ 16 * 65536)
    (s0 s : State) (F R : SepProp) (Q : State → SepProp → Prop)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_418).base + 1284#64)
    (hstat : s.status = .Running)
    (hsp : s.sp = sp0 - 672#64)
    (htr : traceVRegs s = traceVRegs s0)
    (hx19 : s.readReg64 .x19 = slot)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 i)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ sf : State,
      sf.pc = (blkPl_418).base + 1328#64 →
      sf.status = .Running →
      sf.sp = sp0 - 672#64 →
      traceVRegs sf = traceVRegs s0 →
      BitVec.truncate 8 (sf.readReg64 .x19) =
        BitVec.truncate 8 ((computeAtPure p (GF16.new (BitVec.ofNat 16 (i / 16)))).value >>> 8) →
      BitVec.truncate 8 (sf.readReg64 .x21) =
        BitVec.truncate 8 (computeAtPure p (GF16.new (BitVec.ofNat 16 (i / 16)))).value →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x22 = BitVec.ofNat 64 i →
      sf.readReg64 .x23 = BitVec.ofNat 64 (2 * i) →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x29 = sp0 - 96#64 →
      SepWPp ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc sf
        (optPolyCacheSlotAt A slot (some p) ∗
          ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
          ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
          reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗
          stackAt (sp0 - 672#64) computeAtStack ∗ F)
        Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) :
    SepWPp ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc s
      (optPolyCacheSlotAt A slot (some p) ∗
        ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
        ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
        reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗
        stackAt (sp0 - 672#64) computeAtStack ∗ F)
      Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  rcases Prod.mk.inj htr with ⟨htr_tr, htr_vr⟩
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc hnext ⊢
  have hslot16 : slot + 8#64 + 8#64 = slot + 16#64 := by bv_omega
  have h2i_ne : (BitVec.ofNat 64 (2 * i) != BitVec.ofNat 64 (2 * ptsNeeded)) = true := by
    rw [bv64_bne_ofNat (by omega) (by omega), decide_eq_true_eq]; omega
  unfold optPolyCacheSlotAt
  rw [sepExists_sepConj_left]; apply SepWPp.exists_elim; intro ptr_p
  refine SepWPp.pure_elim_focus (1 ≤ p.coefficients.length ∧ p.coefficients.length ≤ 65536 ∧ ptr_p ≠ 0#64)
    (fun ⟨hp_ge1, hp_le, hptr_p_ne⟩ => ?_) (by sep_focus)
  apply of_sepWP_lscl hcl (mid := lsmpl.base 371)
  wp_steps 3
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hstat])
  intro hcl1
  let a : ComputeAtArgs := {
    p_coeffs := ptr_p
    poly := p
    x := GF16.new (BitVec.ofNat 16 (i / 16))
  }
  refine SepWPp.call (x := a) (ret_pc := (blkPl_418).base + 1296#64)
    (F := (slot ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
      ((slot + 8#64) ↦₆₄ ptr_p) ∗
      ((slot + 16#64) ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
      A.live ptr_p (2 * p.coefficients.length) 2 ∗
      ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
      ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗ F)
    hcomp_at
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, hstat])
    (by
      unfold State.spAligned
      simp only [wp_norm, arm64_norm, hsp, sp672_aligned sp0 hsp0])
    (by simp [wp_norm, arm64_norm])
    (fun R' hm => ?_)
    (fun sf code R' _ hex => ?_)
    (fun sf _ hm => ?_)
    (fun sf_c hpc_c hrun_c hsp_c hcs_c => ?_)
  · dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl1, ?_⟩
    have hx2_trunc :
        BitVec.truncate 16 ((BitVec.ofNat 64 i) >>> 4) =
          (GF16.new (BitVec.ofNat 16 (i / 16))).value :=
      bv64_lsr4_truncate16_ofNat (by omega)
    simp only [computeAtPlacedSpec, a, wp_norm, arm64_norm, hsp, hslot16] at hm ⊢
    exact ⟨⟨hx2_trunc, by omega⟩, Satisfies.mono (Entails.of_eq (by ac_rfl)) hm⟩
  · simp only [withLsCodeLoaded, computeAtPlacedSpec] at hex
    exact not_satisfies_false_sepConj hex
  · simp only [withLsCodeLoaded, computeAtPlacedSpec] at hm
    exact allowPanic_frame (fun ⟨hal, hpre⟩ => by
      simp only [allocFailedIn, wp_norm, arm64_norm, htr_tr] at hal hpre ⊢
      exact ⟨hal, hpre⟩) hm
  · conv => arg 4; simp only [withLsCodeLoaded, computeAtPlacedSpec, a, wp_norm, arm64_norm, htr_tr, hsp]
    rcases hcs_c with ⟨_, hx20_c, _, hx22_c, _, hx24_c, hx25_c, hx26_c, _, _, hx29_c, hvregs_c⟩
    refine SepWPp.pure_elim_focus (sf_c.trace = s0.trace ∧
      BitVec.truncate 16 (sf_c.readReg64 .x0) = (computeAtPure p (GF16.new (BitVec.ofNat 16 (i / 16)))).value)
      (fun ⟨htr_c, hx0_c⟩ => ?_) (by sep_focus)
    have hsp_c' : sf_c.sp = sp0 - 672#64 := by simpa [wp_norm, arm64_norm, hsp] using hsp_c
    have hx20_c' : sf_c.readReg64 .x20 = s.readReg64 .x20 := by simpa [wp_norm, arm64_norm] using hx20_c
    have hx22_c' : sf_c.readReg64 .x22 = BitVec.ofNat 64 i := by simpa [wp_norm, arm64_norm, hx22] using hx22_c
    have hx24_c' : sf_c.readReg64 .x24 = s.readReg64 .x24 := by simpa [wp_norm, arm64_norm] using hx24_c
    have hx25_c' : sf_c.readReg64 .x25 = s.readReg64 .x25 := by simpa [wp_norm, arm64_norm] using hx25_c
    have hx26_c' : sf_c.readReg64 .x26 = s.readReg64 .x26 := by simpa [wp_norm, arm64_norm] using hx26_c
    have hx29_c' : sf_c.readReg64 .x29 = sp0 - 96#64 := by simpa [wp_norm, arm64_norm, hx29] using hx29_c
    apply SepWPp.of_sepWP (mid := (blkPl_418).base + 1328#64)
    wp_steps 6
    refine SepWP.weaken_pre
      (show _ ⊢
        optPolyCacheSlotAt A slot (some p) ∗
          ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
          ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
          reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗
          stackAt (sp0 - 672#64) computeAtStack ∗ F by
        unfold optPolyCacheSlotAt
        rw [show gf16SliceAt ptr_p p.coefficients ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗
              stackAt (sp0 - 672#64) computeAtStack ∗
              ((slot ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
                ((slot + 8#64) ↦₆₄ ptr_p) ∗
                ((slot + 16#64) ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
                A.live ptr_p (2 * p.coefficients.length) 2 ∗
                ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
                ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗ F) =
            ((slot ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
              ((slot + 8#64) ↦₆₄ ptr_p) ∗
              ((slot + 16#64) ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
              A.live ptr_p (2 * p.coefficients.length) 2 ∗
              gf16SliceAt ptr_p p.coefficients) ∗
              (((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
                ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
                reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗
                stackAt (sp0 - 672#64) computeAtStack ∗ F) by ac_rfl]
        refine sepConj_mono_left ?_
        exact Entails.sepExists_right ptr_p
          (Entails.pure_right ⟨hp_ge1, hp_le, hptr_p_ne⟩ (Entails.of_eq (by ac_rfl)))) ?_
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_c])
    apply hnext
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm, hrun_c]
    · simp [wp_norm, arm64_norm, hsp_c']
    · simp [traceVRegs, wp_norm, arm64_norm, htr_c, hvregs_c, htr_vr]
    · simp only [wp_norm, arm64_norm]
      exact bv64_ubfx_8_8_truncate8 hx0_c
    · simp only [wp_norm, arm64_norm]
      exact bv64_orr_w0_truncate8 hx0_c
    · simp [wp_norm, arm64_norm, hx20_c']
    · simp [wp_norm, arm64_norm, hx22_c']
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm, hx24_c']
    · simp [wp_norm, arm64_norm, hx25_c']
    · simp [wp_norm, arm64_norm, hx26_c']
    · simp [wp_norm, arm64_norm, hx29_c']

theorem decodedMessageLoop_cl_placed_wpp [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionSpec)
    (hprep : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 372) (withLsCodeLoaded lsmpl (lagrangePreparePlacedSpec A)))
    (hcomp : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 373) (withLsCodeLoaded lsmpl lagrangeCompletePlacedSpec))
    (hcomp_at : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 371) (withLsCodeLoaded lsmpl (computeAtPlacedSpec A)))
    (dec : PolyDecoder) (sp0 pts_base pts_vec_ptr out_ptr : BitVec 64)
    (pins : List VecPin)
    (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (hpts : dec.pts.length = 16) (hpins : pins.length = 16)
    (hsort : PolyDecoderStrictSorted dec)
    (hneed_le : dec.ptsNeeded ≤ 16 * 65536)
    (hall_ge : ∀ k (hk : k < 16), dec.necessaryPoints k ≤ (dec.pts[k]'(by omega)).vec.length)
    (s0 : State) (F R : SepProp) (Q : State → SepProp → Prop) :
    ∀ (rem i : Nat) (polys : List (Option Poly)) (out : List (BitVec 8)) (s : State),
      i + (rem + 1) = dec.ptsNeeded → polys.length = 16 → out.length = 2 * i →
      LibsignalCodeLoaded lsmpl s.mem → s.pc = (blkPl_418).base + 548#64 → s.status = .Running →
      s.sp = sp0 - 672#64 → traceVRegs s = traceVRegs s0 →
      s.readReg64 .x20 = pts_base → s.readReg64 .x22 = BitVec.ofNat 64 i →
      s.readReg64 .x23 = BitVec.ofNat 64 (2 * i) → s.readReg64 .x24 = BitVec.ofNat 64 dec.ptsNeeded →
      s.readReg64 .x25 = 24#64 → s.readReg64 .x26 = sp0 - 600#64 → s.readReg64 .x29 = sp0 - 96#64 →
      (∀ sf : State, sf.pc = (blkPl_418).base + 1404#64 → sf.status = .Running →
        sf.sp = sp0 - 672#64 → traceVRegs sf = traceVRegs s0 → sf.readReg64 .x29 = sp0 - 96#64 →
        let (polysFinal, outFinal) :=
          decodedMessageLoopTotal dec (collectedSlices dec 0 16) i (rem + 1) polys out
        SepWPp ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc sf
          (optPolyCacheListAt A (sp0 - 600#64) polysFinal ∗
            ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗ ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
            ((sp0 - 608#64) ↦₆₄ 16#64) ∗ ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
            ((sp0 - 208#64) ↦₆₄ out_ptr) ∗ ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
            ptSliceRefListAt dec 0 pts_vec_ptr pins ∗ sortedSetPtListPinAt A pts_base pins dec.pts ∗
            (out_ptr ↦ₛ outFinal) ∗ interpolateScratchAt sp0 ∗
            reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗ stackAt (sp0 - 672#64) computeAtStack ∗ F)
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) →
      SepWPp ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc s
        (optPolyCacheListAt A (sp0 - 600#64) polys ∗
          ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗ ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
          ((sp0 - 608#64) ↦₆₄ 16#64) ∗ ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
          ((sp0 - 208#64) ↦₆₄ out_ptr) ∗ ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
          ptSliceRefListAt dec 0 pts_vec_ptr pins ∗ sortedSetPtListPinAt A pts_base pins dec.pts ∗
          (out_ptr ↦ₛ out) ∗ memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (dec.ptsNeeded - i)) ∗
          interpolateScratchAt sp0 ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗
          stackAt (sp0 - 672#64) computeAtStack ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))
  | rem, i, polys, out, s, hsum, hpolys_len, hout_len,
      hcl, hpc, hstat, hsp, htr, hx20, hx22, hx23, hx24, hx25, hx26, hx29, hnext => by
    have hi_lt : i < dec.ptsNeeded := by omega
    have hpoly_lt : i % 16 < 16 := Nat.mod_lt i (by decide)
    have hpoly_pts : i % 16 < dec.pts.length := by omega
    have hpoly_pins : i % 16 < pins.length := by omega
    have hpoly_p : i % 16 < polys.length := by omega
    have hnec_pos : 1 ≤ dec.necessaryPoints (i % 16) := necessaryPoints_pos_of_lt dec hi_lt
    have hnec_le_len : dec.necessaryPoints (i % 16) ≤ (dec.pts[i % 16]'hpoly_pts).vec.length := hall_ge (i % 16) hpoly_lt
    have hle_len : (dec.pts[i % 16]'hpoly_pts).vec.length ≤ 65536 := polyDecoderStrictSorted_elem_length_le hsort hpoly_pts
    have hge_len : 1 ≤ (dec.pts[i % 16]'hpoly_pts).vec.length := by omega
    have ⟨_, hb_lt0⟩ := bsearchLoop_bounds (dec.pts[i % 16]'hpoly_pts).vec
      (BitVec.ofNat 16 (i / 16)) 0 (dec.pts[i % 16]'hpoly_pts).vec.length hge_len (by omega)
    have hb_lt : bsearchLoop (dec.pts[i % 16]'hpoly_pts).vec (BitVec.ofNat 16 (i / 16)) 0
        (dec.pts[i % 16]'hpoly_pts).vec.length < (dec.pts[i % 16]'hpoly_pts).vec.length := by omega
    cases hfound : ((dec.pts[i % 16]'hpoly_pts).vec[bsearchLoop (dec.pts[i % 16]'hpoly_pts).vec (BitVec.ofNat 16 (i / 16)) 0 (dec.pts[i % 16]'hpoly_pts).vec.length]'hb_lt).x.value == BitVec.ofNat 16 (i / 16)
    ·
      apply of_sepWP_lscl hcl (mid := (blkPl_418).base + 660#64)
      refine SepWP.weaken_pre ?_
        (decodedMessage_bsearchStep_placed_sepWP (ext := ext) (A := A) dec sp0 pts_base pins i hpts hpins hi_lt hneed_le hge_len hle_len
          s (optPolyCacheListAt A (sp0 - 600#64) polys ∗ ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
            ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗ ((sp0 - 608#64) ↦₆₄ 16#64) ∗ ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
            ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗ ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
            (out_ptr ↦ₛ out) ∗ memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (dec.ptsNeeded - i)) ∗
            interpolateScratchAt sp0 ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗
            stackAt (sp0 - 672#64) computeAtStack ∗ F)
          _ hpc hstat hx20 hx22 hx23 hx24 hx25 hx26 hx29 ?_ ?_)
      · exact Entails.of_eq (by ac_rfl)
      · dsimp only; intro _ htrue; rw [hfound] at htrue; cases htrue
      · dsimp only
        intro _ hnot_found s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx20_1 hx22_1 hx24_1 hx25_1 hx26_1 hx29_1
        apply SepWP.done hpc1 hrun1
        intro hcl1
        have hstep_pure := decodedMessageLoopTotal_step_not_found dec hpts hsort hpolys_len (rem := rem) (out := out) rfl hb_lt hnot_found
        let ptsSlice := (dec.pts[i % 16]'hpoly_pts).vec.take (dec.necessaryPoints (i % 16))
        let pInterp := (polys[i % 16]'hpoly_p).getD (lagrangeInterpolateTotal ptsSlice)
        let yInterp := computeAtPure pInterp (GF16.new (BitVec.ofNat 16 (i / 16)))
        have hslice_len : ptsSlice.length = dec.necessaryPoints (i % 16) := List.length_take_of_le hnec_le_len
        have hk_pos : 1 ≤ ptsSlice.length := by rw [hslice_len]; exact hnec_pos
        have hk_le : ptsSlice.length ≤ 65536 := by rw [hslice_len]; omega
        have hfocus_pre :
            sortedSetPtListPinAt A pts_base pins dec.pts ∗
              ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
              (optPolyCacheListAt A (sp0 - 600#64) polys ∗
                ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗ ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
                ((sp0 - 608#64) ↦₆₄ 16#64) ∗ ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
                ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗ ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
                (out_ptr ↦ₛ out) ∗ memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (dec.ptsNeeded - i)) ∗
                interpolateScratchAt sp0 ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗
                stackAt (sp0 - 672#64) computeAtStack ∗ F) =
            optPolyCacheSlotAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16))) (polys[i % 16]'hpoly_p) ∗
              ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗ ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
              ((sp0 - 608#64) ↦₆₄ 16#64) ∗
              ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * (i % 16))) (pins[i % 16]'hpoly_pins).ptr ptsSlice.length ∗
              ptSliceAt (pins[i % 16]'hpoly_pins).ptr ptsSlice ∗ interpolateScratchAt sp0 ∗
              reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗ stackAt (sp0 - 672#64) lagrangePrepareStack ∗
              (optPolyCacheListAt A (sp0 - 600#64) (polys.take (i % 16)) ∗
                optPolyCacheListAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16 + 1))) (polys.drop (i % 16 + 1)) ∗
                ptSliceRefListAt dec 0 pts_vec_ptr (pins.take (i % 16)) ∗
                ptSliceRefListAt dec (i % 16 + 1) (pts_vec_ptr + BitVec.ofNat 64 (16 * (i % 16 + 1))) (pins.drop (i % 16 + 1)) ∗
                sortedSetPtListPinAt A pts_base (pins.take (i % 16)) (dec.pts.take (i % 16)) ∗
                ((pts_base + BitVec.ofNat 64 (24 * (i % 16))) ↦₆₄ (pins[i % 16]'hpoly_pins).cap) ∗
                ((pts_base + BitVec.ofNat 64 (24 * (i % 16)) + 8#64) ↦₆₄ (pins[i % 16]'hpoly_pins).ptr) ∗
                ((pts_base + BitVec.ofNat 64 (24 * (i % 16)) + 16#64) ↦₆₄ BitVec.ofNat 64 (dec.pts[i % 16]'hpoly_pts).vec.length) ∗
                ptSliceAt ((pins[i % 16]'hpoly_pins).ptr + BitVec.ofNat 64 (4 * dec.necessaryPoints (i % 16)))
                  ((dec.pts[i % 16]'hpoly_pts).vec.drop (dec.necessaryPoints (i % 16))) ∗
                sortedSetPtPinRest A (pins[i % 16]'hpoly_pins) (dec.pts[i % 16]'hpoly_pts) ∗
                sortedSetPtListPinAt A (pts_base + BitVec.ofNat 64 (24 * (i % 16 + 1))) (pins.drop (i % 16 + 1)) (dec.pts.drop (i % 16 + 1)) ∗
                ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗ ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
                ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗ (out_ptr ↦ₛ out) ∗
                memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (dec.ptsNeeded - i)) ∗
                memRegion ((sp0 - 672#64) - 4352#64) 48 ∗ F) := by
          rw [optPolyCacheListAt_focus A polys (i % 16) (sp0 - 600#64) hpoly_p,
            ptSliceRefListAt_focus dec pins (i % 16) pts_vec_ptr hpoly_pins,
            sortedSetPtListPinAt_focus A pins dec.pts (i % 16) pts_base (by rw [hpins, hpts]) hpoly_pts,
            sortedSetPtPinAt_eq_slice A (pins[i % 16]'hpoly_pins) (dec.pts[i % 16]'hpoly_pts) (pts_base + BitVec.ofNat 64 (24 * (i % 16))),
            ptSliceAt_split_take_drop (dec.pts[i % 16]'hpoly_pts).vec (dec.necessaryPoints (i % 16)) (pins[i % 16]'hpoly_pins).ptr hnec_le_len,
            stackAt_computeAt_eq_prepare (sp0 - 672#64), hslice_len]
          ac_rfl
        apply sepWPp_seq_lscl hcl1 (mid := (blkPl_418).base + 1284#64)
        refine SepWPp.weaken_pre (Entails.of_eq hfocus_pre)
          (lagrangeInterpolate_inlined_cl_placed_wpp h_panic hshim_sat halloc_sat hdealloc_sat hmemcpy_sat hprep hcomp
            sp0 pts_vec_ptr (pins[i % 16]'hpoly_pins).ptr (BitVec.ofNat 64 dec.ptsNeeded) hsp0 (i % 16) (polys[i % 16]'hpoly_p) ptsSlice
            hpoly_lt hk_pos hk_le s0 s1 _ R _
            hcl1 hpc1 hrun1 (by rw [hsp1, hsp]) (by rw [htr1, htr]) hx0_1 hx24_1 hx25_1 hx26_1 hx29_1 ?_)
        intro s2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx22_2 hx24_2 hx25_2 hx26_2 hx29_2
        apply SepWPp.done hpc2 hrun2
        intro hcl2
        have hreasm_mid :
            optPolyCacheSlotAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16))) (some pInterp) ∗
              ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗ ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
              ((sp0 - 608#64) ↦₆₄ 16#64) ∗
              ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * (i % 16))) (pins[i % 16]'hpoly_pins).ptr ptsSlice.length ∗
              ptSliceAt (pins[i % 16]'hpoly_pins).ptr ptsSlice ∗ interpolateScratchAt sp0 ∗
              reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗ stackAt (sp0 - 672#64) lagrangePrepareStack ∗
              (optPolyCacheListAt A (sp0 - 600#64) (polys.take (i % 16)) ∗
                optPolyCacheListAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16 + 1))) (polys.drop (i % 16 + 1)) ∗
                ptSliceRefListAt dec 0 pts_vec_ptr (pins.take (i % 16)) ∗
                ptSliceRefListAt dec (i % 16 + 1) (pts_vec_ptr + BitVec.ofNat 64 (16 * (i % 16 + 1))) (pins.drop (i % 16 + 1)) ∗
                sortedSetPtListPinAt A pts_base (pins.take (i % 16)) (dec.pts.take (i % 16)) ∗
                ((pts_base + BitVec.ofNat 64 (24 * (i % 16))) ↦₆₄ (pins[i % 16]'hpoly_pins).cap) ∗
                ((pts_base + BitVec.ofNat 64 (24 * (i % 16)) + 8#64) ↦₆₄ (pins[i % 16]'hpoly_pins).ptr) ∗
                ((pts_base + BitVec.ofNat 64 (24 * (i % 16)) + 16#64) ↦₆₄ BitVec.ofNat 64 (dec.pts[i % 16]'hpoly_pts).vec.length) ∗
                ptSliceAt ((pins[i % 16]'hpoly_pins).ptr + BitVec.ofNat 64 (4 * dec.necessaryPoints (i % 16)))
                  ((dec.pts[i % 16]'hpoly_pts).vec.drop (dec.necessaryPoints (i % 16))) ∗
                sortedSetPtPinRest A (pins[i % 16]'hpoly_pins) (dec.pts[i % 16]'hpoly_pts) ∗
                sortedSetPtListPinAt A (pts_base + BitVec.ofNat 64 (24 * (i % 16 + 1))) (pins.drop (i % 16 + 1)) (dec.pts.drop (i % 16 + 1)) ∗
                ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗ ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
                ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗ (out_ptr ↦ₛ out) ∗
                memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (dec.ptsNeeded - i)) ∗
                memRegion ((sp0 - 672#64) - 4352#64) 48 ∗ F) =
            optPolyCacheSlotAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16))) (some pInterp) ∗
              ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗ ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
              reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗ stackAt (sp0 - 672#64) computeAtStack ∗
              (optPolyCacheListAt A (sp0 - 600#64) (polys.take (i % 16)) ∗
                optPolyCacheListAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16 + 1))) (polys.drop (i % 16 + 1)) ∗
                ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗ ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
                ((sp0 - 608#64) ↦₆₄ 16#64) ∗ ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
                ptSliceRefListAt dec 0 pts_vec_ptr pins ∗ sortedSetPtListPinAt A pts_base pins dec.pts ∗
                (out_ptr ↦ₛ out) ∗ memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (dec.ptsNeeded - i)) ∗
                interpolateScratchAt sp0 ∗ F) := by
          rw [ptSliceRefListAt_focus dec pins (i % 16) pts_vec_ptr hpoly_pins,
            sortedSetPtListPinAt_focus A pins dec.pts (i % 16) pts_base (by rw [hpins, hpts]) hpoly_pts,
            sortedSetPtPinAt_eq_slice A (pins[i % 16]'hpoly_pins) (dec.pts[i % 16]'hpoly_pts) (pts_base + BitVec.ofNat 64 (24 * (i % 16))),
            ptSliceAt_split_take_drop (dec.pts[i % 16]'hpoly_pts).vec (dec.necessaryPoints (i % 16)) (pins[i % 16]'hpoly_pins).ptr hnec_le_len,
            stackAt_computeAt_eq_prepare (sp0 - 672#64), hslice_len]
          ac_rfl
        apply sepWPp_seq_lscl hcl2 (mid := (blkPl_418).base + 1328#64)
        refine SepWPp.weaken_pre (Entails.of_eq hreasm_mid)
          (decodedMessage_computeAtStep_cl_placed_wpp hcomp_at sp0
            ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16))) hsp0 i dec.ptsNeeded pInterp
            hi_lt hneed_le s0 s2 _ R _ hcl2 hpc2 hrun2 hsp2 htr2 hx19_2 (by rw [hx22_2, hx22_1]) hx29_2 ?_)
        intro s3 hpc3 hrun3 hsp3 htr3 hx19_3 hx21_3 hx20_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx29_3
        apply SepWPp.done hpc3 hrun3
        intro hcl3
        apply of_sepWP_lscl hcl3 (mid := if i + 1 = dec.ptsNeeded then (blkPl_418).base + 1404#64 else (blkPl_418).base + 548#64)
        have hset_polys :
            optPolyCacheListAt A (sp0 - 600#64) (polys.take (i % 16)) ∗
              optPolyCacheSlotAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16))) (some pInterp) ∗
              optPolyCacheListAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16 + 1))) (polys.drop (i % 16 + 1)) =
            optPolyCacheListAt A (sp0 - 600#64) (polys.set (i % 16) (some pInterp)) :=
          (optPolyCacheListAt_set A polys (i % 16) (some pInterp) (sp0 - 600#64) hpoly_p).symm
        refine SepWP.weaken_pre ?_
          (decodedMessage_pushTwoBytes_placed_sepWP (ext := ext) sp0 out_ptr (BitVec.ofNat 64 (2 * i)) i dec.ptsNeeded out
            yInterp.value hi_lt hneed_le hout_len s3
            (optPolyCacheListAt A (sp0 - 600#64) (polys.set (i % 16) (some pInterp)) ∗
              ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗ ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
              ((sp0 - 608#64) ↦₆₄ 16#64) ∗ ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
              sortedSetPtListPinAt A pts_base pins dec.pts ∗ interpolateScratchAt sp0 ∗
              reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗ stackAt (sp0 - 672#64) computeAtStack ∗ F)
            _ hpc3 hrun3 hx19_3 hx21_3 hx22_3 hx23_3 (by rw [hx24_3, hx24_2]) hx29_3 ?_)
        · rw [← hset_polys]; exact Entails.of_eq (by ac_rfl)
        intro s4 hpc4 hrun4 hsp4 htr4 hx20_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx29_4
        apply SepWP.done hpc4 hrun4
        intro hcl4
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
          refine SepWPp.weaken_pre ?_ (hnext s4 hpc4 hrun4 (by rw [hsp4, hsp3]) (by rw [htr4, htr3]) hx29_4)
          rw [hi1_eq]; exact Entails.of_eq (by ac_rfl)
        | succ rem' =>
          have hi1_ne : i + 1 ≠ dec.ptsNeeded := by omega
          simp only [hi1_ne, ↓reduceIte] at hpc4
          refine SepWPp.weaken_pre ?_
            (decodedMessageLoop_cl_placed_wpp h_panic hshim_sat halloc_sat hdealloc_sat hmemcpy_sat hprep hcomp hcomp_at
              dec sp0 pts_base pts_vec_ptr out_ptr pins hsp0 hpts hpins hsort hneed_le hall_ge s0 F R Q
              rem' (i + 1) (polys.set (i % 16) (some pInterp)) (out ++ u16ToBeBytes yInterp.value)
              s4 (by omega) (by simp [hpolys_len]) (by simp [hout_len, u16ToBeBytes]; omega)
              hcl4 hpc4 hrun4 (by rw [hsp4, hsp3]) (by rw [htr4, htr3])
              (by rw [hx20_4, hx20_3, hx20_2, hx20_1]) hx22_4 hx23_4 hx24_4
              (by rw [hx25_4, hx25_3, hx25_2]) (by rw [hx26_4, hx26_3, hx26_2]) hx29_4
              (fun sf hpc_f hrun_f hsp_f htr_f hx29_f => ?_))
          · exact Entails.of_eq (by ac_rfl)
          · rw [← hstep_pure]; exact hnext sf hpc_f hrun_f hsp_f htr_f hx29_f
    ·
      apply of_sepWP_lscl hcl (mid := if i + 1 = dec.ptsNeeded then (blkPl_418).base + 1404#64 else (blkPl_418).base + 548#64)
      refine SepWP.weaken_pre ?_
        (decodedMessage_bsearchStep_placed_sepWP (ext := ext) (A := A) dec sp0 pts_base pins i hpts hpins hi_lt hneed_le hge_len hle_len
          s (optPolyCacheListAt A (sp0 - 600#64) polys ∗ ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
            ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗ ((sp0 - 608#64) ↦₆₄ 16#64) ∗ ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
            ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗ ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
            (out_ptr ↦ₛ out) ∗ memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (dec.ptsNeeded - i)) ∗
            interpolateScratchAt sp0 ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗
            stackAt (sp0 - 672#64) computeAtStack ∗ F)
          _ hpc hstat hx20 hx22 hx23 hx24 hx25 hx26 hx29 ?_ ?_)
      · exact Entails.of_eq (by ac_rfl)
      · dsimp only
        intro _ hfound' s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx21_1 hx20_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx29_1
        have hstep_pure := decodedMessageLoopTotal_step_found dec hpts hsort (rem := rem) (polys := polys) (out := out) rfl hb_lt hfound'
        refine SepWP.weaken_pre ?_
          (decodedMessage_pushTwoBytes_placed_sepWP (ext := ext) sp0 out_ptr (BitVec.ofNat 64 (2 * i)) i dec.ptsNeeded out
            ((dec.pts[i % 16]'hpoly_pts).vec[bsearchLoop (dec.pts[i % 16]'hpoly_pts).vec (BitVec.ofNat 16 (i / 16)) 0 (dec.pts[i % 16]'hpoly_pts).vec.length]'hb_lt).y.value
            hi_lt hneed_le hout_len s1
            (optPolyCacheListAt A (sp0 - 600#64) polys ∗ ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
              ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗ ((sp0 - 608#64) ↦₆₄ 16#64) ∗ ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
              sortedSetPtListPinAt A pts_base pins dec.pts ∗ interpolateScratchAt sp0 ∗
              reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗ stackAt (sp0 - 672#64) computeAtStack ∗ F)
            _ hpc1 hrun1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx29_1 ?_)
        · exact Entails.of_eq (by ac_rfl)
        intro s2 hpc2 hrun2 hsp2 htr2 hx20_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx29_2
        apply SepWP.done hpc2 hrun2
        intro hcl2
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
          refine SepWPp.weaken_pre ?_ (hnext s2 hpc2 hrun2 (by rw [hsp2, hsp1, hsp]) (by rw [htr2, htr1, htr]) hx29_2)
          rw [hi1_eq]; exact Entails.of_eq (by ac_rfl)
        | succ rem' =>
          have hi1_ne : i + 1 ≠ dec.ptsNeeded := by omega
          simp only [hi1_ne, ↓reduceIte] at hpc2
          refine SepWPp.weaken_pre ?_
            (decodedMessageLoop_cl_placed_wpp h_panic hshim_sat halloc_sat hdealloc_sat hmemcpy_sat hprep hcomp hcomp_at
              dec sp0 pts_base pts_vec_ptr out_ptr pins hsp0 hpts hpins hsort hneed_le hall_ge s0 F R Q
              rem' (i + 1) polys
              (out ++ u16ToBeBytes
                ((dec.pts[i % 16]'hpoly_pts).vec[bsearchLoop (dec.pts[i % 16]'hpoly_pts).vec (BitVec.ofNat 16 (i / 16)) 0 (dec.pts[i % 16]'hpoly_pts).vec.length]'hb_lt).y.value)
              s2 (by omega) hpolys_len (by simp [hout_len, u16ToBeBytes]; omega)
              hcl2 hpc2 hrun2 (by rw [hsp2, hsp1, hsp]) (by rw [htr2, htr1, htr])
              (by rw [hx20_2, hx20_1]) hx22_2 hx23_2 hx24_2
              (by rw [hx25_2, hx25_1]) (by rw [hx26_2, hx26_1]) hx29_2
              (fun sf hpc_f hrun_f hsp_f htr_f hx29_f => ?_))
          · exact Entails.of_eq (by ac_rfl)
          · rw [← hstep_pure]; exact hnext sf hpc_f hrun_f hsp_f htr_f hx29_f
      · dsimp only; intro _ hfalse; rw [hfound] at hfalse; cases hfalse

/-! ## 2. Post-`collectPointsVecs` Execution with `withLsCodeLoaded lsmpl` Callees -/

theorem decodedMessage_afterCollect_cl_placed_wpp [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionSpec)
    (hprep : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 372) (withLsCodeLoaded lsmpl (lagrangePreparePlacedSpec A)))
    (hcomp_ok : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 373) (withLsCodeLoaded lsmpl lagrangeCompletePlacedSpec))
    (hcomp_at : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 371) (withLsCodeLoaded lsmpl (computeAtPlacedSpec A)))
    (dec : PolyDecoder) (decA out_sret pv_ptr : BitVec 64) (pins : List VecPin)
    (hcomp_false : dec.isComplete = false) (hpts : dec.pts.length = 16) (hpins : pins.length = 16)
    (hsort : PolyDecoderStrictSorted dec) (hret : (collectPointsVecsTotal dec 0 16 false []).1 = false)
    (s0 s : State) (F R : SepProp) (Q : State → SepProp → Prop)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (hpc : s.pc = (blkPl_418).base + 352#64)
    (hstat : s.status = .Running) (hsp : s.sp = s0.sp - 672#64) (htr : traceVRegs s = traceVRegs s0)
    (hx20 : s.readReg64 .x20 = decA) (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .x30 → sf.status = .Running → sf.sp = s0.sp →
      traceVRegs sf = traceVRegs s0 → CalleeSavedGprsPreserved s0 sf →
      SepWPp ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) (s0.readReg64 .x30) sf
        (optVecU8Of A out_sret (decodedMessageTotal dec) ∗ sortedSetPtListPinAt A decA pins dec.pts ∗
          reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗ stackAt s0.sp decodedMessageStack ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) :
    SepWPp ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (savedRegsAt s0.sp s0 ∗ ((s0.sp - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
        ((s0.sp - 632#64) ↦₆₄ out_sret) ∗ ((s0.sp - 624#64) ↦₆₄ 16#64) ∗
        ((s0.sp - 616#64) ↦₆₄ pv_ptr) ∗ ((s0.sp - 608#64) ↦₆₄ 16#64) ∗
        memRegion (s0.sp - 600#64) 384 ∗ memRegion (s0.sp - 216#64) 24 ∗
        interpolateScratchAt s0.sp ∗ memRegion (s0.sp - 672#64) 8 ∗ memRegion (s0.sp - 120#64) 24 ∗
        memRegion out_sret vecHeaderBytes ∗ A.live pv_ptr 256 8 ∗
        ptSliceRefListAt dec 0 pv_ptr pins ∗ sortedSetPtListPinAt A decA pins dec.pts ∗
        reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗ stackAt (s0.sp - 672#64) extHookStack ∗ F) Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  have ⟨hall_ge, hneed_le⟩ := collectPointsVecs_false_bounds dec hpts hsort hret
  apply of_sepWP_lscl hcl (mid := (blkPl_418).base + 424#64)
  refine SepWP.weaken_pre
    (show _ ⊢
      ((s0.sp - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗ memRegion (s0.sp - 600#64) 384 ∗
        (savedRegsAt s0.sp s0 ∗ ((s0.sp - 632#64) ↦₆₄ out_sret) ∗ ((s0.sp - 624#64) ↦₆₄ 16#64) ∗
          ((s0.sp - 616#64) ↦₆₄ pv_ptr) ∗ ((s0.sp - 608#64) ↦₆₄ 16#64) ∗
          memRegion (s0.sp - 216#64) 24 ∗ interpolateScratchAt s0.sp ∗
          memRegion (s0.sp - 672#64) 8 ∗ memRegion (s0.sp - 120#64) 24 ∗
          memRegion out_sret vecHeaderBytes ∗ A.live pv_ptr 256 8 ∗
          ptSliceRefListAt dec 0 pv_ptr pins ∗ sortedSetPtListPinAt A decA pins dec.pts ∗
          reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗ stackAt (s0.sp - 672#64) extHookStack ∗ F) by exact Entails.of_eq (by ac_rfl))
    (initOptPolyCache_placed_sepWP (ext := ext) (A := A) s0.sp (BitVec.ofNat 64 dec.ptsNeeded) hsp0 s _ _
      hpc hstat hsp (fun s1 hpc1 hrun1 hsp1 htr1 hx20_1 hx24_1 hx29_1 => ?_))
  apply SepWP.done hpc1 hrun1
  intro hcl1
  by_cases hneed0 : dec.ptsNeeded = 0
  · have hx24_0 : s1.readReg64 .x24 = 0#64 := by rw [hx24_1, hneed0]
    apply SepWPp.of_sepWP (mid := s0.readReg64 .x30)
    refine SepWP.weaken_pre
      (show _ ⊢
        memRegion (s0.sp - 216#64) 24 ∗
          (((s0.sp - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
            optPolyCacheListAt A (s0.sp - 600#64) (List.replicate 16 none) ∗
            savedRegsAt s0.sp s0 ∗ ((s0.sp - 632#64) ↦₆₄ out_sret) ∗
            ((s0.sp - 624#64) ↦₆₄ 16#64) ∗ ((s0.sp - 616#64) ↦₆₄ pv_ptr) ∗
            ((s0.sp - 608#64) ↦₆₄ 16#64) ∗ interpolateScratchAt s0.sp ∗
            memRegion (s0.sp - 672#64) 8 ∗ memRegion (s0.sp - 120#64) 24 ∗
            memRegion out_sret vecHeaderBytes ∗ A.live pv_ptr 256 8 ∗
            ptSliceRefListAt dec 0 pv_ptr pins ∗ sortedSetPtListPinAt A decA pins dec.pts ∗
            reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗ stackAt (s0.sp - 672#64) extHookStack ∗ F) by exact Entails.of_eq (by ac_rfl))
      (allocOut_zero_placed_sepWP (ext := ext) s0.sp s1 _ _ hpc1 hrun1 hsp1 hx24_0 (by rw [hx29_1, hx29])
        (fun s2 hpc2 hrun2 hsp2 htr2 hx29_2 => ?_))
    rw [stackAt_extHook_eq_allocHook (s0.sp - 672#64)]
    refine SepWP.weaken_pre
      (show _ ⊢
        optPolyCacheListAt A (s0.sp - 600#64) (List.replicate 16 none) ∗
          ((s0.sp - 632#64) ↦₆₄ out_sret) ∗ ((s0.sp - 216#64) ↦₆₄ 0#64) ∗
          ((s0.sp - 208#64) ↦₆₄ 1#64) ∗ ((s0.sp - 200#64) ↦₆₄ 0#64) ∗
          memRegion out_sret vecHeaderBytes ∗ A.pool ∗ stackAt (s0.sp - 672#64) allocHookStack ∗
          (memRegion ((s0.sp - 672#64) - 16384#64) 12288 ∗ savedRegsAt s0.sp s0 ∗
            ((s0.sp - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗ ((s0.sp - 624#64) ↦₆₄ 16#64) ∗
            ((s0.sp - 616#64) ↦₆₄ pv_ptr) ∗ ((s0.sp - 608#64) ↦₆₄ 16#64) ∗
            interpolateScratchAt s0.sp ∗ memRegion (s0.sp - 672#64) 8 ∗
            memRegion (s0.sp - 120#64) 24 ∗ A.live pv_ptr 256 8 ∗
            ptSliceRefListAt dec 0 pv_ptr pins ∗
            (sortedSetPtListPinAt A decA pins dec.pts ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ F)) by exact Entails.of_eq (by ac_rfl))
      (dropOptPolyCache_from1460_placed_sepWP hdealloc_sat s0.sp out_sret hsp0 s2 _ _
        hpc2 hrun2 hsp2 hx29_2 (fun s3 hpc3 hrun3 hsp3 htr3 => ?_))
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (decodedMessage_finish_from1904_placed_sepWP hdealloc_sat dec pins hpins s0 out_sret pv_ptr
        (BitVec.ofNat 64 dec.ptsNeeded) (some []) hsp0 s3
        (sortedSetPtListPinAt A decA pins dec.pts ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ F) _
        hpc3 hrun3 hsp3 (fun sf hpc_f hrun_f hsp_f htr_f hcs_f => ?_))
    apply SepWP.done hpc_f hrun_f
    have htot := decodedMessageTotal_of_ptsNeeded_zero hcomp_false hpts hret hneed0
    refine SepWPp.weaken_pre
      (show _ ⊢
        optVecU8Of A out_sret (decodedMessageTotal dec) ∗ sortedSetPtListPinAt A decA pins dec.pts ∗
          reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗ stackAt s0.sp decodedMessageStack ∗ F by
        rw [htot]; exact Entails.of_eq (by ac_rfl))
      (hnext sf hpc_f hrun_f hsp_f (by rw [htr_f, htr3, htr2, htr1, htr]) hcs_f)
  · have hge1 : 1 ≤ dec.ptsNeeded := Nat.pos_of_ne_zero hneed0
    rw [stackAt_extHook_eq_computeAt (s0.sp - 672#64), stackAt_computeAt_eq_allocHook (s0.sp - 672#64)]
    apply sepWPp_seq_lscl hcl1 (mid := (blkPl_418).base + 548#64)
    refine SepWPp.weaken_pre
      (show _ ⊢
        memRegion (s0.sp - 216#64) 24 ∗ A.pool ∗ stackAt (s0.sp - 672#64) allocHookStack ∗
          (((s0.sp - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
            optPolyCacheListAt A (s0.sp - 600#64) (List.replicate 16 none) ∗
            savedRegsAt s0.sp s0 ∗ ((s0.sp - 632#64) ↦₆₄ out_sret) ∗
            ((s0.sp - 624#64) ↦₆₄ 16#64) ∗ ((s0.sp - 616#64) ↦₆₄ pv_ptr) ∗
            ((s0.sp - 608#64) ↦₆₄ 16#64) ∗ interpolateScratchAt s0.sp ∗
            memRegion (s0.sp - 672#64) 8 ∗ memRegion (s0.sp - 120#64) 24 ∗
            memRegion out_sret vecHeaderBytes ∗ A.live pv_ptr 256 8 ∗
            ptSliceRefListAt dec 0 pv_ptr pins ∗ sortedSetPtListPinAt A decA pins dec.pts ∗
            reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ memRegion ((s0.sp - 672#64) - 4352#64) 256 ∗
            memRegion ((s0.sp - 672#64) - 16384#64) 12032 ∗ F) by exact Entails.of_eq (by ac_rfl))
      (allocOut_pos_placed_wpp h_panic hshim_sat halloc_sat s0.sp hsp0 dec.ptsNeeded hge1 hneed_le s0 s1 _ R _
        hpc1 hrun1 hsp1 (by rw [htr1, htr]) hx24_1 (by rw [hx29_1, hx29])
        (fun out_ptr s2 hout_ne0 hpc2 hrun2 hsp2 htr2 hx20_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx29_2 => ?_))
    apply SepWPp.done hpc2 hrun2
    intro hcl2
    refine SepWPp.weaken_pre
      (show _ ⊢
        optPolyCacheListAt A (s0.sp - 600#64) (List.replicate 16 none) ∗
          ((s0.sp - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
          ((s0.sp - 616#64) ↦₆₄ pv_ptr) ∗ ((s0.sp - 608#64) ↦₆₄ 16#64) ∗
          ((s0.sp - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
          ((s0.sp - 208#64) ↦₆₄ out_ptr) ∗ ((s0.sp - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * 0)) ∗
          ptSliceRefListAt dec 0 pv_ptr pins ∗ sortedSetPtListPinAt A decA pins dec.pts ∗
          (out_ptr ↦ₛ ([] : List (BitVec 8))) ∗
          memRegion (out_ptr + BitVec.ofNat 64 (2 * 0)) (2 * (dec.ptsNeeded - 0)) ∗
          interpolateScratchAt s0.sp ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗
          stackAt (s0.sp - 672#64) computeAtStack ∗
          (savedRegsAt s0.sp s0 ∗ ((s0.sp - 632#64) ↦₆₄ out_sret) ∗
            ((s0.sp - 624#64) ↦₆₄ 16#64) ∗ memRegion (s0.sp - 672#64) 8 ∗
            memRegion (s0.sp - 120#64) 24 ∗ memRegion out_sret vecHeaderBytes ∗
            A.live pv_ptr 256 8 ∗ A.live out_ptr (2 * dec.ptsNeeded) 1 ∗
            memRegion ((s0.sp - 672#64) - 16384#64) 12032 ∗ F) by
        rw [stackAt_computeAt_eq_allocHook (s0.sp - 672#64)]
        simp only [Nat.mul_zero, Nat.sub_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
        exact Entails.of_eq (by ac_rfl))
      (decodedMessageLoop_cl_placed_wpp h_panic hshim_sat halloc_sat hdealloc_sat hmemcpy_sat hprep hcomp_ok hcomp_at
        dec s0.sp decA pv_ptr out_ptr pins
        hsp0 hpts hpins hsort hneed_le hall_ge s0 _ R Q
        (dec.ptsNeeded - 1) 0 (List.replicate 16 none) [] s2 (by omega) (by simp) (by simp)
        hcl2 hpc2 hrun2 hsp2 htr2 (by rw [hx20_2, hx20_1, hx20]) hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx29_2
        (fun s3 hpc3 hrun3 hsp3 htr3 hx29_3 => ?_))
    have hrem_eq : dec.ptsNeeded - 1 + 1 = dec.ptsNeeded := by omega
    rw [hrem_eq]
    have hpolys_len :
        (decodedMessageLoopTotal dec (collectedSlices dec 0 16) 0 dec.ptsNeeded (List.replicate 16 none) []).1.length = 16 :=
      decodedMessageLoopTotal_fst_length dec (collectedSlices dec 0 16) dec.ptsNeeded 0 (List.replicate 16 none) [] (by simp)
    have hout_len :
        (decodedMessageLoopTotal dec (collectedSlices dec 0 16) 0 dec.ptsNeeded (List.replicate 16 none) []).2.length =
          2 * dec.ptsNeeded := by
      simpa using decodedMessageLoopTotal_snd_length dec (collectedSlices dec 0 16) dec.ptsNeeded 0 (List.replicate 16 none) []
    apply SepWPp.of_sepWP (mid := s0.readReg64 .x30)
    rw [stackAt_computeAt_eq_allocHook (s0.sp - 672#64)]
    have hmem256_12032 :
        memRegion ((s0.sp - 672#64) - 4352#64) 256 ∗ memRegion ((s0.sp - 672#64) - 16384#64) 12032 =
          memRegion ((s0.sp - 672#64) - 16384#64) 12288 := by
      have hsub : (s0.sp - 672#64) - 16384#64 + 12032#64 = (s0.sp - 672#64) - 4352#64 := by bv_omega
      rw [show (12288 : Nat) = 12032 + 256 from rfl,
        memRegion_split ((s0.sp - 672#64) - 16384#64) 12032 256 (by decide), hsub, sepConj_comm]
    refine SepWP.weaken_pre
      (show _ ⊢
        optPolyCacheListAt A (s0.sp - 600#64)
          (decodedMessageLoopTotal dec (collectedSlices dec 0 16) 0 dec.ptsNeeded (List.replicate 16 none) []).1 ∗
          ((s0.sp - 632#64) ↦₆₄ out_sret) ∗
          ((s0.sp - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
          ((s0.sp - 208#64) ↦₆₄ out_ptr) ∗
          ((s0.sp - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
          memRegion out_sret vecHeaderBytes ∗ A.live out_ptr (2 * dec.ptsNeeded) 1 ∗
          (out_ptr ↦ₛ (decodedMessageLoopTotal dec (collectedSlices dec 0 16) 0 dec.ptsNeeded (List.replicate 16 none) []).2) ∗
          A.pool ∗ stackAt (s0.sp - 672#64) allocHookStack ∗
          (memRegion ((s0.sp - 672#64) - 16384#64) 12288 ∗ savedRegsAt s0.sp s0 ∗
            ((s0.sp - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗ ((s0.sp - 624#64) ↦₆₄ 16#64) ∗
            ((s0.sp - 616#64) ↦₆₄ pv_ptr) ∗ ((s0.sp - 608#64) ↦₆₄ 16#64) ∗
            interpolateScratchAt s0.sp ∗ memRegion (s0.sp - 672#64) 8 ∗
            memRegion (s0.sp - 120#64) 24 ∗ A.live pv_ptr 256 8 ∗
            ptSliceRefListAt dec 0 pv_ptr pins ∗
            (sortedSetPtListPinAt A decA pins dec.pts ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ F)) by
        rw [← hmem256_12032]; exact Entails.of_eq (by ac_rfl))
      (dropOptPolyCache_from1404_placed_sepWP hdealloc_sat s0.sp out_sret out_ptr hsp0 dec.ptsNeeded hge1 hneed_le
        (decodedMessageLoopTotal dec (collectedSlices dec 0 16) 0 dec.ptsNeeded (List.replicate 16 none) []).1 hpolys_len
        (decodedMessageLoopTotal dec (collectedSlices dec 0 16) 0 dec.ptsNeeded (List.replicate 16 none) []).2 hout_len
        hout_ne0 s3 _ _ hpc3 hrun3 hsp3 hx29_3 (fun s4 hpc4 hrun4 hsp4 htr4 => ?_))
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (decodedMessage_finish_from1904_placed_sepWP hdealloc_sat dec pins hpins s0 out_sret pv_ptr
        (BitVec.ofNat 64 dec.ptsNeeded)
        (some (decodedMessageLoopTotal dec (collectedSlices dec 0 16) 0 dec.ptsNeeded (List.replicate 16 none) []).2) hsp0 s4
        (sortedSetPtListPinAt A decA pins dec.pts ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ F) _
        hpc4 hrun4 hsp4 (fun sf hpc_f hrun_f hsp_f htr_f hcs_f => ?_))
    apply SepWP.done hpc_f hrun_f
    have htot := decodedMessageTotal_of_collect_false hcomp_false hpts hret
    refine SepWPp.weaken_pre
      (show _ ⊢
        optVecU8Of A out_sret (decodedMessageTotal dec) ∗ sortedSetPtListPinAt A decA pins dec.pts ∗
          reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗ stackAt s0.sp decodedMessageStack ∗ F by
        rw [htot]; exact Entails.of_eq (by ac_rfl))
      (hnext sf hpc_f hrun_f hsp_f (by rw [htr_f, htr4, htr3]) hcs_f)

/-! ## 3. Top-Level Entry Proof with `withLsCodeLoaded` / `withLsCodeRoLoaded` -/

theorem polyDecoderDecodedMessage_cl_placed_ok_of_contracts [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionSpec)
    (hprep : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 372) (withLsCodeLoaded lsmpl (lagrangePreparePlacedSpec A)))
    (hcomp_ok : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 373) (withLsCodeLoaded lsmpl lagrangeCompletePlacedSpec))
    (hcomp_at : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 371) (withLsCodeLoaded lsmpl (computeAtPlacedSpec A))) :
    subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (blkPl_418).base (withLsCodeLoaded lsmpl (decodedMessagePlacedSpec A)) := by
  simp only [withLsCodeLoaded, decodedMessagePlacedSpec]; wpp_init x s0
  have hx8 : s0.readReg64 (Reg.gpr 8#5) = x.out := by assumption
  have hx0 : s0.readReg64 (Reg.gpr 0#5) = x.decA := by assumption
  have hsort : PolyDecoderStrictSorted x.dec := by assumption
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  clear h h_1 h_2 h_3 hpre
  have hshim : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) sessionShimSpec :=
    SpqrV1.Alloc.spqr_hook_ok_of_mem hshim_sat
  have halloc : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustAllocSpec A) :=
    SpqrV1.Alloc.spqr_hook_ok_of_mem halloc_sat
  have hpan_err :
      ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)).externAt? (lsρ spqrHandleErrorSym) =
        some Rust.panicked :=
    (SpqrV1.Alloc.spqr_externAt?_of_mem).trans h_panic
  have hsp0 : s0.sp &&& 0xf#64 = 0#64 := beq_iff_eq.mp hsp_align
  wp_conv_pre =>
    dsimp only [polyDecoderAt, NUM_POLYS, CHUNK_SIZE, boolByte, polyDecoderPadSize,
      polyDecoderPtsNeededOff, polyDecoderIsCompleteOff, polyDecoderPadOff, BitVec.ofNat_eq_ofNat]
    rw [show memRegion x.out vecHeaderBytes ∗
          (⌜x.dec.pts.length = 16 ∧ x.dec.ptsNeeded < 2 ^ 64⌝ ∗ sortedSetPtListOf A x.decA x.dec.pts ∗
            ((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
            ((x.decA + 392#64) ↦₈ if x.dec.isComplete then 1#8 else 0#8) ∗
            memRegion (x.decA + 393#64) 7) ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗ stackAt s0.sp decodedMessageStack =
        ⌜x.dec.pts.length = 16 ∧ x.dec.ptsNeeded < 2 ^ 64⌝ ∗
          (stackAt s0.sp decodedMessageStack ∗ memRegion x.out vecHeaderBytes ∗
            sortedSetPtListOf A x.decA x.dec.pts ∗
            ((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
            ((x.decA + 392#64) ↦₈ if x.dec.isComplete then 1#8 else 0#8) ∗
            memRegion (x.decA + 393#64) 7 ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool) by ac_rfl]
  apply SepWPp.pure_left; rintro ⟨hpts_len, hneed_lt⟩
  have hlen_bound : ∀ s ∈ x.dec.pts, s.vec.length ≤ 65536 := by
    intro s hs; rcases List.getElem_of_mem hs with ⟨i, hi, rfl⟩
    exact polyDecoderStrictSorted_elem_length_le hsort hi
  wp_conv_pre => rw [stackAt_decodedMessage_eq s0.sp]
  apply of_sepWP_lscl hcl0 (mid := (blkPl_418).base + 32#64)
  refine SepWP.weaken_pre
    (show _ ⊢ memRegion (s0.sp - 96#64) 96 ∗
      (memRegion (s0.sp - 672#64) 576 ∗ stackAt (s0.sp - 672#64) extHookStack ∗
        memRegion x.out vecHeaderBytes ∗ sortedSetPtListOf A x.decA x.dec.pts ∗
        ((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
        ((x.decA + 392#64) ↦₈ if x.dec.isComplete then 1#8 else 0#8) ∗
        memRegion (x.decA + 393#64) 7 ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool) by exact Entails.of_eq (by ac_rfl))
    (decodedMessage_prologue_placed_sepWP (ext := ext) s0 _ _ hsp0 hpc hrun
      (fun s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx29_1 hx30_1 => ?_))
  rcases Prod.mk.inj htr1 with ⟨htr1_tr, htr1_vr⟩
  apply SepWP.done hpc1 hrun1
  intro hcl1
  dsimp only [Reg.x0, Reg.x8, Reg.x29, Reg.x30] at hx0_1 hx8_1 hx29_1 hx30_1
  rw [hx0] at hx0_1; rw [hx8] at hx8_1
  have hsp1_al : s1.sp &&& 15#64 = 0#64 := by rw [hsp1]; exact sp672_aligned s0.sp hsp0
  have hsp1_aligned : s1.spAligned = true := by unfold State.spAligned; rw [hsp1_al]; rfl
  cases hcomp : x.dec.isComplete
  ·
    wp_conv_pre => simp only [Bool.false_eq_true, ↓reduceIte]
    refine SepWPp.weaken_pre
      (sepConj_mono_right (sepConj_mono_left (memRegion576_split_for_decodedMessage s0.sp))) ?_
    wp_conv_pre => rw [stackAt_extHook_eq_allocHook (s0.sp - 672#64)]
    try dsimp only [BitVec.ofNat_eq_ofNat] at hshim halloc hpan_err hpc1 ⊢
    apply of_sepWP_lscl hcl1 (mid := (blkPl_418).base + 76#64)
    wp_conv_pre => simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    wp_pull_exists; rename_i w_4 w_3 w_2 w_1 w
    wp_steps 5; wp_call hshim; wp_steps 3
    have hpow8 : ∃ m, 8 = 2 ^ m := ⟨3, rfl⟩
    wp_call halloc
    apply SepWP.done hpc_sf_1 (by wp_norm_lhs)
    intro hcl_sf1
    by_cases hptr0 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
    · have hcbz : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = true := by simp [hptr0]
      wp_conv_pre => rw [alloc_post_pos' hptr0]
      apply SepWPp.pure_left; intro htr_fail
      apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
      wp_steps 4
      apply SepWP.done (by rfl) (by wp_norm_lhs)
      have htr_panic_eq :
          (Rust.panicked ((((sf_1.writeReg64 (Reg.gpr 0#5) 8#64).writeReg64 (Reg.gpr 1#5)
            256#64).writeReg64 (Reg.gpr 30#5)
            ((blkPl_418).base + 1968#64)).setPC (lsρ spqrHandleErrorSym))).trace = s0.trace ++ [allocFailedEvent] := by
        change sf_1.trace = s0.trace ++ [allocFailedEvent]; rw [htr_fail, h, htr1_tr]
      refine SepWPp.panic (by wp_norm_lhs) (by simpa [arm64_norm, wp_norm] using hpan_err)
        (fun hm => by
          rw [← sepConj_assoc]
          exact allowPanic_panicked (φ := allocFailedIn s0 _ ∧ s0.trace <+: _)
            ⟨allocFailedIn_of_trace_eq' htr_panic_eq,
              by rw [htr_panic_eq]; exact List.prefix_append s0.trace [allocFailedEvent]⟩ hm)
    · have hcbz : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hptr0
      wp_conv_pre => rw [alloc_post_neg' hptr0]
      apply SepWPp.pure_left; rintro ⟨_hptr_mod, htr_ok⟩
      apply of_sepWP_lscl hcl_sf1 (mid := (blkPl_418).base + 80#64)
      wp_steps 1
      apply SepWP.done (by simp [wp_norm, arm64_norm, hcbz]) (by simp [wp_norm, arm64_norm, hrun_sf_1])
      intro hcl_sf1'
      rw [h_1, hsp1]
      apply of_sepWP_lscl hcl_sf1' (mid := (blkPl_418).base + 128#64)
      refine SepWP.weaken_pre
        (show _ ⊢
          ((x.decA + polyDecoderPtsNeededOff) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
            (∃∗ w648 : BitVec 64, (s0.sp - 648#64) ↦₆₄ w648) ∗
            (∃∗ w624 : BitVec 64, (s0.sp - 624#64) ↦₆₄ w624) ∗
            (∃∗ w616 : BitVec 64, (s0.sp - 616#64) ↦₆₄ w616) ∗
            (∃∗ w608 : BitVec 64, (s0.sp - 608#64) ↦₆₄ w608) ∗
            (savedRegsAt s0.sp s0 ∗ ((s0.sp - 632#64) ↦₆₄ x.out) ∗
              memRegion (s0.sp - 600#64) 384 ∗ memRegion (s0.sp - 216#64) 24 ∗
              interpolateScratchAt s0.sp ∗ memRegion (s0.sp - 672#64) 8 ∗
              memRegion (s0.sp - 120#64) 24 ∗ stackAt (s0.sp - 672#64) extHookStack ∗
              memRegion x.out vecHeaderBytes ∗ A.live (sf_1.readReg64 (Reg.gpr 0#5)) 256 8 ∗
              memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 256 ∗
              sortedSetPtListOf A x.decA x.dec.pts ∗ ((x.decA + 392#64) ↦₈ 0#8) ∗
              memRegion (x.decA + 393#64) 7 ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool) by
          rw [stackAt_extHook_eq_allocHook (s0.sp - 672#64),
            show s0.sp - 672#64 - 16384#64 = s0.sp - 17056#64 by bv_omega]
          try dsimp only [polyDecoderPtsNeededOff, BitVec.ofNat_eq_ofNat]
          refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_left (Entails.sepExists_intro w)))
          refine Entails.trans ?_
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (Entails.sepExists_intro w_2))))
          refine Entails.trans ?_
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (Entails.sepExists_intro w_3)))))
          refine Entails.trans ?_
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (Entails.sepExists_intro w_4))))))
          exact Entails.of_eq (by ac_rfl))
        (decodedMessage_allocPv_setup_placed_sepWP (ext := ext) x.dec s0.sp x.decA (sf_1.readReg64 (Reg.gpr 0#5)) hsp0 hneed_lt _ _ _
          (by rfl)
          (by simp [wp_norm, arm64_norm, hrun_sf_1]) (by simp [wp_norm, arm64_norm, hsp_sf, h_1, hsp1])
          (by simp [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm]; rw [h_13, h_3])
          (fun s2 hpc2 hrun2 hsp2 htr2 hx0_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx29_2 hx30_2 => ?_))
      have htr2' : traceVRegs s2 = traceVRegs s0 := by rw [htr2]; simp [traceVRegs, wp_norm, arm64_norm, *]
      have hx29_2' : s2.readReg64 .x29 = s0.sp - 96#64 := by
        simp [wp_norm, arm64_norm, *]
      wp_conv_pre =>
        rw [sortedSetPtListOf_eq_exists_pins A x.dec.pts x.decA]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      wp_pull_exists; rename_i pins
      apply SepWP.done hpc2 hrun2
      intro hcl2
      wp_conv_pre =>
        try dsimp only [polyDecoderPtsNeededOff, BitVec.ofNat_eq_ofNat]
        rw [show ((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
              ((s0.sp - 648#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
              ((s0.sp - 624#64) ↦₆₄ 16#64) ∗ ((s0.sp - 616#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗
              ((s0.sp - 608#64) ↦₆₄ 0#64) ∗ savedRegsAt s0.sp s0 ∗
              ((s0.sp - 632#64) ↦₆₄ x.out) ∗ memRegion (s0.sp - 600#64) 384 ∗
              memRegion (s0.sp - 216#64) 24 ∗ interpolateScratchAt s0.sp ∗
              memRegion (s0.sp - 672#64) 8 ∗ memRegion (s0.sp - 120#64) 24 ∗
              stackAt (s0.sp - 672#64) extHookStack ∗ memRegion x.out vecHeaderBytes ∗
              A.live (sf_1.readReg64 (Reg.gpr 0#5)) 256 8 ∗ memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 256 ∗
              ⌜pins.length = x.dec.pts.length⌝ ∗ sortedSetPtListPinAt A x.decA pins x.dec.pts ∗
              ((x.decA + 392#64) ↦₈ 0#8) ∗ memRegion (x.decA + 393#64) 7 ∗
              tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool =
            ⌜pins.length = x.dec.pts.length⌝ ∗
              (((s0.sp - 624#64) ↦₆₄ 16#64) ∗ ((s0.sp - 608#64) ↦₆₄ 0#64) ∗
                sortedSetPtListPinAt A x.decA pins x.dec.pts ∗
                memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 256 ∗
                (savedRegsAt s0.sp s0 ∗ ((s0.sp - 648#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
                  ((s0.sp - 632#64) ↦₆₄ x.out) ∗ ((s0.sp - 616#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗
                  memRegion (s0.sp - 600#64) 384 ∗ memRegion (s0.sp - 216#64) 24 ∗
                  interpolateScratchAt s0.sp ∗ memRegion (s0.sp - 672#64) 8 ∗
                  memRegion (s0.sp - 120#64) 24 ∗ memRegion x.out vecHeaderBytes ∗
                  A.live (sf_1.readReg64 (Reg.gpr 0#5)) 256 8 ∗
                  reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗ stackAt (s0.sp - 672#64) extHookStack ∗
                  (((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
                    ((x.decA + 392#64) ↦₈ 0#8) ∗
                    memRegion (x.decA + 393#64) 7))) by ac_rfl]
      apply SepWPp.pure_left; intro hpins
      have hpins16 : pins.length = 16 := by rw [hpins, hpts_len]
      cases hcol : (collectPointsVecsTotal x.dec 0 16 false []).1
      ·
        have ⟨hall_ge, _⟩ := collectPointsVecs_false_bounds x.dec hpts_len hsort hcol
        apply of_sepWP_lscl hcl2 (mid := (blkPl_418).base + 352#64)
        refine SepWP.weaken_pre
          (show _ ⊢
            ((s0.sp - 624#64) ↦₆₄ 16#64) ∗ ((s0.sp - 608#64) ↦₆₄ 0#64) ∗
              sortedSetPtListPinAt A x.decA pins x.dec.pts ∗
              ptSliceRefListAt x.dec 0 (sf_1.readReg64 (Reg.gpr 0#5)) (pins.take 0) ∗
              memRegion ((sf_1.readReg64 (Reg.gpr 0#5)) + BitVec.ofNat 64 (16 * 0)) (16 * (16 - 0)) ∗
              (savedRegsAt s0.sp s0 ∗ ((s0.sp - 648#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
                ((s0.sp - 632#64) ↦₆₄ x.out) ∗ ((s0.sp - 616#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗
                memRegion (s0.sp - 600#64) 384 ∗ memRegion (s0.sp - 216#64) 24 ∗
                interpolateScratchAt s0.sp ∗ memRegion (s0.sp - 672#64) 8 ∗
                memRegion (s0.sp - 120#64) 24 ∗ memRegion x.out vecHeaderBytes ∗
                A.live (sf_1.readReg64 (Reg.gpr 0#5)) 256 8 ∗
                reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗ stackAt (s0.sp - 672#64) extHookStack ∗
                (((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
                  ((x.decA + 392#64) ↦₈ 0#8) ∗
                  memRegion (x.decA + 393#64) 7)) by
            simp only [List.take_zero, ptSliceRefListAt, Nat.mul_zero, Nat.sub_zero,
              BitVec.ofNat_eq_ofNat, BitVec.add_zero, emp_sepConj]
            exact Entails.of_eq (by ac_rfl))
          (collectPointsVecs_ok_loop_placed_sepWP (ext := ext) x.dec x.decA (sf_1.readReg64 (Reg.gpr 0#5)) s0.sp pins
            hpts_len hpins16 hneed_lt hlen_bound hall_ge hsp0 15 0 s2 0#64 _ _ (by decide)
            hpc2 hrun2 hsp2 hx0_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2
            (fun s3 hpc3 hrun3 hsp3 htr3 _hx0_3 hx20_3 hx29_3 _hx30_3 => ?_))
        apply SepWP.done hpc3 hrun3
        intro hcl3
        conv => arg 6; ext sf P_f; rw [← sepConj_assoc]
        refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
          (decodedMessage_afterCollect_cl_placed_wpp h_panic hshim_sat halloc_sat hdealloc_sat hmemcpy_sat hprep hcomp_ok hcomp_at
            x.dec x.decA x.out (sf_1.readReg64 (Reg.gpr 0#5)) pins
            hcomp hpts_len hpins16 hsort hcol s0 s3
            (((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
              ((x.decA + 392#64) ↦₈ 0#8) ∗
              memRegion (x.decA + 393#64) 7) R _
            hcl3 hsp0 hpc3 hrun3 hsp3 (by rw [htr3, htr2']) hx20_3 (by rw [hx29_3, hx29_2'])
            (fun sf hpc_f hrun_f hsp_f htr_f hcs_f => ?_))
        rcases calleeSavedPreserved_of_gprs_traceVRegs hcs_f htr_f with ⟨hcs_f, htr_f⟩
        refine SepWPp.weaken_pre
          (show _ ⊢
            ⌜sf.trace = s0.trace⌝ ∗ optVecU8Of A x.out (decodedMessageTotal x.dec) ∗
              polyDecoderAt A x.decA x.dec ∗
              tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗ stackAt s0.sp decodedMessageStack by
            refine Entails.trans
              (sepConj_mono_right (sepConj_mono_left
                (sortedSetPtListPinAt_entails_sortedSetPtListOf A pins x.dec.pts x.decA hpins))) ?_
            refine Entails.pure_right htr_f ?_
            refine Entails.trans (Entails.of_eq (show _ =
              (sortedSetPtListOf A x.decA x.dec.pts ∗
                ((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
                ((x.decA + 392#64) ↦₈ 0#8) ∗ memRegion (x.decA + 393#64) 7) ∗
              (optVecU8Of A x.out (decodedMessageTotal x.dec) ∗
                tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗ stackAt s0.sp decodedMessageStack) by ac_rfl)) ?_
            rw [show (0#8 : BitVec 8) = if x.dec.isComplete then 1#8 else 0#8 by rw [hcomp]; rfl]
            refine Entails.trans (sepConj_mono_left (reassemble_polyDecoderAt x.decA x.dec hpts_len hneed_lt)) ?_
            exact Entails.of_eq (by ac_rfl))
          (SepWPp.done hpc_f hrun_f ⟨fun hm => by simpa only [sepConj_assoc] using hm, hsp_f, hcs_f⟩)
      ·
        have hex_lt := exists_lt_necessaryPoints_of_collect_true x.dec hpts_len hcol
        apply SepWPp.of_sepWP (mid := s0.readReg64 .x30)
        refine collectPointsVecs_none_loop_placed_sepWP (ext := ext) x.dec x.decA (sf_1.readReg64 (Reg.gpr 0#5)) s0.sp pins
          hpts_len hpins16 hneed_lt hlen_bound hsp0
          15 0 0 false s2 0#64 _ _ (by decide) (by decide) (Or.inr hex_lt)
          hpc2 hrun2 hsp2 hx0_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2
          (fun s3 pvLenFinal hpc3 hrun3 hsp3 htr3 _hx29_3 _hx30_3 => ?_)
        refine SepWP.weaken_pre
          (show _ ⊢
            (interpolateScratchAt s0.sp ∗ memRegion (s0.sp - 672#64) 8 ∗ memRegion (s0.sp - 120#64) 24) ∗
              (((s0.sp - 648#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
                ((s0.sp - 632#64) ↦₆₄ x.out) ∗ ((s0.sp - 624#64) ↦₆₄ 16#64) ∗
                ((s0.sp - 616#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗
                ((s0.sp - 608#64) ↦₆₄ pvLenFinal) ∗ memRegion x.out vecHeaderBytes ∗
                A.live (sf_1.readReg64 (Reg.gpr 0#5)) 256 8 ∗ memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 256 ∗
                memRegion (s0.sp - 600#64) 384 ∗ memRegion (s0.sp - 216#64) 24 ∗
                savedRegsAt s0.sp s0 ∗ A.pool ∗ stackAt (s0.sp - 672#64) extHookStack ∗
                (sortedSetPtListPinAt A x.decA pins x.dec.pts ∗
                  ((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
                  ((x.decA + 392#64) ↦₈ 0#8) ∗
                  memRegion (x.decA + 393#64) 7 ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt)) by
            exact Entails.of_eq (by ac_rfl)) ?_
        refine SepWP.weaken_pre (sepConj_mono_left (scratch_and_pads_entails_regions s0.sp)) ?_
        refine SepWP.weaken_pre
          (show _ ⊢
            (memRegion (s0.sp - 600#64) 384 ∗ memRegion (s0.sp - 216#64) 24 ∗ memRegion (s0.sp - 192#64) 96) ∗
              (((s0.sp - 648#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
                ((s0.sp - 632#64) ↦₆₄ x.out) ∗ ((s0.sp - 624#64) ↦₆₄ 16#64) ∗
                ((s0.sp - 616#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗
                ((s0.sp - 608#64) ↦₆₄ pvLenFinal) ∗ memRegion x.out vecHeaderBytes ∗
                A.live (sf_1.readReg64 (Reg.gpr 0#5)) 256 8 ∗ memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 256 ∗
                memRegion (s0.sp - 672#64) 24 ∗ memRegion (s0.sp - 640#64) 8 ∗
                savedRegsAt s0.sp s0 ∗ A.pool ∗ stackAt (s0.sp - 672#64) extHookStack ∗
                (sortedSetPtListPinAt A x.decA pins x.dec.pts ∗
                  ((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
                  ((x.decA + 392#64) ↦₈ 0#8) ∗
                  memRegion (x.decA + 393#64) 7 ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt)) by
            exact Entails.of_eq (by ac_rfl)) ?_
        refine SepWP.weaken_pre (sepConj_mono_left (memRegion_384_24_96_entails_504 s0.sp)) ?_
        refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
          (decodedMessage_epilogue_from288_placed_sepWP hdealloc_sat s0 s0.sp x.out (sf_1.readReg64 (Reg.gpr 0#5))
            (BitVec.ofNat 64 x.dec.ptsNeeded) pvLenFinal hsp0 s3
            (sortedSetPtListPinAt A x.decA pins x.dec.pts ∗
              ((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
              ((x.decA + 392#64) ↦₈ 0#8) ∗
              memRegion (x.decA + 393#64) 7 ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt) _
            hpc3 hrun3 hsp3 (fun sf hpc_f hrun_f hsp_f htr_f hcs_f => ?_))
        apply SepWP.done hpc_f hrun_f
        have htot := decodedMessageTotal_of_collect_true hcomp hpts_len hcol
        have htr_f_vr : traceVRegs sf = traceVRegs s0 := by rw [htr_f, htr3, htr2']
        rcases calleeSavedPreserved_of_gprs_traceVRegs hcs_f htr_f_vr with ⟨hcs_f, htr_f'⟩
        refine SepWPp.weaken_pre
          (show _ ⊢
            ⌜sf.trace = s0.trace⌝ ∗ optVecU8Of A x.out (decodedMessageTotal x.dec) ∗
              polyDecoderAt A x.decA x.dec ∗
              tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗ stackAt s0.sp decodedMessageStack by
            rw [htot]
            refine Entails.trans
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
                (sortedSetPtListPinAt_entails_sortedSetPtListOf A pins x.dec.pts x.decA hpins))))) ?_
            refine Entails.pure_right htr_f' ?_
            refine Entails.trans (Entails.of_eq (show _ =
              (sortedSetPtListOf A x.decA x.dec.pts ∗
                ((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
                ((x.decA + 392#64) ↦₈ 0#8) ∗ memRegion (x.decA + 393#64) 7) ∗
              (optVecU8Of A x.out none ∗
                tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗ stackAt s0.sp decodedMessageStack) by ac_rfl)) ?_
            rw [show (0#8 : BitVec 8) = if x.dec.isComplete then 1#8 else 0#8 by rw [hcomp]; rfl]
            refine Entails.trans (sepConj_mono_left (reassemble_polyDecoderAt x.decA x.dec hpts_len hneed_lt)) ?_
            exact Entails.of_eq (by ac_rfl))
          (SepWPp.done hpc_f hrun_f ⟨fun hm => by simpa only [sepConj_assoc] using hm, hsp_f, hcs_f⟩)
  ·
    wp_conv_pre => simp only [↓reduceIte]
    have hout_split : memRegion x.out vecHeaderBytes =
        (∃∗ w0 : BitVec 64, x.out ↦₆₄ w0) ∗ memRegion (x.out + 8#64) 16 := by
      rw [show vecHeaderBytes = 8 + 16 from rfl,
        memRegion_split x.out 8 16 (by decide), ProofLib.memRegion_eight x.out]
    wp_conv_pre => rw [hout_split]
    try dsimp only [BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    apply SepWPp.of_sepWP (mid := s0.readReg64 .x30)
    wp_conv_pre => simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    wp_pull_exists
    wp_steps 5
    have hnone_eq :
        (x.out ↦₆₄ bv% (2 ^ 64 - 1)) ∗ memRegion (x.out + 8#64) 16 =
          optVecU8Of A x.out none := by unfold optVecU8Of noneCap; rfl
    refine SepWP.weaken_pre
      (show _ ⊢
        savedRegsAt s0.sp s0 ∗ memRegion (s0.sp - 672#64) 576 ∗
          stackAt (s0.sp - 672#64) extHookStack ∗
          (optVecU8Of A x.out none ∗ sortedSetPtListOf A x.decA x.dec.pts ∗
            ((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
            ((x.decA + 392#64) ↦₈ 1#8) ∗ memRegion (x.decA + 393#64) 7 ∗
            tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool) by
        rw [← hnone_eq]; exact Entails.of_eq (by ac_rfl))
      (decodedMessage_epilogue_ret_placed_sepWP (ext := ext) s0 s0.sp hsp0 _ _ _
        (by rfl)
        (by simp [wp_norm, arm64_norm, hrun1]) (by simpa [wp_norm, arm64_norm] using hsp1)
        (fun sf hpc_f hrun_f hsp_f htr_f hcs_f => ?_))
    apply SepWP.done hpc_f hrun_f
    have htot := decodedMessageTotal_of_isComplete_true hcomp
    have htr_f_vr : traceVRegs sf = traceVRegs s0 := by simpa [wp_norm, arm64_norm, htr1] using htr_f
    rcases calleeSavedPreserved_of_gprs_traceVRegs hcs_f htr_f_vr with ⟨hcs_f, htr_f'⟩
    refine SepWPp.weaken_pre
      (show _ ⊢
        ⌜sf.trace = s0.trace⌝ ∗ optVecU8Of A x.out (decodedMessageTotal x.dec) ∗
          polyDecoderAt A x.decA x.dec ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗ stackAt s0.sp decodedMessageStack by
        rw [htot]
        refine Entails.pure_right htr_f' ?_
        refine Entails.trans (Entails.of_eq (show _ =
          (sortedSetPtListOf A x.decA x.dec.pts ∗
            ((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
            ((x.decA + 392#64) ↦₈ 1#8) ∗ memRegion (x.decA + 393#64) 7) ∗
          (optVecU8Of A x.out none ∗
            tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗ stackAt s0.sp decodedMessageStack) by ac_rfl)) ?_
        rw [show (1#8 : BitVec 8) = if x.dec.isComplete then 1#8 else 0#8 by rw [hcomp]; rfl]
        refine Entails.trans (sepConj_mono_left (reassemble_polyDecoderAt x.decA x.dec hpts_len hneed_lt)) ?_
        exact Entails.of_eq (by ac_rfl))
      (SepWPp.done hpc_f hrun_f ⟨fun hm => by simpa only [sepConj_assoc] using hm, hsp_f, hcs_f⟩)

/-! ## 4. Closed Relocatable Theorems Discharging Blocks `372`, `373`, and `371` -/

private theorem subroutine_ok_withLsCodeLoaded_of_plain {α : Type} {prog : Program}
    {entry : BitVec 64} {pl : Arm64.Obj.MultiPlacement} {spec : Spec α}
    (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withLsCodeLoaded pl spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => (extract_withLsCodeLoaded hp).2)
    (fun _ _ _ _ hq => hq)

theorem polyDecoderDecodedMessage_cl_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc_sat : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionSpec)
    (hmemset_sat : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionSpec) :
    subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (blkPl_418).base (withLsCodeLoaded lsmpl (decodedMessagePlacedSpec A)) :=
  polyDecoderDecodedMessage_cl_placed_ok_of_contracts
    h_panic hshim_sat halloc_sat hdealloc_sat hmemcpy_sat
    (ls_subroutine_ok_of_block (i := 418) (j := 372)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (lagrangePrepare_placed_ok_of_hookSat A ext h_panic hshim_sat halloc_sat hmemset_sat)))
    (ls_subroutine_ok_of_block (i := 418) (j := 373)
      (lagrangeComplete_placed_ok ext))
    (ls_subroutine_ok_of_block (i := 418) (j := 371)
      (computeAt_placed_ok A ext h_panic hshim_sat halloc_sat hrealloc_sat hdealloc_sat))

theorem polyDecoderDecodedMessage_cro_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc_sat : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionSpec)
    (hmemset_sat : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionSpec) :
    subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (blkPl_418).base (withLsCodeRoLoaded lsmpl (decodedMessagePlacedSpec A)) :=
  CryptoVerification.LibsignalTripleRatchet.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (polyDecoderDecodedMessage_cl_placed_ok h_panic hshim_sat halloc_sat hrealloc_sat
      hdealloc_sat hmemcpy_sat hmemset_sat)

theorem polyDecoderDecodedMessage_cro_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc_sat : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionSpec)
    (hmemset_sat : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionSpec) :
    subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (blkPl_418).base (withLsCodeRoLoaded lsmpl (polyDecoderDecodedMessagePlacedSpec A)) :=
  polyDecoderDecodedMessage_placed_cro_of_decodedMessage
    (polyDecoderDecodedMessage_cro_placed_ok h_panic hshim_sat halloc_sat hrealloc_sat
      hdealloc_sat hmemcpy_sat hmemset_sat)

theorem polyDecodedMessagePlacedOkX_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc_sat : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionSpec)
    (hmemset_sat : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionSpec) :
    PolyDecodedMessagePlacedOkX A ext :=
  polyDecodedMessagePlacedOkX_of_decodedMessage
    (polyDecoderDecodedMessage_cro_placed_ok h_panic hshim_sat halloc_sat hrealloc_sat
      hdealloc_sat hmemcpy_sat hmemset_sat)

end CryptoVerification.SpqrV1.Poly.DecodedMessage

namespace CryptoVerification.SpqrV1.States.Leaves

export CryptoVerification.SpqrV1.Poly.DecodedMessage
  (polyDecoderDecodedMessage_cl_placed_ok_of_contracts
   polyDecoderDecodedMessage_cl_placed_ok
   polyDecoderDecodedMessage_cro_placed_ok
   polyDecoderDecodedMessage_cro_placed_ok_x
   polyDecodedMessagePlacedOkX_of_hooks)

end CryptoVerification.SpqrV1.States.Leaves

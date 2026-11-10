/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.InterpolateFull
import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.InterpolateFullPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.LoopPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.MainLoop
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Proof -- shake: keep

/-!
# `<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message`: Relocatable Main Loop

Relocatable `[LibsignalPlacement]` proof of the evaluation and interpolation loop (`+548..+1404`)
on Block `418` (`decodedMessageLoop_placed_wpp`).
-/

@[expose] public section

set_option autoImplicit false

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
   lagrangePrepareStack lagrangePrepare_ok lagrangePrepare_placed_ok polyOf_eq)
open CryptoVerification.SpqrV1.Poly.LagrangeComplete
open CryptoVerification.SpqrV1.GF.UnacceleratedMul CryptoVerification.SpqrV1.GF.Mul2U16

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  AddChunkNorm.sp_setPC_pre AddChunkNorm.sp_setMem_setPC_pre
  AddChunkNorm.readReg64_setPC_pre AddChunkNorm.readReg64_setMem_setPC_pre
  AddChunkNorm.readReg32_setPC_pre AddChunkNorm.readReg32_setMem_setPC_pre
  AddChunkNorm.readReg_setPC_pre AddChunkNorm.readReg_setMem_setPC_pre
  sp96_sub120 sp96_sub112 sp96_sub104
  bv64_and15_ofNat bv64_umaddl24_mod16
  bv64_ofNat_mul2_comm bv64_ofNat_one_add_mul2

/-- Step 1 of the main loop (`[LibsignalPlacement]`):
    Looks up `xVal = BitVec.ofNat 16 (i / 16)` in `dec.pts[i % 16]` via binary search. -/
theorem decodedMessage_bsearchStep_placed_sepWP [lsmpl : LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (dec : PolyDecoder) (sp0 pts_base : BitVec 64) (pins : List VecPin) (i : Nat)
    (hpts : dec.pts.length = 16) (hpins : pins.length = 16)
    (hi_lt : i < dec.ptsNeeded) (hneed_le : dec.ptsNeeded ≤ 16 * 65536)
    (hge_len : 1 ≤ (dec.pts[i % 16]'(by have := Nat.mod_lt i (by decide : 0 < 16); omega)).vec.length)
    (hle_len : (dec.pts[i % 16]'(by have := Nat.mod_lt i (by decide : 0 < 16); omega)).vec.length ≤ 65536)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_418).base + 548#64)
    (hstat : s.status = .Running)
    (hx20 : s.readReg64 .x20 = pts_base)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 i)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (2 * i))
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 dec.ptsNeeded)
    (hx25 : s.readReg64 .x25 = 24#64)
    (hx26 : s.readReg64 .x26 = sp0 - 600#64)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hcont_found :
      let poly := i % 16
      let hpoly_pts : poly < dec.pts.length := by have := Nat.mod_lt i (by decide : 0 < 16); omega
      let sPt := dec.pts[poly]'hpoly_pts
      let xVal := BitVec.ofNat 16 (i / 16)
      let bIdx := bsearchLoop sPt.vec xVal 0 sPt.vec.length
      ∀ (hb_lt : bIdx < sPt.vec.length),
        ((sPt.vec[bIdx]'hb_lt).x.value == xVal) = true →
        ∀ (sf : State),
          sf.pc = (blkPl_418).base + 1328#64 →
          sf.status = .Running →
          sf.sp = s.sp →
          traceVRegs sf = traceVRegs s →
          BitVec.truncate 8 (sf.readReg64 .x19) = BitVec.truncate 8 ((sPt.vec[bIdx]'hb_lt).y.value >>> 8) →
          BitVec.truncate 8 (sf.readReg64 .x21) = BitVec.truncate 8 (sPt.vec[bIdx]'hb_lt).y.value →
          sf.readReg64 .x20 = pts_base →
          sf.readReg64 .x22 = BitVec.ofNat 64 i →
          sf.readReg64 .x23 = BitVec.ofNat 64 (2 * i) →
          sf.readReg64 .x24 = BitVec.ofNat 64 dec.ptsNeeded →
          sf.readReg64 .x25 = 24#64 →
          sf.readReg64 .x26 = sp0 - 600#64 →
          sf.readReg64 .x29 = sp0 - 96#64 →
          SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf
            (sortedSetPtListPinAt A pts_base pins dec.pts ∗
              ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗ P)
            post)
    (hcont_miss :
      let poly := i % 16
      let hpoly_pts : poly < dec.pts.length := by have := Nat.mod_lt i (by decide : 0 < 16); omega
      let sPt := dec.pts[poly]'hpoly_pts
      let xVal := BitVec.ofNat 16 (i / 16)
      let bIdx := bsearchLoop sPt.vec xVal 0 sPt.vec.length
      ∀ (hb_lt : bIdx < sPt.vec.length),
        ((sPt.vec[bIdx]'hb_lt).x.value == xVal) = false →
        ∀ (sf : State),
          sf.pc = (blkPl_418).base + 660#64 →
          sf.status = .Running →
          sf.sp = s.sp →
          traceVRegs sf = traceVRegs s →
          sf.readReg64 .x0 = BitVec.ofNat 64 poly →
          sf.readReg64 .x20 = pts_base →
          sf.readReg64 .x22 = BitVec.ofNat 64 i →
          sf.readReg64 .x24 = BitVec.ofNat 64 dec.ptsNeeded →
          sf.readReg64 .x25 = 24#64 →
          sf.readReg64 .x26 = sp0 - 600#64 →
          sf.readReg64 .x29 = sp0 - 96#64 →
          SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf
            (sortedSetPtListPinAt A pts_base pins dec.pts ∗
              ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗ P)
            post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc s
      (sortedSetPtListPinAt A pts_base pins dec.pts ∗
        ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗ P)
      post := by
  have hpoly_lt : i % 16 < 16 := Nat.mod_lt i (by decide)
  have hpoly_pts : i % 16 < dec.pts.length := by omega
  have hpoly_pins : i % 16 < pins.length := by omega
  have hbsearch := @bsearch_to_624_placed_sepWP lsmpl ext ret_pc (pins[i % 16]'hpoly_pins).ptr
    (dec.pts[i % 16]'hpoly_pts).vec (BitVec.ofNat 16 (i / 16)) hge_len hle_len
  try dsimp only [BitVec.ofNat_eq_ofNat] at hbsearch hpc hcont_found hcont_miss ⊢
  have hlen_ne0 : (BitVec.ofNat 64 (dec.pts[i % 16]'hpoly_pts).vec.length == 0#64) = false := by
    rw [bv64_beq_ofNat (by omega) (by decide), decide_eq_false_iff_not]; omega
  have hlsr4 := bv32_lsr4_zeroExtend_ofNat (show i < 16 * 65536 by omega)
  rw [sortedSetPtListPinAt_focus A pins dec.pts (i % 16) pts_base (by rw [hpins, hpts]) hpoly_pts,
    sortedSetPtPinAt_eq_slice A (pins[i % 16]'hpoly_pins) (dec.pts[i % 16]'hpoly_pts)
      (pts_base + BitVec.ofNat 64 (24 * (i % 16)))]
  wp_steps 6
  refine SepWP.weaken_pre
    (show _ ⊢
      ptSliceAt (pins[i % 16]'hpoly_pins).ptr (dec.pts[i % 16]'hpoly_pts).vec ∗
        (sortedSetPtListPinAt A pts_base (pins.take (i % 16)) (dec.pts.take (i % 16)) ∗
          ((pts_base + BitVec.ofNat 64 (24 * (i % 16))) ↦₆₄ (pins[i % 16]'hpoly_pins).cap) ∗
          ((pts_base + BitVec.ofNat 64 (24 * (i % 16)) + 8#64) ↦₆₄ (pins[i % 16]'hpoly_pins).ptr) ∗
          ((pts_base + BitVec.ofNat 64 (24 * (i % 16)) + 16#64) ↦₆₄
            BitVec.ofNat 64 (dec.pts[i % 16]'hpoly_pts).vec.length) ∗
          sortedSetPtPinRest A (pins[i % 16]'hpoly_pins) (dec.pts[i % 16]'hpoly_pts) ∗
          sortedSetPtListPinAt A (pts_base + BitVec.ofNat 64 (24 * (i % 16 + 1)))
            (pins.drop (i % 16 + 1)) (dec.pts.drop (i % 16 + 1)) ∗
          ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗ P) by
      exact Entails.of_eq (by ac_rfl)) ?_
  refine hbsearch _ _ post
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, hstat])
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, hlsr4])
    (by simp [wp_norm, arm64_norm])
    (fun s1 hpc1 hstat1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hx20_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx29_1 _ => ?_)
  have ⟨_, hb_lt0⟩ := bsearchLoop_bounds (dec.pts[i % 16]'hpoly_pts).vec
    (BitVec.ofNat 16 (i / 16)) 0 (dec.pts[i % 16]'hpoly_pts).vec.length hge_len (by omega)
  have hb_lt : bsearchLoop (dec.pts[i % 16]'hpoly_pts).vec (BitVec.ofNat 16 (i / 16)) 0
      (dec.pts[i % 16]'hpoly_pts).vec.length < (dec.pts[i % 16]'hpoly_pts).vec.length := by
    omega
  have hx0_1' : s1.readReg64 .x0 = BitVec.ofNat 64 (i % 16) := by
    simpa [wp_norm, arm64_norm, hx22] using hx0_1
  have hx9_32 : s1.readReg32 .x9 = BitVec.zeroExtend 32 (BitVec.ofNat 16 (i / 16)) := by
    rw [State.readReg32, hx9_1]
    bv_bits
  have hx20_1' : s1.readReg64 .x20 = pts_base := by simpa [wp_norm, arm64_norm, hx20] using hx20_1
  have hx22_1' : s1.readReg64 .x22 = BitVec.ofNat 64 i := by simpa [wp_norm, arm64_norm, hx22] using hx22_1
  have hx23_1' : s1.readReg64 .x23 = BitVec.ofNat 64 (2 * i) := by simpa [wp_norm, arm64_norm, hx23] using hx23_1
  have hx24_1' : s1.readReg64 .x24 = BitVec.ofNat 64 dec.ptsNeeded := by simpa [wp_norm, arm64_norm, hx24] using hx24_1
  have hx25_1' : s1.readReg64 .x25 = 24#64 := by simpa [wp_norm, arm64_norm, hx25] using hx25_1
  have hx26_1' : s1.readReg64 .x26 = sp0 - 600#64 := by simpa [wp_norm, arm64_norm, hx26] using hx26_1
  have hx29_1' : s1.readReg64 .x29 = sp0 - 96#64 := by simpa [wp_norm, arm64_norm, hx29] using hx29_1
  let bIdx := bsearchLoop (dec.pts[i % 16]'hpoly_pts).vec (BitVec.ofNat 16 (i / 16)) 0
    (dec.pts[i % 16]'hpoly_pts).vec.length
  rw [ptSliceAt_focus (dec.pts[i % 16]'hpoly_pts).vec bIdx (pins[i % 16]'hpoly_pins).ptr hb_lt]
  unfold ptAt
  wp_steps 3
  rw [bv16_bne_zeroExtend32 ((dec.pts[i % 16]'hpoly_pts).vec[bIdx]'hb_lt).x.value (BitVec.ofNat 16 (i / 16))]
  cases hbeq : ((dec.pts[i % 16]'hpoly_pts).vec[bIdx]'hb_lt).x.value == BitVec.ofNat 16 (i / 16)
  · simp only [Bool.not_false, ↓reduceIte]
    refine SepWP.weaken_pre
      (show _ ⊢
        (sortedSetPtListPinAt A pts_base pins dec.pts ∗
          ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗ P) by
        rw [sortedSetPtListPinAt_focus A pins dec.pts (i % 16) pts_base (by rw [hpins, hpts]) hpoly_pts,
          sortedSetPtPinAt_eq_slice A (pins[i % 16]'hpoly_pins) (dec.pts[i % 16]'hpoly_pts)
            (pts_base + BitVec.ofNat 64 (24 * (i % 16))),
          ptSliceAt_focus (dec.pts[i % 16]'hpoly_pts).vec bIdx (pins[i % 16]'hpoly_pins).ptr hb_lt]
        unfold ptAt
        exact Entails.of_eq (by ac_rfl)) ?_
    apply hcont_miss hb_lt hbeq
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm, hstat1]
    · simpa [wp_norm, arm64_norm] using hsp1
    · simpa [wp_norm, arm64_norm] using htr1
    · simp [wp_norm, arm64_norm, hx0_1']
    · simp [wp_norm, arm64_norm, hx20_1']
    · simp [wp_norm, arm64_norm, hx22_1']
    · simp [wp_norm, arm64_norm, hx24_1']
    · simp [wp_norm, arm64_norm, hx25_1']
    · simp [wp_norm, arm64_norm, hx26_1']
    · simp [wp_norm, arm64_norm, hx29_1']
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have h2i_ne : (BitVec.ofNat 64 (2 * i) == BitVec.ofNat 64 (2 * dec.ptsNeeded)) = false := by
      rw [bv64_beq_ofNat (by omega) (by omega), decide_eq_false_iff_not]; omega
    wp_steps 6
    refine SepWP.weaken_pre
      (show _ ⊢
        (sortedSetPtListPinAt A pts_base pins dec.pts ∗
          ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗ P) by
        rw [sortedSetPtListPinAt_focus A pins dec.pts (i % 16) pts_base (by rw [hpins, hpts]) hpoly_pts,
          sortedSetPtPinAt_eq_slice A (pins[i % 16]'hpoly_pins) (dec.pts[i % 16]'hpoly_pts)
            (pts_base + BitVec.ofNat 64 (24 * (i % 16))),
          ptSliceAt_focus (dec.pts[i % 16]'hpoly_pts).vec bIdx (pins[i % 16]'hpoly_pins).ptr hb_lt]
        unfold ptAt
        exact Entails.of_eq (by ac_rfl)) ?_
    apply hcont_found hb_lt hbeq
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm, hstat1]
    · simpa [wp_norm, arm64_norm] using hsp1
    · simpa [wp_norm, arm64_norm] using htr1
    · simp [wp_norm, arm64_norm, bv16_lsr8_zeroExtend64_truncate8]; rfl
    · simp [wp_norm, arm64_norm, bv16_zeroExtend64_truncate8]; rfl
    · simp [wp_norm, arm64_norm, hx20_1']
    · simp [wp_norm, arm64_norm, hx22_1']
    · simp [wp_norm, arm64_norm, hx23_1']
    · simp [wp_norm, arm64_norm, hx24_1']
    · simp [wp_norm, arm64_norm, hx25_1']
    · simp [wp_norm, arm64_norm, hx26_1']
    · simp [wp_norm, arm64_norm, hx29_1']

/-- Step 2b of the main loop (`[LibsignalPlacement]`):
    Loads `(ptr_p, len_p)` from `slot`, evaluates `computeAtPure p (GF16.new (BitVec.ofNat 16 (i / 16)))`
    via `computeAt_placed_ok`, and prepares `w19`/`w21`/`x23` at `entry + 1328#64`. -/
theorem decodedMessage_computeAtStep_placed_wpp [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (hcomp_at : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 371) (computeAtPlacedSpec A))
    (sp0 slot : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (i ptsNeeded : Nat) (p : Poly)
    (hi_lt : i < ptsNeeded) (hneed_le : ptsNeeded ≤ 16 * 65536)
    (s0 s : State) (F R : SepProp) (Q : State → SepProp → Prop)
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
  apply SepWPp.of_sepWP (mid := lsmpl.base 371)
  wp_steps 3
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hstat])
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
  · have hx2_trunc :
        BitVec.truncate 16 ((BitVec.ofNat 64 i) >>> 4) =
          (GF16.new (BitVec.ofNat 16 (i / 16))).value :=
      bv64_lsr4_truncate16_ofNat (by omega)
    simp only [computeAtPlacedSpec, a, wp_norm, arm64_norm, hsp, hslot16] at hm ⊢
    exact ⟨⟨hx2_trunc, by omega⟩, Satisfies.mono (Entails.of_eq (by ac_rfl)) hm⟩
  · simp only [computeAtPlacedSpec] at hex
    exact not_satisfies_false_sepConj hex
  · simp only [computeAtPlacedSpec] at hm
    exact allowPanic_frame (fun ⟨hal, hpre⟩ => by
      simp only [allocFailedIn, wp_norm, arm64_norm, htr_tr] at hal hpre ⊢
      exact ⟨hal, hpre⟩) hm
  · conv => arg 4; simp only [computeAtPlacedSpec, a, wp_norm, arm64_norm, htr_tr, hsp]
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

/-- Step 3 of the main loop (`[LibsignalPlacement]`):
    Appends `u16ToBeBytes yVal` to `out` at `out_ptr + 2 * i` and increments `i` and `2 * i`. -/
theorem decodedMessage_pushTwoBytes_placed_sepWP [lsmpl : LibsignalPlacement]
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (sp0 out_ptr old_len_slot : BitVec 64) (i ptsNeeded : Nat)
    (out : List (BitVec 8)) (yVal : BitVec 16)
    (hi_lt : i < ptsNeeded) (hneed_le : ptsNeeded ≤ 16 * 65536)
    (hout_len : out.length = 2 * i)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_418).base + 1328#64)
    (hstat : s.status = .Running)
    (hx19 : BitVec.truncate 8 (s.readReg64 .x19) = BitVec.truncate 8 (yVal >>> 8))
    (hx21 : BitVec.truncate 8 (s.readReg64 .x21) = BitVec.truncate 8 yVal)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 i)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (2 * i))
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 ptsNeeded)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hcont : ∀ sf : State,
      sf.pc = (if i + 1 = ptsNeeded then
        (blkPl_418).base + 1404#64
      else
        (blkPl_418).base + 548#64) →
      sf.status = .Running →
      sf.sp = s.sp →
      traceVRegs sf = traceVRegs s →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x22 = BitVec.ofNat 64 (i + 1) →
      sf.readReg64 .x23 = BitVec.ofNat 64 (2 * (i + 1)) →
      sf.readReg64 .x24 = BitVec.ofNat 64 ptsNeeded →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x29 = sp0 - 96#64 →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf
        (((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
          ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
          ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * (i + 1))) ∗
          (out_ptr ↦ₛ (out ++ u16ToBeBytes yVal)) ∗
          memRegion (out_ptr + BitVec.ofNat 64 (2 * (i + 1))) (2 * (ptsNeeded - (i + 1))) ∗ P)
        post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc s
      (((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
        ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
        ((sp0 - 200#64) ↦₆₄ old_len_slot) ∗
        (out_ptr ↦ₛ out) ∗
        memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (ptsNeeded - i)) ∗ P)
      post := by
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc hcont ⊢
  have h2i_add1 : BitVec.ofNat 64 (2 * i) + 1#64 = BitVec.ofNat 64 (2 * i + 1) := by
    rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
  have h2i1_ne : (BitVec.ofNat 64 (2 * i + 1) != BitVec.ofNat 64 (2 * ptsNeeded)) = true := by
    rw [bv64_bne_ofNat (by omega) (by omega), decide_eq_true_eq]; omega
  have hi_add1 : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by
    rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
  have h2i2 : 2 * i + 2 = 2 * (i + 1) := by omega
  have h2i_add2 : BitVec.ofNat 64 (2 * i) + 2#64 = BitVec.ofNat 64 (2 * (i + 1)) := by
    rw [show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, ← BitVec.ofNat_add, h2i2]
  have hi1_eq : (BitVec.ofNat 64 (i + 1) == BitVec.ofNat 64 ptsNeeded) = decide (i + 1 = ptsNeeded) :=
    bv64_beq_ofNat (by omega) (by omega)
  rw [memRegion_out_split2 out_ptr hi_lt (by omega)]
  wp_pull_exists
  wp_steps 14
  refine SepWP.weaken_pre
    (show _ ⊢
      (((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
        ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
        ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * (i + 1))) ∗
        (out_ptr ↦ₛ (out ++ u16ToBeBytes yVal)) ∗
        memRegion (out_ptr + BitVec.ofNat 64 (2 * (i + 1))) (2 * (ptsNeeded - (i + 1))) ∗ P) by
      rw [← pointsToBytes_append_u16ToBeBytes out_ptr out yVal, hout_len]
      exact Entails.of_eq (by ac_rfl)) ?_
  apply hcont
  · by_cases heq : i + 1 = ptsNeeded <;> simp [wp_norm, arm64_norm, hi1_eq, heq]
  · simp [wp_norm, arm64_norm, hstat]
  · simp [wp_norm, arm64_norm]
  · simp [wp_norm, arm64_norm]
  · simp [wp_norm, arm64_norm]
  · simp [wp_norm, arm64_norm]
  · simp [wp_norm, arm64_norm, h2i_add2]
  · simp [wp_norm, arm64_norm, hx24]
  · simp [wp_norm, arm64_norm]
  · simp [wp_norm, arm64_norm]
  · simp [wp_norm, arm64_norm, hx29]

/-- Full evaluation/interpolation loop (`[LibsignalPlacement]`):
    executes `rem + 1` iterations from `i` to `dec.ptsNeeded`, matching
    `decodedMessageLoopTotal dec (collectedSlices dec 0 16) i (rem + 1) polys out`. -/
theorem decodedMessageLoop_placed_wpp [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionSpec)
    (hprep : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 372) (lagrangePreparePlacedSpec A))
    (hcomp : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 373)
      (lagrangeCompletePlacedSpec))
    (hcomp_at : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 371)
      (computeAtPlacedSpec A))
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
      s.pc = (blkPl_418).base + 548#64 →
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
        sf.pc = (blkPl_418).base + 1404#64 →
        sf.status = .Running →
        sf.sp = sp0 - 672#64 →
        traceVRegs sf = traceVRegs s0 →
        sf.readReg64 .x29 = sp0 - 96#64 →
        let (polysFinal, outFinal) :=
          decodedMessageLoopTotal dec (collectedSlices dec 0 16) i (rem + 1) polys out
        SepWPp ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc sf
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
            reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗
            stackAt (sp0 - 672#64) computeAtStack ∗ F)
          Q
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) →
      SepWPp ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc s
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
          reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗
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
    · -- Not found (`entry + 660#64`): interpolate (if needed), then `compute_at`, then push 2 bytes
      apply SepWPp.of_sepWP (mid := (blkPl_418).base + 660#64)
      refine SepWP.weaken_pre ?_
        (decodedMessage_bsearchStep_placed_sepWP (ext := ext) (A := A) dec sp0 pts_base pins i hpts hpins hi_lt hneed_le hge_len hle_len
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
            reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗
            stackAt (sp0 - 672#64) computeAtStack ∗ F)
          _ hpc hstat hx20 hx22 hx23 hx24 hx25 hx26 hx29 ?_ ?_)
      · exact Entails.of_eq (by ac_rfl)
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
                reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗
                stackAt (sp0 - 672#64) computeAtStack ∗ F) =
            optPolyCacheSlotAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16))) (polys[i % 16]'hpoly_p) ∗
              ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
              ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
              ((sp0 - 608#64) ↦₆₄ 16#64) ∗
              ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * (i % 16)))
                (pins[i % 16]'hpoly_pins).ptr ptsSlice.length ∗
              ptSliceAt (pins[i % 16]'hpoly_pins).ptr ptsSlice ∗
              interpolateScratchAt sp0 ∗
              reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗
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
          ac_rfl
        refine SepWPp.weaken_pre (Entails.of_eq hfocus_pre)
          (lagrangeInterpolate_inlined_placed_wpp h_panic hshim_sat halloc_sat hdealloc_sat hmemcpy_sat hprep hcomp
            sp0 pts_vec_ptr (pins[i % 16]'hpoly_pins).ptr
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
              reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗
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
                memRegion ((sp0 - 672#64) - 4352#64) 48 ∗ F) =
            optPolyCacheSlotAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16))) (some pInterp) ∗
              ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
              ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
              reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗
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
          ac_rfl
        refine SepWPp.weaken_pre (Entails.of_eq hreasm_mid)
          (decodedMessage_computeAtStep_placed_wpp hcomp_at sp0
            ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16))) hsp0 i dec.ptsNeeded pInterp
            hi_lt hneed_le s0 s2 _ R Q
            hpc2 hrun2 hsp2 htr2 hx19_2 (by rw [hx22_2, hx22_1]) hx29_2 ?_)
        intro s3 hpc3 hrun3 hsp3 htr3 hx19_3 hx21_3 hx20_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx29_3
        apply SepWPp.of_sepWP
          (mid := if i + 1 = dec.ptsNeeded then
            (blkPl_418).base + 1404#64
          else
            (blkPl_418).base + 548#64)
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
              ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
              ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
              ((sp0 - 608#64) ↦₆₄ 16#64) ∗
              ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
              sortedSetPtListPinAt A pts_base pins dec.pts ∗
              interpolateScratchAt sp0 ∗
              reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗
              stackAt (sp0 - 672#64) computeAtStack ∗ F)
            _ hpc3 hrun3 hx19_3 hx21_3 hx22_3 hx23_3 (by rw [hx24_3, hx24_2]) hx29_3 ?_)
        · rw [← hset_polys]
          exact Entails.of_eq (by ac_rfl)
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
          exact Entails.of_eq (by ac_rfl)
        | succ rem' =>
          have hi1_ne : i + 1 ≠ dec.ptsNeeded := by omega
          simp only [hi1_ne, ↓reduceIte] at hpc4
          refine SepWPp.weaken_pre ?_
            (decodedMessageLoop_placed_wpp h_panic hshim_sat halloc_sat hdealloc_sat hmemcpy_sat hprep hcomp hcomp_at
              dec sp0 pts_base pts_vec_ptr out_ptr pins
              hsp0 hpts hpins hsort hneed_le hall_ge s0 F R Q
              rem' (i + 1) (polys.set (i % 16) (some pInterp))
              (out ++ u16ToBeBytes yInterp.value)
              s4 (by omega) (by simp [hpolys_len]) (by simp [hout_len, u16ToBeBytes]; omega)
              hpc4 hrun4 (by rw [hsp4, hsp3]) (by rw [htr4, htr3])
              (by rw [hx20_4, hx20_3, hx20_2, hx20_1]) hx22_4 hx23_4 hx24_4
              (by rw [hx25_4, hx25_3, hx25_2]) (by rw [hx26_4, hx26_3, hx26_2]) hx29_4
              (fun sf hpc_f hrun_f hsp_f htr_f hx29_f => ?_))
          · exact Entails.of_eq (by ac_rfl)
          · rw [← hstep_pure]
            exact hnext sf hpc_f hrun_f hsp_f htr_f hx29_f
    · -- Found in `dec.pts[i % 16]` at `entry + 1328#64`
      apply SepWPp.of_sepWP
        (mid := if i + 1 = dec.ptsNeeded then
          (blkPl_418).base + 1404#64
        else
          (blkPl_418).base + 548#64)
      refine SepWP.weaken_pre ?_
        (decodedMessage_bsearchStep_placed_sepWP (ext := ext) (A := A) dec sp0 pts_base pins i hpts hpins hi_lt hneed_le hge_len hle_len
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
            reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗
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
            (optPolyCacheListAt A (sp0 - 600#64) polys ∗
              ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
              ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
              ((sp0 - 608#64) ↦₆₄ 16#64) ∗
              ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
              sortedSetPtListPinAt A pts_base pins dec.pts ∗
              interpolateScratchAt sp0 ∗
              reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗
              stackAt (sp0 - 672#64) computeAtStack ∗ F)
            _ hpc1 hrun1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx29_1 ?_)
        · exact Entails.of_eq (by ac_rfl)
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
          exact Entails.of_eq (by ac_rfl)
        | succ rem' =>
          have hi1_ne : i + 1 ≠ dec.ptsNeeded := by omega
          simp only [hi1_ne, ↓reduceIte] at hpc2
          refine SepWPp.weaken_pre ?_
            (decodedMessageLoop_placed_wpp h_panic hshim_sat halloc_sat hdealloc_sat hmemcpy_sat hprep hcomp hcomp_at
              dec sp0 pts_base pts_vec_ptr out_ptr pins
              hsp0 hpts hpins hsort hneed_le hall_ge s0 F R Q
              rem' (i + 1) polys
              (out ++ u16ToBeBytes
                ((dec.pts[i % 16]'hpoly_pts).vec[bsearchLoop (dec.pts[i % 16]'hpoly_pts).vec (BitVec.ofNat 16 (i / 16)) 0 (dec.pts[i % 16]'hpoly_pts).vec.length]'hb_lt).y.value)
              s2 (by omega) hpolys_len (by simp [hout_len, u16ToBeBytes]; omega)
              hpc2 hrun2 (by rw [hsp2, hsp1, hsp]) (by rw [htr2, htr1, htr])
              (by rw [hx20_2, hx20_1]) hx22_2 hx23_2 hx24_2
              (by rw [hx25_2, hx25_1]) (by rw [hx26_2, hx26_1]) hx29_2
              (fun sf hpc_f hrun_f hsp_f htr_f hx29_f => ?_))
          · exact Entails.of_eq (by ac_rfl)
          · rw [← hstep_pure]
            exact hnext sf hpc_f hrun_f hsp_f htr_f hx29_f
      · dsimp only
        intro _ hfalse
        rw [hfound] at hfalse
        cases hfalse

end CryptoVerification.SpqrV1.Poly.DecodedMessage

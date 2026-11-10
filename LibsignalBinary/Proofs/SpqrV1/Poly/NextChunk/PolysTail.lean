/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsFast
import LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.Proof
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PolysLoop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk`: Polynomial Evaluation Tail Loop

Verifies the polynomial evaluation tail loop (`+296 -> +4484`) executed on indices `i0..15` after
`points_to_polys` transitions the encoder from `EncoderState::Points` to `EncoderState::Polys`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.NextChunk

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.ComputeAt
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  LagrangePrepare.sp_setPC_pre LagrangePrepare.sp_setMem_setPC_pre
  LagrangePrepare.readReg64_setPC_pre LagrangePrepare.readReg64_setMem_setPC_pre
  LagrangePrepare.readReg32_setPC_pre LagrangePrepare.readReg32_setMem_setPC_pre
  LagrangePrepare.readReg_setPC_pre LagrangePrepare.readReg_setMem_setPC_pre

attribute [local simp, local arm64_norm, local wp_norm]
  polyEncoderTagOff polyEncoderVecsOff polyEncoderVecsSize
  polyEncoderIdxOff polyEncoderPadOff polyEncoderPadSize
  polyEncoderPointsTag polyEncoderPolysTag
  chunkDataOff chunkIndexOff chunkSize
  madd_24_eq madd_24_eq' ofNat_add_one_eq
  ofNat_two_mul_add_one ofNat_two_mul_add_two

/-! ## 1. Arithmetic & List Helpers for the Tail Loop -/

theorem trunc8_zext64_trunc32_of_trunc16 {w0 : BitVec 64} {v : BitVec 16}
    (h : w0.truncate 16 = v) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 w0)) =
      BitVec.setWidth 8 v := by
  revert h; bv_slice

theorem ubfx8_trunc8_of_trunc16 {w0 : BitVec 64} {v : BitVec 16}
    (h : w0.truncate 16 = v) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 w0) >>> 8 &&& 255#64) =
      BitVec.setWidth 8 (v >>> 8) := by
  revert h; bv_slice

theorem computeAt_tail_pre_split (p_coeffs : BitVec 64) (poly : LibsignalSpqrV1.Poly)
    (b fsp : BitVec 64) (A : RustAlloc)
    (F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16 F17 F18 F19 F20 F21 F22 F23 : SepProp) :
    (F1 ∗ F2 ∗ F3 ∗ (gf16SliceAt p_coeffs poly.coefficients ∗ F4)) ∗
      F5 ∗ F6 ∗ F7 ∗ F8 ∗ F9 ∗ F10 ∗ F11 ∗ F12 ∗ F13 ∗ F14 ∗ F15 ∗ F16 ∗ F17 ∗ F18 ∗ F19 ∗ F20 ∗ F21 ∗ F22 ∗
      tokenInitAt b ∗ reduceTableAt b ∗ A.pool ∗
      F23 ∗ stackAt fsp computeAtStack =
      (gf16SliceAt p_coeffs poly.coefficients ∗
        tokenInitAt b ∗ reduceTableAt b ∗ A.pool ∗ stackAt fsp computeAtStack) ∗
      (F1 ∗ F2 ∗ F3 ∗ F4 ∗ F5 ∗ F6 ∗ F7 ∗ F8 ∗ F9 ∗ F10 ∗
        F11 ∗ F12 ∗ F13 ∗ F14 ∗ F15 ∗ F16 ∗ F17 ∗ F18 ∗ F19 ∗ F20 ∗ F21 ∗ F22 ∗ F23) := by
  ac_rfl

/-! ## 2. Single Step of the Polynomial Evaluation Tail Loop (`0x6a4ac..0x6a504 -> 0x6a480..0x6a4a8`) -/

set_option maxHeartbeats 1600000 in
theorem polysTailLoop_step_sepWPp
    (A : RustAlloc) (b : BitVec 64) (ext : String → Option (State → State))
    (hb : b &&& 0xfff#64 = 0#64) (hA : AllocContracts b A ext)
    (x : PolyNextChunkGhost) (polys : List LibsignalSpqrV1.Poly) (hlen_polys : polys.length = 16)
    (out_ptr u48 : BitVec 64) (prefix_bytes : List (BitVec 8)) (R : SepProp)
    {Q : State → SepProp → Prop}
    (i rem : Nat) (hrem_eq : i + (rem + 1) = 16) (hprefix : prefix_bytes.length = 2 * i)
    (s0 s : State)
    (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 296#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1200#64)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 i)
    (hx19 : s.readReg64 .x19 = x.encA + 8#64)
    (hx24 : s.readReg64 .x24 = x.encA)
    (hx27 : s.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hnext : ∀ sf : State,
      sf.pc = (if rem == 0 then
          (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4484#64
        else
          (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 296#64) →
      sf.status = .Running →
      sf.sp = s0.sp - 1200#64 →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      sf.readReg64 .x9 = BitVec.ofNat 64 (i + 1) →
      sf.readReg64 .x19 = x.encA + 8#64 →
      sf.readReg64 .x20 = BitVec.ofNat 64 (2 * (i + 1)) →
      sf.readReg64 .x24 = x.encA →
      sf.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64 →
      sf.readReg64 .x28 = 24#64 →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 Reg.lr) sf
        ((out_ptr ↦ₛ (prefix_bytes ++ chunkPolysBytes (x.enc.idx.setWidth 16) polys i 1)) ∗
         memRegion (out_ptr + BitVec.ofNat 64 (2 * (i + 1))) (32 - 2 * (i + 1)) ∗
         A.live out_ptr 32 1 ∗
         memRegion x.outA chunkSize ∗
         (x.encA ↦₆₄ polyEncoderPolysTag) ∗
         polyListOf A (x.encA + 8#64) polys ∗
         ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
         memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
         (((s0.sp - 1200#64) + 48#64) ↦₆₄ u48) ∗
         (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
         (((s0.sp - 1200#64) + 88#64) ↦₆₄ (x.encA + 8#64)) ∗
         (((s0.sp - 1200#64) + 104#64) ↦₆₄ BitVec.ofNat 64 (if rem == 0 then i else i + 1)) ∗
         (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗
         (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
         (((s0.sp - 1200#64) + 248#64) ↦₆₄ BitVec.ofNat 64 (2 * (i + 1))) ∗
         localFramePointsRest (s0.sp - 1200#64) ∗
         savedCells s0 ∗
         tokenInitAt b ∗
         reduceTableAt b ∗
         A.pool ∗
         stackAt (s0.sp - 1200#64) nextChunkCalleeStack)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s
      ((out_ptr ↦ₛ prefix_bytes) ∗
       memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (32 - 2 * i) ∗
       A.live out_ptr 32 1 ∗
       memRegion x.outA chunkSize ∗
       (x.encA ↦₆₄ polyEncoderPolysTag) ∗
       polyListOf A (x.encA + 8#64) polys ∗
       ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
       memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
       (((s0.sp - 1200#64) + 48#64) ↦₆₄ u48) ∗
       (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
       (((s0.sp - 1200#64) + 88#64) ↦₆₄ (x.encA + 8#64)) ∗
       (((s0.sp - 1200#64) + 104#64) ↦₆₄ BitVec.ofNat 64 i) ∗
       (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗
       (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
       (((s0.sp - 1200#64) + 248#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
       localFramePointsRest (s0.sp - 1200#64) ∗
       savedCells s0 ∗
       tokenInitAt b ∗
       reduceTableAt b ∗
       A.pool ∗
       stackAt (s0.sp - 1200#64) nextChunkCalleeStack)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hi16 : i < 16 := by omega
  have hi_len : i < polys.length := by omega
  have hcomp := computeAt_ok b hb A ext hA
  dsimp only [tripleRatchetProgAtExt] at hcomp
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0xfc 136
  clear hA
  rw [polyListOf_split_idx A (x.encA + 8#64) polys i hi_len]
  apply SepWPp.fold (polyOf_unfold A ((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) (polys[i]'hi_len)) (by sep_focus)
  simp only [sepExists_sepConj_left]
  apply sepWPp_exists_left; intro cap
  apply sepWPp_exists_left; intro ptr
  have hpure_pull :
      ∀ (P_c P_p P_l : SepProp) (φ : Prop) (P_body Rest : SepProp),
        (P_c ∗ P_p ∗ P_l ∗ ⌜φ⌝ ∗ P_body) ∗ Rest =
          ⌜φ⌝ ∗ ((P_c ∗ P_p ∗ P_l ∗ P_body) ∗ Rest) := by
    intros; ac_rfl
  rw [hpure_pull]
  apply SepWPp.pure_left; rintro ⟨hlen_cap, hcap_bound, hptr_ne⟩
  rw [polyBufBody_eq_slice_rest A cap ptr (polys[i]'hi_len) hlen_cap]
  have hlen_bound : 2 * (polys[i]'hi_len).coefficients.length + 2 ≤ 2 ^ 63 :=
    polyCoefficients_len_bound_of_cap hlen_cap hcap_bound
  have hfn_off := nextChunk_add_computeAt_off b (Rust.withPanics ext)
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr computeAtName)
  wp_steps 4
  apply SepWP.done (by rw [← hfn_off]; wp_norm_goal) (by wp_norm_lhs)
  rw [stackAt_nextChunkCallee_split_computeAt (s0.sp - 1200#64)]
  have hsp_al : s0.sp - 1200#64 &&& 15#64 = 0#64 := by revert hsp0; bv_bits
  refine call_computeAt_sepWPp hcomp
    (ret_pc := entry + 312#64)
    (x_gf := GF16.new (x.enc.idx.setWidth 16))
    ?_ ?_ ?_ hsp_al ?_ ?_ ?_ ?_ ?_ hlen_bound
    (computeAt_tail_pre_split ptr (polys[i]'hi_len) b (s0.sp - 1200#64) A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    ?_
  · rw [← hfn_off]; wp_norm_goal
  · wp_norm_lhs
  · simpa [arm64_norm, wp_norm] using hsp
  · wp_norm_lhs
  · simpa [arm64_norm, wp_norm] using htr
  · wp_norm_lhs
  · wp_norm_lhs
  · simp [GF16.new, arm64_norm, wp_norm, hx27]
  intro sf1 hpc1 hrun1 hsp1' hcs1 htr1' hx0_1
  rcases hcs1 with ⟨_, _, _, _, _, hx24_cs, _, _, hx27_cs, hx28_cs, _, hvregs_cs⟩
  have hvregs_1 : calleeSavedVRegs sf1 = calleeSavedVRegs s0 := by
    rw [hvregs_cs]; simpa [arm64_norm, wp_norm] using hvregs
  have hx24_1 : sf1.readReg64 .x24 = x.encA := by
    rw [Reg.x24, hx24_cs]; simpa [arm64_norm, wp_norm] using hx24
  have hx27_1 : sf1.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64 := by
    rw [Reg.x27, hx27_cs]; simpa [arm64_norm, wp_norm] using hx27
  have hx28_1 : sf1.readReg64 .x28 = 24#64 := by
    rw [Reg.x28, hx28_cs]; simpa [arm64_norm, wp_norm] using hx28
  rcases ofNat_beq_false_of_lt (a := 2 * i) (b := 32) (by omega) (by omega) with
    ⟨hcmp1_eq, hcmp1_sub, _, _⟩
  rcases ofNat_beq_false_of_lt (a := 2 * i + 1) (b := 32) (by omega) (by omega) with
    ⟨hcmp2_eq, hcmp2_sub, _, _⟩
  rcases ofNat_add_one_beq_16 hi16 with ⟨h16_eq, h16_sub⟩
  have h32_eq : (32#64 : BitVec 64) = BitVec.ofNat 64 32 := rfl
  rw [← h32_eq] at hcmp1_eq hcmp1_sub hcmp2_eq hcmp2_sub
  apply SepWPp.of_sepWP (mid := if rem == 0 then entry + 4484#64 else entry + 296#64)
  apply SepWP.fold (memRegion_split_two_bytes out_ptr i hi16) (by sep_focus)
  apply sepWP_exists_left_sep; intro b0
  apply sepWP_exists_left_sep; intro b1
  wp_steps 22
  have hb0_eq :
      BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 (sf1.readReg64 (Reg.gpr 0#5))) >>> 8 &&& 255#64) =
        BitVec.setWidth 8 ((computeAtPure (polys[i]'hi_len) (GF16.new (x.enc.idx.setWidth 16))).value >>> 8) :=
    ubfx8_trunc8_of_trunc16 hx0_1
  have hb1_eq :
      BitVec.zeroExtend 8 (sf1.readReg64 (Reg.gpr 0#5)) =
        BitVec.setWidth 8 (computeAtPure (polys[i]'hi_len) (GF16.new (x.enc.idx.setWidth 16))).value :=
    trunc8_of_trunc16 hx0_1
  have hb1_eq' :
      BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 (sf1.readReg64 (Reg.gpr 0#5)))) =
        BitVec.setWidth 8 (computeAtPure (polys[i]'hi_len) (GF16.new (x.enc.idx.setWidth 16))).value :=
    trunc8_zext64_trunc32_of_trunc16 hx0_1
  wp_conv_pre => simp only [hb0_eq, hb1_eq, hb1_eq']
  have hfold_bytes :
      (out_ptr ↦ₛ prefix_bytes) ∗
        ((out_ptr + BitVec.ofNat 64 (2 * i)) ↦₈
          BitVec.setWidth 8 ((computeAtPure (polys[i]'hi_len) (GF16.new (x.enc.idx.setWidth 16))).value >>> 8)) ∗
        ((out_ptr + BitVec.ofNat 64 (2 * i + 1)) ↦₈
          BitVec.setWidth 8 (computeAtPure (polys[i]'hi_len) (GF16.new (x.enc.idx.setWidth 16))).value) ⊢
        (out_ptr ↦ₛ (prefix_bytes ++ chunkPolysBytes (x.enc.idx.setWidth 16) polys i 1)) := by
    have h1 : chunkPolysBytes (x.enc.idx.setWidth 16) polys i 1 =
        [BitVec.setWidth 8 ((computeAtPure (polys[i]'hi_len) (GF16.new (x.enc.idx.setWidth 16))).value >>> 8),
         BitVec.setWidth 8 (computeAtPure (polys[i]'hi_len) (GF16.new (x.enc.idx.setWidth 16))).value] := by
      simp [chunkPolysBytes, u16ToBeBytes, hi_len]
    rw [h1]
    exact pointsToBytes_append_two_bytes out_ptr prefix_bytes i hprefix _ _
  have hfold_list :
      polyListOf A (x.encA + 8#64) (polys.take i) ∗
        polyOf A ((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) (polys[i]'hi_len) ∗
        polyListOf A ((x.encA + 8#64) + BitVec.ofNat 64 (24 * (i + 1))) (polys.drop (i + 1)) ⊢
        polyListOf A (x.encA + 8#64) polys := by
    rw [← polyListOf_split_idx A (x.encA + 8#64) polys i hi_len]
    exact Entails.refl _
  have hfold_stack :
      memRegion ((s0.sp - 1200#64) - 17232#64) 12880 ∗
        stackAt (s0.sp - 1200#64) computeAtStack ⊢
        stackAt (s0.sp - 1200#64) nextChunkCalleeStack := by
    rw [← stackAt_nextChunkCallee_split_computeAt (s0.sp - 1200#64)]
    exact Entails.refl _
  apply SepWP.fold hfold_bytes (by sep_focus)
  apply SepWP.fold
    (polyOf_fold A ((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) cap ptr (polys[i]'hi_len)
      ⟨hlen_cap, hcap_bound, hptr_ne⟩)
    (by sep_focus)
  apply SepWP.fold hfold_list (by sep_focus)
  apply SepWP.fold hfold_stack (by sep_focus)
  by_cases hrem0 : rem = 0
  · have hi15 : i = 15 := by omega
    subst hi15; subst hrem0
    wp_steps 1
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.weaken_pre (Entails.of_eq (by simp only [arm64_norm, beq_self_eq_true, ↓reduceIte]; ac_rfl))
      (hnext _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    · wp_norm_goal
    · wp_norm_lhs
    · simpa [arm64_norm, wp_norm] using hsp1'
    · simpa [arm64_norm, wp_norm] using htr1'
    · simpa [arm64_norm, wp_norm] using hvregs_1
    · wp_norm_lhs
    · wp_norm_lhs
    · wp_norm_lhs
    · simpa [arm64_norm, wp_norm] using hx24_1
    · simpa [arm64_norm, wp_norm] using hx27_1
    · simpa [arm64_norm, wp_norm] using hx28_1
  · have hi15 : i ≠ 15 := by omega
    have hi15_beq : (i == 15) = false := beq_eq_false_iff_ne.mpr hi15
    have hrem0_beq : (rem == 0) = false := beq_eq_false_iff_ne.mpr hrem0
    rw [hi15_beq] at h16_eq h16_sub
    wp_steps 3
    apply SepWP.done (by rw [hrem0_beq]; wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.weaken_pre (Entails.of_eq (by rw [hrem0_beq]; simp only [arm64_norm, Bool.false_eq_true, ↓reduceIte]; ac_rfl))
      (hnext _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    · rw [hrem0_beq]; wp_norm_goal
    · wp_norm_lhs
    · simpa [arm64_norm, wp_norm] using hsp1'
    · simpa [arm64_norm, wp_norm] using htr1'
    · simpa [arm64_norm, wp_norm] using hvregs_1
    · wp_norm_lhs
    · wp_norm_lhs
    · wp_norm_lhs
    · simpa [arm64_norm, wp_norm] using hx24_1
    · simpa [arm64_norm, wp_norm] using hx27_1
    · simpa [arm64_norm, wp_norm] using hx28_1

/-! ## 3. Multi-Step Induction for the Polynomial Evaluation Tail Loop -/

theorem polysTailLoop_sepWPp
    (A : RustAlloc) (b : BitVec 64) (ext : String → Option (State → State))
    (hb : b &&& 0xfff#64 = 0#64) (hA : AllocContracts b A ext)
    (x : PolyNextChunkGhost) (polys : List LibsignalSpqrV1.Poly) (hlen_polys : polys.length = 16)
    (out_ptr u48 : BitVec 64) (R : SepProp)
    {Q : State → SepProp → Prop}
    (s0 : State) (hsp0 : s0.sp &&& 0xf#64 = 0#64) :
    ∀ (rem i : Nat) (prefix_bytes : List (BitVec 8)) (s : State),
      i + (rem + 1) = 16 →
      prefix_bytes.length = 2 * i →
      s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 296#64 →
      s.status = .Running →
      s.sp = s0.sp - 1200#64 →
      s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      s.readReg64 .x9 = BitVec.ofNat 64 i →
      s.readReg64 .x19 = x.encA + 8#64 →
      s.readReg64 .x24 = x.encA →
      s.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64 →
      s.readReg64 .x28 = 24#64 →
      (∀ sf : State,
        sf.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4484#64 →
        sf.status = .Running →
        sf.sp = s0.sp - 1200#64 →
        sf.trace = s0.trace →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        sf.readReg64 .x20 = 32#64 →
        sf.readReg64 .x24 = x.encA →
        sf.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64 →
        SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 Reg.lr) sf
          ((out_ptr ↦ₛ (prefix_bytes ++ chunkPolysBytes (x.enc.idx.setWidth 16) polys i (rem + 1))) ∗
           A.live out_ptr 32 1 ∗
           memRegion x.outA chunkSize ∗
           (x.encA ↦₆₄ polyEncoderPolysTag) ∗
           polyListOf A (x.encA + 8#64) polys ∗
           ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
           memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
           (((s0.sp - 1200#64) + 48#64) ↦₆₄ u48) ∗
           (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
           (((s0.sp - 1200#64) + 88#64) ↦₆₄ (x.encA + 8#64)) ∗
           (((s0.sp - 1200#64) + 104#64) ↦₆₄ 15#64) ∗
           (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗
           (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
           (((s0.sp - 1200#64) + 248#64) ↦₆₄ 32#64) ∗
           localFramePointsRest (s0.sp - 1200#64) ∗
           savedCells s0 ∗
           tokenInitAt b ∗
           reduceTableAt b ∗
           A.pool ∗
           stackAt (s0.sp - 1200#64) nextChunkCalleeStack)
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s
        ((out_ptr ↦ₛ prefix_bytes) ∗
         memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (32 - 2 * i) ∗
         A.live out_ptr 32 1 ∗
         memRegion x.outA chunkSize ∗
         (x.encA ↦₆₄ polyEncoderPolysTag) ∗
         polyListOf A (x.encA + 8#64) polys ∗
         ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
         memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
         (((s0.sp - 1200#64) + 48#64) ↦₆₄ u48) ∗
         (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
         (((s0.sp - 1200#64) + 88#64) ↦₆₄ (x.encA + 8#64)) ∗
         (((s0.sp - 1200#64) + 104#64) ↦₆₄ BitVec.ofNat 64 i) ∗
         (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗
         (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
         (((s0.sp - 1200#64) + 248#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
         localFramePointsRest (s0.sp - 1200#64) ∗
         savedCells s0 ∗
         tokenInitAt b ∗
         reduceTableAt b ∗
         A.pool ∗
         stackAt (s0.sp - 1200#64) nextChunkCalleeStack)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))
  | 0, i, prefix_bytes, s, hrem_eq, hprefix, hpc, hrun, hsp, htr, hvregs, hx9, hx19, hx24, hx27, hx28, hnext => by
    have hi : i = 15 := by omega
    subst hi
    refine polysTailLoop_step_sepWPp A b ext hb hA x polys hlen_polys out_ptr u48 prefix_bytes R
      15 0 hrem_eq hprefix s0 s hsp0 hpc hrun hsp htr hvregs hx9 hx19 hx24 hx27 hx28 ?_
    intro sf hpcf hrunf hspf htrf hvregsf _ _ hx20f hx24f hx27f _
    simp only [beq_self_eq_true, ↓reduceIte] at hpcf ⊢
    have hrem_zero : 32 - 2 * (15 + 1) = 0 := rfl
    have h2_16 : BitVec.ofNat 64 (2 * (15 + 1)) = 32#64 := rfl
    have h15 : BitVec.ofNat 64 15 = 15#64 := rfl
    rw [hrem_zero, ProofLib.memRegion_zero, h2_16, h15]
    rw [h2_16] at hx20f
    refine SepWPp.weaken_pre (Entails.of_eq ?_)
      (hnext sf hpcf hrunf hspf htrf hvregsf hx20f hx24f hx27f)
    simp only [emp_sepConj, sepConj_emp]
  | rem + 1, i, prefix_bytes, s, hrem_eq, hprefix, hpc, hrun, hsp, htr, hvregs, hx9, hx19, hx24, hx27, hx28, hnext => by
    have hi_len : i < polys.length := by omega
    refine polysTailLoop_step_sepWPp A b ext hb hA x polys hlen_polys out_ptr u48 prefix_bytes R
      i (rem + 1) hrem_eq hprefix s0 s hsp0 hpc hrun hsp htr hvregs hx9 hx19 hx24 hx27 hx28 ?_
    intro sf hpcf hrunf hspf htrf hvregsf hx9f hx19f _ hx24f hx27f hx28f
    have hne : ((rem + 1) == 0) = false := rfl
    simp only [hne, Bool.false_eq_true, ↓reduceIte] at hpcf ⊢
    have hrem' : (i + 1) + (rem + 1) = 16 := by omega
    have hprefix' : (prefix_bytes ++ chunkPolysBytes (x.enc.idx.setWidth 16) polys i 1).length = 2 * (i + 1) := by
      simp [List.length_append, hprefix, chunkPolysBytes, u16ToBeBytes, hi_len]; omega
    refine polysTailLoop_sepWPp A b ext hb hA x polys hlen_polys out_ptr u48 R s0 hsp0
      rem (i + 1) (prefix_bytes ++ chunkPolysBytes (x.enc.idx.setWidth 16) polys i 1) sf
      hrem' hprefix' hpcf hrunf hspf htrf hvregsf hx9f hx19f hx24f hx27f hx28f ?_
    intro sf2 hpcf2 hrunf2 hspf2 htrf2 hvregsf2 hx20f2 hx24f2 hx27f2
    have happ :
        (prefix_bytes ++ chunkPolysBytes (x.enc.idx.setWidth 16) polys i 1) ++
          chunkPolysBytes (x.enc.idx.setWidth 16) polys (i + 1) (rem + 1) =
        prefix_bytes ++ chunkPolysBytes (x.enc.idx.setWidth 16) polys i (rem + 1 + 1) := by
      have h1 : 1 + (rem + 1) = rem + 1 + 1 := by omega
      rw [List.append_assoc, ← chunkPolysBytes_add (x.enc.idx.setWidth 16) polys 1 i (rem + 1), h1]
    rw [happ]
    exact hnext sf2 hpcf2 hrunf2 hspf2 htrf2 hvregsf2 hx20f2 hx24f2 hx27f2

end CryptoVerification.SpqrV1.Poly.NextChunk

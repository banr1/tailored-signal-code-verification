/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangeComplete.Defs
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.PolyPart1CodeSym
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

/-!
# `<Poly>::lagrange_interpolate_complete`: Binary Verification

Verifies `<spqr::encoding::polynomial::Poly>::lagrange_interpolate_complete` (`0x61ec4`,
Block `373`) against `lagrangeCompleteSpec` and `lagrangeCompletePlacedSpec`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.LagrangeComplete

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.DivImpl
open CryptoVerification.SpqrV1.Poly

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

attribute [local wp_norm] zeroExtend_16_truncate_32_64

gen_decodes libsignalSessionCode_tree lagrangeCompleteBin [0x5cacc → 0x5cd7c]

theorem fnAddr_adrp_61f00 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr lagrangeCompleteName + 60#64) &&&
      0xfffffffffffff000#64) = b + 0x5c000#64 := by
  rw [Program.fnAddr_rebase, lagrangeComplete_fnOff]
  revert hb; bv_bits

theorem fnAddr_adrp_61f04 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr lagrangeCompleteName + 64#64) &&&
      0xfffffffffffff000#64) = b + 0x5c000#64 := by
  rw [Program.fnAddr_rebase, lagrangeComplete_fnOff]
  revert hb; bv_bits

theorem fnAddr_adrp_61f14 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr lagrangeCompleteName + 80#64) &&&
      0xfffffffffffff000#64) = b + 0x5c000#64 := by
  rw [Program.fnAddr_rebase, lagrangeComplete_fnOff]
  revert hb; bv_bits

theorem fnAddr_adrp_61ff4 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr lagrangeCompleteName + 304#64) &&&
      0xfffffffffffff000#64) = b + 0x5c000#64 := by
  rw [Program.fnAddr_rebase, lagrangeComplete_fnOff]
  revert hb; bv_bits

/-! ## Loop 1 (`0x61f18..0x61fc4`, offset `+84..+256`): `lagrangeDenominator` -/

theorem unacceleratedMul_at_lagrangeComplete (b : BitVec 64) (ext : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr lagrangeCompleteName + BitVec.ofNat 64 7648)
      (unacceleratedMulSpec b) :=
  sub_ok_at_of_fnAddr (unacceleratedMul_ok b ext) lagrangeCompleteName 7648
    (by rw [lagrangeComplete_fnOff, unacceleratedMul_fnOff])

set_option maxHeartbeats 1600000 in
theorem denomLoop_sepWP (b : BitVec 64) (ext : String → Option (State → State))
    (hb : b &&& 0xfff#64 = 0#64)
    (ptsPtr : BitVec 64) (pts : List Pt) (hpts_len : 4 * pts.length < 2 ^ 64)
    (i : Nat) (hi : i < pts.length)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop) :
    ∀ (rem j : Nat) (_hrem : j + rem = pts.length) (acc : GF16)
      (s : State) (F : SepProp),
      s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr lagrangeCompleteName + 84#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      BitVec.truncate 16 (s.readReg64 .x0) = acc.value →
      s.readReg64 .x19 = ptsPtr + BitVec.ofNat 64 (4 * j) →
      s.readReg64 .x24 = b + bv% (ls_xref% 0x5e628 0x5e62c) →
      s.readReg64 .x26 = ptsPtr + BitVec.ofNat 64 (4 * i) →
      s.readReg64 .x27 = b + bv% (page% (ls_xref% 0x5e638 0x5e63c)) →
      s.readReg64 .x28 = ptsPtr + BitVec.ofNat 64 (4 * pts.length) →
      (∀ (sf : State),
        sf.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr lagrangeCompleteName + 256#64 →
        sf.status = .Running →
        sf.sp = s.sp →
        sf.trace = s.trace →
        BitVec.truncate 16 (sf.readReg64 .x0) =
          ((pts.drop j).foldl (denomStep (pts[i]'hi).x) acc).value →
        sf.readReg64 .x20 = s.readReg64 .x20 →
        sf.readReg64 .x22 = s.readReg64 .x22 →
        sf.readReg64 .x24 = b + bv% (ls_xref% 0x5e628 0x5e62c) →
        sf.readReg64 .x25 = s.readReg64 .x25 →
        sf.readReg64 .x26 = ptsPtr + BitVec.ofNat 64 (4 * i) →
        sf.readReg64 .x27 = b + bv% (page% (ls_xref% 0x5e638 0x5e63c)) →
        sf.readReg64 .x28 = ptsPtr + BitVec.ofNat 64 (4 * pts.length) →
        sf.readReg64 .x29 = s.readReg64 .x29 →
        calleeSavedVRegs sf = calleeSavedVRegs s →
        SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret_pc sf
          (ptSliceAt ptsPtr pts ∗ tokenInitAt b ∗ reduceTableAt b ∗ F) Q) →
      SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret_pc s
        (ptSliceAt ptsPtr pts ∗ tokenInitAt b ∗ reduceTableAt b ∗ F) Q := by
  intro rem
  induction rem with
  | zero =>
    intro j hrem acc s F hpc hrun hsp_align hx0 hx19 hx24 hx26 hx27 hx28 hnext
    have hj_eq : j = pts.length := by omega
    subst hj_eq
    have hfn : libsignalSessionCode.fnOff lagrangeCompleteName = 0x5cacc := lagrangeComplete_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode lagrangeCompleteBin b
      (Rust.withPanics ext) hfn 0x5cacc 0x54 8
    clear hfn
    generalize_entry hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr lagrangeCompleteName = entry
    examples_hide_fetches
    wp_steps 2
    simp only [List.drop_length, List.foldl_nil] at hnext
    exact hnext _ (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by simpa [arm64_norm] using hx0)
      (by wp_norm_lhs) (by wp_norm_lhs)
      (by simpa [arm64_norm] using hx24)
      (by wp_norm_lhs)
      (by simpa [arm64_norm] using hx26)
      (by simpa [arm64_norm] using hx27)
      (by simpa [arm64_norm] using hx28)
      (by wp_norm_lhs)
      (by wp_norm_lhs)
  | succ rem' ih =>
    intro j hrem acc s F hpc hrun hsp_align hx0 hx19 hx24 hx26 hx27 hx28 hnext
    have hj : j < pts.length := by omega
    have hdrop : pts.drop j = (pts[j]'hj) :: pts.drop (j + 1) := List.drop_eq_getElem_cons hj
    have hmul : subroutine_ok (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr lagrangeCompleteName + BitVec.ofNat 64 7648)
        (unacceleratedMulSpec b) := unacceleratedMul_at_lagrangeComplete b ext
    have hfn : libsignalSessionCode.fnOff lagrangeCompleteName = 0x5cacc := lagrangeComplete_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode lagrangeCompleteBin b
      (Rust.withPanics ext) hfn 0x5cacc 0x54 48
    code_fetches_range CryptoVerification.libsignalSessionCode lagrangeCompleteBin b
      (Rust.withPanics ext) hfn 0x5cacc 0xf8 8
    dsimp only [tripleRatchetProgAtExt] at hmul
    clear hfn
    have halign_bd8 := aligned_86bd8 b hb
    generalize_entry hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr lagrangeCompleteName = entry
    examples_hide_fetches
    rcases ptr_sub_four_mul_ne_zero ptsPtr hj hpts_len with ⟨hne, hne'⟩
    wp_steps 2
    wp_simp_pre [ptSliceAt_focus_x hj ptsPtr]
    wp_steps 1
    wp_conv_pre =>
      rw [← sepConj_assoc, ← ptSliceAt_focus_x hj ptsPtr, ptSliceAt_focus_x hi ptsPtr, sepConj_assoc]
    wp_steps 1
    wp_conv_pre =>
      rw [← sepConj_assoc, ← ptSliceAt_focus_x hi ptsPtr]
    wp_steps 1
    cases hpx : ((pts[i]'hi).x == (pts[j]'hj).x) with
    | false =>
      -- Non-diagonal point (`pi.x != pj.x`): multiply denominator by `pi.x ^ pj.x`
      have hval_ne : (pts[i]'hi).x.value ≠ (pts[j]'hj).x.value := by
        intro heq
        have htrue : ((pts[i]'hi).x == (pts[j]'hj).x) = true := by
          rw [gf16_beq_iff, beq_iff_eq]
          exact heq
        rw [hpx] at htrue
        contradiction
      rcases cmp32_zext16_ne_zero _ _ hval_ne with ⟨hcmp1, hcmp2, hcmp3, hcmp4⟩
      wp_steps 1
      wp_simp_pre [tokenInitAt]
      apply step_ldar32
      · wp_norm_lhs
      · wp_norm_lhs
      · wp_assumption
      · wp_norm_lhs
      · wp_norm_lhs
      · exact halign_bd8
      · wp_sep_access
      · wp_norm_lhs
      wp_steps 6
      apply SepWP.fold (tokenInitAt_fold b) (by sep_focus)
      wp_call hmul
      wp_steps 1
      wp_conv_pre => rw [perm_denom_pre]
      apply ih (j + 1) (by omega) (GF16.mul acc (GF16.sub (pts[i]'hi).x (pts[j]'hj).x))
      · wp_norm_lhs
      · wp_norm_lhs
      · simpa [arm64_norm, wp_norm, hsp_sf] using hsp_align
      · simp only [arm64_norm, wp_norm, h_10]
        have heor :
            BitVec.truncate 16 (BitVec.zeroExtend 64 (pts[j]'hj).x.value ^^^ BitVec.zeroExtend 64 (pts[i]'hi).x.value) =
              (GF16.sub (pts[i]'hi).x (pts[j]'hj).x).value := by
          change BitVec.truncate 16 (BitVec.zeroExtend 64 (pts[j]'hj).x.value ^^^ BitVec.zeroExtend 64 (pts[i]'hi).x.value) =
            (pts[i]'hi).x.value ^^^ (pts[j]'hj).x.value
          ext k hk
          simp [Bool.xor_comm]
        rw [heor]
        rfl
      · simp only [arm64_norm, wp_norm, h]
        exact ptr_add_four_step ptsPtr j
      · simpa [arm64_norm, wp_norm, h_5] using hx24
      · simpa [arm64_norm, wp_norm, h_7] using hx26
      · simpa [arm64_norm, wp_norm, h_8] using hx27
      · simpa [arm64_norm, wp_norm, h_9] using hx28
      · intro sf' hpc_f hrun_f hsp_f htr_f hx0_f hx20_f hx22_f hx24_f hx25_f hx26_f hx27_f hx28_f hx29_f hvregs_f
        refine hnext sf' hpc_f hrun_f ?_ ?_ ?_ ?_ ?_ hx24_f ?_ hx26_f hx27_f hx28_f ?_ ?_
        · simpa [arm64_norm, wp_norm, hsp_sf] using hsp_f
        · simpa [arm64_norm, wp_norm, hpost] using htr_f
        · rw [hdrop, List.foldl_cons, denomStep]
          simp only [hpx, Bool.false_eq_true, ↓reduceIte]
          exact hx0_f
        · simpa [arm64_norm, wp_norm, h_1] using hx20_f
        · simpa [arm64_norm, wp_norm, h_3] using hx22_f
        · simpa [arm64_norm, wp_norm, h_6] using hx25_f
        · simpa [arm64_norm, wp_norm, hcs_sf] using hx29_f
        · simpa [arm64_norm, wp_norm, hvregs] using hvregs_f
    | true =>
      -- Diagonal point (`pi.x == pj.x`): skip factor
      have hval_eq : (pts[i]'hi).x.value = (pts[j]'hj).x.value := by
        rw [gf16_beq_iff, beq_iff_eq] at hpx
        exact hpx
      rcases cmp32_zext16_eq_zero _ _ hval_eq with ⟨hcmp1, hcmp2, hcmp3, hcmp4⟩
      wp_steps 1
      apply ih (j + 1) (by omega) acc
      · wp_norm_lhs
      · wp_norm_lhs
      · simpa [arm64_norm, wp_norm] using hsp_align
      · simpa [arm64_norm, wp_norm] using hx0
      · simp only [arm64_norm, wp_norm]
        exact ptr_add_four_step ptsPtr j
      · simpa [arm64_norm, wp_norm] using hx24
      · simpa [arm64_norm, wp_norm] using hx26
      · simpa [arm64_norm, wp_norm] using hx27
      · simpa [arm64_norm, wp_norm] using hx28
      · intro sf' hpc_f hrun_f hsp_f htr_f hx0_f hx20_f hx22_f hx24_f hx25_f hx26_f hx27_f hx28_f hx29_f hvregs_f
        refine hnext sf' hpc_f hrun_f ?_ ?_ ?_ ?_ ?_ hx24_f ?_ hx26_f hx27_f hx28_f ?_ ?_
        · simpa [arm64_norm, wp_norm] using hsp_f
        · simpa [arm64_norm, wp_norm] using htr_f
        · rw [hdrop, List.foldl_cons, denomStep]
          simp only [hpx, ↓reduceIte]
          exact hx0_f
        · simpa [arm64_norm, wp_norm] using hx20_f
        · simpa [arm64_norm, wp_norm] using hx22_f
        · simpa [arm64_norm, wp_norm] using hx25_f
        · simpa [arm64_norm, wp_norm] using hx29_f
        · simpa [arm64_norm, wp_norm] using hvregs_f

/-! ## Loop 2 (`0x62024..0x62020`, offset `+352..+348`): `lagrangeCompleteDivLoop` -/

@[local arm64_norm, local wp_norm]
private theorem ptr_sub_two_step_norm (ptr : BitVec 64) (rem : Nat) :
    ptr + BitVec.ofNat 64 (2 * (rem + 1)) + 0xfffffffffffffffe#64 =
      ptr + BitVec.ofNat 64 (2 * rem) :=
  ptr_sub_two_step ptr rem

@[local arm64_norm, local wp_norm]
private theorem ptr_sub_two_step_norm' (ptr : BitVec 64) (rem : Nat) :
    ptr + BitVec.ofNat 64 (2 * (rem + 1)) - 2#64 =
      ptr + BitVec.ofNat 64 (2 * rem) := by
  have h1 : BitVec.ofNat 64 (2 * (rem + 1)) = BitVec.ofNat 64 (2 * rem) + 2#64 := by
    rw [show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, ← BitVec.ofNat_add]
    congr 1
  rw [h1, ← BitVec.add_assoc, BitVec.add_sub_cancel]

@[local arm64_norm, local wp_norm]
private theorem truncate16_eor_zext32 (u : BitVec 16) (v : BitVec 64) :
    BitVec.truncate 16
      (BitVec.zeroExtend 64
        (BitVec.zeroExtend 32 (BitVec.zeroExtend 64 u) ^^^
         BitVec.zeroExtend 32 (BitVec.zeroExtend 64 (BitVec.zeroExtend 32 v)))) =
      u ^^^ BitVec.truncate 16 v := by
  ext i hi
  simp

@[local arm64_norm, local wp_norm]
private theorem truncate16_eor_zext_truncate32 (u : BitVec 16) (v : BitVec 64) :
    BitVec.truncate 16
      (BitVec.zeroExtend 64
        (BitVec.zeroExtend 32 (BitVec.zeroExtend 64 u) ^^^
         BitVec.zeroExtend 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 v)))) =
      u ^^^ BitVec.truncate 16 v := by
  ext i hi
  simp

@[local arm64_norm, local wp_norm]
private theorem truncate16_eor_zext64_truncate32 (u : BitVec 16) (v : BitVec 64) :
    BitVec.truncate 16 (BitVec.zeroExtend 64 u ^^^ BitVec.zeroExtend 64 (BitVec.truncate 32 v)) =
      u ^^^ BitVec.truncate 16 v := by
  ext i hi
  simp

set_option maxHeartbeats 1600000 in
theorem divLoop_sepWP (b : BitVec 64) (ext : String → Option (State → State))
    (hb : b &&& 0xfff#64 = 0#64)
    (coeffsPtr : BitVec 64) (pix scale : GF16)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop) :
    ∀ (rem : Nat) (cs : List GF16) (_hrem : rem + 1 < cs.length) (_hlen : 2 * cs.length < 2 ^ 64)
      (s : State) (F : SepProp),
      s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr lagrangeCompleteName + 352#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      BitVec.truncate 16 (s.readReg64 .x19) = scale.value →
      BitVec.truncate 16 (s.readReg64 .x20) = pix.value →
      s.readReg64 .x21 = coeffsPtr + BitVec.ofNat 64 (2 * (rem + 1)) →
      s.readReg64 .x22 = BitVec.ofNat 64 (rem + 1) →
      s.readReg64 .x24 = b + bv% (ls_xref% 0x5e628 0x5e62c) →
      s.readReg64 .x27 = b + bv% (page% (ls_xref% 0x5e638 0x5e63c)) →
      (∀ (sf : State),
        sf.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr lagrangeCompleteName + 656#64 →
        sf.status = .Running →
        sf.sp = s.sp →
        sf.trace = s.trace →
        calleeSavedVRegs sf = calleeSavedVRegs s →
        SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret_pc sf
          (gf16SliceAt coeffsPtr (divLoopPure pix scale (rem + 1) cs) ∗
           tokenInitAt b ∗ reduceTableAt b ∗ F) Q) →
      SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret_pc s
        (gf16SliceAt coeffsPtr cs ∗ tokenInitAt b ∗ reduceTableAt b ∗ F) Q := by
  intro rem
  induction rem with
  | zero =>
    intro cs hrem hlen s F hpc hrun hsp_align hx19 hx20 hx21 hx22 hx24 hx27 hnext
    have hrem1 : 1 < cs.length := hrem
    have hmul : subroutine_ok (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr lagrangeCompleteName + BitVec.ofNat 64 7648)
        (unacceleratedMulSpec b) := unacceleratedMul_at_lagrangeComplete b ext
    have hfn : libsignalSessionCode.fnOff lagrangeCompleteName = 0x5cacc := lagrangeComplete_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode lagrangeCompleteBin b
      (Rust.withPanics ext) hfn 0x5cacc 0x144 216
    dsimp only [tripleRatchetProgAtExt] at hmul; clear hfn
    have halign_bd8 := aligned_86bd8 b hb
    generalize_entry hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr lagrangeCompleteName = entry
    examples_hide_fetches
    wp_simp_pre [gf16SliceAt_focus hrem1 coeffsPtr, tokenInitAt]
    wp_steps 1
    apply step_ldar32 (by wp_norm_lhs) (by wp_norm_lhs) (by wp_assumption)
      (by wp_norm_lhs) (by wp_norm_lhs) halign_bd8 (by wp_sep_access) (by wp_norm_lhs)
    wp_steps 6
    apply SepWP.fold (tokenInitAt_fold b) (by sep_focus)
    wp_call hmul
    wp_steps 1
    wp_simp_pre [tokenInitAt]
    apply step_ldar32 (by wp_norm_lhs) (by wp_norm_lhs) (by wp_assumption)
      (by wp_norm_lhs) (by wp_norm_lhs) halign_bd8 (by wp_sep_access) (by wp_norm_lhs)
    wp_steps 7
    apply SepWP.fold (tokenInitAt_fold b) (by sep_focus)
    wp_call hmul
    wp_steps 1
    have hrem0 : 0 < (cs.set 1 ⟨unaccelerated.mul (cs[1]'hrem1).value scale.value⟩).length := by
      simp [List.length_set]; omega
    wp_conv_pre => rw [gf16SliceAt_update_one_assoc hrem1 coeffsPtr, gf16SliceAt_focus_assoc hrem0 coeffsPtr]
    wp_steps 5
    have hlist :
        (cs.set 1 ⟨unaccelerated.mul (cs[1]'hrem1).value scale.value⟩).set 0
          ⟨((cs.set 1 ⟨unaccelerated.mul (cs[1]'hrem1).value scale.value⟩)[0]'hrem0).value ^^^
            unaccelerated.mul (cs[1]'hrem1).value pix.value⟩ =
        divLoopPure pix scale (0 + 1) cs := by
      simpa [divLoopPure] using divLoop_step_eq pix scale 0 cs hrem
    wp_conv_pre => rw [gf16SliceAt_update_assoc hrem0 coeffsPtr, hlist, perm_div_pre]
    exact hnext _ (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by simp [arm64_norm, wp_norm, hvregs_1, hvregs])
  | succ rem' ih =>
    intro cs hrem hlen s F hpc hrun hsp_align hx19 hx20 hx21 hx22 hx24 hx27 hnext
    have hmul : subroutine_ok (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr lagrangeCompleteName + BitVec.ofNat 64 7648)
        (unacceleratedMulSpec b) := unacceleratedMul_at_lagrangeComplete b ext
    have hfn : libsignalSessionCode.fnOff lagrangeCompleteName = 0x5cacc := lagrangeComplete_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode lagrangeCompleteBin b
      (Rust.withPanics ext) hfn 0x5cacc 0x144 216
    dsimp only [tripleRatchetProgAtExt] at hmul; clear hfn
    have halign_bd8 := aligned_86bd8 b hb
    generalize_entry hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr lagrangeCompleteName = entry
    examples_hide_fetches
    rcases bv_sub_one_succ rem' (by omega) with ⟨hsub1, hsub2, hsub3⟩
    wp_simp_pre [gf16SliceAt_focus hrem coeffsPtr, tokenInitAt]
    wp_steps 1
    apply step_ldar32 (by wp_norm_lhs) (by wp_norm_lhs) (by wp_assumption)
      (by wp_norm_lhs) (by wp_norm_lhs) halign_bd8 (by wp_sep_access) (by wp_norm_lhs)
    wp_steps 6
    apply SepWP.fold (tokenInitAt_fold b) (by sep_focus)
    wp_call hmul
    wp_steps 1
    wp_simp_pre [tokenInitAt]
    apply step_ldar32 (by wp_norm_lhs) (by wp_norm_lhs) (by wp_assumption)
      (by wp_norm_lhs) (by wp_norm_lhs) halign_bd8 (by wp_sep_access) (by wp_norm_lhs)
    wp_steps 7
    apply SepWP.fold (tokenInitAt_fold b) (by sep_focus)
    wp_call hmul
    wp_steps 1
    have hrem1 : rem' + 1 < (cs.set (rem' + 1 + 1) ⟨unaccelerated.mul (cs[rem' + 1 + 1]'hrem).value scale.value⟩).length := by
      simp [List.length_set]; omega
    wp_conv_pre => rw [gf16SliceAt_update_assoc hrem coeffsPtr, gf16SliceAt_focus_assoc hrem1 coeffsPtr]
    wp_steps 5
    let cs_next :=
      let cIdx := cs[rem' + 1 + 1]?.getD GF16.ZERO
      let cPrev := cs[rem' + 1]?.getD GF16.ZERO
      let negativeDelta := GF16.mul cIdx pix
      let coeffs1 := cs.set (rem' + 1 + 1) (GF16.mul cIdx scale)
      coeffs1.set (rem' + 1) (GF16.add cPrev negativeDelta)
    have hlist :
        (cs.set (rem' + 1 + 1) ⟨unaccelerated.mul (cs[rem' + 1 + 1]'hrem).value scale.value⟩).set (rem' + 1)
          ⟨((cs.set (rem' + 1 + 1) ⟨unaccelerated.mul (cs[rem' + 1 + 1]'hrem).value scale.value⟩)[rem' + 1]'hrem1).value ^^^
            unaccelerated.mul (cs[rem' + 1 + 1]'hrem).value pix.value⟩ =
        cs_next := divLoop_step_eq pix scale (rem' + 1) cs hrem
    wp_conv_pre => rw [gf16SliceAt_update_assoc hrem1 coeffsPtr, hlist, perm_div_pre]
    apply ih cs_next (by simp [cs_next, List.length_set]; omega) (by simp [cs_next, List.length_set]; omega)
    · wp_norm_lhs
    · wp_norm_lhs
    · simpa [arm64_norm, wp_norm, hsp_sf_1, hsp_sf] using hsp_align
    · simpa [arm64_norm, wp_norm, h_11, h] using hx19
    · simpa [arm64_norm, wp_norm, h_12, h_1] using hx20
    · wp_norm_lhs
    · simp [arm64_norm, wp_norm]
    · simpa [arm64_norm, wp_norm, h_16, h_5] using hx24
    · simpa [arm64_norm, wp_norm, h_19, h_8] using hx27
    · intro sf' hpc_f hrun_f hsp_f htr_f hvregs_f
      exact hnext sf' hpc_f hrun_f
        (by simpa [arm64_norm, wp_norm, hsp_sf_1, hsp_sf] using hsp_f)
        (by simpa [arm64_norm, wp_norm, hpost_1, hpost] using htr_f)
        (by simpa [arm64_norm, wp_norm, hvregs_1, hvregs] using hvregs_f)

/-! ## Epilogue (`0x62154..0x62170`, offset `+656..+688`) -/

set_option maxHeartbeats 800000 in
theorem epilogue_sepWP (b : BitVec 64) (ext : String → Option (State → State))
    (x : LagrangeCompleteArgs) (s0 s : State) (R : SepProp)
    (s112 s104 : BitVec 16)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr lagrangeCompleteName + 656#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 128#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 .lr) s
      (gf16SliceAt x.coeffsPtr (lagrangeCompletePure x.self x.pts x.i).coefficients ∗
       ptSliceAt x.ptsPtr x.pts ∗ tokenInitAt b ∗ reduceTableAt b ∗
       stackAt (s0.sp - 128#64) divImplStack ∗ memRegion (s0.sp - 128#64) 16 ∗
       ((s0.sp - 112#64) ↦₁₆ s112) ∗ memRegion (s0.sp - 110#64) 6 ∗
       ((s0.sp - 104#64) ↦₁₆ s104) ∗ memRegion (s0.sp - 102#64) 6 ∗
       ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
       ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗ R)
      (fun sf P_f => (sf.mem ⊨ P_f) →
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (sf.mem ⊨ (lagrangeCompleteSpec b).post x s0 sf ∗ R)) := by
  have hfn : libsignalSessionCode.fnOff lagrangeCompleteName = 0x5cacc := lagrangeComplete_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode lagrangeCompleteBin b
    (Rust.withPanics ext) hfn 0x5cacc 0x290 32
  clear hfn
  generalize_entry hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr lagrangeCompleteName = entry
  examples_hide_fetches
  wp_steps
  refine SepWP.fold
    (stackAt_lagrangeComplete_merge s0.sp (s0.sp - 128#64) s112 s104
      (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
      (s0.readReg64 (Reg.gpr 28#5)) (s0.readReg64 (Reg.gpr 27#5))
      (s0.readReg64 (Reg.gpr 26#5)) (s0.readReg64 (Reg.gpr 25#5))
      (s0.readReg64 (Reg.gpr 24#5)) (s0.readReg64 (Reg.gpr 23#5))
      (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
      (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5)) rfl)
    (by sep_focus) ?_
  dsimp only [lagrangeCompleteSpec]
  wp_done

/-! ## Top-level theorem: `lagrangeComplete_ok` -/

theorem divImpl_at_lagrangeComplete (b : BitVec 64) (ext : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr lagrangeCompleteName - BitVec.ofNat 64 52212)
      (divImplSpec b) := by
  have h := divImpl_ok b ext
  have haddr :
      (tripleRatchetProgAtExt b ext).fnAddr divImplName =
        (tripleRatchetProgAtExt b ext).fnAddr lagrangeCompleteName - BitVec.ofNat 64 52212 := by
    simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, divImpl_fnOff, lagrangeComplete_fnOff]
    bv_arith
  rwa [← haddr]

private theorem ule_of_lt_pts {i n : Nat} (hi : i < n) (hn : 4 * n < 2 ^ 64) :
    BitVec.ule (BitVec.ofNat 64 n) (BitVec.ofNat 64 i) = false := by
  simp only [BitVec.ule, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : i < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
    decide_eq_false_iff_not]
  omega

private theorem perm_to_denom (C P T R F : SepProp) :
    C ∗ P ∗ T ∗ R ∗ F = P ∗ T ∗ R ∗ C ∗ F := by
  rw [← sepConj_assoc C, sepConj_comm C P, sepConj_assoc P,
      ← sepConj_assoc C, sepConj_comm C T, sepConj_assoc T,
      ← sepConj_assoc C, sepConj_comm C R, sepConj_assoc R]

@[local arm64_norm, local wp_norm]
private theorem lsl_two_eq_four_mul_norm (n : Nat) :
    (BitVec.ofNat 64 n) <<< 2#64 = BitVec.ofNat 64 (4 * n) := lsl_two_eq_four_mul n

@[local arm64_norm, local wp_norm]
private theorem lsl_two_nat_eq_four_mul_norm (n : Nat) :
    (BitVec.ofNat 64 n) <<< 2 = BitVec.ofNat 64 (4 * n) := lsl_two_eq_four_mul n

@[local arm64_norm, local wp_norm]
private theorem lsl_one_eq_two_mul_norm (n : Nat) :
    (BitVec.ofNat 64 n) <<< 1#64 = BitVec.ofNat 64 (2 * n) := lsl_one_eq_two_mul n

@[local arm64_norm, local wp_norm]
private theorem lsl_one_nat_eq_two_mul_norm (n : Nat) :
    (BitVec.ofNat 64 n) <<< 1 = BitVec.ofNat 64 (2 * n) := lsl_one_eq_two_mul n

private theorem perm_to_div (S1 S2 T R St P C F : SepProp) :
    S1 ∗ S2 ∗ T ∗ R ∗ St ∗ P ∗ C ∗ F =
      C ∗ T ∗ R ∗ S1 ∗ S2 ∗ St ∗ P ∗ F := by
  rw [← sepConj_assoc P C F, sepConj_comm P C, sepConj_assoc C P F,
      ← sepConj_assoc St C, sepConj_comm St C, sepConj_assoc C St,
      ← sepConj_assoc R C, sepConj_comm R C, sepConj_assoc C R,
      ← sepConj_assoc T C, sepConj_comm T C, sepConj_assoc C T,
      ← sepConj_assoc S2 C, sepConj_comm S2 C, sepConj_assoc C S2,
      ← sepConj_assoc S1 C, sepConj_comm S1 C, sepConj_assoc C S1,
      ← sepConj_assoc S2 T, sepConj_comm S2 T, sepConj_assoc T S2,
      ← sepConj_assoc S1 T, sepConj_comm S1 T, sepConj_assoc T S1,
      ← sepConj_assoc S2 R, sepConj_comm S2 R, sepConj_assoc R S2,
      ← sepConj_assoc S1 R, sepConj_comm S1 R, sepConj_assoc R S1]

private theorem truncate16_zext64_truncate32 (v : BitVec 64) :
    BitVec.truncate 16 (BitVec.zeroExtend 64 (BitVec.truncate 32 v)) =
      BitVec.truncate 16 v := by
  ext i hi; simp

set_option maxHeartbeats 1600000 in
theorem lagrangeComplete_ok (b : BitVec 64) (ext : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr lagrangeCompleteName)
      (lagrangeCompleteSpec b) := by
  have hfn : libsignalSessionCode.fnOff lagrangeCompleteName = 0x5cacc := lagrangeComplete_fnOff
  code_fetches CryptoVerification.libsignalSessionCode lagrangeCompleteBin b
    (Rust.withPanics ext) hfn 0x5cacc 84
  code_fetches_range CryptoVerification.libsignalSessionCode lagrangeCompleteBin b
    (Rust.withPanics ext) hfn 0x5cacc 0x100 92
  dsimp only [tripleRatchetProgAtExt]; clear hfn
  simp only [lagrangeCompleteSpec]
  wp_init x s0
  have hpc' : s0.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr lagrangeCompleteName := by
    rw [Program.fnAddr_rebase, lagrangeComplete_fnOff]; exact hpc
  clear hpc
  have hadrp1 := fnAddr_adrp_61f00 (H := Rust.withPanics ext) h_1
  have hadrp2 := fnAddr_adrp_61f04 (H := Rust.withPanics ext) h_1
  have hadrp3 := fnAddr_adrp_61f14 (H := Rust.withPanics ext) h_1
  have hadrp4 := fnAddr_adrp_61ff4 (H := Rust.withPanics ext) h_1
  have hule_i : BitVec.ule (BitVec.ofNat 64 x.pts.length) (BitVec.ofNat 64 x.i) = false :=
    ule_of_lt_pts h_7 h
  generalize_entry hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr lagrangeCompleteName = entry
  examples_hide_fetches
  wp_simp_pre [stackAt_lagrangeComplete_split]
  wp_pull_exists
  wp_steps 21
  wp_conv_pre => rw [perm_to_denom]
  rw [← hentry]
  apply denomLoop_sepWP b ext h_1 x.ptsPtr x.pts h x.i h_7 (s0.readReg64 .lr) _
    x.pts.length 0 (by omega) GF16.ONE
  · wp_norm_lhs
  · wp_norm_lhs
  · simpa [arm64_norm, wp_norm] using hsp_align
  · rfl
  · simp [arm64_norm, wp_norm]
  · simp [arm64_norm, wp_norm]
  · simp [arm64_norm, wp_norm]
  · simp [arm64_norm, wp_norm]
  · simp [arm64_norm, wp_norm]
  · intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx20_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs1
    rw [hentry] at hpc1
    simp only [arm64_norm, wp_norm] at hsp1 htr1 hx20_1 hx22_1 hx25_1 hx29_1 hvregs1
    simp only [List.drop_zero, ← lagrangeDenominator_eq_foldl] at hx0_1
    have hdiv : subroutine_ok (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr lagrangeCompleteName - BitVec.ofNat 64 52212)
        (divImplSpec b) := divImpl_at_lagrangeComplete b ext
    dsimp only [tripleRatchetProgAtExt] at hdiv; rw [hentry] at hdiv
    wp_simp_pre [ptSliceAt_focus_y h_7 x.ptsPtr]
    wp_steps 7
    wp_conv_pre =>
      rw [← sepConj_assoc ((x.ptsPtr + BitVec.ofNat 64 (4 * x.i) + 2#64) ↦₁₆ _),
          ← ptSliceAt_focus_y h_7 x.ptsPtr]
    wp_call hdiv
    wp_steps 2
    by_cases hlen2 : x.self.coefficients.length < 2
    · have hult2 : (BitVec.ofNat 64 x.self.coefficients.length).ult 2#64 = true := by
        simp only [BitVec.ult, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : x.self.coefficients.length < 2 ^ 64), decide_eq_true_eq]
        omega
      have hpure_eq : (lagrangeCompletePure x.self x.pts x.i).coefficients = x.self.coefficients := by
        have hsub0 : x.self.coefficients.length - 1 = 0 := by omega
        simp [lagrangeCompletePure, List.getElem?_eq_getElem h_7, hsub0, divLoopPure]
      code_fetches_range CryptoVerification.libsignalSessionCode lagrangeCompleteBin b
        (Rust.withPanics ext) lagrangeComplete_fnOff 0x5cacc 0x290 32
      rw [hentry] at *; examples_hide_fetches; rw [hsp1]
      wp_steps
      refine SepWP.fold
        (stackAt_lagrangeComplete_merge s0.sp (s0.sp - 128#64) (x.pts[x.i]'h_7).y.value
          (Poly.lagrangeDenominator (x.pts[x.i]'h_7).x x.pts).value
          (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
          (s0.readReg64 (Reg.gpr 28#5)) (s0.readReg64 (Reg.gpr 27#5))
          (s0.readReg64 (Reg.gpr 26#5)) (s0.readReg64 (Reg.gpr 25#5))
          (s0.readReg64 (Reg.gpr 24#5)) (s0.readReg64 (Reg.gpr 23#5))
          (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
          (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5)) rfl)
        (by sep_focus) ?_
      rw [hpure_eq]; wp_done
    · have hult2 : (BitVec.ofNat 64 x.self.coefficients.length).ult 2#64 = false := by
        simp only [BitVec.ult, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : x.self.coefficients.length < 2 ^ 64), decide_eq_false_iff_not]
        omega
      wp_conv_pre => rw [ptSliceAt_focus_x h_7 x.ptsPtr]
      wp_steps 8
      wp_conv_pre => rw [← ptSliceAt_focus_x h_7 x.ptsPtr, perm_to_div]
      let rem := x.self.coefficients.length - 2
      have hrem_eq : rem + 1 + 1 = x.self.coefficients.length := by omega
      let pix := (x.pts[x.i]'h_7).x
      let scale := (x.pts[x.i]'h_7).y.divImpl (Poly.lagrangeDenominator pix x.pts)
      rw [← hentry]
      apply divLoop_sepWP b ext h_1 x.coeffsPtr pix scale (s0.readReg64 .lr) _
        rem x.self.coefficients (by omega) h_8
      · wp_norm_lhs
      · wp_norm_lhs
      · simpa [arm64_norm, wp_norm, hsp_sf, hsp1] using hsp_align
      · simp only [arm64_norm, wp_norm, truncate16_zext64_truncate32]; exact h_19
      · simp only [arm64_norm, wp_norm, truncate16_zext64]; rfl
      · simp only [arm64_norm, wp_norm, ← hrem_eq, ptr_sub_two_step_norm']
      · simp only [arm64_norm, wp_norm, ← hrem_eq]
        rw [show (rem + 1 + 1 : Nat) = (rem + 1) + 1 from rfl,
            BitVec.ofNat_add, show BitVec.ofNat 64 1 = 1#64 from rfl, BitVec.add_sub_cancel]
      · simpa [arm64_norm, wp_norm, h_14] using hx24_1
      · simpa [arm64_norm, wp_norm, h_17] using hx27_1
      · intro s2 hpc2 hrun2 hsp2 htr2 hvregs2
        have hpure_eq :
            divLoopPure pix scale (rem + 1) x.self.coefficients =
              (lagrangeCompletePure x.self x.pts x.i).coefficients := by
          have hsub1 : rem + 1 = x.self.coefficients.length - 1 := by omega
          have hnotle1 : ¬ x.self.coefficients.length ≤ 1 := by omega
          simp [lagrangeCompletePure, List.getElem?_eq_getElem h_7, hsub1, hnotle1, GF16.div, pix, scale]
        code_fetches_range CryptoVerification.libsignalSessionCode lagrangeCompleteBin b
          (Rust.withPanics ext) lagrangeComplete_fnOff 0x5cacc 0x290 32
        rw [hentry] at *; examples_hide_fetches
        simp only [arm64_norm, wp_norm, hsp_sf, hsp1, hpost, htr1, hvregs, hvregs1] at hsp2 htr2 hvregs2
        rw [hsp1, hpure_eq]
        wp_steps
        refine SepWP.fold
          (stackAt_lagrangeComplete_merge s0.sp (s0.sp - 128#64) (x.pts[x.i]'h_7).y.value
            (Poly.lagrangeDenominator (x.pts[x.i]'h_7).x x.pts).value
            (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
            (s0.readReg64 (Reg.gpr 28#5)) (s0.readReg64 (Reg.gpr 27#5))
            (s0.readReg64 (Reg.gpr 26#5)) (s0.readReg64 (Reg.gpr 25#5))
            (s0.readReg64 (Reg.gpr 24#5)) (s0.readReg64 (Reg.gpr 23#5))
            (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
            (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5)) rfl)
          (by sep_focus) ?_
        wp_done

/-! ## Relocatable `[LibsignalPlacement]` Proof (Block `373`) -/

set_option maxHeartbeats 1600000 in
theorem denomLoop_placed_sepWP [LibsignalPlacement] (ext : String → Option (State → State))
    (ptsPtr : BitVec 64) (pts : List Pt) (hpts_len : 4 * pts.length < 2 ^ 64)
    (i : Nat) (hi : i < pts.length)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop) :
    ∀ (rem j : Nat) (_hrem : j + rem = pts.length) (acc : GF16)
      (s : State) (F : SepProp),
      LibsignalCodeLoaded lsmpl s.mem →
      s.pc = (blkPl_373).base + 84#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      BitVec.truncate 16 (s.readReg64 .x0) = acc.value →
      s.readReg64 .x19 = ptsPtr + BitVec.ofNat 64 (4 * j) →
      s.readReg64 .x24 = lsρ tokenName + 8#64 →
      s.readReg64 .x26 = ptsPtr + BitVec.ofNat 64 (4 * i) →
      s.readReg64 .x27 = Obj.pageOf (lsρ tokenStorageName) →
      s.readReg64 .x28 = ptsPtr + BitVec.ofNat 64 (4 * pts.length) →
      (∀ (sf : State),
        LibsignalCodeLoaded lsmpl sf.mem →
        sf.pc = (blkPl_373).base + 256#64 →
        sf.status = .Running →
        sf.sp = s.sp →
        sf.trace = s.trace →
        BitVec.truncate 16 (sf.readReg64 .x0) =
          ((pts.drop j).foldl (denomStep (pts[i]'hi).x) acc).value →
        sf.readReg64 .x20 = s.readReg64 .x20 →
        sf.readReg64 .x22 = s.readReg64 .x22 →
        sf.readReg64 .x24 = lsρ tokenName + 8#64 →
        sf.readReg64 .x25 = s.readReg64 .x25 →
        sf.readReg64 .x26 = ptsPtr + BitVec.ofNat 64 (4 * i) →
        sf.readReg64 .x27 = Obj.pageOf (lsρ tokenStorageName) →
        sf.readReg64 .x28 = ptsPtr + BitVec.ofNat 64 (4 * pts.length) →
        sf.readReg64 .x29 = s.readReg64 .x29 →
        calleeSavedVRegs sf = calleeSavedVRegs s →
        SepWP ((blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext)) ret_pc sf
          (ptSliceAt ptsPtr pts ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q) →
      SepWP ((blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext)) ret_pc s
        (ptSliceAt ptsPtr pts ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q := by
  intro rem
  induction rem with
  | zero =>
    intro j hrem acc s F hcl hpc hrun hsp_align hx0 hx19 hx24 hx26 hx27 hx28 hnext
    have hj_eq : j = pts.length := by omega
    subst hj_eq
    wp_steps 2
    simp only [List.drop_length, List.foldl_nil] at hnext
    exact hnext _ hcl (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by simpa [arm64_norm] using hx0) (by wp_norm_lhs) (by wp_norm_lhs)
      (by simpa [arm64_norm] using hx24) (by wp_norm_lhs)
      (by simpa [arm64_norm] using hx26) (by simpa [arm64_norm] using hx27)
      (by simpa [arm64_norm] using hx28) (by wp_norm_lhs) (by wp_norm_lhs)
  | succ rem' ih =>
    intro j hrem acc s F hcl hpc hrun hsp_align hx0 hx19 hx24 hx26 hx27 hx28 hnext
    have hj : j < pts.length := by omega
    have hdrop : pts.drop j = (pts[j]'hj) :: pts.drop (j + 1) := List.drop_eq_getElem_cons hj
    have halign_bd8 := aligned_tokenOnce_placed
    rcases ptr_sub_four_mul_ne_zero ptsPtr hj hpts_len with ⟨hne, hne'⟩
    wp_steps 2
    wp_simp_pre [ptSliceAt_focus_x hj ptsPtr]
    wp_steps 1
    wp_conv_pre =>
      rw [← sepConj_assoc, ← ptSliceAt_focus_x hj ptsPtr, ptSliceAt_focus_x hi ptsPtr, sepConj_assoc]
    wp_steps 1
    wp_conv_pre => rw [← sepConj_assoc, ← ptSliceAt_focus_x hi ptsPtr]
    wp_steps 1
    cases hpx : ((pts[i]'hi).x == (pts[j]'hj).x) with
    | false =>
      have hval_ne : (pts[i]'hi).x.value ≠ (pts[j]'hj).x.value := by
        intro heq
        have htrue : ((pts[i]'hi).x == (pts[j]'hj).x) = true := by rw [gf16_beq_iff, beq_iff_eq]; exact heq
        rw [hpx] at htrue; contradiction
      rcases cmp32_zext16_ne_zero _ _ hval_ne with ⟨hcmp1, hcmp2, hcmp3, hcmp4⟩
      have hmul := lscall_blk (callerProg := (blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext))
        (unacceleratedMul_placed_ok (Rust.withPanics ext)) hcl
      simp only [withMemEq, unacceleratedMulPlacedSpec] at hmul
      apply sepWP_seq_lscl (by exact hcl) (mid := (blkPl_373).base + 84#64)
      wp_steps 1
      wp_simp_pre [tokenInitPlacedAt]
      apply step_ldar32
      · wp_norm_lhs
      · wp_norm_lhs
      · exact blkPC_373_rebase_fetch_0x6c (blkPl_373).base (Rust.withPanics ext)
      · wp_norm_lhs
      · wp_norm_lhs
      · exact halign_bd8
      · wp_sep_access
      · wp_norm_lhs
      wp_steps 6
      apply SepWP.fold tokenInitPlacedAt_fold (by sep_focus)
      wp_call hmul
      wp_steps 1
      apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
      intro hcl_next
      wp_conv_pre => rw [perm_denom_pre]
      apply ih (j + 1) (by omega) (GF16.mul acc (GF16.sub (pts[i]'hi).x (pts[j]'hj).x)) _ F (by exact hcl_next)
      · wp_norm_lhs
      · wp_norm_lhs
      · simpa [arm64_norm, wp_norm, hsp_sf] using hsp_align
      · simp only [arm64_norm, wp_norm, h_10]
        have heor :
            BitVec.truncate 16 (BitVec.zeroExtend 64 (pts[j]'hj).x.value ^^^ BitVec.zeroExtend 64 (pts[i]'hi).x.value) =
              (GF16.sub (pts[i]'hi).x (pts[j]'hj).x).value := by
          change BitVec.truncate 16 (BitVec.zeroExtend 64 (pts[j]'hj).x.value ^^^ BitVec.zeroExtend 64 (pts[i]'hi).x.value) =
            (pts[i]'hi).x.value ^^^ (pts[j]'hj).x.value
          ext k hk; simp [Bool.xor_comm]
        rw [heor]; rfl
      · simp only [arm64_norm, wp_norm, h]; exact ptr_add_four_step ptsPtr j
      · simpa [arm64_norm, wp_norm, h_5] using hx24
      · simpa [arm64_norm, wp_norm, h_7] using hx26
      · simpa [arm64_norm, wp_norm, h_8] using hx27
      · simpa [arm64_norm, wp_norm, h_9] using hx28
      · intro sf' hcl_f hpc_f hrun_f hsp_f htr_f hx0_f hx20_f hx22_f hx24_f hx25_f hx26_f hx27_f hx28_f hx29_f hvregs_f
        refine hnext sf' hcl_f hpc_f hrun_f ?_ ?_ ?_ ?_ ?_ hx24_f ?_ hx26_f hx27_f hx28_f ?_ ?_
        · simpa [arm64_norm, wp_norm, hsp_sf] using hsp_f
        · simpa [arm64_norm, wp_norm, hpost] using htr_f
        · rw [hdrop, List.foldl_cons, denomStep]; simp only [hpx, Bool.false_eq_true, ↓reduceIte]; exact hx0_f
        · simpa [arm64_norm, wp_norm, h_1] using hx20_f
        · simpa [arm64_norm, wp_norm, h_3] using hx22_f
        · simpa [arm64_norm, wp_norm, h_6] using hx25_f
        · simpa [arm64_norm, wp_norm, hcs_sf] using hx29_f
        · simpa [arm64_norm, wp_norm, hvregs] using hvregs_f
    | true =>
      have hval_eq : (pts[i]'hi).x.value = (pts[j]'hj).x.value := by rw [gf16_beq_iff, beq_iff_eq] at hpx; exact hpx
      rcases cmp32_zext16_eq_zero _ _ hval_eq with ⟨hcmp1, hcmp2, hcmp3, hcmp4⟩
      wp_steps 1
      apply ih (j + 1) (by omega) acc _ F (by exact hcl)
      · wp_norm_lhs
      · wp_norm_lhs
      · simpa [arm64_norm, wp_norm] using hsp_align
      · simpa [arm64_norm, wp_norm] using hx0
      · simp only [arm64_norm, wp_norm]; exact ptr_add_four_step ptsPtr j
      · simpa [arm64_norm, wp_norm] using hx24
      · simpa [arm64_norm, wp_norm] using hx26
      · simpa [arm64_norm, wp_norm] using hx27
      · simpa [arm64_norm, wp_norm] using hx28
      · intro sf' hcl_f hpc_f hrun_f hsp_f htr_f hx0_f hx20_f hx22_f hx24_f hx25_f hx26_f hx27_f hx28_f hx29_f hvregs_f
        refine hnext sf' hcl_f hpc_f hrun_f ?_ ?_ ?_ ?_ ?_ hx24_f ?_ hx26_f hx27_f hx28_f ?_ ?_
        · simpa [arm64_norm, wp_norm] using hsp_f
        · simpa [arm64_norm, wp_norm] using htr_f
        · rw [hdrop, List.foldl_cons, denomStep]; simp only [hpx, ↓reduceIte]; exact hx0_f
        · simpa [arm64_norm, wp_norm] using hx20_f
        · simpa [arm64_norm, wp_norm] using hx22_f
        · simpa [arm64_norm, wp_norm] using hx25_f
        · simpa [arm64_norm, wp_norm] using hx29_f
        · simpa [arm64_norm, wp_norm] using hvregs_f

set_option maxHeartbeats 1600000 in
theorem divLoop_placed_sepWP [LibsignalPlacement] (ext : String → Option (State → State))
    (coeffsPtr : BitVec 64) (pix scale : GF16)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop) :
    ∀ (rem : Nat) (cs : List GF16) (_hrem : rem + 1 < cs.length) (_hlen : 2 * cs.length < 2 ^ 64)
      (s : State) (F : SepProp),
      LibsignalCodeLoaded lsmpl s.mem →
      s.pc = (blkPl_373).base + 352#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      BitVec.truncate 16 (s.readReg64 .x19) = scale.value →
      BitVec.truncate 16 (s.readReg64 .x20) = pix.value →
      s.readReg64 .x21 = coeffsPtr + BitVec.ofNat 64 (2 * (rem + 1)) →
      s.readReg64 .x22 = BitVec.ofNat 64 (rem + 1) →
      s.readReg64 .x24 = lsρ tokenName + 8#64 →
      s.readReg64 .x27 = Obj.pageOf (lsρ tokenStorageName) →
      (∀ (sf : State),
        sf.pc = (blkPl_373).base + 656#64 →
        sf.status = .Running →
        sf.sp = s.sp →
        sf.trace = s.trace →
        calleeSavedVRegs sf = calleeSavedVRegs s →
        SepWP ((blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext)) ret_pc sf
          (gf16SliceAt coeffsPtr (divLoopPure pix scale (rem + 1) cs) ∗
           tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q) →
      SepWP ((blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext)) ret_pc s
        (gf16SliceAt coeffsPtr cs ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q := by
  intro rem
  induction rem with
  | zero =>
    intro cs hrem hlen s F hcl hpc hrun hsp_align hx19 hx20 hx21 hx22 hx24 hx27 hnext
    have hrem1 : 1 < cs.length := hrem
    have halign_bd8 := aligned_tokenOnce_placed
    have hmul := lscall_blk (callerProg := (blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext))
      (unacceleratedMul_placed_ok (Rust.withPanics ext)) hcl
    simp only [withMemEq, unacceleratedMulPlacedSpec] at hmul
    apply sepWP_seq_lscl hcl (mid := (blkPl_373).base + 492#64)
    wp_simp_pre [gf16SliceAt_focus hrem1 coeffsPtr, tokenInitPlacedAt]
    wp_steps 1
    apply step_ldar32
    · wp_norm_lhs
    · wp_norm_lhs
    · exact blkPC_373_rebase_fetch_0x164 (blkPl_373).base (Rust.withPanics ext)
    · wp_norm_lhs
    · wp_norm_lhs
    · exact halign_bd8
    · wp_sep_access
    · wp_norm_lhs
    wp_steps 6
    apply SepWP.fold tokenInitPlacedAt_fold (by sep_focus)
    wp_call hmul
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl1
    have hmul1 := lscall_blk (callerProg := (blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext))
      (unacceleratedMul_placed_ok (Rust.withPanics ext)) hcl1
    simp only [withMemEq, unacceleratedMulPlacedSpec] at hmul1
    wp_steps 1
    wp_simp_pre [tokenInitPlacedAt]
    apply step_ldar32
    · wp_norm_lhs
    · wp_norm_lhs
    · exact blkPC_373_rebase_fetch_0x1f0 (blkPl_373).base (Rust.withPanics ext)
    · wp_norm_lhs
    · wp_norm_lhs
    · exact halign_bd8
    · wp_sep_access
    · wp_norm_lhs
    wp_steps 7
    apply SepWP.fold tokenInitPlacedAt_fold (by sep_focus)
    wp_call hmul1
    wp_steps 1
    have hrem0 : 0 < (cs.set 1 ⟨unaccelerated.mul (cs[1]'hrem1).value scale.value⟩).length := by
      simp [List.length_set]; omega
    wp_conv_pre => rw [gf16SliceAt_update_one_assoc hrem1 coeffsPtr, gf16SliceAt_focus_assoc hrem0 coeffsPtr]
    wp_steps 5
    have hlist :
        (cs.set 1 ⟨unaccelerated.mul (cs[1]'hrem1).value scale.value⟩).set 0
          ⟨((cs.set 1 ⟨unaccelerated.mul (cs[1]'hrem1).value scale.value⟩)[0]'hrem0).value ^^^
            unaccelerated.mul (cs[1]'hrem1).value pix.value⟩ =
        divLoopPure pix scale (0 + 1) cs := by
      simpa [divLoopPure] using divLoop_step_eq pix scale 0 cs hrem
    wp_conv_pre => rw [gf16SliceAt_update_assoc hrem0 coeffsPtr, hlist, perm_div_pre]
    exact hnext _ (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by simp [arm64_norm, wp_norm, hvregs_1, hvregs])
  | succ rem' ih =>
    intro cs hrem hlen s F hcl hpc hrun hsp_align hx19 hx20 hx21 hx22 hx24 hx27 hnext
    have halign_bd8 := aligned_tokenOnce_placed
    rcases bv_sub_one_succ rem' (by omega) with ⟨hsub1, hsub2, hsub3⟩
    have hmul := lscall_blk (callerProg := (blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext))
      (unacceleratedMul_placed_ok (Rust.withPanics ext)) hcl
    simp only [withMemEq, unacceleratedMulPlacedSpec] at hmul
    apply sepWP_seq_lscl hcl (mid := (blkPl_373).base + 492#64)
    wp_simp_pre [gf16SliceAt_focus hrem coeffsPtr, tokenInitPlacedAt]
    wp_steps 1
    apply step_ldar32
    · wp_norm_lhs
    · wp_norm_lhs
    · exact blkPC_373_rebase_fetch_0x164 (blkPl_373).base (Rust.withPanics ext)
    · wp_norm_lhs
    · wp_norm_lhs
    · exact halign_bd8
    · wp_sep_access
    · wp_norm_lhs
    wp_steps 6
    apply SepWP.fold tokenInitPlacedAt_fold (by sep_focus)
    wp_call hmul
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl1
    have hmul1 := lscall_blk (callerProg := (blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext))
      (unacceleratedMul_placed_ok (Rust.withPanics ext)) hcl1
    simp only [withMemEq, unacceleratedMulPlacedSpec] at hmul1
    apply sepWP_seq_lscl hcl1 (mid := (blkPl_373).base + 352#64)
    wp_steps 1
    wp_simp_pre [tokenInitPlacedAt]
    apply step_ldar32
    · wp_norm_lhs
    · wp_norm_lhs
    · exact blkPC_373_rebase_fetch_0x1f0 (blkPl_373).base (Rust.withPanics ext)
    · wp_norm_lhs
    · wp_norm_lhs
    · exact halign_bd8
    · wp_sep_access
    · wp_norm_lhs
    wp_steps 7
    apply SepWP.fold tokenInitPlacedAt_fold (by sep_focus)
    wp_call hmul1
    wp_steps 1
    have hrem1 : rem' + 1 < (cs.set (rem' + 1 + 1) ⟨unaccelerated.mul (cs[rem' + 1 + 1]'hrem).value scale.value⟩).length := by
      simp [List.length_set]; omega
    wp_conv_pre => rw [gf16SliceAt_update_assoc hrem coeffsPtr, gf16SliceAt_focus_assoc hrem1 coeffsPtr]
    wp_steps 5
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl2
    let cs_next :=
      let cIdx := cs[rem' + 1 + 1]?.getD GF16.ZERO
      let cPrev := cs[rem' + 1]?.getD GF16.ZERO
      let negativeDelta := GF16.mul cIdx pix
      let coeffs1 := cs.set (rem' + 1 + 1) (GF16.mul cIdx scale)
      coeffs1.set (rem' + 1) (GF16.add cPrev negativeDelta)
    have hlist :
        (cs.set (rem' + 1 + 1) ⟨unaccelerated.mul (cs[rem' + 1 + 1]'hrem).value scale.value⟩).set (rem' + 1)
          ⟨((cs.set (rem' + 1 + 1) ⟨unaccelerated.mul (cs[rem' + 1 + 1]'hrem).value scale.value⟩)[rem' + 1]'hrem1).value ^^^
            unaccelerated.mul (cs[rem' + 1 + 1]'hrem).value pix.value⟩ =
        cs_next := divLoop_step_eq pix scale (rem' + 1) cs hrem
    wp_conv_pre => rw [gf16SliceAt_update_assoc hrem1 coeffsPtr, hlist, perm_div_pre]
    apply ih cs_next (by simp [cs_next, List.length_set]; omega) (by simp [cs_next, List.length_set]; omega) _ F hcl2
    · wp_norm_lhs
    · wp_norm_lhs
    · simpa [arm64_norm, wp_norm, hsp_sf_1, hsp_sf] using hsp_align
    · simpa [arm64_norm, wp_norm, h_11, h] using hx19
    · simpa [arm64_norm, wp_norm, h_12, h_1] using hx20
    · wp_norm_lhs
    · simp [arm64_norm, wp_norm]
    · simpa [arm64_norm, wp_norm, h_16, h_5] using hx24
    · simpa [arm64_norm, wp_norm, h_19, h_8] using hx27
    · intro sf' hpc_f hrun_f hsp_f htr_f hvregs_f
      exact hnext sf' hpc_f hrun_f
        (by simpa [arm64_norm, wp_norm, hsp_sf_1, hsp_sf] using hsp_f)
        (by simpa [arm64_norm, wp_norm, hpost_1, hpost] using htr_f)
        (by simpa [arm64_norm, wp_norm, hvregs_1, hvregs] using hvregs_f)

set_option maxHeartbeats 1600000 in
theorem lagrangeComplete_placed_ok [LibsignalPlacement] (ext : String → Option (State → State)) :
    subroutine_ok ((blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext))
      (blkPl_373).base (withLsCodeLoaded lsmpl lagrangeCompletePlacedSpec) := by
  simp only [withLsCodeLoaded, lagrangeCompletePlacedSpec]
  wp_init x s0
  have hule_i : BitVec.ule (BitVec.ofNat 64 x.pts.length) (BitVec.ofNat 64 x.i) = false :=
    ule_of_lt_pts h_7 h_1
  wp_simp_pre [stackAt_lagrangeComplete_split]
  wp_pull_exists
  apply sepWP_seq_lscl h (mid := (blkPl_373).base + 84#64)
  wp_steps 21
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  intro hcl0
  wp_conv_pre => rw [perm_to_denom]
  apply denomLoop_placed_sepWP ext x.ptsPtr x.pts h_1 x.i h_7 (s0.readReg64 .lr) _
    x.pts.length 0 (by omega) GF16.ONE _ _ hcl0
  · wp_norm_lhs
  · wp_norm_lhs
  · simpa [arm64_norm, wp_norm] using hsp_align
  · rfl
  · simp [arm64_norm, wp_norm]
  · simp [arm64_norm, wp_norm]
  · simp [arm64_norm, wp_norm]
  · simp [arm64_norm, wp_norm]
  · simp [arm64_norm, wp_norm]
  · intro s1 hcl1 hpc1 hrun1 hsp1 htr1 hx0_1 hx20_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs1
    simp only [arm64_norm, wp_norm] at hsp1 htr1 hx20_1 hx22_1 hx25_1 hx29_1 hvregs1
    simp only [List.drop_zero, ← lagrangeDenominator_eq_foldl] at hx0_1
    apply sepWP_seq_lscl hcl1 (mid := (blkPl_373).base + 280#64)
    wp_simp_pre [ptSliceAt_focus_y h_7 x.ptsPtr]
    wp_steps 7
    wp_conv_pre =>
      rw [← sepConj_assoc ((x.ptsPtr + BitVec.ofNat 64 (4 * x.i) + 2#64) ↦₁₆ _),
          ← ptSliceAt_focus_y h_7 x.ptsPtr]
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl_div
    have hdiv_call := lscall_blk_cl (callerProg := (blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext))
      (divImpl_placed_ok (Rust.withPanics ext)) hcl_div
    simp only [withMemEq, divImplPlacedSpec] at hdiv_call
    apply sepWP_seq_lscl hcl_div (mid := (blkPl_373).base + 284#64)
    wp_call hdiv_call
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl2
    wp_steps 2
    by_cases hlen2 : x.self.coefficients.length < 2
    · have hult2 : (BitVec.ofNat 64 x.self.coefficients.length).ult 2#64 = true := by
        simp only [BitVec.ult, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : x.self.coefficients.length < 2 ^ 64), decide_eq_true_eq]
        omega
      have hpure_eq : (lagrangeCompletePure x.self x.pts x.i).coefficients = x.self.coefficients := by
        have hsub0 : x.self.coefficients.length - 1 = 0 := by omega
        simp [lagrangeCompletePure, List.getElem?_eq_getElem h_7, hsub0, divLoopPure]
      rw [hsp1]
      wp_steps
      refine SepWP.fold
        (stackAt_lagrangeComplete_merge s0.sp (s0.sp - 128#64) (x.pts[x.i]'h_7).y.value
          (Poly.lagrangeDenominator (x.pts[x.i]'h_7).x x.pts).value
          (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
          (s0.readReg64 (Reg.gpr 28#5)) (s0.readReg64 (Reg.gpr 27#5))
          (s0.readReg64 (Reg.gpr 26#5)) (s0.readReg64 (Reg.gpr 25#5))
          (s0.readReg64 (Reg.gpr 24#5)) (s0.readReg64 (Reg.gpr 23#5))
          (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
          (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5)) rfl)
        (by sep_focus) ?_
      rw [hpure_eq]; wp_done
    · have hult2 : (BitVec.ofNat 64 x.self.coefficients.length).ult 2#64 = false := by
        simp only [BitVec.ult, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : x.self.coefficients.length < 2 ^ 64), decide_eq_false_iff_not]
        omega
      wp_conv_pre => rw [ptSliceAt_focus_x h_7 x.ptsPtr]
      wp_steps 8
      wp_conv_pre => rw [← ptSliceAt_focus_x h_7 x.ptsPtr, perm_to_div]
      let rem := x.self.coefficients.length - 2
      have hrem_eq : rem + 1 + 1 = x.self.coefficients.length := by omega
      let pix := (x.pts[x.i]'h_7).x
      let scale := (x.pts[x.i]'h_7).y.divImpl (Poly.lagrangeDenominator pix x.pts)
      apply divLoop_placed_sepWP ext x.coeffsPtr pix scale (s0.readReg64 .lr) _
        rem x.self.coefficients (by omega) h_8 _ _ (by exact hcl2)
      · wp_norm_lhs
      · wp_norm_lhs
      · simpa [arm64_norm, wp_norm, hsp_sf, hsp1] using hsp_align
      · simp only [arm64_norm, wp_norm, truncate16_zext64_truncate32]; exact h_19
      · simp only [arm64_norm, wp_norm, truncate16_zext64]; rfl
      · simp only [arm64_norm, wp_norm, ← hrem_eq, ptr_sub_two_step_norm']
      · simp only [arm64_norm, wp_norm, ← hrem_eq]
        rw [show (rem + 1 + 1 : Nat) = (rem + 1) + 1 from rfl,
            BitVec.ofNat_add, show BitVec.ofNat 64 1 = 1#64 from rfl, BitVec.add_sub_cancel]
      · simpa [arm64_norm, wp_norm, h_14] using hx24_1
      · simpa [arm64_norm, wp_norm, h_17] using hx27_1
      · intro s2 hpc2 hrun2 hsp2 htr2 hvregs2
        have hpure_eq :
            divLoopPure pix scale (rem + 1) x.self.coefficients =
              (lagrangeCompletePure x.self x.pts x.i).coefficients := by
          have hsub1 : rem + 1 = x.self.coefficients.length - 1 := by omega
          have hnotle1 : ¬ x.self.coefficients.length ≤ 1 := by omega
          simp [lagrangeCompletePure, List.getElem?_eq_getElem h_7, hsub1, hnotle1, GF16.div, pix, scale]
        simp only [arm64_norm, wp_norm, hsp_sf, hsp1, hpost, htr1, hvregs, hvregs1] at hsp2 htr2 hvregs2
        rw [hsp1, hpure_eq]
        wp_steps
        refine SepWP.fold
          (stackAt_lagrangeComplete_merge s0.sp (s0.sp - 128#64) (x.pts[x.i]'h_7).y.value
            (Poly.lagrangeDenominator (x.pts[x.i]'h_7).x x.pts).value
            (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
            (s0.readReg64 (Reg.gpr 28#5)) (s0.readReg64 (Reg.gpr 27#5))
            (s0.readReg64 (Reg.gpr 26#5)) (s0.readReg64 (Reg.gpr 25#5))
            (s0.readReg64 (Reg.gpr 24#5)) (s0.readReg64 (Reg.gpr 23#5))
            (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
            (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5)) rfl)
          (by sep_focus) ?_
        wp_done

end CryptoVerification.SpqrV1.Poly.LagrangeComplete

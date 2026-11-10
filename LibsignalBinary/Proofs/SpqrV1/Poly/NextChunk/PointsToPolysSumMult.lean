/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSumMult1
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallbackLoop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk`: Inlined `gf::parallel_mult`

**Checked by Lean.**

Verifies the pair loop, register reload, and full inlined `spqr::encoding::gf::parallel_mult`
(`0x6ae34..0x6b24c`, `+2736 -> +3784`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.NextChunk

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.ComputeAt
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  exists_pow_two_eq_two_sm exists_pow_two_eq_eight_sm
  fnAddr_adrp_6ae54 fnAddr_adrp_6b0c8 fnAddr_adrp_6b0e0 fnAddr_adrp_6b19c fnAddr_adrp_6b1ac
  polyReduce_asm_eq
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  LagrangePrepare.sp_setPC_pre LagrangePrepare.sp_setMem_setPC_pre
  LagrangePrepare.readReg64_setPC_pre LagrangePrepare.readReg64_setMem_setPC_pre
  LagrangePrepare.readReg32_setPC_pre LagrangePrepare.readReg32_setMem_setPC_pre
  LagrangePrepare.readReg_setPC_pre LagrangePrepare.readReg_setMem_setPC_pre
  truncate32_zext64_sm truncate32_zext64_16_sm truncate32_shl_zext64_32_sm
  truncate16_zext64_16_sm zext16_trunc32_zext64_16_sm
  truncate32_xor_zext64_sm truncate32_and_zext64_sm
  truncate64_sxth32_16_sm sbfx_bit0_sxth32_sm
  pmTerm_bit0_sm pmTerm_bit0_zext64_sm truncate16_truncate32_64_sm
  sxth32_shl30_asr31 sxth32_shl29_asr31 sxth32_shl28_asr31 sxth32_shl27_asr31
  sxth32_shl26_asr31 sxth32_shl25_asr31 sxth32_shl24_asr31 sxth32_shl23_asr31
  sxth32_shl22_asr31 sxth32_shl21_asr31 sxth32_shl20_asr31 sxth32_shl19_asr31
  sxth32_shl18_asr31 sxth32_shl17_asr31
  pmTerm_mid_sm csel_gt_cmn1_sxth32_sm csel_gt_cmn1_sxth32_zext_sm
  polyMul_pair_c1_eq polyMul_pair_c2_eq

/-! ## 1. Single Iteration of the Pair Loop (`+3384`) -/

private theorem zext64_and_mask32 (w : BitVec 32) (b : Bool) :
    BitVec.zeroExtend 64 w &&& (if b = true then 4294967295#64 else 0#64) =
      BitVec.zeroExtend 64 (w &&& (if b = true then 0xffff_ffff#32 else 0#32)) := by
  cases b <;> bv_slice

@[local arm64_norm ↓, local wp_norm ↓]
theorem pmTerm_bit0_64 (yv x : BitVec 16) :
    (if x.getLsbD 0 = true then 4294967295#64 else 0#64) &&& BitVec.zeroExtend 64 yv =
      BitVec.zeroExtend 64 (pmTerm_sm yv x 0) := by
  have h : pmTerm_sm yv x 0 =
      (BitVec.zeroExtend 32 yv <<< 0) &&& (if x.getLsbD 0 = true then 0xffff_ffff#32 else 0#32) := by
    unfold pmTerm_sm; rfl
  rw [h]; generalize x.getLsbD 0 = b; cases b <;> bv_slice

@[local arm64_norm ↓, local wp_norm ↓]
theorem pmTerm_mid_64 (yv x : BitVec 16) (i : Nat) :
    BitVec.zeroExtend 64 (BitVec.zeroExtend 32 yv <<< i) &&&
      (if x.getLsbD i = true then 4294967295#64 else 0#64) =
      BitVec.zeroExtend 64 (pmTerm_sm yv x i) := by
  have h : pmTerm_sm yv x i =
      (BitVec.zeroExtend 32 yv <<< i) &&& (if x.getLsbD i = true then 0xffff_ffff#32 else 0#32) := by
    unfold pmTerm_sm; rfl
  rw [h]; exact zext64_and_mask32 _ _

@[local arm64_norm, local wp_norm]
theorem sub2_ofNat_pair (k : Nat) :
    BitVec.ofNat 64 (2 * (k + 1)) - 2#64 = BitVec.ofNat 64 (2 * k) := by
  have h2 : BitVec.ofNat 64 (2 * (k + 1)) = BitVec.ofNat 64 (2 * k) + 2#64 := by
    rw [show 2 * (k + 1) = 2 * k + 2 by omega, BitVec.ofNat_add]
  rw [h2]; bv_omega

@[local arm64_norm, local wp_norm]
theorem sub2_ofNat_pair_add (k : Nat) :
    BitVec.ofNat 64 (2 * (k + 1)) + 18446744073709551614#64 = BitVec.ofNat 64 (2 * k) := by
  have h1 : (18446744073709551614#64 : BitVec 64) = -2#64 := rfl
  have h2 : BitVec.ofNat 64 (2 * (k + 1)) = BitVec.ofNat 64 (2 * k) + 2#64 := by
    rw [show 2 * (k + 1) = 2 * k + 2 by omega, BitVec.ofNat_add]
  rw [h1, h2]; bv_omega

@[local arm64_norm, local wp_norm]
theorem add2_ofNat_pair (k : Nat) :
    BitVec.ofNat 64 (2 * (k + 1)) + 2#64 = BitVec.ofNat 64 (2 * (k + 2)) := by
  rw [show 2 * (k + 2) = 2 * (k + 1) + 2 by omega, BitVec.ofNat_add]

theorem ule_n_2k {k n : Nat} (hk : 2 * (k + 1) ≤ n) (hn : n ≤ 0x0555555555555555) :
    (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 (2 * k)) = false := by
  rw [Bool.eq_false_iff, Ne, BitVec.ule_iff_toNat_le, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega

theorem ult_2k_n {k n : Nat} (hk : 2 * (k + 1) ≤ n) (hn : n ≤ 0x0555555555555555) :
    (!((BitVec.ofNat 64 (2 * k)).ult (BitVec.ofNat 64 n))) = false := by
  rw [Bool.not_eq_false', BitVec.ult_iff_toNat_lt, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega

theorem ult_n_2k2 {k n : Nat} (hn : n ≤ 0x0555555555555555) (hk : 2 * (k + 1) ≤ n) :
    (BitVec.ofNat 64 n).ult (BitVec.ofNat 64 (2 * (k + 2))) = decide (n < 2 * (k + 2)) := by
  by_cases h : n < 2 * (k + 2)
  · rw [decide_eq_true_iff.mpr h, BitVec.ult_iff_toNat_lt, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  · rw [decide_eq_false_iff_not.mpr h, Bool.eq_false_iff, Ne, BitVec.ult_iff_toNat_lt,
        BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega

theorem hi_2k2_n {k n : Nat} (hn : n ≤ 0x0555555555555555) (hk : 2 * (k + 1) ≤ n) :
    ((!((BitVec.ofNat 64 (2 * (k + 2))).ult (BitVec.ofNat 64 n))) &&
     !(BitVec.ofNat 64 (2 * (k + 2)) == BitVec.ofNat 64 n)) = decide (n < 2 * (k + 2)) := by
  have h1 : (BitVec.ofNat 64 (2 * (k + 2))).toNat = 2 * (k + 2) := Nat.mod_eq_of_lt (by omega)
  have h2 : (BitVec.ofNat 64 n).toNat = n := Nat.mod_eq_of_lt (by omega)
  by_cases hlt : n < 2 * (k + 2)
  · have hult : (BitVec.ofNat 64 (2 * (k + 2))).ult (BitVec.ofNat 64 n) = false := by
      rw [Bool.eq_false_iff, Ne, BitVec.ult_iff_toNat_lt, h1, h2]; omega
    have hbeq : (BitVec.ofNat 64 (2 * (k + 2)) == BitVec.ofNat 64 n) = false := by
      rw [beq_eq_false_iff_ne]; intro heq
      have hto := congrArg BitVec.toNat heq; rw [h1, h2] at hto; omega
    simp [hlt, hult, hbeq]
  · by_cases heq : 2 * (k + 2) = n
    · subst heq; simp
    · have hult : (BitVec.ofNat 64 (2 * (k + 2))).ult (BitVec.ofNat 64 n) = true := by
        rw [BitVec.ult_iff_toNat_lt, h1, h2]; omega
      simp [hlt, hult]

set_option maxHeartbeats 1600000 in
theorem parallelMultPairStep_sepWP {b : BitVec 64} {ext : String → Option (State → State)}
    {ret : BitVec 64} {post : State → SepProp → Prop}
    (hb : b &&& 0xfff#64 = 0#64)
    (k n : Nat) (hk : 2 * (k + 1) ≤ n) (hn : n ≤ 0x0555555555555555)
    (yv : BitVec 16) (c1 c2 : GF16)
    (s : State) (fsp ptr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 3384#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx18 : s.readReg64 .x18 = b + bv% (ls_xref% 0x5e970 0x5e974))
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 n)
    (hx21 : s.readReg64 .x21 = BitVec.zeroExtend 64 yv)
    (hx24 : s.readReg64 .x24 = ptr)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 (2 * (k + 1)))
    (hcont : ∀ s1 : State,
      s1.pc = (if decide (n < 2 * (k + 2)) then
          (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 3576#64
        else
          (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 3384#64) →
      s1.status = .Running → s1.sp = fsp → s1.trace = s.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x18 = b + bv% (ls_xref% 0x5e970 0x5e974) →
      s1.readReg64 .x20 = BitVec.ofNat 64 n →
      s1.readReg64 .x21 = BitVec.zeroExtend 64 yv →
      s1.readReg64 .x24 = ptr + 4#64 →
      s1.readReg64 .x26 = BitVec.ofNat 64 (2 * (k + 2)) →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s1
        (gf16At ⟨unaccelerated.mul yv c1.value⟩ ptr ∗
         gf16At ⟨unaccelerated.mul yv c2.value⟩ (ptr + 2#64) ∗
         ((fsp + 136#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         shiftTableAt fsp yv ∗ tokenInitAt b ∗ reduceTableAt b ∗ Frame) post) :
    SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s
      (gf16At c1 ptr ∗ gf16At c2 (ptr + 2#64) ∗
       ((fsp + 136#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       shiftTableAt fsp yv ∗ tokenInitAt b ∗ reduceTableAt b ∗ Frame) post := by
  have hadrp1 := fnAddr_adrp_6b0c8 (H := Rust.withPanics ext) hb
  have hadrp2 := fnAddr_adrp_6b0e0 (H := Rust.withPanics ext) hb
  have halign := GF.Mul2U16.aligned_86bd8 b hb
  have hsub2 := sub2_ofNat_pair k
  have hadd2 := add2_ofNat_pair k
  have hule := ule_n_2k hk hn
  have hult := ult_2k_n hk hn
  have hult2 := ult_n_2k2 hn hk
  have hhi := hi_2k2_n hn hk
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0xb40 556
  dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hadrp1 hadrp2 hpc hcont ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  unfold gf16At shiftTableAt tokenInitAt; dsimp only
  wp_steps 7
  apply step_ldar32
  · wp_norm_lhs
  · wp_norm_lhs
  · wp_assumption
  · wp_norm_lhs
  · wp_norm_lhs
  · exact halign
  · wp_sep_access
  · wp_norm_lhs
  wp_steps 5
  wp_steps 68
  wp_conv_pre =>
    rw [reduceTableAt_focus16 b (BitVec.truncate 8 (unaccelerated.polyMul yv c1.value >>> 24)),
        uxtw1_idx1_eq (unaccelerated.polyMul yv c1.value)]
  wp_steps 40
  wp_conv_pre =>
    rw [← uxtw1_idx1_eq (unaccelerated.polyMul yv c1.value),
        ← reduceTableAt_focus16 b (BitVec.truncate 8 (unaccelerated.polyMul yv c1.value >>> 24)),
        reduceTableAt_focus16 b
          (BitVec.truncate 8
            ((unaccelerated.polyMul yv c1.value ^^^
                BitVec.zeroExtend 32
                    (reduce.reduceByteEntry (BitVec.truncate 8 (unaccelerated.polyMul yv c1.value >>> 24))) <<<
                  8) >>>
              16)),
        uxtw1_idx2_eq]
  wp_steps 10
  wp_conv_pre =>
    rw [← uxtw1_idx2_eq,
        ← reduceTableAt_focus16 b
          (BitVec.truncate 8
            ((unaccelerated.polyMul yv c1.value ^^^
                BitVec.zeroExtend 32
                    (reduce.reduceByteEntry (BitVec.truncate 8 (unaccelerated.polyMul yv c1.value >>> 24))) <<<
                  8) >>>
              16)),
        reduceTableAt_focus16 b (BitVec.truncate 8 (unaccelerated.polyMul yv c2.value >>> 24)),
        uxtw1_idx1_eq (unaccelerated.polyMul yv c2.value)]
  wp_steps 3
  wp_conv_pre =>
    rw [← uxtw1_idx1_eq (unaccelerated.polyMul yv c2.value),
        ← reduceTableAt_focus16 b (BitVec.truncate 8 (unaccelerated.polyMul yv c2.value >>> 24)),
        reduceTableAt_focus16 b
          (BitVec.truncate 8
            ((unaccelerated.polyMul yv c2.value ^^^
                BitVec.zeroExtend 32
                    (reduce.reduceByteEntry (BitVec.truncate 8 (unaccelerated.polyMul yv c2.value >>> 24))) <<<
                  8) >>>
              16)),
        uxtw1_idx2_eq]
  wp_steps 5
  wp_conv_pre =>
    rw [← uxtw1_idx2_eq,
        ← reduceTableAt_focus16 b
          (BitVec.truncate 8
            ((unaccelerated.polyMul yv c2.value ^^^
                BitVec.zeroExtend 32
                    (reduce.reduceByteEntry (BitVec.truncate 8 (unaccelerated.polyMul yv c2.value >>> 24))) <<<
                  8) >>>
              16))]
  unfold gf16At shiftTableAt tokenInitAt at hcont; dsimp only at hcont
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (hcont _
      (by simp only [wp_norm, hule, hult, hult2, hhi])
      (by wp_norm_lhs) (by simp only [wp_norm, hsp]) (by simp only [arm64_norm, wp_norm]) rfl
      (by simp only [wp_norm, hx18]) (by simp only [wp_norm])
      (by simp only [wp_norm, hx21]) (by simp only [wp_norm, hx24])
      (by simp only [wp_norm, hx26, hadd2]) (by wp_norm_lhs))

/-! ## 2. Pair Loop, Reload, and Full `parallelMult_sepWP` (`+2736 -> +3784`) -/

/-- Action of the pair loop (`0x6b0bc..0x6b0ec -> 0x6aec4..0x6b0b8`) on a `List GF16`:
    multiplies all complete pairs by `yv` and leaves a trailing odd element unchanged. -/
def parallelMultPairs (yv : BitVec 16) : List GF16 → List GF16
  | [] => []
  | [last] => [last]
  | c1 :: c2 :: rest =>
    ⟨unaccelerated.mul yv c1.value⟩ ::
    ⟨unaccelerated.mul yv c2.value⟩ ::
    parallelMultPairs yv rest

@[simp]
theorem parallelMultPairs_nil (yv : BitVec 16) :
    parallelMultPairs yv [] = [] := rfl

@[simp]
theorem parallelMultPairs_singleton (yv : BitVec 16) (last : GF16) :
    parallelMultPairs yv [last] = [last] := rfl

@[simp]
theorem parallelMultPairs_pair_cons (yv : BitVec 16) (c1 c2 : GF16) (rest : List GF16) :
    parallelMultPairs yv (c1 :: c2 :: rest) =
      ⟨unaccelerated.mul yv c1.value⟩ ::
      ⟨unaccelerated.mul yv c2.value⟩ ::
      parallelMultPairs yv rest := rfl

theorem parallelMultPairs_even_eq (yv : BitVec 16) :
    ∀ cs : List GF16, cs.length % 2 = 0 →
      parallelMultPairs yv cs = parallelMult ⟨yv⟩ cs
  | [], _ => rfl
  | [_], h => by simp at h
  | c1 :: c2 :: rest, h => by
    have h' : rest.length % 2 = 0 := by simp at h; omega
    simp [parallelMultPairs_pair_cons, parallelMult_pair_cons, parallelMultPairs_even_eq yv rest h']

theorem gf16SliceAt_pair_cons (ptr : BitVec 64) (c1 c2 : GF16) (rest : List GF16) :
    gf16SliceAt ptr (c1 :: c2 :: rest) =
      (gf16At c1 ptr ∗ gf16At c2 (ptr + 2#64) ∗ gf16SliceAt (ptr + 4#64) rest) := by
  simp only [gf16SliceAt, arrayAt, gf16Stride, BitVec.ofNat_eq_ofNat, sepConj_assoc]
  rw [show (ptr + 2#64) + 2#64 = ptr + 4#64 by bv_omega]

theorem gf16SliceAt_parallelMultPairs_odd (yv : BitVec 16) :
    ∀ (cs : List GF16) (ptr : BitVec 64),
      cs.length % 2 = 1 →
      ∃ (last : GF16) (Rest : SepProp),
        gf16SliceAt ptr (parallelMultPairs yv cs) =
          (gf16At last (ptr + BitVec.ofNat 64 (2 * (2 * (cs.length / 2)))) ∗ Rest) ∧
        (gf16At ⟨unaccelerated.mul last.value yv⟩
           (ptr + BitVec.ofNat 64 (2 * (2 * (cs.length / 2)))) ∗ Rest) =
          gf16SliceAt ptr (parallelMult ⟨yv⟩ cs)
  | [], _, h => by simp at h
  | [last], ptr, _ => by
    have h0 : ptr + BitVec.ofNat 64 (2 * (2 * (1 / 2))) = ptr := by bv_omega
    refine ⟨last, emp, ?_, ?_⟩ <;>
      simp only [List.length_singleton, parallelMultPairs_singleton, parallelMult_singleton,
        gf16SliceAt, arrayAt, h0]
  | c1 :: c2 :: rest, ptr, h => by
    have h' : rest.length % 2 = 1 := by simp at h; omega
    obtain ⟨last, Rest', hpre, hpost⟩ := gf16SliceAt_parallelMultPairs_odd yv rest (ptr + 4#64) h'
    have haddr : (ptr + 4#64) + BitVec.ofNat 64 (2 * (2 * (rest.length / 2))) =
        ptr + BitVec.ofNat 64 (2 * (2 * ((c1 :: c2 :: rest).length / 2))) := by
      have hdiv : (c1 :: c2 :: rest).length / 2 = rest.length / 2 + 1 := by simp; omega
      rw [hdiv, show 2 * (2 * (rest.length / 2 + 1)) = 4 + 2 * (2 * (rest.length / 2)) by omega,
          BitVec.ofNat_add]; bv_omega
    refine ⟨last,
      gf16At ⟨unaccelerated.mul yv c1.value⟩ ptr ∗
        gf16At ⟨unaccelerated.mul yv c2.value⟩ (ptr + 2#64) ∗ Rest',
      ?_, ?_⟩
    · rw [parallelMultPairs_pair_cons, gf16SliceAt_pair_cons, hpre, ← haddr]; ac_rfl
    · rw [parallelMult_pair_cons, gf16SliceAt_pair_cons, ← hpost, ← haddr]; dsimp only; ac_rfl

/-- Multi-iteration pair loop (`0x6b0bc..0x6b0ec -> 0x6aec4..0x6b0b8`, `+3384 -> +3576`). -/
theorem parallelMultPairLoop_sepWP {b : BitVec 64} {ext : String → Option (State → State)}
    {ret : BitVec 64} {post : State → SepProp → Prop}
    (hb : b &&& 0xfff#64 = 0#64) (yv : BitVec 16) :
    ∀ (rest : List GF16) (k n : Nat) (hrest_ge : 2 ≤ rest.length)
      (hn_eq : n = 2 * k + rest.length) (hn : n ≤ 0x0555555555555555)
      (s : State) (fsp ptr : BitVec 64)
      (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
      (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 3384#64)
      (hrun : s.status = .Running) (hsp : s.sp = fsp)
      (hx18 : s.readReg64 .x18 = b + bv% (ls_xref% 0x5e970 0x5e974))
      (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 n)
      (hx21 : s.readReg64 .x21 = BitVec.zeroExtend 64 yv)
      (hx24 : s.readReg64 .x24 = ptr)
      (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 (2 * (k + 1)))
      (hcont : ∀ s1 : State,
        s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 3576#64 →
        s1.status = .Running → s1.sp = fsp → s1.trace = s.trace →
        calleeSavedVRegs s1 = calleeSavedVRegs s →
        s1.readReg64 .x20 = BitVec.ofNat 64 n →
        s1.readReg64 .x21 = BitVec.zeroExtend 64 yv →
        s1.readReg64 .x26 = BitVec.ofNat 64 (2 * (n / 2 + 1)) →
        s1.readReg64 .x29 = s.readReg64 .x29 →
        SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s1
          (gf16SliceAt ptr (parallelMultPairs yv rest) ∗
           ((fsp + 136#64) ↦₆₄ BitVec.ofNat 64 n) ∗
           shiftTableAt fsp yv ∗ tokenInitAt b ∗ reduceTableAt b ∗ Frame) post),
      SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s
        (gf16SliceAt ptr rest ∗
         ((fsp + 136#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         shiftTableAt fsp yv ∗ tokenInitAt b ∗ reduceTableAt b ∗ Frame) post
  | [], _, _, hge, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp at hge
  | [_], _, _, hge, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp at hge
  | c1 :: c2 :: rest', k, n, _, hn_eq, hn, s, fsp, ptr, hfsp_align, Frame,
    hpc, hrun, hsp, hx18, hx20, hx21, hx24, hx26, hcont => by
    have hk : 2 * (k + 1) ≤ n := by simp at hn_eq; omega
    rw [gf16SliceAt_pair_cons]
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (parallelMultPairStep_sepWP hb k n hk hn yv c1 c2 s fsp ptr hfsp_align
        (gf16SliceAt (ptr + 4#64) rest' ∗ Frame)
        hpc hrun hsp hx18 hx20 hx21 hx24 hx26 ?_)
    intro s1 hpc1 hrun1 hsp1 htr1 hvregs1 hx18_1 hx20_1 hx21_1 hx24_1 hx26_1 hx29_1
    cases rest' with
    | nil =>
      have hlt : decide (n < 2 * (k + 2)) = true := by rw [decide_eq_true_iff]; simp at hn_eq; omega
      have hdiv : k + 2 = n / 2 + 1 := by simp at hn_eq; omega
      simp only [hlt, ↓reduceIte] at hpc1
      rw [hdiv] at hx26_1
      have hpair := gf16SliceAt_pair_cons ptr ⟨unaccelerated.mul yv c1.value⟩
        ⟨unaccelerated.mul yv c2.value⟩ (parallelMultPairs yv [])
      rw [← parallelMultPairs_pair_cons] at hpair
      refine SepWP.weaken_pre (Entails.of_eq (by rw [hpair]; ac_rfl))
        (hcont s1 hpc1 hrun1 hsp1 htr1 hvregs1 hx20_1 hx21_1 hx26_1 hx29_1)
    | cons c3 rest'' =>
      cases rest'' with
      | nil =>
        have hlt : decide (n < 2 * (k + 2)) = true := by rw [decide_eq_true_iff]; simp at hn_eq; omega
        have hdiv : k + 2 = n / 2 + 1 := by simp at hn_eq; omega
        simp only [hlt, ↓reduceIte] at hpc1
        rw [hdiv] at hx26_1
        have hpair := gf16SliceAt_pair_cons ptr ⟨unaccelerated.mul yv c1.value⟩
          ⟨unaccelerated.mul yv c2.value⟩ (parallelMultPairs yv [c3])
        rw [← parallelMultPairs_pair_cons] at hpair
        refine SepWP.weaken_pre (Entails.of_eq (by rw [hpair]; ac_rfl))
          (hcont s1 hpc1 hrun1 hsp1 htr1 hvregs1 hx20_1 hx21_1 hx26_1 hx29_1)
      | cons c4 rest''' =>
        have hlt : decide (n < 2 * (k + 2)) = false := by rw [decide_eq_false_iff_not]; simp at hn_eq; omega
        simp only [hlt, Bool.false_eq_true, ↓reduceIte] at hpc1
        have hge' : 2 ≤ (c3 :: c4 :: rest''').length := by simp
        have hn_eq' : n = 2 * (k + 1) + (c3 :: c4 :: rest''').length := by simp at hn_eq ⊢; omega
        refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
          (parallelMultPairLoop_sepWP hb yv (c3 :: c4 :: rest''') (k + 1) n hge' hn_eq' hn
            s1 fsp (ptr + 4#64) hfsp_align
            (gf16At ⟨unaccelerated.mul yv c1.value⟩ ptr ∗
             gf16At ⟨unaccelerated.mul yv c2.value⟩ (ptr + 2#64) ∗ Frame)
            hpc1 hrun1 hsp1 hx18_1 hx20_1 hx21_1 hx24_1 hx26_1 ?_)
        intro s2 hpc2 hrun2 hsp2 htr2 hvregs2 hx20_2 hx21_2 hx26_2 hx29_2
        have hpair := gf16SliceAt_pair_cons ptr ⟨unaccelerated.mul yv c1.value⟩
          ⟨unaccelerated.mul yv c2.value⟩ (parallelMultPairs yv (c3 :: c4 :: rest'''))
        rw [← parallelMultPairs_pair_cons] at hpair
        refine SepWP.weaken_pre (Entails.of_eq (by rw [hpair]; ac_rfl))
          (hcont s2 hpc2 hrun2 hsp2 (by rw [htr2, htr1]) (by rw [hvregs2, hvregs1]) hx20_2 hx21_2 hx26_2 (by rw [hx29_2, hx29_1]))

theorem ule_n_even {n : Nat} (hn : n ≤ 0x0555555555555555) :
    (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 (2 * (n / 2))) = decide (n % 2 = 0) := by
  by_cases h : n % 2 = 0
  · rw [decide_eq_true_iff.mpr h, BitVec.ule_iff_toNat_le, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  · rw [decide_eq_false_iff_not.mpr h, Bool.eq_false_iff, Ne, BitVec.ule_iff_toNat_le,
        BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega

theorem not_ult_even {n : Nat} (hn : n ≤ 0x0555555555555555) :
    (!((BitVec.ofNat 64 (2 * (n / 2))).ult (BitVec.ofNat 64 n))) = decide (n % 2 = 0) := by
  by_cases h : n % 2 = 0
  · rw [decide_eq_true_iff.mpr h, Bool.not_eq_true', Bool.eq_false_iff, Ne, BitVec.ult_iff_toNat_lt,
        BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  · rw [decide_eq_false_iff_not.mpr h, Bool.not_eq_false', BitVec.ult_iff_toNat_lt,
        BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega

/-- Reload block after the pair loop (`0x6b17c..0x6b198`, `+3576 -> +3784` if even, `+3608` if odd). -/
theorem parallelMultReload_sepWP {b : BitVec 64} {ext : String → Option (State → State)}
    {ret : BitVec 64} {post : State → SepProp → Prop}
    (n : Nat) (hn : n ≤ 0x0555555555555555) (yv : BitVec 16)
    (s : State) (fsp clonePtr v24 v25 v26 v27 : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 3576#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 n)
    (hx21 : s.readReg64 .x21 = BitVec.zeroExtend 64 yv)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 (2 * (n / 2 + 1)))
    (hcont : ∀ s1 : State,
      s1.pc = (if decide (n % 2 = 0) then
          (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 3784#64
        else
          (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 3608#64) →
      s1.status = .Running → s1.sp = fsp → s1.trace = s.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x19 = BitVec.ofNat 64 (2 * (n / 2)) →
      s1.readReg64 .x20 = BitVec.ofNat 64 n →
      s1.readReg64 .x21 = BitVec.zeroExtend 64 yv →
      s1.readReg64 .x22 = clonePtr →
      s1.readReg64 .x24 = v24 → s1.readReg64 .x25 = v25 →
      s1.readReg64 .x26 = v26 → s1.readReg64 .x27 = v27 →
      s1.readReg64 .x28 = 24#64 → s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s1
        (((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ v24) ∗
         ((fsp + 80#64) ↦₆₄ v26) ∗ ((fsp + 96#64) ↦₆₄ v25) ∗
         ((fsp + 112#64) ↦₆₄ clonePtr) ∗ Frame) post) :
    SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s
      (((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ v24) ∗
       ((fsp + 80#64) ↦₆₄ v26) ∗ ((fsp + 96#64) ↦₆₄ v25) ∗
       ((fsp + 112#64) ↦₆₄ clonePtr) ∗ Frame) post := by
  have hsub2 := sub2_ofNat_pair (n / 2)
  have hule := ule_n_even hn
  have hult := not_ult_even hn
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0xdf8 32
  dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc hcont ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  wp_steps
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (hcont _ (by simp only [wp_norm, hsub2, hule, hult]) (by wp_norm_lhs)
      (by simp only [wp_norm, hsp]) (by simp only [arm64_norm, wp_norm]) rfl
      (by simp only [wp_norm, hsub2]) (by simp only [wp_norm, hx20])
      (by simp only [wp_norm, hx21]) (by wp_norm_lhs)
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by wp_norm_lhs) (by wp_norm_lhs))

/-- Full inlined `spqr::encoding::gf::parallel_mult` (`0x6ae34..0x6b24c`, `+2736 -> +3784`).
    Multiplies every coefficient in `cs` (`cs ≠ []`) in-place by `pt.y = ⟨yv⟩` and preserves
    `x22, x24, x25, x26, x27, x28 = 24#64, x29`. -/
theorem parallelMult_sepWP {b : BitVec 64} {ext : String → Option (State → State)}
    {ret : BitVec 64} {post : State → SepProp → Prop}
    (hb : b &&& 0xfff#64 = 0#64)
    (cs : List GF16) (hcs_ne : cs ≠ []) (hn : cs.length ≤ 0x0555555555555555)
    (yv : BitVec 16)
    (s : State) (fsp clonePtr v24 v25 v26 v27 u112 u136 : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 2736#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 cs.length)
    (hx21 : s.readReg64 .x21 = BitVec.zeroExtend 64 yv)
    (hx22 : s.readReg64 .x22 = clonePtr)
    (hx24 : s.readReg64 .x24 = v24)
    (hx25 : s.readReg64 .x25 = v25)
    (hx26 : s.readReg64 .x26 = v26)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hcont : ∀ s1 : State,
      s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 3784#64 →
      s1.status = .Running → s1.sp = fsp → s1.trace = s.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x20 = BitVec.ofNat 64 cs.length →
      s1.readReg64 .x22 = clonePtr →
      s1.readReg64 .x24 = v24 → s1.readReg64 .x25 = v25 →
      s1.readReg64 .x26 = v26 → s1.readReg64 .x27 = v27 →
      s1.readReg64 .x28 = 24#64 → s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s1
        (gf16SliceAt clonePtr (parallelMult ⟨yv⟩ cs) ∗
         ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ v24) ∗
         ((fsp + 80#64) ↦₆₄ v26) ∗ ((fsp + 96#64) ↦₆₄ v25) ∗
         ∃∗ u112' : BitVec 64, ∃∗ u136' : BitVec 64,
           ((fsp + 112#64) ↦₆₄ u112') ∗ ((fsp + 136#64) ↦₆₄ u136') ∗
           shiftSlotsRawAt fsp ∗ tokenInitAt b ∗ reduceTableAt b ∗ Frame) post) :
    SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s
      (gf16SliceAt clonePtr cs ∗
       ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ v24) ∗
       ((fsp + 80#64) ↦₆₄ v26) ∗ ((fsp + 96#64) ↦₆₄ v25) ∗
       ((fsp + 112#64) ↦₆₄ u112) ∗ ((fsp + 136#64) ↦₆₄ u136) ∗
       shiftSlotsRawAt fsp ∗ tokenInitAt b ∗ reduceTableAt b ∗ Frame) post := by
  rcases cs with _ | ⟨c0, rest⟩
  · contradiction
  · rcases rest with _ | ⟨c1, rest'⟩
    · -- Case `cs = [c0]` (`cs.length = 1`): branches to `+3608` (`0x6b19c`)
      poly_next_chunk_fetches_range b (Rust.withPanics ext) 0xab0 16
      dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat,
        List.length_singleton] at hpc hx20 hcont ⊢
      generalize_entry hentry :
        (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
      examples_hide_fetches
      wp_steps
      subst hentry
      have h0 : clonePtr + BitVec.ofNat 64 (2 * 0) = clonePtr := by bv_omega
      simp only [parallelMult_singleton, gf16SliceAt, arrayAt, sepConj_emp] at hcont ⊢
      rw [← h0]
      refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
        (parallelMultOddTail_sepWP hb 0 yv c0 (by decide) _ fsp clonePtr hfsp_align
          (((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ v24) ∗
           ((fsp + 80#64) ↦₆₄ v26) ∗ ((fsp + 96#64) ↦₆₄ v25) ∗
           ((fsp + 112#64) ↦₆₄ u112) ∗ ((fsp + 136#64) ↦₆₄ u136) ∗
           shiftSlotsRawAt fsp ∗ Frame)
          (by wp_norm_goal) (by wp_norm_lhs) (by simp only [wp_norm, hsp])
          (by wp_norm_lhs) (by simp only [wp_norm, hx21]) (by simp only [wp_norm, hx22]) ?_)
      intro s1 hpc1 hrun1 hsp1 htr1 hvregs1 hx20_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
      rw [h0]
      refine SepWP.weaken_pre ?_
        (hcont s1 hpc1 hrun1 hsp1 (by simp only [arm64_norm, wp_norm] at htr1; exact htr1)
          (by simp only [arm64_norm, wp_norm] at hvregs1; exact hvregs1)
          (by simp only [wp_norm, hx20] at hx20_1; exact hx20_1) hx22_1
          (by simp only [wp_norm, hx24] at hx24_1; exact hx24_1)
          (by simp only [wp_norm, hx25] at hx25_1; exact hx25_1)
          (by simp only [wp_norm, hx26] at hx26_1; exact hx26_1)
          (by simp only [wp_norm, hx27] at hx27_1; exact hx27_1)
          (by simp only [wp_norm, hx28] at hx28_1; exact hx28_1)
          (by simp only [wp_norm] at hx29_1; exact hx29_1))
      refine Entails.trans (Entails.of_eq (show
        (gf16At ⟨unaccelerated.mul c0.value yv⟩ clonePtr ∗ tokenInitAt b ∗ reduceTableAt b ∗
         ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ v24) ∗
         ((fsp + 80#64) ↦₆₄ v26) ∗ ((fsp + 96#64) ↦₆₄ v25) ∗
         ((fsp + 112#64) ↦₆₄ u112) ∗ ((fsp + 136#64) ↦₆₄ u136) ∗
         shiftSlotsRawAt fsp ∗ Frame) =
        (gf16At ⟨unaccelerated.mul c0.value yv⟩ clonePtr ∗
         ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ v24) ∗
         ((fsp + 80#64) ↦₆₄ v26) ∗ ((fsp + 96#64) ↦₆₄ v25) ∗
         (((fsp + 112#64) ↦₆₄ u112) ∗ ((fsp + 136#64) ↦₆₄ u136) ∗
          shiftSlotsRawAt fsp ∗ tokenInitAt b ∗ reduceTableAt b ∗ Frame)) by ac_rfl)) ?_
      refine sepConj_mono_fbl (Entails.refl _) (sepConj_mono_fbl (Entails.refl _)
        (sepConj_mono_fbl (Entails.refl _) (sepConj_mono_fbl (Entails.refl _)
          (sepConj_mono_fbl (Entails.refl _) ?_))))
      exact Entails.sepExists_right u112 (Entails.sepExists_right u136 (Entails.refl _))
    · -- Case `cs = c0 :: c1 :: rest'` (`2 ≤ cs.length`): steps to `+2752` (`0x6ae44`)
      have hlen_lt : (c0 :: c1 :: rest').length < 2 ^ 64 := by omega
      have hlen_ge : 2 ≤ (c0 :: c1 :: rest').length := by simp
      have hne1 : (BitVec.ofNat 64 (c0 :: c1 :: rest').length != 1#64) = true := by
        rw [bne_iff_ne]; intro heq
        have hto := congrArg BitVec.toNat heq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen_lt] at hto
        change (c0 :: c1 :: rest').length = 1 at hto
        omega
      have hbeq1 : (BitVec.ofNat 64 (c0 :: c1 :: rest').length == 1#64) = false := by
        rw [beq_eq_false_iff_ne]; exact bne_iff_ne.mp hne1
      poly_next_chunk_fetches_range b (Rust.withPanics ext) 0xab0 8
      dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc hcont ⊢
      generalize_entry hentry :
        (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
      examples_hide_fetches
      wp_steps
      subst hentry
      refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
        (shiftTableInit_sepWP hb (c0 :: c1 :: rest').length yv _ fsp clonePtr hfsp_align u112 u136
          (gf16SliceAt clonePtr (c0 :: c1 :: rest') ∗
           ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ v24) ∗
           ((fsp + 80#64) ↦₆₄ v26) ∗ ((fsp + 96#64) ↦₆₄ v25) ∗
           tokenInitAt b ∗ reduceTableAt b ∗ Frame)
          (by simp only [wp_norm, hne1, hbeq1]) (by wp_norm_lhs) (by simp only [wp_norm, hsp])
          (by simp only [wp_norm, hx20]) (by simp only [wp_norm, hx21]) (by simp only [wp_norm, hx22]) ?_)
      intro s1 hpc1 hrun1 hsp1 htr1 hvregs1 hx18_1 hx20_1 hx21_1 hx22_1 hx24_1 hx26_1 hx28_1 hx29_1 hx30_1
      refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
        (parallelMultPairLoop_sepWP hb yv (c0 :: c1 :: rest') 0 (c0 :: c1 :: rest').length
          (by simp) (by omega) hn s1 fsp clonePtr hfsp_align
          (((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ v24) ∗
           ((fsp + 80#64) ↦₆₄ v26) ∗ ((fsp + 96#64) ↦₆₄ v25) ∗
           ((fsp + 112#64) ↦₆₄ clonePtr) ∗ Frame)
          hpc1 hrun1 hsp1 hx18_1 hx20_1 hx21_1 hx24_1 hx26_1 ?_)
      intro s2 hpc2 hrun2 hsp2 htr2 hvregs2 hx20_2 hx21_2 hx26_2 hx29_2
      refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
        (parallelMultReload_sepWP (c0 :: c1 :: rest').length hn yv s2 fsp clonePtr v24 v25 v26 v27
          hfsp_align
          (gf16SliceAt clonePtr (parallelMultPairs yv (c0 :: c1 :: rest')) ∗
           ((fsp + 136#64) ↦₆₄ BitVec.ofNat 64 (c0 :: c1 :: rest').length) ∗
           shiftTableAt fsp yv ∗ tokenInitAt b ∗ reduceTableAt b ∗ Frame)
          hpc2 hrun2 hsp2 hx20_2 hx21_2 hx26_2 ?_)
      intro s3 hpc3 hrun3 hsp3 htr3 hvregs3 hx19_3 hx20_3 hx21_3 hx22_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3
      by_cases heven : (c0 :: c1 :: rest').length % 2 = 0
      · have hdec : decide ((c0 :: c1 :: rest').length % 2 = 0) = true := decide_eq_true heven
        simp only [hdec, ↓reduceIte] at hpc3
        rw [parallelMultPairs_even_eq yv (c0 :: c1 :: rest') heven]
        refine SepWP.weaken_pre ?_
          (hcont s3 hpc3 hrun3 hsp3
            (by rw [htr3, htr2, htr1]; simp only [arm64_norm, wp_norm])
            (by rw [hvregs3, hvregs2, hvregs1]; simp only [arm64_norm, wp_norm])
            hx20_3 hx22_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3
            (by rw [hx29_3, hx29_2, hx29_1]; simp only [wp_norm]))
        refine Entails.trans (Entails.of_eq (show
          (((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ v24) ∗
           ((fsp + 80#64) ↦₆₄ v26) ∗ ((fsp + 96#64) ↦₆₄ v25) ∗
           ((fsp + 112#64) ↦₆₄ clonePtr) ∗
           gf16SliceAt clonePtr (parallelMult ⟨yv⟩ (c0 :: c1 :: rest')) ∗
           ((fsp + 136#64) ↦₆₄ BitVec.ofNat 64 (c0 :: c1 :: rest').length) ∗
           shiftTableAt fsp yv ∗ tokenInitAt b ∗ reduceTableAt b ∗ Frame) =
          (gf16SliceAt clonePtr (parallelMult ⟨yv⟩ (c0 :: c1 :: rest')) ∗
           ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ v24) ∗
           ((fsp + 80#64) ↦₆₄ v26) ∗ ((fsp + 96#64) ↦₆₄ v25) ∗
           (((fsp + 112#64) ↦₆₄ clonePtr) ∗
            ((fsp + 136#64) ↦₆₄ BitVec.ofNat 64 (c0 :: c1 :: rest').length) ∗
            shiftTableAt fsp yv ∗ tokenInitAt b ∗ reduceTableAt b ∗ Frame)) by ac_rfl)) ?_
        refine sepConj_mono_fbl (Entails.refl _) (sepConj_mono_fbl (Entails.refl _)
          (sepConj_mono_fbl (Entails.refl _) (sepConj_mono_fbl (Entails.refl _)
            (sepConj_mono_fbl (Entails.refl _) ?_))))
        refine Entails.sepExists_right clonePtr
          (Entails.sepExists_right (BitVec.ofNat 64 (c0 :: c1 :: rest').length) ?_)
        exact sepConj_mono_fbl (Entails.refl _) (sepConj_mono_fbl (Entails.refl _)
          (sepConj_mono_fbl (shiftTableAt_entails_raw fsp yv) (Entails.refl _)))
      · have hodd : (c0 :: c1 :: rest').length % 2 = 1 := by omega
        have hdec : decide ((c0 :: c1 :: rest').length % 2 = 0) = false := decide_eq_false heven
        simp only [hdec, Bool.false_eq_true, ↓reduceIte] at hpc3
        obtain ⟨last, Rest, hpre, hpost⟩ :=
          gf16SliceAt_parallelMultPairs_odd yv (c0 :: c1 :: rest') clonePtr hodd
        rw [hpre]
        refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
          (parallelMultOddTail_sepWP hb (2 * ((c0 :: c1 :: rest').length / 2)) yv last
            (by omega) s3 fsp clonePtr hfsp_align
            (Rest ∗ ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ v24) ∗
             ((fsp + 80#64) ↦₆₄ v26) ∗ ((fsp + 96#64) ↦₆₄ v25) ∗
             ((fsp + 112#64) ↦₆₄ clonePtr) ∗
             ((fsp + 136#64) ↦₆₄ BitVec.ofNat 64 (c0 :: c1 :: rest').length) ∗
             shiftTableAt fsp yv ∗ Frame)
            hpc3 hrun3 hsp3 hx19_3 hx21_3 hx22_3 ?_)
        intro s4 hpc4 hrun4 hsp4 htr4 hvregs4 hx20_4 hx22_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4
        have hcomb :
            (gf16At ⟨unaccelerated.mul last.value yv⟩
               (clonePtr + BitVec.ofNat 64 (2 * (2 * ((c0 :: c1 :: rest').length / 2)))) ∗
             tokenInitAt b ∗ reduceTableAt b ∗ Rest ∗
             ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ v24) ∗
             ((fsp + 80#64) ↦₆₄ v26) ∗ ((fsp + 96#64) ↦₆₄ v25) ∗
             ((fsp + 112#64) ↦₆₄ clonePtr) ∗
             ((fsp + 136#64) ↦₆₄ BitVec.ofNat 64 (c0 :: c1 :: rest').length) ∗
             shiftTableAt fsp yv ∗ Frame) =
            (gf16SliceAt clonePtr (parallelMult ⟨yv⟩ (c0 :: c1 :: rest')) ∗
             ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ v24) ∗
             ((fsp + 80#64) ↦₆₄ v26) ∗ ((fsp + 96#64) ↦₆₄ v25) ∗
             (((fsp + 112#64) ↦₆₄ clonePtr) ∗
              ((fsp + 136#64) ↦₆₄ BitVec.ofNat 64 (c0 :: c1 :: rest').length) ∗
              shiftTableAt fsp yv ∗ tokenInitAt b ∗ reduceTableAt b ∗ Frame)) := by
          rw [← hpost]; ac_rfl
        rw [hcomb]
        refine SepWP.weaken_pre ?_
          (hcont s4 hpc4 hrun4 hsp4
            (by rw [htr4, htr3, htr2, htr1]; simp only [arm64_norm, wp_norm])
            (by rw [hvregs4, hvregs3, hvregs2, hvregs1]; simp only [arm64_norm, wp_norm])
            (by rw [hx20_4, hx20_3]) hx22_4
            (by rw [hx24_4, hx24_3]) (by rw [hx25_4, hx25_3])
            (by rw [hx26_4, hx26_3]) (by rw [hx27_4, hx27_3])
            (by rw [hx28_4, hx28_3])
            (by rw [hx29_4, hx29_3, hx29_2, hx29_1]; simp only [wp_norm]))
        refine sepConj_mono_fbl (Entails.refl _) (sepConj_mono_fbl (Entails.refl _)
          (sepConj_mono_fbl (Entails.refl _) (sepConj_mono_fbl (Entails.refl _)
            (sepConj_mono_fbl (Entails.refl _) ?_))))
        refine Entails.sepExists_right clonePtr
          (Entails.sepExists_right (BitVec.ofNat 64 (c0 :: c1 :: rest').length) ?_)
        exact sepConj_mono_fbl (Entails.refl _) (sepConj_mono_fbl (Entails.refl _)
          (sepConj_mono_fbl (shiftTableAt_entails_raw fsp yv) (Entails.refl _)))

end CryptoVerification.SpqrV1.Poly.NextChunk

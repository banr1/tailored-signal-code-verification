/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget
public meta import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysDefs
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSum1Placed
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSumMult1Placed
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSumMultPlaced
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk` (Block `416`): Budget-Threaded `gf::parallel_mult`

Relocatable `[LibsignalPlacement]` verification of `unacceleratedMul_placed_vm_ok` (Block `384`)
and inlined `gf::parallel_mult` (`+2736 -> +3784` in Block `416`) threading `RustCliAllocBudget M`
and `VmPreserved`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSumPlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkPC_384 blkPC_416 blkPl_384 blkPl_416
   lscall_blk lsmpl lsρ sepWP_seq_lscl withMemEq)
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open CryptoVerification.RustHeap (arrayAt)
open CryptoVerification.LibsignalSpqrV1 (GF16 parallelMult)
open CryptoVerification.LibsignalSpqrV1.reduce (reduceByteEntry)
open CryptoVerification.LibsignalSpqrV1.unaccelerated (mul polyMul)
open CryptoVerification.SpqrV1.GF.Mul2U16
  (aligned_tokenOnce_placed step_ldar32 tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
  (polyMul_asm_eq polyReduce_asm_eq reduceTablePlacedAt reduceTablePlacedAt_focus16
   reduceTableSym uxtw1_idx1_eq uxtw1_idx2_eq)
open CryptoVerification.SpqrV1.Poly (gf16At gf16SliceAt)
open CryptoVerification.SpqrV1.Poly.ComputeAt
  (readReg32_setMem_pre readReg64_setMem_pre readReg_setMem_pre sp_setMem_pre)
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
  (readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
   readReg_setMem_setPC_pre readReg_setPC_pre sp_setMem_setPC_pre sp_setPC_pre)
open CryptoVerification.SpqrV1.Poly.NextChunk
  (csel_gt_cmn1_sxth32_sm_pl csel_gt_cmn1_sxth32_zext_sm_pl
   exists_pow_two_eq_eight_sm_pl exists_pow_two_eq_two_sm_pl
   gf16SliceAt_pair_cons_pl gf16SliceAt_parallelMultPairs_odd_pl
   parallelMultPairs_even_eq_pl parallelMultPairs_pair_cons_pl
   parallelMultPairs_pl parallelMult_singleton_pl
   pmTerm_bit0_sm_pl pmTerm_bit0_zext64_sm_pl pmTerm_mid_sm_pl pmTerm_sm_pl
   polyMul_pair_c1_eq_pl polyMul_pair_c2_eq_pl
   sbfx_bit0_sxth32_sm_pl
   shiftSlotsRawAt_pl shiftTableAt_entails_raw_pl shiftTableAt_pl
   sxth32_shl17_asr31_pl sxth32_shl18_asr31_pl sxth32_shl19_asr31_pl sxth32_shl20_asr31_pl
   sxth32_shl21_asr31_pl sxth32_shl22_asr31_pl sxth32_shl23_asr31_pl sxth32_shl24_asr31_pl
   sxth32_shl25_asr31_pl sxth32_shl26_asr31_pl sxth32_shl27_asr31_pl sxth32_shl28_asr31_pl
   sxth32_shl29_asr31_pl sxth32_shl30_asr31_pl
   truncate16_truncate32_64_sm_pl truncate16_zext64_16_sm_pl
   truncate32_and_zext64_sm_pl truncate32_shl_zext64_32_sm_pl
   truncate32_xor_zext64_sm_pl truncate32_zext64_16_sm_pl truncate32_zext64_sm_pl
   truncate64_sxth32_16_sm_pl zext16_trunc32_zext64_16_sm_pl)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget
  (sepWP_seg_416)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

private theorem pc_setMem_pre (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by cases s; rfl
private theorem status_setMem_pre (s : State) (m : Memory) : (s.setMem m).status = s.status := by
  cases s; rfl
private theorem pstate_setMem_pre (s : State) (m : Memory) : (s.setMem m).pstate = s.pstate := by
  cases s; rfl
private theorem trace_setMem_pre (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by
  cases s; rfl
private theorem fs_setMem_pre (s : State) (m : Memory) : (s.setMem m).fs = s.fs := by cases s; rfl
private theorem sigActions_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).sigActions = s.sigActions := by cases s; rfl
private theorem tpidrEl0_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
private theorem brkStart_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).brkStart = s.brkStart := by cases s; rfl
private theorem oracle_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).oracle = s.oracle := by cases s; rfl
private theorem symtab_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).symtab = s.symtab := by cases s; rfl
private theorem calleeSavedVRegs_setMem_pre (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  exists_pow_two_eq_two_sm_pl exists_pow_two_eq_eight_sm_pl polyReduce_asm_eq
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre pc_setMem_pre status_setMem_pre pstate_setMem_pre trace_setMem_pre
  fs_setMem_pre sigActions_setMem_pre tpidrEl0_setMem_pre brkStart_setMem_pre
  oracle_setMem_pre symtab_setMem_pre calleeSavedVRegs_setMem_pre
  readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

/-! ## 1. `VmPreserved`-Enhanced `unaccelerated::mul` (Block `384`) -/

/-- Relocatable specification of `spqr::encoding::gf::unaccelerated::mul` (Block `384`)
    augmenting `unacceleratedMulPlacedSpec` with `VmPreserved s0 sf` in the single pure postcondition. -/
def unacceleratedMulPlacedVmSpec [LibsignalPlacement] : Spec (BitVec 16 × BitVec 16) where
  pre := fun (a, b_arg) s =>
    ⌜BitVec.truncate 16 (s.readReg64 .x0) = a ∧
      BitVec.truncate 16 (s.readReg64 .x1) = b_arg⌝ ∗
      reduceTablePlacedAt
  post := fun (a, b_arg) s0 sf =>
    ⌜BitVec.truncate 16 (sf.readReg64 .x0) = mul a b_arg ∧
      sf.trace = s0.trace ∧
      VmPreserved s0 sf⌝ ∗
      reduceTablePlacedAt

/-- Block `384` (`spqr::encoding::gf::unaccelerated::mul`, zero memory stores) meets
    `unacceleratedMulPlacedVmSpec`. -/
theorem unacceleratedMul_placed_vm_ok [LibsignalPlacement] (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_384).rebase (blkPl_384).base H) (blkPl_384).base
      unacceleratedMulPlacedVmSpec := by
  simp only [unacceleratedMulPlacedVmSpec]
  wp_init ab s0
  wp_steps 52
  rw [polyMul_asm_eq]
  wp_steps 1
  wp_conv_pre =>
    rw [reduceTablePlacedAt_focus16 (BitVec.truncate 8 (polyMul ab.1 ab.2 >>> 24)),
        uxtw1_idx1_eq (polyMul ab.1 ab.2)]
  wp_steps 3
  wp_conv_pre =>
    rw [← uxtw1_idx1_eq (polyMul ab.1 ab.2),
        ← reduceTablePlacedAt_focus16 (BitVec.truncate 8 (polyMul ab.1 ab.2 >>> 24)),
        reduceTablePlacedAt_focus16
          (BitVec.truncate 8
            ((polyMul ab.1 ab.2 ^^^
                BitVec.zeroExtend 32
                    (reduceByteEntry (BitVec.truncate 8 (polyMul ab.1 ab.2 >>> 24))) <<<
                  8) >>>
              16)),
        uxtw1_idx2_eq]
  wp_steps 3
  wp_conv_pre =>
    rw [← uxtw1_idx2_eq,
        ← reduceTablePlacedAt_focus16
          (BitVec.truncate 8
            ((polyMul ab.1 ab.2 ^^^
                BitVec.zeroExtend 32
                    (reduceByteEntry (BitVec.truncate 8 (polyMul ab.1 ab.2 >>> 24))) <<<
                  8) >>>
              16))]
  wp_done

/-! ## 2. Budget-Threaded `gf::parallel_mult` (`+2736 -> +3784`, Block `416`) -/

attribute [local arm64_norm ↓, local wp_norm ↓]
  truncate32_zext64_sm_pl truncate32_zext64_16_sm_pl truncate32_shl_zext64_32_sm_pl
  truncate16_zext64_16_sm_pl zext16_trunc32_zext64_16_sm_pl
  truncate32_xor_zext64_sm_pl truncate32_and_zext64_sm_pl
  truncate64_sxth32_16_sm_pl sbfx_bit0_sxth32_sm_pl
  pmTerm_bit0_sm_pl pmTerm_bit0_zext64_sm_pl truncate16_truncate32_64_sm_pl
  sxth32_shl30_asr31_pl sxth32_shl29_asr31_pl sxth32_shl28_asr31_pl sxth32_shl27_asr31_pl
  sxth32_shl26_asr31_pl sxth32_shl25_asr31_pl sxth32_shl24_asr31_pl sxth32_shl23_asr31_pl
  sxth32_shl22_asr31_pl sxth32_shl21_asr31_pl sxth32_shl20_asr31_pl sxth32_shl19_asr31_pl
  sxth32_shl18_asr31_pl sxth32_shl17_asr31_pl
  pmTerm_mid_sm_pl csel_gt_cmn1_sxth32_sm_pl csel_gt_cmn1_sxth32_zext_sm_pl
  polyMul_pair_c1_eq_pl polyMul_pair_c2_eq_pl

@[local arm64_norm, local wp_norm]
private theorem shl_one_ofNat_eq_nat_aux (n : Nat) :
    BitVec.ofNat 64 n <<< 1 = BitVec.ofNat 64 (2 * n) := by
  have h1 : (BitVec.ofNat 64 n <<< 1).toNat = (BitVec.ofNat 64 (2 * n)).toNat := by
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
    have hsh : ∀ x : Nat, x <<< 1 = 2 * x := fun x => by rw [Nat.shiftLeft_eq]; omega
    rw [hsh]
    exact Nat.mul_mod_mod 2 n (2 ^ 64)
  exact BitVec.eq_of_toNat_eq h1

private theorem zext64_and_mask32_aux (w : BitVec 32) (b : Bool) :
    BitVec.zeroExtend 64 w &&& (if b = true then 4294967295#64 else 0#64) =
      BitVec.zeroExtend 64 (w &&& (if b = true then 0xffff_ffff#32 else 0#32)) := by
  cases b <;> bv_slice

@[local arm64_norm ↓, local wp_norm ↓]
private theorem pmTerm_bit0_64_aux (yv x : BitVec 16) :
    (if x.getLsbD 0 = true then 4294967295#64 else 0#64) &&& BitVec.zeroExtend 64 yv =
      BitVec.zeroExtend 64 (pmTerm_sm_pl yv x 0) := by
  have h : pmTerm_sm_pl yv x 0 =
      (BitVec.zeroExtend 32 yv <<< 0) &&& (if x.getLsbD 0 = true then 0xffff_ffff#32 else 0#32) := by
    unfold pmTerm_sm_pl; rfl
  rw [h]; generalize x.getLsbD 0 = b; cases b <;> bv_slice

@[local arm64_norm ↓, local wp_norm ↓]
private theorem pmTerm_mid_64_aux (yv x : BitVec 16) (i : Nat) :
    BitVec.zeroExtend 64 (BitVec.zeroExtend 32 yv <<< i) &&&
      (if x.getLsbD i = true then 4294967295#64 else 0#64) =
      BitVec.zeroExtend 64 (pmTerm_sm_pl yv x i) := by
  have h : pmTerm_sm_pl yv x i =
      (BitVec.zeroExtend 32 yv <<< i) &&& (if x.getLsbD i = true then 0xffff_ffff#32 else 0#32) := by
    unfold pmTerm_sm_pl; rfl
  rw [h]; exact zext64_and_mask32_aux _ _

@[local arm64_norm, local wp_norm]
private theorem sub2_ofNat_pair_aux (k : Nat) :
    BitVec.ofNat 64 (2 * (k + 1)) - 2#64 = BitVec.ofNat 64 (2 * k) := by
  have h2 : BitVec.ofNat 64 (2 * (k + 1)) = BitVec.ofNat 64 (2 * k) + 2#64 := by
    rw [show 2 * (k + 1) = 2 * k + 2 by omega, BitVec.ofNat_add]
  rw [h2]; bv_omega

@[local arm64_norm, local wp_norm]
private theorem sub2_ofNat_pair_add_aux (k : Nat) :
    BitVec.ofNat 64 (2 * (k + 1)) + 0xfffffffffffffffe#64 = BitVec.ofNat 64 (2 * k) := by
  have h1 : (0xfffffffffffffffe#64 : BitVec 64) = -2#64 := rfl
  have h2 : BitVec.ofNat 64 (2 * (k + 1)) = BitVec.ofNat 64 (2 * k) + 2#64 := by
    rw [show 2 * (k + 1) = 2 * k + 2 by omega, BitVec.ofNat_add]
  rw [h1, h2]; bv_omega

@[local arm64_norm, local wp_norm]
private theorem add2_ofNat_pair_aux (k : Nat) :
    BitVec.ofNat 64 (2 * (k + 1)) + 2#64 = BitVec.ofNat 64 (2 * (k + 2)) := by
  rw [show 2 * (k + 2) = 2 * (k + 1) + 2 by omega, BitVec.ofNat_add]

private theorem ule_n_2k_aux {k n : Nat} (hk : 2 * (k + 1) ≤ n) (hn : n ≤ 0x0555555555555555) :
    (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 (2 * k)) = false := by
  rw [Bool.eq_false_iff, Ne, BitVec.ule_iff_toNat_le, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega

private theorem ult_2k_n_aux {k n : Nat} (hk : 2 * (k + 1) ≤ n) (hn : n ≤ 0x0555555555555555) :
    (!((BitVec.ofNat 64 (2 * k)).ult (BitVec.ofNat 64 n))) = false := by
  rw [Bool.not_eq_false', BitVec.ult_iff_toNat_lt, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega

private theorem ult_n_2k2_aux {k n : Nat} (hn : n ≤ 0x0555555555555555) (hk : 2 * (k + 1) ≤ n) :
    (BitVec.ofNat 64 n).ult (BitVec.ofNat 64 (2 * (k + 2))) = decide (n < 2 * (k + 2)) := by
  by_cases h : n < 2 * (k + 2)
  · rw [decide_eq_true_iff.mpr h, BitVec.ult_iff_toNat_lt, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  · rw [decide_eq_false_iff_not.mpr h, Bool.eq_false_iff, Ne, BitVec.ult_iff_toNat_lt,
        BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega

private theorem hi_2k2_n_aux {k n : Nat} (hn : n ≤ 0x0555555555555555) (hk : 2 * (k + 1) ≤ n) :
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

private theorem ule_n_even_aux {n : Nat} (hn : n ≤ 0x0555555555555555) :
    (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 (2 * (n / 2))) = decide (n % 2 = 0) := by
  by_cases h : n % 2 = 0
  · rw [decide_eq_true_iff.mpr h, BitVec.ule_iff_toNat_le, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  · rw [decide_eq_false_iff_not.mpr h, Bool.eq_false_iff, Ne, BitVec.ule_iff_toNat_le,
        BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega

private theorem not_ult_even_aux {n : Nat} (hn : n ≤ 0x0555555555555555) :
    (!((BitVec.ofNat 64 (2 * (n / 2))).ult (BitVec.ofNat 64 n))) = decide (n % 2 = 0) := by
  by_cases h : n % 2 = 0
  · rw [decide_eq_true_iff.mpr h, Bool.not_eq_true', Bool.eq_false_iff, Ne, BitVec.ult_iff_toNat_lt,
        BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  · rw [decide_eq_false_iff_not.mpr h, Bool.not_eq_false', BitVec.ult_iff_toNat_lt,
        BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega

/-- Budget-threaded precomputed shift-table setup (`(blkPl_416).base + 2752#64 -> + 3384#64`). -/
theorem shiftTableInit_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {post : State → SepProp → Prop}
    (n : Nat) (yv : BitVec 16)
    (s : State) (fsp clonePtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u112 u136 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 2752#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 n)
    (hx21 : s.readReg64 .x21 = BitVec.zeroExtend 64 yv)
    (hx22 : s.readReg64 .x22 = clonePtr)
    (hcont : ∀ s1 : State,
      s1.pc = (blkPl_416).base + 3384#64 →
      s1.status = .Running → s1.sp = fsp → s1.trace = s.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x18 = lsρ reduceTableSym →
      s1.readReg64 .x20 = BitVec.ofNat 64 n →
      s1.readReg64 .x21 = BitVec.zeroExtend 64 yv →
      s1.readReg64 .x22 = clonePtr →
      s1.readReg64 .x24 = clonePtr →
      s1.readReg64 .x26 = 2#64 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      s1.readReg64 .x30 = s.readReg64 .x30 →
      SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s1
        (A.pool lim st s1 ∗
         shiftTableAt_pl fsp yv ∗ ((fsp + 112#64) ↦₆₄ clonePtr) ∗
         ((fsp + 136#64) ↦₆₄ BitVec.ofNat 64 n) ∗ Frame) post) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s
      (A.pool lim st s ∗
       shiftSlotsRawAt_pl fsp ∗ ((fsp + 112#64) ↦₆₄ u112) ∗
       ((fsp + 136#64) ↦₆₄ u136) ∗ Frame) post := by
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc hcont ⊢
  unfold shiftSlotsRawAt_pl
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro d148; apply SepWP.exists_elim; intro d152
  apply SepWP.exists_elim; intro d156; apply SepWP.exists_elim; intro d160
  apply SepWP.exists_elim; intro d164; apply SepWP.exists_elim; intro d168
  apply SepWP.exists_elim; intro d172; apply SepWP.exists_elim; intro d176
  apply SepWP.exists_elim; intro d180; apply SepWP.exists_elim; intro d184
  apply SepWP.exists_elim; intro d192; apply SepWP.exists_elim; intro d200
  apply SepWP.exists_elim; intro d208; apply SepWP.exists_elim; intro d216
  apply SepWP.exists_elim; intro d224
  apply sepWP_seg_416 (mid := (blkPl_416).base + 3384#64)
  intro _m_strip
  wp_steps 32
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by simp only [arm64_norm, wp_norm, hrun, hsp]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  unfold shiftTableAt_pl at hcont; dsimp only at hcont
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (hcont _ (by wp_norm_goal) (by wp_norm_lhs) (by simp only [arm64_norm, wp_norm, hsp])
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm])
      (by simp only [arm64_norm, wp_norm])
      (by simp only [arm64_norm, wp_norm, hx20]) (by simp only [arm64_norm, wp_norm, hx21])
      (by simp only [arm64_norm, wp_norm, hx22]) (by simp only [arm64_norm, wp_norm, hx22])
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs))

/-- Budget-threaded odd trailing element (`(blkPl_416).base + 3608#64 -> + 3784#64`). -/
theorem parallelMultOddTail_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {post : State → SepProp → Prop}
    (idx : Nat) (yv : BitVec 16) (last : GF16) (hidx_lt : 2 * idx < 2 ^ 63)
    (s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp clonePtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 3608#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 idx)
    (hx21 : s.readReg64 .x21 = BitVec.zeroExtend 64 yv)
    (hx22 : s.readReg64 .x22 = clonePtr)
    (hcont : ∀ s1 : State,
      LibsignalCodeLoaded lsmpl s1.mem →
      s1.pc = (blkPl_416).base + 3784#64 →
      s1.status = .Running → s1.sp = fsp → s1.trace = s.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x22 = clonePtr →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s1
        (A.pool lim st s1 ∗
         gf16At ⟨mul last.value yv⟩ (clonePtr + BitVec.ofNat 64 (2 * idx)) ∗
         tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ Frame) post) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s
      (A.pool lim st s ∗
       gf16At last (clonePtr + BitVec.ofNat 64 (2 * idx)) ∗
       tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ Frame) post := by
  apply sepWP_seq_lscl (mid := (blkPl_416).base + 3784#64) hcl
  have hmul : subroutine_ok ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (lsmpl.base 384) (withMemEq s.mem unacceleratedMulPlacedVmSpec) :=
    lscall_blk (unacceleratedMul_placed_vm_ok (Rust.withPanics ext)) hcl
  have halign := aligned_tokenOnce_placed
  try dsimp only [BitVec.ofNat_eq_ofNat] at hmul hpc hcont ⊢
  have hlsl : BitVec.ofNat 64 idx <<< 1 = BitVec.ofNat 64 (2 * idx) := shl_one_ofNat_eq_nat_aux idx
  unfold gf16At tokenInitPlacedAt
  wp_steps 2
  apply step_ldar32
  · wp_norm_lhs
  · wp_norm_lhs
  · simp only [arm64_norm]; rfl
  · wp_norm_lhs
  · wp_norm_lhs
  · exact halign
  · wp_sep_access
  · wp_norm_lhs
  wp_steps 8
  wp_conv_pre => simp only [arm64_norm, wp_norm]
  wp_call hmul
  have hvm_sf : VmPreserved s sf :=
    VmPreserved.trans (by simp only [arm64_norm, wp_norm]) hpost
  have hpool_sf : A.pool lim st s = A.pool lim st sf :=
    (A.pool_transport lim st s sf hvm_sf).symm
  wp_conv_pre => rw [hpool_sf]
  apply sepWP_seg_416 (mid := (blkPl_416).base + 3784#64)
  intro _m_strip
  wp_steps 1
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by simp only [arm64_norm, wp_norm, hrun_sf]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl1
  unfold gf16At tokenInitPlacedAt at hcont; dsimp only at hcont
  have htr_sf : sf.trace = s.trace := by assumption
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (hcont _ hcl1 (by wp_norm_goal) (by wp_norm_lhs)
      (by simp only [arm64_norm, wp_norm, ‹sf.sp = _›, hsp])
      (by simp only [arm64_norm, wp_norm, htr_sf])
      (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, h_1])
      (by simp only [arm64_norm, wp_norm, h_3, hx22])
      (by simp only [arm64_norm, wp_norm, h_5])
      (by simp only [arm64_norm, wp_norm, h_6])
      (by simp only [arm64_norm, wp_norm, h_7])
      (by simp only [arm64_norm, wp_norm, h_8])
      (by simp only [arm64_norm, wp_norm, h_9])
      (by simp only [arm64_norm, wp_norm, hcs_sf]))

set_option maxHeartbeats 1600000 in
/-- Budget-threaded single iteration of the `gf::parallel_mult` pair loop (`+3384`). -/
theorem parallelMultPairStep_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {post : State → SepProp → Prop}
    (k n : Nat) (hk : 2 * (k + 1) ≤ n) (hn : n ≤ 0x0555555555555555)
    (yv : BitVec 16) (c1 c2 : GF16)
    (s : State) (fsp ptr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 3384#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx18 : s.readReg64 .x18 = lsρ reduceTableSym)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 n)
    (hx21 : s.readReg64 .x21 = BitVec.zeroExtend 64 yv)
    (hx24 : s.readReg64 .x24 = ptr)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 (2 * (k + 1)))
    (hcont : ∀ s1 : State,
      s1.pc = (if decide (n < 2 * (k + 2)) then
          (blkPl_416).base + 3576#64
        else
          (blkPl_416).base + 3384#64) →
      s1.status = .Running → s1.sp = fsp → s1.trace = s.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x18 = lsρ reduceTableSym →
      s1.readReg64 .x20 = BitVec.ofNat 64 n →
      s1.readReg64 .x21 = BitVec.zeroExtend 64 yv →
      s1.readReg64 .x24 = ptr + 4#64 →
      s1.readReg64 .x26 = BitVec.ofNat 64 (2 * (k + 2)) →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s1
        (A.pool lim st s1 ∗
         gf16At ⟨mul yv c1.value⟩ ptr ∗
         gf16At ⟨mul yv c2.value⟩ (ptr + 2#64) ∗
         ((fsp + 136#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         shiftTableAt_pl fsp yv ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ Frame) post) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s
      (A.pool lim st s ∗
       gf16At c1 ptr ∗ gf16At c2 (ptr + 2#64) ∗
       ((fsp + 136#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       shiftTableAt_pl fsp yv ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ Frame) post := by
  have halign := aligned_tokenOnce_placed
  have hsub2 := sub2_ofNat_pair_aux k
  have hadd2 := add2_ofNat_pair_aux k
  have hule := ule_n_2k_aux hk hn
  have hult := ult_2k_n_aux hk hn
  have hult2 := ult_n_2k2_aux hn hk
  have hhi := hi_2k2_n_aux hn hk
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc hcont ⊢
  unfold gf16At shiftTableAt_pl tokenInitPlacedAt; dsimp only
  apply sepWP_seg_416
    (mid := if decide (n < 2 * (k + 2)) then
        (blkPl_416).base + 3576#64
      else
        (blkPl_416).base + 3384#64)
  intro _m_strip
  wp_steps 7
  apply step_ldar32
  · wp_norm_lhs
  · wp_norm_lhs
  · simp only [arm64_norm]; rfl
  · wp_norm_lhs
  · wp_norm_lhs
  · exact halign
  · wp_sep_access
  · wp_norm_lhs
  wp_steps 5
  wp_steps 68
  wp_conv_pre =>
    rw [reduceTablePlacedAt_focus16 (BitVec.truncate 8 (polyMul yv c1.value >>> 24)),
        uxtw1_idx1_eq (polyMul yv c1.value)]
  wp_steps 40
  wp_conv_pre =>
    rw [← uxtw1_idx1_eq (polyMul yv c1.value),
        ← reduceTablePlacedAt_focus16 (BitVec.truncate 8 (polyMul yv c1.value >>> 24)),
        reduceTablePlacedAt_focus16
          (BitVec.truncate 8
            ((polyMul yv c1.value ^^^
                BitVec.zeroExtend 32
                    (reduceByteEntry (BitVec.truncate 8 (polyMul yv c1.value >>> 24))) <<<
                  8) >>>
              16)),
        uxtw1_idx2_eq]
  wp_steps 10
  wp_conv_pre =>
    rw [← uxtw1_idx2_eq,
        ← reduceTablePlacedAt_focus16
          (BitVec.truncate 8
            ((polyMul yv c1.value ^^^
                BitVec.zeroExtend 32
                    (reduceByteEntry (BitVec.truncate 8 (polyMul yv c1.value >>> 24))) <<<
                  8) >>>
              16)),
        reduceTablePlacedAt_focus16 (BitVec.truncate 8 (polyMul yv c2.value >>> 24)),
        uxtw1_idx1_eq (polyMul yv c2.value)]
  wp_steps 3
  wp_conv_pre =>
    rw [← uxtw1_idx1_eq (polyMul yv c2.value),
        ← reduceTablePlacedAt_focus16 (BitVec.truncate 8 (polyMul yv c2.value >>> 24)),
        reduceTablePlacedAt_focus16
          (BitVec.truncate 8
            ((polyMul yv c2.value ^^^
                BitVec.zeroExtend 32
                    (reduceByteEntry (BitVec.truncate 8 (polyMul yv c2.value >>> 24))) <<<
                  8) >>>
              16)),
        uxtw1_idx2_eq]
  wp_steps 5
  wp_conv_pre =>
    rw [← uxtw1_idx2_eq,
        ← reduceTablePlacedAt_focus16
          (BitVec.truncate 8
            ((polyMul yv c2.value ^^^
                BitVec.zeroExtend 32
                    (reduceByteEntry (BitVec.truncate 8 (polyMul yv c2.value >>> 24))) <<<
                  8) >>>
              16))]
  wp_steps 1
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hule, hult, hult2, hhi])
    (by wp_norm_lhs)
    fun _m_real _hnsp => ?_
  refine SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by simp only [arm64_norm, wp_norm, hrun, hsp, hule, hult, hult2, hhi]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  unfold gf16At shiftTableAt_pl tokenInitPlacedAt at hcont; dsimp only at hcont
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (hcont _
      (by simp only [arm64_norm, wp_norm, hule, hult, hult2, hhi])
      (by wp_norm_lhs)
      (by simp only [arm64_norm, wp_norm, hsp])
      (by simp only [arm64_norm, wp_norm])
      (by simp only [arm64_norm, wp_norm])
      (by simp only [arm64_norm, wp_norm, hx18])
      (by simp only [arm64_norm, wp_norm])
      (by simp only [arm64_norm, wp_norm, hx21])
      (by simp only [arm64_norm, wp_norm, hx24])
      (by simp only [arm64_norm, wp_norm, hx26, hadd2])
      (by wp_norm_lhs))

/-- Budget-threaded multi-iteration pair loop (`(blkPl_416).base + 3384#64 -> + 3576#64`). -/
theorem parallelMultPairLoop_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {post : State → SepProp → Prop}
    (yv : BitVec 16) :
    ∀ (rest : List GF16) (k n : Nat) (hrest_ge : 2 ≤ rest.length)
      (hn_eq : n = 2 * k + rest.length) (hn : n ≤ 0x0555555555555555)
      (s : State) (fsp ptr : BitVec 64)
      (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
      (hpc : s.pc = (blkPl_416).base + 3384#64)
      (hrun : s.status = .Running) (hsp : s.sp = fsp)
      (hx18 : s.readReg64 .x18 = lsρ reduceTableSym)
      (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 n)
      (hx21 : s.readReg64 .x21 = BitVec.zeroExtend 64 yv)
      (hx24 : s.readReg64 .x24 = ptr)
      (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 (2 * (k + 1)))
      (hcont : ∀ s1 : State,
        s1.pc = (blkPl_416).base + 3576#64 →
        s1.status = .Running → s1.sp = fsp → s1.trace = s.trace →
        calleeSavedVRegs s1 = calleeSavedVRegs s →
        s1.readReg64 .x20 = BitVec.ofNat 64 n →
        s1.readReg64 .x21 = BitVec.zeroExtend 64 yv →
        s1.readReg64 .x26 = BitVec.ofNat 64 (2 * (n / 2 + 1)) →
        s1.readReg64 .x29 = s.readReg64 .x29 →
        SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s1
          (A.pool lim st s1 ∗
           gf16SliceAt ptr (parallelMultPairs_pl yv rest) ∗
           ((fsp + 136#64) ↦₆₄ BitVec.ofNat 64 n) ∗
           shiftTableAt_pl fsp yv ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ Frame) post),
      SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s
        (A.pool lim st s ∗
         gf16SliceAt ptr rest ∗
         ((fsp + 136#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         shiftTableAt_pl fsp yv ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ Frame) post
  | [], _, _, hge, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp at hge
  | [_], _, _, hge, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp at hge
  | c1 :: c2 :: rest', k, n, _, hn_eq, hn, s, fsp, ptr, hfsp_align, Frame,
    hpc, hrun, hsp, hx18, hx20, hx21, hx24, hx26, hcont => by
    have hk : 2 * (k + 1) ≤ n := by simp at hn_eq; omega
    rw [gf16SliceAt_pair_cons_pl]
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (parallelMultPairStep_placed_sepWP (M := M) (A := A) (lim := lim) (st := st)
        k n hk hn yv c1 c2 s fsp ptr hfsp_align
        (gf16SliceAt (ptr + 4#64) rest' ∗ Frame)
        hpc hrun hsp hx18 hx20 hx21 hx24 hx26 ?_)
    intro s1 hpc1 hrun1 hsp1 htr1 hvregs1 hx18_1 hx20_1 hx21_1 hx24_1 hx26_1 hx29_1
    cases rest' with
    | nil =>
      have hlt : decide (n < 2 * (k + 2)) = true := by rw [decide_eq_true_iff]; simp at hn_eq; omega
      have hdiv : k + 2 = n / 2 + 1 := by simp at hn_eq; omega
      simp only [hlt, ↓reduceIte] at hpc1
      rw [hdiv] at hx26_1
      have hpair := gf16SliceAt_pair_cons_pl ptr ⟨mul yv c1.value⟩
        ⟨mul yv c2.value⟩ (parallelMultPairs_pl yv [])
      rw [← parallelMultPairs_pair_cons_pl] at hpair
      refine SepWP.weaken_pre (Entails.of_eq (by rw [hpair]; sep_ac_rfl))
        (hcont s1 hpc1 hrun1 hsp1 htr1 hvregs1 hx20_1 hx21_1 hx26_1 hx29_1)
    | cons c3 rest'' =>
      cases rest'' with
      | nil =>
        have hlt : decide (n < 2 * (k + 2)) = true := by rw [decide_eq_true_iff]; simp at hn_eq; omega
        have hdiv : k + 2 = n / 2 + 1 := by simp at hn_eq; omega
        simp only [hlt, ↓reduceIte] at hpc1
        rw [hdiv] at hx26_1
        have hpair := gf16SliceAt_pair_cons_pl ptr ⟨mul yv c1.value⟩
          ⟨mul yv c2.value⟩ (parallelMultPairs_pl yv [c3])
        rw [← parallelMultPairs_pair_cons_pl] at hpair
        refine SepWP.weaken_pre (Entails.of_eq (by rw [hpair]; sep_ac_rfl))
          (hcont s1 hpc1 hrun1 hsp1 htr1 hvregs1 hx20_1 hx21_1 hx26_1 hx29_1)
      | cons c4 rest''' =>
        have hlt : decide (n < 2 * (k + 2)) = false := by rw [decide_eq_false_iff_not]; simp at hn_eq; omega
        simp only [hlt, Bool.false_eq_true, ↓reduceIte] at hpc1
        have hge' : 2 ≤ (c3 :: c4 :: rest''').length := by simp
        have hn_eq' : n = 2 * (k + 1) + (c3 :: c4 :: rest''').length := by simp at hn_eq ⊢; omega
        refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (parallelMultPairLoop_placed_sepWP (M := M) (A := A) (lim := lim) (st := st)
            yv (c3 :: c4 :: rest''') (k + 1) n hge' hn_eq' hn
            s1 fsp (ptr + 4#64) hfsp_align
            (gf16At ⟨mul yv c1.value⟩ ptr ∗
             gf16At ⟨mul yv c2.value⟩ (ptr + 2#64) ∗ Frame)
            hpc1 hrun1 hsp1 hx18_1 hx20_1 hx21_1 hx24_1 hx26_1 ?_)
        intro s2 hpc2 hrun2 hsp2 htr2 hvregs2 hx20_2 hx21_2 hx26_2 hx29_2
        have hpair := gf16SliceAt_pair_cons_pl ptr ⟨mul yv c1.value⟩
          ⟨mul yv c2.value⟩ (parallelMultPairs_pl yv (c3 :: c4 :: rest'''))
        rw [← parallelMultPairs_pair_cons_pl] at hpair
        refine SepWP.weaken_pre (Entails.of_eq (by rw [hpair]; sep_ac_rfl))
          (hcont s2 hpc2 hrun2 hsp2 (by rw [htr2, htr1]) (by rw [hvregs2, hvregs1])
            hx20_2 hx21_2 hx26_2 (by rw [hx29_2, hx29_1]))

/-- Budget-threaded reload block after the pair loop (`+3576 -> +3784` if even, `+3608` if odd). -/
theorem parallelMultReload_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {post : State → SepProp → Prop}
    (n : Nat) (hn : n ≤ 0x0555555555555555) (yv : BitVec 16)
    (s : State) (fsp clonePtr v24 v25 v26 v27 : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 3576#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 n)
    (hx21 : s.readReg64 .x21 = BitVec.zeroExtend 64 yv)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 (2 * (n / 2 + 1)))
    (hcont : ∀ s1 : State,
      s1.pc = (if decide (n % 2 = 0) then
          (blkPl_416).base + 3784#64
        else
          (blkPl_416).base + 3608#64) →
      s1.status = .Running → s1.sp = fsp → s1.trace = s.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x19 = BitVec.ofNat 64 (2 * (n / 2)) →
      s1.readReg64 .x20 = BitVec.ofNat 64 n →
      s1.readReg64 .x21 = BitVec.zeroExtend 64 yv →
      s1.readReg64 .x22 = clonePtr →
      s1.readReg64 .x24 = v24 → s1.readReg64 .x25 = v25 →
      s1.readReg64 .x26 = v26 → s1.readReg64 .x27 = v27 →
      s1.readReg64 .x28 = 24#64 → s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s1
        (A.pool lim st s1 ∗
         ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ v24) ∗
         ((fsp + 80#64) ↦₆₄ v26) ∗ ((fsp + 96#64) ↦₆₄ v25) ∗
         ((fsp + 112#64) ↦₆₄ clonePtr) ∗ Frame) post) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s
      (A.pool lim st s ∗
       ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ v24) ∗
       ((fsp + 80#64) ↦₆₄ v26) ∗ ((fsp + 96#64) ↦₆₄ v25) ∗
       ((fsp + 112#64) ↦₆₄ clonePtr) ∗ Frame) post := by
  have hsub2 := sub2_ofNat_pair_aux (n / 2)
  have hule := ule_n_even_aux hn
  have hult := not_ult_even_aux hn
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc hcont ⊢
  apply sepWP_seg_416
    (mid := if decide (n % 2 = 0) then
        (blkPl_416).base + 3784#64
      else
        (blkPl_416).base + 3608#64)
  intro _m_strip
  wp_steps 8
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hsub2, hule, hult])
    (by wp_norm_lhs)
    fun _m_real _hnsp => ?_
  refine SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by simp only [arm64_norm, wp_norm, hrun, hsp, hsub2, hule, hult]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (hcont _
      (by simp only [arm64_norm, wp_norm, hsub2, hule, hult])
      (by wp_norm_lhs)
      (by simp only [arm64_norm, wp_norm, hsp])
      (by simp only [arm64_norm, wp_norm])
      (by simp only [arm64_norm, wp_norm])
      (by simp only [arm64_norm, wp_norm, hsub2])
      (by simp only [arm64_norm, wp_norm, hx20])
      (by simp only [arm64_norm, wp_norm, hx21])
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by wp_norm_lhs) (by wp_norm_lhs))

/-- Budget-threaded full inlined `spqr::encoding::gf::parallel_mult` (`+2736 -> +3784`). -/
theorem parallelMult_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {post : State → SepProp → Prop}
    (cs : List GF16) (hcs_ne : cs ≠ []) (hn : cs.length ≤ 0x0555555555555555)
    (yv : BitVec 16)
    (s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp clonePtr v24 v25 v26 v27 u112 u136 : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 2736#64)
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
      LibsignalCodeLoaded lsmpl s1.mem →
      s1.pc = (blkPl_416).base + 3784#64 →
      s1.status = .Running → s1.sp = fsp → s1.trace = s.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x20 = BitVec.ofNat 64 cs.length →
      s1.readReg64 .x22 = clonePtr →
      s1.readReg64 .x24 = v24 → s1.readReg64 .x25 = v25 →
      s1.readReg64 .x26 = v26 → s1.readReg64 .x27 = v27 →
      s1.readReg64 .x28 = 24#64 → s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s1
        (A.pool lim st s1 ∗
         gf16SliceAt clonePtr (parallelMult ⟨yv⟩ cs) ∗
         ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ v24) ∗
         ((fsp + 80#64) ↦₆₄ v26) ∗ ((fsp + 96#64) ↦₆₄ v25) ∗
         ∃∗ u112' : BitVec 64, ∃∗ u136' : BitVec 64,
           ((fsp + 112#64) ↦₆₄ u112') ∗ ((fsp + 136#64) ↦₆₄ u136') ∗
           shiftSlotsRawAt_pl fsp ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ Frame) post) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s
      (A.pool lim st s ∗
       gf16SliceAt clonePtr cs ∗
       ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ v24) ∗
       ((fsp + 80#64) ↦₆₄ v26) ∗ ((fsp + 96#64) ↦₆₄ v25) ∗
       ((fsp + 112#64) ↦₆₄ u112) ∗ ((fsp + 136#64) ↦₆₄ u136) ∗
       shiftSlotsRawAt_pl fsp ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ Frame) post := by
  rcases cs with _ | ⟨c0, rest⟩
  · contradiction
  · rcases rest with _ | ⟨c1, rest'⟩
    · try dsimp only [BitVec.ofNat_eq_ofNat, List.length_singleton] at hpc hx20 hcont ⊢
      wp_steps 4
      wp_conv_pre => simp only [arm64_norm, wp_norm]
      have h0 : clonePtr + BitVec.ofNat 64 (2 * 0) = clonePtr := by bv_omega
      simp only [parallelMult_singleton_pl, gf16SliceAt, arrayAt, sepConj_emp] at hcont ⊢
      rw [← h0]
      refine SepWP.weaken_pre
        (by simp only [arm64_norm, wp_norm]; exact Entails.of_eq (by sep_ac_rfl))
        (parallelMultOddTail_placed_sepWP (M := M) (A := A) (lim := lim) (st := st)
          0 yv c0 (by decide) _
          (by simp only [arm64_norm, wp_norm]; exact hcl) fsp clonePtr hfsp_align
          (((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ v24) ∗
           ((fsp + 80#64) ↦₆₄ v26) ∗ ((fsp + 96#64) ↦₆₄ v25) ∗
           ((fsp + 112#64) ↦₆₄ u112) ∗ ((fsp + 136#64) ↦₆₄ u136) ∗
           shiftSlotsRawAt_pl fsp ∗ Frame)
          (by wp_norm_goal) (by wp_norm_lhs) (by simp only [arm64_norm, wp_norm, hsp])
          (by wp_norm_lhs) (by simp only [arm64_norm, wp_norm, hx21])
          (by simp only [arm64_norm, wp_norm, hx22]) ?_)
      intro s1 hcl1 hpc1 hrun1 hsp1 htr1 hvregs1 hx20_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
      rw [h0]
      refine SepWP.weaken_pre ?_
        (hcont s1 hcl1 hpc1 hrun1 hsp1
          (by simp only [arm64_norm, wp_norm] at htr1; exact htr1)
          (by simp only [arm64_norm, wp_norm] at hvregs1; exact hvregs1)
          (by simp only [arm64_norm, wp_norm, hx20] at hx20_1; exact hx20_1) hx22_1
          (by simp only [arm64_norm, wp_norm, hx24] at hx24_1; exact hx24_1)
          (by simp only [arm64_norm, wp_norm, hx25] at hx25_1; exact hx25_1)
          (by simp only [arm64_norm, wp_norm, hx26] at hx26_1; exact hx26_1)
          (by simp only [arm64_norm, wp_norm, hx27] at hx27_1; exact hx27_1)
          (by simp only [arm64_norm, wp_norm, hx28] at hx28_1; exact hx28_1)
          (by simp only [arm64_norm, wp_norm] at hx29_1; exact hx29_1))
      refine Entails.trans (Entails.of_eq (show
        (A.pool lim st s1 ∗
         gf16At ⟨mul c0.value yv⟩ clonePtr ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
         ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ v24) ∗
         ((fsp + 80#64) ↦₆₄ v26) ∗ ((fsp + 96#64) ↦₆₄ v25) ∗
         ((fsp + 112#64) ↦₆₄ u112) ∗ ((fsp + 136#64) ↦₆₄ u136) ∗
         shiftSlotsRawAt_pl fsp ∗ Frame) =
        (A.pool lim st s1 ∗
         gf16At ⟨mul c0.value yv⟩ clonePtr ∗
         ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ v24) ∗
         ((fsp + 80#64) ↦₆₄ v26) ∗ ((fsp + 96#64) ↦₆₄ v25) ∗
         (((fsp + 112#64) ↦₆₄ u112) ∗ ((fsp + 136#64) ↦₆₄ u136) ∗
          shiftSlotsRawAt_pl fsp ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ Frame)) by sep_ac_rfl)) ?_
      refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))))
      exact Entails.sepExists_right u112 (Entails.sepExists_right u136 (Entails.refl _))
    · have hlen_lt : (c0 :: c1 :: rest').length < 2 ^ 64 := by omega
      have hne1 : (BitVec.ofNat 64 (c0 :: c1 :: rest').length != 1#64) = true := by
        rw [bne_iff_ne]; intro heq
        have hto := congrArg BitVec.toNat heq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen_lt] at hto
        simp only [List.length_cons] at hto
        change rest'.length + 1 + 1 = 1 at hto
        omega
      have hbeq1 : (BitVec.ofNat 64 (c0 :: c1 :: rest').length == 1#64) = false := by
        rw [beq_eq_false_iff_ne]; exact bne_iff_ne.mp hne1
      try dsimp only [BitVec.ofNat_eq_ofNat] at hpc hcont ⊢
      let mid3 := if decide ((c0 :: c1 :: rest').length % 2 = 0) then
          (blkPl_416).base + 3784#64
        else
          (blkPl_416).base + 3608#64
      apply sepWP_seq_lscl (mid := mid3) hcl
      wp_steps 2
      wp_conv_pre => simp only [arm64_norm, wp_norm]
      refine SepWP.weaken_pre
        (by simp only [arm64_norm, wp_norm]; exact Entails.of_eq (by sep_ac_rfl))
        (shiftTableInit_placed_sepWP (M := M) (A := A) (lim := lim) (st := st)
          (c0 :: c1 :: rest').length yv _ fsp clonePtr hfsp_align u112 u136
          (gf16SliceAt clonePtr (c0 :: c1 :: rest') ∗
           ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ v24) ∗
           ((fsp + 80#64) ↦₆₄ v26) ∗ ((fsp + 96#64) ↦₆₄ v25) ∗
           tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ Frame)
          (by simp only [arm64_norm, wp_norm, hne1, hbeq1]) (by wp_norm_lhs)
          (by simp only [arm64_norm, wp_norm, hsp])
          (by simp only [arm64_norm, wp_norm, hx20])
          (by simp only [arm64_norm, wp_norm, hx21])
          (by simp only [arm64_norm, wp_norm, hx22]) ?_)
      intro s1 hpc1 hrun1 hsp1 htr1 hvregs1 hx18_1 hx20_1 hx21_1 hx22_1 hx24_1 hx26_1 hx28_1 hx29_1 hx30_1
      refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (parallelMultPairLoop_placed_sepWP (M := M) (A := A) (lim := lim) (st := st)
          yv (c0 :: c1 :: rest') 0 (c0 :: c1 :: rest').length
          (by simp) (by omega) hn s1 fsp clonePtr hfsp_align
          (((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ v24) ∗
           ((fsp + 80#64) ↦₆₄ v26) ∗ ((fsp + 96#64) ↦₆₄ v25) ∗
           ((fsp + 112#64) ↦₆₄ clonePtr) ∗ Frame)
          hpc1 hrun1 hsp1 hx18_1 hx20_1 hx21_1 hx24_1 hx26_1 ?_)
      intro s2 hpc2 hrun2 hsp2 htr2 hvregs2 hx20_2 hx21_2 hx26_2 hx29_2
      refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (parallelMultReload_placed_sepWP (M := M) (A := A) (lim := lim) (st := st)
          (c0 :: c1 :: rest').length hn yv s2 fsp clonePtr v24 v25 v26 v27
          hfsp_align
          (gf16SliceAt clonePtr (parallelMultPairs_pl yv (c0 :: c1 :: rest')) ∗
           ((fsp + 136#64) ↦₆₄ BitVec.ofNat 64 (c0 :: c1 :: rest').length) ∗
           shiftTableAt_pl fsp yv ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ Frame)
          hpc2 hrun2 hsp2 hx20_2 hx21_2 hx26_2 ?_)
      intro s3 hpc3 hrun3 hsp3 htr3 hvregs3 hx19_3 hx20_3 hx21_3 hx22_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3
      apply SepWP.done hpc3 hrun3
      intro hcl3
      by_cases heven : (c0 :: c1 :: rest').length % 2 = 0
      · have hdec : decide ((c0 :: c1 :: rest').length % 2 = 0) = true := decide_eq_true heven
        simp only [hdec, ↓reduceIte] at hpc3
        rw [parallelMultPairs_even_eq_pl yv (c0 :: c1 :: rest') heven]
        refine SepWP.weaken_pre ?_
          (hcont s3 hcl3 hpc3 hrun3 hsp3
            (by rw [htr3, htr2, htr1]; simp only [arm64_norm, wp_norm])
            (by rw [hvregs3, hvregs2, hvregs1]; simp only [arm64_norm, wp_norm])
            hx20_3 hx22_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3
            (by rw [hx29_3, hx29_2, hx29_1]; simp only [arm64_norm, wp_norm]))
        refine Entails.trans (Entails.of_eq (show
          (A.pool lim st s3 ∗
           ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ v24) ∗
           ((fsp + 80#64) ↦₆₄ v26) ∗ ((fsp + 96#64) ↦₆₄ v25) ∗
           ((fsp + 112#64) ↦₆₄ clonePtr) ∗
           gf16SliceAt clonePtr (parallelMult ⟨yv⟩ (c0 :: c1 :: rest')) ∗
           ((fsp + 136#64) ↦₆₄ BitVec.ofNat 64 (c0 :: c1 :: rest').length) ∗
           shiftTableAt_pl fsp yv ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ Frame) =
          (A.pool lim st s3 ∗
           gf16SliceAt clonePtr (parallelMult ⟨yv⟩ (c0 :: c1 :: rest')) ∗
           ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ v24) ∗
           ((fsp + 80#64) ↦₆₄ v26) ∗ ((fsp + 96#64) ↦₆₄ v25) ∗
           (((fsp + 112#64) ↦₆₄ clonePtr) ∗
            ((fsp + 136#64) ↦₆₄ BitVec.ofNat 64 (c0 :: c1 :: rest').length) ∗
            shiftTableAt_pl fsp yv ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ Frame)) by sep_ac_rfl)) ?_
        refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))))
        refine Entails.sepExists_right clonePtr
          (Entails.sepExists_right (BitVec.ofNat 64 (c0 :: c1 :: rest').length) ?_)
        exact sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (shiftTableAt_entails_raw_pl fsp yv)))
      · have hodd : (c0 :: c1 :: rest').length % 2 = 1 := by omega
        have hdec : decide ((c0 :: c1 :: rest').length % 2 = 0) = false := decide_eq_false heven
        simp only [hdec, Bool.false_eq_true, ↓reduceIte] at hpc3
        obtain ⟨last, Rest, hpre, hpost⟩ :=
          gf16SliceAt_parallelMultPairs_odd_pl yv (c0 :: c1 :: rest') clonePtr hodd
        rw [hpre]
        refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (parallelMultOddTail_placed_sepWP (M := M) (A := A) (lim := lim) (st := st)
            (2 * ((c0 :: c1 :: rest').length / 2)) yv last
            (by omega) s3 hcl3 fsp clonePtr hfsp_align
            (Rest ∗ ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ v24) ∗
             ((fsp + 80#64) ↦₆₄ v26) ∗ ((fsp + 96#64) ↦₆₄ v25) ∗
             ((fsp + 112#64) ↦₆₄ clonePtr) ∗
             ((fsp + 136#64) ↦₆₄ BitVec.ofNat 64 (c0 :: c1 :: rest').length) ∗
             shiftTableAt_pl fsp yv ∗ Frame)
            hpc3 hrun3 hsp3 hx19_3 hx21_3 hx22_3 ?_)
        intro s4 hcl4 hpc4 hrun4 hsp4 htr4 hvregs4 hx20_4 hx22_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4
        have hcomb :
            (A.pool lim st s4 ∗
             gf16At ⟨mul last.value yv⟩
               (clonePtr + BitVec.ofNat 64 (2 * (2 * ((c0 :: c1 :: rest').length / 2)))) ∗
             tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ Rest ∗
             ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ v24) ∗
             ((fsp + 80#64) ↦₆₄ v26) ∗ ((fsp + 96#64) ↦₆₄ v25) ∗
             ((fsp + 112#64) ↦₆₄ clonePtr) ∗
             ((fsp + 136#64) ↦₆₄ BitVec.ofNat 64 (c0 :: c1 :: rest').length) ∗
             shiftTableAt_pl fsp yv ∗ Frame) =
            (A.pool lim st s4 ∗
             gf16SliceAt clonePtr (parallelMult ⟨yv⟩ (c0 :: c1 :: rest')) ∗
             ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ v24) ∗
             ((fsp + 80#64) ↦₆₄ v26) ∗ ((fsp + 96#64) ↦₆₄ v25) ∗
             (((fsp + 112#64) ↦₆₄ clonePtr) ∗
              ((fsp + 136#64) ↦₆₄ BitVec.ofNat 64 (c0 :: c1 :: rest').length) ∗
              shiftTableAt_pl fsp yv ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ Frame)) := by
          rw [← hpost]; sep_ac_rfl
        rw [hcomb]
        refine SepWP.weaken_pre ?_
          (hcont s4 hcl4 hpc4 hrun4 hsp4
            (by rw [htr4, htr3, htr2, htr1]; simp only [arm64_norm, wp_norm])
            (by rw [hvregs4, hvregs3, hvregs2, hvregs1]; simp only [arm64_norm, wp_norm])
            (by rw [hx20_4, hx20_3]) hx22_4
            (by rw [hx24_4, hx24_3]) (by rw [hx25_4, hx25_3])
            (by rw [hx26_4, hx26_3]) (by rw [hx27_4, hx27_3])
            (by rw [hx28_4, hx28_3])
            (by rw [hx29_4, hx29_3, hx29_2, hx29_1]; simp only [arm64_norm, wp_norm]))
        refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))))
        refine Entails.sepExists_right clonePtr
          (Entails.sepExists_right (BitVec.ofNat 64 (c0 :: c1 :: rest').length) ?_)
        exact sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (shiftTableAt_entails_raw_pl fsp yv)))

end LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSumPlacedBudgetAux

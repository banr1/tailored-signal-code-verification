/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.PolyPart1CodeSym
public import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Proof
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

/-!
# `<Poly>::lagrange_interpolate_prepare`: Budget-Threaded Verification

Relocatable `[LibsignalPlacement]` verification of
`<spqr::encoding::polynomial::Poly>::lagrange_interpolate_prepare` (Block `372`) against
`lagrangePreparePlacedSpec M A lim`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.ProofBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalHooks LibsignalPlacement blkLib_eq_372 blkPC_372 blkPC_372_rebase_fetch_0xe0
   blkPl_372 lsρ)
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalSpqrV1 (GF16 Poly Pt)
open CryptoVerification.LibsignalSpqrV1.reduce (reduceByteEntry)
open CryptoVerification.LibsignalSpqrV1.unaccelerated (mul polyMul)
open CryptoVerification.LibsignalTripleRatchet (memsetName)
open CryptoVerification.SpqrV1.Alloc
  (spqrRustAllocSym spqrRustNoAllocShimSym spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.GF.Mul2U16
  (aligned_tokenOnce_placed step_ldar32 tokenInitPlacedAt tokenInitPlacedAt_fold
   zeroExtend_16_truncate_32_64)
open scoped CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
  (reduceTablePlacedAt reduceTablePlacedAt_focus16 reduceTableSym uxtw1_idx1_eq uxtw1_idx2_eq)
open scoped CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.Poly (gf16SliceAt polyOf ptSliceAt)
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
  (LagrangePrepareArgs add_neg_rem_eq_k_prev adds_neg_one_carry aligned16_add_mul_two
   and_65535_zext64_16 and_one_of_mod_two cmn_k_prev_ne_zero combine_init_slice
   gf16SliceAt_focus_assoc gf16SliceAt_replicate_zero gf16SliceAt_update_assoc gf16SliceRest
   lagrangePreparePure lagrangePreparePure_length lagrangePrepareStack len_succ_bit62_false
   memRegion_24 memRegion_alloc_split multXdiffLoopPure multXdiffLoopPure_length
   multXdiffLoopPure_succ neg_sub_one neg_succ_add_one neg_succ_ule_add_one ofNat_add_one_shl_one
   ofNat_add_one_shl_one_nat ofNat_bne_true_of_lt ofNat_shl_one ofNat_shl_one_nat ofNat_shl_two
   ofNat_succ_sub_one_shl_one ofNat_two_mul_succ_toNat ofNat_two_mul_toNat outerLoop_frame_eq
   polyOf_of_exact_cap prepareLoopPure prepareLoopPure_succ prepare_polyMul_asm_eq
   prepare_polyReduce_xor_eq ptSliceAt_focus_x_assoc ptr_add_two_of_pos ptr_sub_two_succ
   readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
   readReg_setMem_setPC_pre readReg_setPC_pre sbfx64_one_eq sbfxMask32 sbfxMask64
   sbfxMask64_from_if sp_setMem_setPC_pre sp_setPC_pre stackAt_lagrangePrepare_merge
   stackAt_lagrangePrepare_split sub_two_toNat_eq sxth32Zext64 truncate32_if_all_ones
   truncate32_sext64_16 truncate32_zext64 zext64_zext32_16)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
   RustCliAllocBudget RustLayoutOk VmPreserved rustAllocEvents rustCliAllocBudgetSpec
   rustCliAllocNoOomSpec subroutine_ok_allocNoOom_of_budget)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.DefsBudget
  (LagrangePrepareEnv lagrangePreparePlacedSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemsetRegionBudgetSpec sessionShimBudgetSpec)

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

private theorem sp_setMem_pre (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by cases s; rfl
private theorem pc_setMem_pre (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by cases s; rfl
private theorem status_setMem_pre (s : State) (m : Memory) : (s.setMem m).status = s.status := by
  cases s; rfl
private theorem pstate_setMem_pre (s : State) (m : Memory) : (s.setMem m).pstate = s.pstate := by
  cases s; rfl
private theorem trace_setMem_pre (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by
  cases s; rfl
private theorem readReg64_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases s; rfl
private theorem readReg32_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases s; rfl
private theorem readReg_setMem_pre (s : State) (m : Memory) (w : Width) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases s; rfl
private theorem calleeSavedVRegs_setMem_pre (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre pc_setMem_pre status_setMem_pre pstate_setMem_pre trace_setMem_pre
  readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre calleeSavedVRegs_setMem_pre
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
attribute [local wp_norm] zeroExtend_16_truncate_32_64
attribute [local arm64_norm, local wp_norm]
  ofNat_shl_two truncate32_sext64_16 sbfx64_one_eq
  truncate32_if_all_ones truncate32_zext64 zext64_zext32_16
  and_65535_zext64_16 prepare_polyReduce_xor_eq

/-! ## `tpidrEl0`-Preserving Relocatable Inner & Outer Loop Helpers (Block `372`) -/

set_option maxHeartbeats 1600000 in
private theorem innerPolyMul_placed_tp [LibsignalPlacement]
    (H : LibsignalHooks)
    (sp0 ptr : BitVec 64) (hptr_al : ptr &&& 1#64 = 0#64)
    (k : Nat) (hk1 : 1 ≤ k)
    (cv yv : BitVec 16)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop)
    (s : State) (F : SepProp)
    (hpc : s.pc = (blkPl_372).base + 212#64)
    (hrun : s.status = .Running)
    (hx21 : s.readReg64 .x21 = sbfxMask64 yv 6)
    (hx22 : s.readReg64 .x22 = sbfxMask64 yv 7)
    (hx24 : s.readReg64 .x24 = ptr + BitVec.ofNat 64 (2 * (k - 1)))
    (hx25 : s.readReg64 .x25 = sxth32Zext64 yv)
    (hx26 : s.readReg64 .x26 = sbfxMask64 yv 8)
    (hx28 : s.readReg64 .x28 = sbfxMask64 yv 9)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ sf : State,
      sf.pc = (blkPl_372).base + 508#64 →
      sf.status = .Running →
      sf.sp = s.sp →
      sf.trace = s.trace →
      sf.tpidrEl0 = s.tpidrEl0 →
      sf.readReg64 .x8 = BitVec.zeroExtend 64 (polyMul cv yv) →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = sbfxMask64 yv 6 →
      sf.readReg64 .x22 = sbfxMask64 yv 7 →
      sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = ptr + BitVec.ofNat 64 (2 * k) →
      sf.readReg64 .x25 = sxth32Zext64 yv →
      sf.readReg64 .x26 = sbfxMask64 yv 8 →
      sf.readReg64 .x27 = s.readReg64 .x27 →
      sf.readReg64 .x28 = sbfxMask64 yv 9 →
      sf.readReg64 .x29 = sp0 - 96#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP ((blkPC_372).rebase (blkPl_372).base H) ret_pc sf
        (tokenInitPlacedAt ∗
         ((sp0 - 132#64) ↦₃₂ sbfxMask32 yv 10) ∗
         ((sp0 - 128#64) ↦₃₂ sbfxMask32 yv 11) ∗
         ((sp0 - 124#64) ↦₃₂ sbfxMask32 yv 12) ∗
         ((sp0 - 120#64) ↦₃₂ sbfxMask32 yv 13) ∗
         ((sp0 - 116#64) ↦₃₂ sbfxMask32 yv 14) ∗
         ((ptr + BitVec.ofNat 64 (2 * k)) ↦₁₆ cv) ∗ F) Q) :
    SepWP ((blkPC_372).rebase (blkPl_372).base H) ret_pc s
      (tokenInitPlacedAt ∗
       ((sp0 - 132#64) ↦₃₂ sbfxMask32 yv 10) ∗
       ((sp0 - 128#64) ↦₃₂ sbfxMask32 yv 11) ∗
       ((sp0 - 124#64) ↦₃₂ sbfxMask32 yv 12) ∗
       ((sp0 - 120#64) ↦₃₂ sbfxMask32 yv 13) ∗
       ((sp0 - 116#64) ↦₃₂ sbfxMask32 yv 14) ∗
       ((ptr + BitVec.ofNat 64 (2 * k)) ↦₁₆ cv) ∗ F) Q := by
  have halign_bd8 := aligned_tokenOnce_placed
  have hptr_step := ptr_add_two_of_pos ptr hk1
  have hal_k := aligned16_add_mul_two ptr hptr_al k
  wp_simp_pre [tokenInitPlacedAt]
  wp_steps 3
  apply step_ldar32 (by wp_norm_lhs) (by wp_norm_lhs)
    (blkPC_372_rebase_fetch_0xe0 (blkPl_372).base H)
    (by wp_norm_lhs) (by wp_norm_lhs) halign_bd8 (by wp_sep_access) (by wp_norm_lhs)
  wp_steps 6
  apply SepWP.fold tokenInitPlacedAt_fold (by sep_focus)
  wp_steps 42
  apply hnext _ (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
  · simp only [arm64_norm, wp_norm]; exact prepare_polyMul_asm_eq cv yv
  · wp_norm_lhs
  · wp_norm_lhs
  · simpa [arm64_norm, wp_norm] using hx21
  · simpa [arm64_norm, wp_norm] using hx22
  · wp_norm_lhs
  · wp_norm_lhs
  · simpa [arm64_norm, wp_norm] using hx25
  · simpa [arm64_norm, wp_norm] using hx26
  · wp_norm_lhs
  · simpa [arm64_norm, wp_norm] using hx28
  · simpa [arm64_norm, wp_norm] using hx29
  · wp_norm_lhs

private theorem uxtw1_idx1_eq' (p : BitVec 32) :
    BitVec.ofNat 64 (2 * (BitVec.truncate 8 (p >>> 24)).toNat) =
      BitVec.zeroExtend 64 (p >>> 24) <<< 1 := by
  rw [uxtw1_idx1_eq]; bv_bits

set_option maxHeartbeats 1600000 in
private theorem innerStep_placed_tp [LibsignalPlacement]
    (H : LibsignalHooks)
    (sp0 ptr : BitVec 64) (hptr_al : ptr &&& 1#64 = 0#64)
    (n : Nat) (hn_bound : n + 1 < 2 ^ 63)
    (yv : BitVec 16)
    (rem' k : Nat) (cs : List GF16)
    (hk1 : 1 ≤ k) (hk_rem : k + rem' = n) (hcs_len : cs.length = n + 1)
    (hk : k < cs.length) (hk_prev : k - 1 < cs.length)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop)
    (s : State) (F : SepProp)
    (hpc : s.pc = (blkPl_372).base + 212#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ptr + BitVec.ofNat 64 (2 * (k - 1)))
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 n)
    (hx21 : s.readReg64 .x21 = sbfxMask64 yv 6)
    (hx22 : s.readReg64 .x22 = sbfxMask64 yv 7)
    (hx23 : s.readReg64 .x23 = lsρ reduceTableSym)
    (hx24 : s.readReg64 .x24 = ptr + BitVec.ofNat 64 (2 * (k - 1)))
    (hx25 : s.readReg64 .x25 = sxth32Zext64 yv)
    (hx26 : s.readReg64 .x26 = sbfxMask64 yv 8)
    (hx27 : s.readReg64 .x27 = 0#64 - BitVec.ofNat 64 (rem' + 1))
    (hx28 : s.readReg64 .x28 = sbfxMask64 yv 9)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ sf : State,
      sf.pc = (blkPl_372).base + 564#64 →
      sf.status = .Running →
      sf.sp = s.sp →
      sf.trace = s.trace →
      sf.tpidrEl0 = s.tpidrEl0 →
      sf.pstate = addsPState64 (0#64 - BitVec.ofNat 64 (rem' + 1)) 1#64 →
      sf.readReg64 .x19 = ptr + BitVec.ofNat 64 (2 * k) →
      sf.readReg64 .x20 = BitVec.ofNat 64 n →
      sf.readReg64 .x21 = sbfxMask64 yv 6 →
      sf.readReg64 .x22 = sbfxMask64 yv 7 →
      sf.readReg64 .x23 = lsρ reduceTableSym →
      sf.readReg64 .x24 = ptr + BitVec.ofNat 64 (2 * k) →
      sf.readReg64 .x25 = sxth32Zext64 yv →
      sf.readReg64 .x26 = sbfxMask64 yv 8 →
      sf.readReg64 .x27 = 0#64 - BitVec.ofNat 64 (rem' + 1) + 1#64 →
      sf.readReg64 .x28 = sbfxMask64 yv 9 →
      sf.readReg64 .x29 = sp0 - 96#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP ((blkPC_372).rebase (blkPl_372).base H) ret_pc sf
        (tokenInitPlacedAt ∗
         ((sp0 - 132#64) ↦₃₂ sbfxMask32 yv 10) ∗
         ((sp0 - 128#64) ↦₃₂ sbfxMask32 yv 11) ∗
         ((sp0 - 124#64) ↦₃₂ sbfxMask32 yv 12) ∗
         ((sp0 - 120#64) ↦₃₂ sbfxMask32 yv 13) ∗
         ((sp0 - 116#64) ↦₃₂ sbfxMask32 yv 14) ∗
         gf16SliceAt ptr
           (cs.set (k - 1) ⟨(cs[k - 1]'hk_prev).value ^^^ mul (cs[k]'hk).value yv⟩) ∗
         reduceTablePlacedAt ∗ F) Q) :
    SepWP ((blkPC_372).rebase (blkPl_372).base H) ret_pc s
      (tokenInitPlacedAt ∗
       ((sp0 - 132#64) ↦₃₂ sbfxMask32 yv 10) ∗
       ((sp0 - 128#64) ↦₃₂ sbfxMask32 yv 11) ∗
       ((sp0 - 124#64) ↦₃₂ sbfxMask32 yv 12) ∗
       ((sp0 - 120#64) ↦₃₂ sbfxMask32 yv 13) ∗
       ((sp0 - 116#64) ↦₃₂ sbfxMask32 yv 14) ∗
       gf16SliceAt ptr cs ∗
       reduceTablePlacedAt ∗ F) Q := by
  wp_conv_pre => rw [gf16SliceAt_focus_assoc hk ptr]
  apply innerPolyMul_placed_tp H sp0 ptr hptr_al k hk1 (cs[k]'hk).value yv ret_pc Q s
    (gf16SliceRest ptr cs k ∗ reduceTablePlacedAt ∗ F)
    hpc hrun hx21 hx22 hx24 hx25 hx26 hx28 hx29
  intro s1 hpc1 hrun1 hsp1 htrace1 htp1 hx8_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs1
  rw [hx19] at hx19_1; rw [hx20] at hx20_1; rw [hx23] at hx23_1; rw [hx27] at hx27_1
  have hadd_k := add_neg_rem_eq_k_prev hk1 hk_rem
  have hcmn := cmn_k_prev_ne_zero hk1 (by omega)
  have hal_prev := aligned16_add_mul_two ptr hptr_al (k - 1)
  wp_conv_pre => rw [← gf16SliceAt_focus_assoc hk ptr, gf16SliceAt_focus_assoc hk_prev ptr]
  wp_steps 6
  wp_conv_pre =>
    rw [reduceTablePlacedAt_focus16 (BitVec.truncate 8 (polyMul (cs[k]'hk).value yv >>> 24)),
        uxtw1_idx1_eq' (polyMul (cs[k]'hk).value yv)]
  wp_steps 4
  wp_conv_pre =>
    rw [← uxtw1_idx1_eq' (polyMul (cs[k]'hk).value yv),
        ← reduceTablePlacedAt_focus16 (BitVec.truncate 8 (polyMul (cs[k]'hk).value yv >>> 24)),
        reduceTablePlacedAt_focus16
          (BitVec.truncate 8
            ((polyMul (cs[k]'hk).value yv ^^^
                BitVec.zeroExtend 32
                    (reduceByteEntry (BitVec.truncate 8 (polyMul (cs[k]'hk).value yv >>> 24))) <<<
                  8) >>>
              16)),
        uxtw1_idx2_eq]
  wp_steps 4
  wp_conv_pre =>
    rw [← uxtw1_idx2_eq,
        ← reduceTablePlacedAt_focus16
          (BitVec.truncate 8
            ((polyMul (cs[k]'hk).value yv ^^^
                BitVec.zeroExtend 32
                    (reduceByteEntry (BitVec.truncate 8 (polyMul (cs[k]'hk).value yv >>> 24))) <<<
                  8) >>>
              16)),
        gf16SliceAt_update_assoc hk_prev ptr]
  apply hnext _ (by wp_norm_lhs) (by wp_norm_lhs) (by simpa [arm64_norm, wp_norm] using hsp1)
    (by simpa [arm64_norm, wp_norm] using htrace1) (by simpa [arm64_norm, wp_norm] using htp1)
    (by wp_norm_lhs) (by wp_norm_lhs)
    (by simpa [arm64_norm, wp_norm] using hx20_1) (by simpa [arm64_norm, wp_norm] using hx21_1)
    (by simpa [arm64_norm, wp_norm] using hx22_1) (by simpa [arm64_norm, wp_norm] using hx23_1)
    (by simpa [arm64_norm, wp_norm] using hx24_1) (by simpa [arm64_norm, wp_norm] using hx25_1)
    (by simpa [arm64_norm, wp_norm] using hx26_1) (by wp_norm_lhs)
    (by simpa [arm64_norm, wp_norm] using hx28_1) (by simpa [arm64_norm, wp_norm] using hx29_1)
    (by simpa [arm64_norm, wp_norm] using hvregs1)

set_option maxHeartbeats 1600000 in
private theorem innerLoop_placed_tp [LibsignalPlacement]
    (H : LibsignalHooks)
    (sp0 ptr : BitVec 64) (hptr_al : ptr &&& 1#64 = 0#64)
    (n : Nat) (hn_bound : n + 1 < 2 ^ 63)
    (yv : BitVec 16)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop) :
    ∀ (rem' k : Nat) (cs : List GF16)
      (_hk1 : 1 ≤ k) (_hk_rem : k + rem' = n) (_hcs_len : cs.length = n + 1)
      (s : State) (F : SepProp),
      s.pc = (blkPl_372).base + 212#64 →
      s.status = .Running →
      s.readReg64 .x19 = ptr + BitVec.ofNat 64 (2 * (k - 1)) →
      s.readReg64 .x20 = BitVec.ofNat 64 n →
      s.readReg64 .x21 = sbfxMask64 yv 6 →
      s.readReg64 .x22 = sbfxMask64 yv 7 →
      s.readReg64 .x23 = lsρ reduceTableSym →
      s.readReg64 .x24 = ptr + BitVec.ofNat 64 (2 * (k - 1)) →
      s.readReg64 .x25 = sxth32Zext64 yv →
      s.readReg64 .x26 = sbfxMask64 yv 8 →
      s.readReg64 .x27 = 0#64 - BitVec.ofNat 64 (rem' + 1) →
      s.readReg64 .x28 = sbfxMask64 yv 9 →
      s.readReg64 .x29 = sp0 - 96#64 →
      (∀ sf : State,
        sf.pc = (blkPl_372).base + 568#64 →
        sf.status = .Running →
        sf.sp = s.sp →
        sf.trace = s.trace →
        sf.tpidrEl0 = s.tpidrEl0 →
        sf.readReg64 .x20 = BitVec.ofNat 64 n →
        sf.readReg64 .x23 = lsρ reduceTableSym →
        sf.readReg64 .x29 = sp0 - 96#64 →
        calleeSavedVRegs sf = calleeSavedVRegs s →
        SepWP ((blkPC_372).rebase (blkPl_372).base H) ret_pc sf
          (tokenInitPlacedAt ∗
           ((sp0 - 132#64) ↦₃₂ sbfxMask32 yv 10) ∗
           ((sp0 - 128#64) ↦₃₂ sbfxMask32 yv 11) ∗
           ((sp0 - 124#64) ↦₃₂ sbfxMask32 yv 12) ∗
           ((sp0 - 120#64) ↦₃₂ sbfxMask32 yv 13) ∗
           ((sp0 - 116#64) ↦₃₂ sbfxMask32 yv 14) ∗
           gf16SliceAt ptr (multXdiffLoopPure ⟨yv⟩ k (rem' + 1) cs) ∗
           reduceTablePlacedAt ∗ F) Q) →
      SepWP ((blkPC_372).rebase (blkPl_372).base H) ret_pc s
        (tokenInitPlacedAt ∗
         ((sp0 - 132#64) ↦₃₂ sbfxMask32 yv 10) ∗
         ((sp0 - 128#64) ↦₃₂ sbfxMask32 yv 11) ∗
         ((sp0 - 124#64) ↦₃₂ sbfxMask32 yv 12) ∗
         ((sp0 - 120#64) ↦₃₂ sbfxMask32 yv 13) ∗
         ((sp0 - 116#64) ↦₃₂ sbfxMask32 yv 14) ∗
         gf16SliceAt ptr cs ∗
         reduceTablePlacedAt ∗ F) Q := by
  intro rem'
  induction rem' with
  | zero =>
    intro k cs hk1 hk_rem hcs_len s F hpc hrun hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hnext
    have hk : k < cs.length := by omega
    have hk_prev : k - 1 < cs.length := by omega
    apply innerStep_placed_tp H sp0 ptr hptr_al n hn_bound yv 0 k cs hk1 hk_rem hcs_len hk hk_prev
      ret_pc Q s F hpc hrun hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29
    intro s1 hpc1 hrun1 hsp1 htrace1 htp1 hpstate1 _hx19_1 hx20_1 _hx21_1 _hx22_1 hx23_1 _hx24_1 _hx25_1 _hx26_1 _hx27_1 _hx28_1 hx29_1 hvregs1
    have hcarry := adds_neg_one_carry
    wp_steps 1
    rw [multXdiffLoopPure_succ yv k 0 cs hk hk_prev] at hnext
    exact hnext _ (by wp_norm_lhs) (by wp_norm_lhs) (by simpa [arm64_norm, wp_norm] using hsp1)
      (by simpa [arm64_norm, wp_norm] using htrace1) (by simpa [arm64_norm, wp_norm] using htp1)
      (by simpa [arm64_norm, wp_norm] using hx20_1)
      (by simpa [arm64_norm, wp_norm] using hx23_1) (by simpa [arm64_norm, wp_norm] using hx29_1)
      (by simpa [arm64_norm, wp_norm] using hvregs1)
  | succ r ih =>
    intro k cs hk1 hk_rem hcs_len s F hpc hrun hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hnext
    have hk : k < cs.length := by omega
    have hk_prev : k - 1 < cs.length := by omega
    apply innerStep_placed_tp H sp0 ptr hptr_al n hn_bound yv (r + 1) k cs hk1 hk_rem hcs_len hk hk_prev
      ret_pc Q s F hpc hrun hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29
    intro s1 hpc1 hrun1 hsp1 htrace1 htp1 hpstate1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs1
    have hcarry := neg_succ_ule_add_one (r := r) (by omega)
    wp_steps 1
    apply ih (k + 1)
      (cs.set (k - 1) ⟨(cs[k - 1]'hk_prev).value ^^^ mul (cs[k]'hk).value yv⟩)
      (by omega) (by omega) (by simp [List.length_set, hcs_len]) _ F
      (by wp_norm_lhs) (by wp_norm_lhs)
      (by simpa [arm64_norm, wp_norm] using hx19_1)
      (by simpa [arm64_norm, wp_norm] using hx20_1)
      (by simpa [arm64_norm, wp_norm] using hx21_1)
      (by simpa [arm64_norm, wp_norm] using hx22_1)
      (by simpa [arm64_norm, wp_norm] using hx23_1)
      (by simpa [arm64_norm, wp_norm] using hx24_1)
      (by simpa [arm64_norm, wp_norm] using hx25_1)
      (by simpa [arm64_norm, wp_norm] using hx26_1)
      (by simpa [arm64_norm, wp_norm, neg_succ_add_one (r + 1)] using hx27_1)
      (by simpa [arm64_norm, wp_norm] using hx28_1)
      (by simpa [arm64_norm, wp_norm] using hx29_1)
    intro sf hpc_f hrun_f hsp_f htrace_f htp_f hx20_f hx23_f hx29_f hvregs_f
    rw [multXdiffLoopPure_succ yv k (r + 1) cs hk hk_prev] at hnext
    exact hnext sf hpc_f hrun_f
      (by rw [hsp_f]; simpa [arm64_norm, wp_norm] using hsp1)
      (by rw [htrace_f]; simpa [arm64_norm, wp_norm] using htrace1)
      (by rw [htp_f]; simpa [arm64_norm, wp_norm] using htp1)
      hx20_f hx23_f hx29_f
      (by rw [hvregs_f]; simpa [arm64_norm, wp_norm] using hvregs1)

set_option maxHeartbeats 1600000 in
private theorem outerStep_placed_tp [LibsignalPlacement]
    (H : LibsignalHooks)
    (sp0 ptr ptsPtr : BitVec 64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64) (hptr_al : ptr &&& 1#64 = 0#64)
    (pts : List Pt) (hn_bound : pts.length + 1 < 2 ^ 63)
    (r_out i : Nat) (p : Poly)
    (hi_rem : i + (r_out + 1) = pts.length) (hp_len : p.coefficients.length = pts.length + 1)
    (hi : i < pts.length)
    (v160 v152 v144 : BitVec 64)
    (w132 w128 w124 w120 w116 : BitVec 32)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop)
    (s : State) (F : SepProp)
    (hpc : s.pc = (blkPl_372).base + 132#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 208#64)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 i)
    (hx19 : s.readReg64 .x19 = ptr + BitVec.ofNat 64 (2 * r_out))
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 pts.length)
    (hx23 : s.readReg64 .x23 = lsρ reduceTableSym)
    (hx27 : s.readReg64 .x27 = 0#64 - BitVec.ofNat 64 (i + 1))
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ sf : State,
      sf.pc = (blkPl_372).base + 588#64 →
      sf.status = .Running →
      sf.sp = sp0 - 208#64 →
      sf.trace = s.trace →
      sf.tpidrEl0 = s.tpidrEl0 →
      sf.pstate = subsPState64 (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 pts.length) →
      sf.readReg64 .x9 = BitVec.ofNat 64 (i + 1) →
      sf.readReg64 .x19 = ptr + BitVec.ofNat 64 (2 * r_out) - 2#64 →
      sf.readReg64 .x20 = BitVec.ofNat 64 pts.length →
      sf.readReg64 .x23 = lsρ reduceTableSym →
      sf.readReg64 .x27 = 0#64 - BitVec.ofNat 64 (i + 1) - 1#64 →
      sf.readReg64 .x29 = sp0 - 96#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP ((blkPC_372).rebase (blkPl_372).base H) ret_pc sf
        (tokenInitPlacedAt ∗
         ((sp0 - 132#64) ↦₃₂ sbfxMask32 (pts[i]'hi).x.value 10) ∗
         ((sp0 - 128#64) ↦₃₂ sbfxMask32 (pts[i]'hi).x.value 11) ∗
         ((sp0 - 124#64) ↦₃₂ sbfxMask32 (pts[i]'hi).x.value 12) ∗
         ((sp0 - 120#64) ↦₃₂ sbfxMask32 (pts[i]'hi).x.value 13) ∗
         ((sp0 - 116#64) ↦₃₂ sbfxMask32 (pts[i]'hi).x.value 14) ∗
         gf16SliceAt ptr
           (multXdiffLoopPure (pts[i]'hi).x (r_out + 1) (i + 1) p.coefficients) ∗
         reduceTablePlacedAt ∗
         ((sp0 - 168#64) ↦₆₄ ptsPtr) ∗
         ((sp0 - 160#64) ↦₆₄ BitVec.ofNat 64 (i + 1)) ∗
         ((sp0 - 152#64) ↦₆₄ (0#64 - BitVec.ofNat 64 (i + 1))) ∗
         ((sp0 - 144#64) ↦₆₄ (ptr + BitVec.ofNat 64 (2 * r_out))) ∗
         ptSliceAt ptsPtr pts ∗ F) Q) :
    SepWP ((blkPC_372).rebase (blkPl_372).base H) ret_pc s
      (tokenInitPlacedAt ∗
       ((sp0 - 132#64) ↦₃₂ w132) ∗
       ((sp0 - 128#64) ↦₃₂ w128) ∗
       ((sp0 - 124#64) ↦₃₂ w124) ∗
       ((sp0 - 120#64) ↦₃₂ w120) ∗
       ((sp0 - 116#64) ↦₃₂ w116) ∗
       gf16SliceAt ptr p.coefficients ∗
       reduceTablePlacedAt ∗
       ((sp0 - 168#64) ↦₆₄ ptsPtr) ∗
       ((sp0 - 160#64) ↦₆₄ v160) ∗
       ((sp0 - 152#64) ↦₆₄ v152) ∗
       ((sp0 - 144#64) ↦₆₄ v144) ∗
       ptSliceAt ptsPtr pts ∗ F) Q := by
  have hi_succ : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by
    rw [← BitVec.ofNat_add]
  wp_conv_pre => rw [ptSliceAt_focus_x_assoc hi ptsPtr]
  wp_steps 20
  wp_conv_pre => rw [← ptSliceAt_focus_x_assoc hi ptsPtr]
  apply innerLoop_placed_tp H sp0 ptr hptr_al pts.length hn_bound (pts[i]'hi).x.value
    ret_pc Q i (r_out + 1) p.coefficients (by omega) (by omega) hp_len _
    (((sp0 - 168#64) ↦₆₄ ptsPtr) ∗
     ((sp0 - 160#64) ↦₆₄ BitVec.ofNat 64 (i + 1)) ∗
     ((sp0 - 152#64) ↦₆₄ (0#64 - BitVec.ofNat 64 (i + 1))) ∗
     ((sp0 - 144#64) ↦₆₄ (ptr + BitVec.ofNat 64 (2 * r_out))) ∗
     ptSliceAt ptsPtr pts ∗ F)
    (by wp_norm_lhs) (by wp_norm_lhs)
    (by simpa [arm64_norm, wp_norm] using hx19)
    (by simpa [arm64_norm, wp_norm] using hx20)
    (by simp only [arm64_norm, wp_norm]; exact sbfxMask64_from_if _ _)
    (by simp only [arm64_norm, wp_norm]; exact sbfxMask64_from_if _ _)
    (by simpa [arm64_norm, wp_norm] using hx23)
    (by wp_norm_lhs) (by wp_norm_lhs)
    (by simp only [arm64_norm, wp_norm]; exact sbfxMask64_from_if _ _)
    (by simpa [arm64_norm, wp_norm] using hx27)
    (by simp only [arm64_norm, wp_norm]; exact sbfxMask64_from_if _ _)
    (by simpa [arm64_norm, wp_norm] using hx29)
  intro s1 hpc1 hrun1 hsp1 htrace1 htp1 hx20_1 hx23_1 hx29_1 hvregs1
  have hsp1' : s1.sp = sp0 - 208#64 := by rw [hsp1]; simpa [arm64_norm, wp_norm] using hsp
  have htrace1' : s1.trace = s.trace := by simpa [arm64_norm, wp_norm] using htrace1
  have htp1' : s1.tpidrEl0 = s.tpidrEl0 := by simpa [arm64_norm, wp_norm] using htp1
  have hvregs1' : calleeSavedVRegs s1 = calleeSavedVRegs s := by simpa [arm64_norm, wp_norm] using hvregs1
  wp_steps 5
  apply hnext _ (by wp_norm_lhs) (by wp_norm_lhs)
    (by simpa [arm64_norm, wp_norm] using hsp1')
    (by simpa [arm64_norm, wp_norm] using htrace1')
    (by simpa [arm64_norm, wp_norm] using htp1')
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by simpa [arm64_norm, wp_norm] using hx20_1)
    (by simpa [arm64_norm, wp_norm] using hx23_1)
    (by wp_norm_lhs)
    (by simpa [arm64_norm, wp_norm] using hx29_1)
    (by simpa [arm64_norm, wp_norm] using hvregs1')

set_option maxHeartbeats 1600000 in
private theorem outerLoop_placed_tp [LibsignalPlacement]
    (H : LibsignalHooks)
    (sp0 ptr ptsPtr : BitVec 64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64) (hptr_al : ptr &&& 1#64 = 0#64)
    (pts : List Pt) (hn_bound : pts.length + 1 < 2 ^ 63)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop) :
    ∀ (r_out i : Nat) (p : Poly)
      (_hi_rem : i + (r_out + 1) = pts.length) (_hp_len : p.coefficients.length = pts.length + 1)
      (v160 v152 v144 : BitVec 64)
      (w132 w128 w124 w120 w116 : BitVec 32)
      (s : State) (F : SepProp),
      s.pc = (blkPl_372).base + 132#64 →
      s.status = .Running →
      s.sp = sp0 - 208#64 →
      s.readReg64 .x9 = BitVec.ofNat 64 i →
      s.readReg64 .x19 = ptr + BitVec.ofNat 64 (2 * r_out) →
      s.readReg64 .x20 = BitVec.ofNat 64 pts.length →
      s.readReg64 .x23 = lsρ reduceTableSym →
      s.readReg64 .x27 = 0#64 - BitVec.ofNat 64 (i + 1) →
      s.readReg64 .x29 = sp0 - 96#64 →
      (∀ (v160' v152' v144' : BitVec 64) (w132' w128' w124' w120' w116' : BitVec 32) (sf : State),
        sf.pc = (blkPl_372).base + 608#64 →
        sf.status = .Running →
        sf.sp = sp0 - 208#64 →
        sf.trace = s.trace →
        sf.tpidrEl0 = s.tpidrEl0 →
        calleeSavedVRegs sf = calleeSavedVRegs s →
        SepWP ((blkPC_372).rebase (blkPl_372).base H) ret_pc sf
          (tokenInitPlacedAt ∗
           ((sp0 - 132#64) ↦₃₂ w132') ∗
           ((sp0 - 128#64) ↦₃₂ w128') ∗
           ((sp0 - 124#64) ↦₃₂ w124') ∗
           ((sp0 - 120#64) ↦₃₂ w120') ∗
           ((sp0 - 116#64) ↦₃₂ w116') ∗
           gf16SliceAt ptr (prepareLoopPure pts pts.length i (r_out + 1) p).coefficients ∗
           reduceTablePlacedAt ∗
           ((sp0 - 168#64) ↦₆₄ ptsPtr) ∗
           ((sp0 - 160#64) ↦₆₄ v160') ∗
           ((sp0 - 152#64) ↦₆₄ v152') ∗
           ((sp0 - 144#64) ↦₆₄ v144') ∗
           ptSliceAt ptsPtr pts ∗ F) Q) →
      SepWP ((blkPC_372).rebase (blkPl_372).base H) ret_pc s
        (tokenInitPlacedAt ∗
         ((sp0 - 132#64) ↦₃₂ w132) ∗
         ((sp0 - 128#64) ↦₃₂ w128) ∗
         ((sp0 - 124#64) ↦₃₂ w124) ∗
         ((sp0 - 120#64) ↦₃₂ w120) ∗
         ((sp0 - 116#64) ↦₃₂ w116) ∗
         gf16SliceAt ptr p.coefficients ∗
         reduceTablePlacedAt ∗
         ((sp0 - 168#64) ↦₆₄ ptsPtr) ∗
         ((sp0 - 160#64) ↦₆₄ v160) ∗
         ((sp0 - 152#64) ↦₆₄ v152) ∗
         ((sp0 - 144#64) ↦₆₄ v144) ∗
         ptSliceAt ptsPtr pts ∗ F) Q := by
  intro r_out
  induction r_out with
  | zero =>
    intro i p hi_rem hp_len v160 v152 v144 w132 w128 w124 w120 w116 s F
      hpc hrun hsp hx9 hx19 hx20 hx23 hx27 hx29 hnext
    have hi : i < pts.length := by omega
    apply outerStep_placed_tp H sp0 ptr ptsPtr hsp0 hptr_al pts hn_bound
      0 i p hi_rem hp_len hi v160 v152 v144 w132 w128 w124 w120 w116 ret_pc Q s F
      hpc hrun hsp hx9 hx19 hx20 hx23 hx27 hx29
    intro s1 hpc1 hrun1 hsp1 htrace1 htp1 hpstate1 _hx9_1 _hx19_1 _hx20_1 _hx23_1 _hx27_1 _hx29_1 hvregs1
    have heq_len : i + 1 = pts.length := by omega
    rw [heq_len] at hpstate1
    wp_steps 2
    rw [prepareLoopPure_succ pts i 0 p hi_rem hp_len hi] at hnext
    dsimp only [prepareLoopPure] at hnext
    exact hnext
      (BitVec.ofNat 64 (i + 1)) (0#64 - BitVec.ofNat 64 (i + 1)) (ptr + BitVec.ofNat 64 (2 * 0))
      (sbfxMask32 (pts[i]'hi).x.value 10) (sbfxMask32 (pts[i]'hi).x.value 11)
      (sbfxMask32 (pts[i]'hi).x.value 12) (sbfxMask32 (pts[i]'hi).x.value 13)
      (sbfxMask32 (pts[i]'hi).x.value 14) _
      (by wp_norm_lhs) (by wp_norm_lhs)
      (by simpa [arm64_norm, wp_norm] using hsp1)
      (by simpa [arm64_norm, wp_norm] using htrace1)
      (by simpa [arm64_norm, wp_norm] using htp1)
      (by simpa [arm64_norm, wp_norm] using hvregs1)
  | succ r_out' ih =>
    intro i p hi_rem hp_len v160 v152 v144 w132 w128 w124 w120 w116 s F
      hpc hrun hsp hx9 hx19 hx20 hx23 hx27 hx29 hnext
    have hi : i < pts.length := by omega
    apply outerStep_placed_tp H sp0 ptr ptsPtr hsp0 hptr_al pts hn_bound
      (r_out' + 1) i p hi_rem hp_len hi v160 v152 v144 w132 w128 w124 w120 w116 ret_pc Q s F
      hpc hrun hsp hx9 hx19 hx20 hx23 hx27 hx29
    intro s1 hpc1 hrun1 hsp1 htrace1 htp1 hpstate1 hx9_1 hx19_1 hx20_1 hx23_1 hx27_1 hx29_1 hvregs1
    have hne_len := ofNat_bne_true_of_lt (a := i + 1) (b := pts.length) (by omega) (by omega)
    wp_steps 1
    apply ih (i + 1) ⟨multXdiffLoopPure (pts[i]'hi).x (r_out' + 1 + 1) (i + 1) p.coefficients⟩
      (by omega) (by simp [multXdiffLoopPure_length, hp_len])
      (BitVec.ofNat 64 (i + 1)) (0#64 - BitVec.ofNat 64 (i + 1)) (ptr + BitVec.ofNat 64 (2 * (r_out' + 1)))
      (sbfxMask32 (pts[i]'hi).x.value 10) (sbfxMask32 (pts[i]'hi).x.value 11)
      (sbfxMask32 (pts[i]'hi).x.value 12) (sbfxMask32 (pts[i]'hi).x.value 13)
      (sbfxMask32 (pts[i]'hi).x.value 14) _ F
      (by wp_norm_lhs) (by wp_norm_lhs)
      (by simpa [arm64_norm, wp_norm] using hsp1)
      (by simpa [arm64_norm, wp_norm] using hx9_1)
      (by simpa [arm64_norm, wp_norm, ptr_sub_two_succ ptr r_out'] using hx19_1)
      (by simpa [arm64_norm, wp_norm] using hx20_1)
      (by simpa [arm64_norm, wp_norm] using hx23_1)
      (by simpa [arm64_norm, wp_norm, neg_sub_one (i + 1)] using hx27_1)
      (by simpa [arm64_norm, wp_norm] using hx29_1)
    intro v160' v152' v144' w132' w128' w124' w120' w116' sf hpc_f hrun_f hsp_f htrace_f htp_f hvregs_f
    rw [prepareLoopPure_succ pts i (r_out' + 1) p hi_rem hp_len hi] at hnext
    exact hnext v160' v152' v144' w132' w128' w124' w120' w116' sf hpc_f hrun_f hsp_f
      (by rw [htrace_f]; simpa [arm64_norm, wp_norm] using htrace1)
      (by rw [htp_f]; simpa [arm64_norm, wp_norm] using htp1)
      (by rw [hvregs_f]; simpa [arm64_norm, wp_norm] using hvregs1)

/-! ## Budget-Threaded Epilogue & Entry Contract (Block `372`) -/

private theorem epilogue_placed_sepWP [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    (a : LagrangePrepareArgs) (R : SepProp) (s0 s : State)
    (ptr o0 o1 o2 : BitVec 64)
    (v168 v160 v152 v144 : BitVec 64)
    (w132 w128 w124 w120 w116 : BitVec 32)
    (hsp_align : s0.sp &&& 0xf#64 = 0#64)
    (hptr_ne : ptr ≠ 0#64)
    (hpc : s.pc = (blkPl_372).base + 608#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (A.pool lim (M.stepEvents (rustAllocEvents (2 * (a.pts.length + 1)) 2) st) s ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        A.live ptr (2 * (a.pts.length + 1)) 2 ∗
        gf16SliceAt ptr (lagrangePreparePure a.pts).coefficients ∗
        (a.out ↦₆₄ o0) ∗ ((a.out + 8#64) ↦₆₄ o1) ∗ ((a.out + 16#64) ↦₆₄ o2) ∗
        ptSliceAt a.ptsPtr a.pts ∗
        reduceTablePlacedAt ∗
        tokenInitPlacedAt ∗
        memRegion (s0.sp - 208#64) 16 ∗
        ((s0.sp - 192#64) ↦₆₄ ptr) ∗
        ((s0.sp - 184#64) ↦₆₄ a.out) ∗
        ((s0.sp - 176#64) ↦₆₄ BitVec.ofNat 64 (a.pts.length + 1)) ∗
        ((s0.sp - 168#64) ↦₆₄ v168) ∗
        ((s0.sp - 160#64) ↦₆₄ v160) ∗
        ((s0.sp - 152#64) ↦₆₄ v152) ∗
        ((s0.sp - 144#64) ↦₆₄ v144) ∗
        memRegion (s0.sp - 136#64) 4 ∗
        ((s0.sp - 132#64) ↦₃₂ w132) ∗
        ((s0.sp - 128#64) ↦₃₂ w128) ∗
        ((s0.sp - 124#64) ↦₃₂ w124) ∗
        ((s0.sp - 120#64) ↦₃₂ w120) ∗
        ((s0.sp - 116#64) ↦₃₂ w116) ∗
        memRegion (s0.sp - 112#64) 16 ∗
        ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
        ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
        ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            ∃∗ evs : List AllocEvent,
              ⌜LagrangePrepareEnv a evs ∧ sf.trace = s0.trace⌝ ∗
              polyOf A.repAlloc a.out (lagrangePreparePure a.pts) ∗
              ptSliceAt a.ptsPtr a.pts ∗
              reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
              A.pool lim (M.stepEvents evs st) sf ∗
              stackAt s0.sp lagrangePrepareStack ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  have hbound : 4 * (a.pts.length + 1) < 2 ^ 63 := a.hlen_bound
  have hev : LagrangePrepareEnv a (rustAllocEvents (2 * (a.pts.length + 1)) 2) := rfl
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem]
  refine SepWP.fold
    (stackAt_lagrangePrepare_merge s0.sp (s0.sp - 208#64)
      ptr a.out (BitVec.ofNat 64 (a.pts.length + 1)) v168 v160 v152 v144
      w132 w128 w124 w120 w116
      (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28) (s0.readReg64 .x27)
      (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
      (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)
      rfl)
    (by sep_focus) ?_
  refine SepWP.fold
    (polyOf_of_exact_cap A.repAlloc a.out ptr (lagrangePreparePure a.pts) (a.pts.length + 1)
      (by omega) (lagrangePreparePure_length a.pts) (by omega) hptr_ne)
    (by dsimp only [RustCliAllocBudget.repAlloc]; sep_focus) ?_
  wp_done

set_option hygiene false in
local macro "wp_steps_rw_pool " mid:term:max stTerm:term:max : tactic => `(tactic| (
  apply sepWP_seg_ls_vm
    (Q := (blkPC_372).rebase (blkPl_372).base (hooksException (Rust.withPanics ext)))
    blkLib_eq_372 (mid := $mid)
  intro _m_strip
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  have _hp := (A.pool_transport lim $stTerm _ _
    (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))).symm
  wp_conv_pre => rw [_hp]
  clear _hp))

set_option maxHeartbeats 800000 in
/-- Relocatable (`[LibsignalPlacement]`) `<spqr::encoding::polynomial::Poly>::lagrange_interpolate_prepare`
(Block `372`) satisfies `lagrangePreparePlacedSpec M A lim`. -/
theorem lagrangePrepare_placed_ok [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (hshim : subroutine_ok ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) sessionShimBudgetSpec)
    (halloc : subroutine_ok ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hmemset : subroutine_ok ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext))
      (lsρ memsetName) sessionMemsetRegionBudgetSpec) :
    subroutine_ok ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext))
      (blkPl_372).base (lagrangePreparePlacedSpec M A lim) := by
  have halloc' : subroutine_ok ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocNoOomSpec M A lim false) :=
    subroutine_ok_allocNoOom_of_budget halloc
  dsimp only [sessionShimBudgetSpec] at hshim
  dsimp only [sessionMemsetRegionBudgetSpec] at hmemset
  dsimp only [rustCliAllocNoOomSpec, RustLayoutOk, CryptoVerification.RustHeap.LayoutOk,
    ↓reduceIte] at halloc'
  simp only [lagrangePreparePlacedSpec]
  wp_init g s0
  rcases g with ⟨a, st⟩
  dsimp only at *
  have hsp0 : s0.sp &&& 0xf#64 = 0#64 := beq_iff_eq.mp hsp_align
  have hbound : 4 * (a.pts.length + 1) < 2 ^ 63 := a.hlen_bound
  have hfits_ev : FitsEvents M lim st (rustAllocEvents (2 * (a.pts.length + 1)) 2) :=
    h _ rfl
  have hfe_raw : FitsEvents M lim st [.alloc (2 * (a.pts.length + 1))] := by
    simpa [rustAllocEvents] using hfits_ev
  rcases hfe_raw with ⟨⟨hwma, henf, hram, hva⟩, -⟩
  have hbit62 : (((BitVec.ofNat 64 a.pts.length + 1#64) &&& 4611686018427387904#64) != 0#64) = false :=
    len_succ_bit62_false a.pts.length hbound
  have hshl_succ : (BitVec.ofNat 64 a.pts.length + 1#64) <<< 1#64 = BitVec.ofNat 64 (2 * (a.pts.length + 1)) :=
    ofNat_add_one_shl_one a.pts.length
  have hshl_succ_nat : (BitVec.ofNat 64 a.pts.length + 1#64) <<< (1 : Nat) = BitVec.ofNat 64 (2 * (a.pts.length + 1)) :=
    ofNat_add_one_shl_one_nat a.pts.length
  have htoNat_succ : (BitVec.ofNat 64 (2 * (a.pts.length + 1))).toNat = 2 * (a.pts.length + 1) :=
    ofNat_two_mul_succ_toNat a.pts.length hbound
  have hpow2 : ∃ k, 2 = 2 ^ k := ⟨1, rfl⟩
  have hpos : 0 < 2 * (a.pts.length + 1) := by omega
  have hal : (2 : Nat) ≤ 2 ^ 31 := by decide
  have hsum : 2 * (a.pts.length + 1) + 2 ≤ 2 ^ 63 := by omega
  have hn_bound : a.pts.length + 1 < 2 ^ 63 := by omega
  have hn_lt64 : a.pts.length < 2 ^ 64 := by omega
  have halloc_le64 : 2 * (a.pts.length + 1) ≤ 2 ^ 64 := by omega
  wp_simp_pre only [memRegion_24 a.out, stackAt_lagrangePrepare_split s0.sp]
  wp_pull_exists
  wp_steps_rw_pool (lsρ spqrRustNoAllocShimSym) st
  simp only [State.setMem_setMem]
  wp_call hshim ()
  have hsp_sf0 : sf.sp = s0.sp - 208#64 := h_6
  have htr_sf0 : sf.trace = s0.trace := h_4
  have hvregs_sf0 : calleeSavedVRegs sf = calleeSavedVRegs s0 := hvregs
  have hp0 := (A.pool_transport lim st _ sf h_5).symm
  wp_conv_pre => rw [hp0]
  clear hp0
  wp_steps_rw_pool (lsρ spqrRustAllocSym) st
  simp only [State.setMem_setMem]
  wp_call halloc' (2 * (a.pts.length + 1), 2, st)
  let st1 : M.σ := M.stepEvents (rustAllocEvents (2 * (a.pts.length + 1)) 2) st
  have hsp_sf1 : sf_1.sp = s0.sp - 208#64 := hsp_sf.trans hsp_sf0
  have htr_sf1 : sf_1.trace = s0.trace := by
    refine Eq.trans h_27.2.1 ?_
    simp only [arm64_norm, wp_norm, htr_sf0]
  have hvregs_sf1 : calleeSavedVRegs sf_1 = calleeSavedVRegs s0 := hvregs_1.trans hvregs_sf0
  wp_conv_pre => simp only [hsp_sf0, hsp_sf1]
  have hptr0 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := h_28
  have hptr_mod : (sf_1.readReg64 (Reg.gpr 0#5)).toNat % 2 = 0 := hpost
  have hcbz : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hptr0
  have hptr_al : sf_1.readReg64 (Reg.gpr 0#5) &&& 1#64 = 0#64 :=
    and_one_of_mod_two hptr_mod
  have hlen_add1 : BitVec.ofNat 64 a.pts.length + 1#64 = BitVec.ofNat 64 (a.pts.length + 1) := by
    rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
  by_cases hpts_nil : a.pts = []
  · have hx20_0 : (BitVec.ofNat 64 a.pts.length == 0#64) = true := by rw [hpts_nil]; rfl
    have hmem2 :
        memRegion (sf_1.readReg64 (Reg.gpr 0#5)) (2 * (a.pts.length + 1)) =
          ∃∗ v0 : BitVec 16, (sf_1.readReg64 (Reg.gpr 0#5)) ↦₁₆ v0 := by
      rw [hpts_nil, List.length_nil, Nat.zero_add, Nat.mul_one, memRegion_two]
    wp_conv_pre => rw [hmem2]
    wp_pull_exists
    wp_steps_rw_pool ((blkPl_372).base + 608#64) st1
    simp only [State.setMem_setMem]
    have hslice_nil :
        ((sf_1.readReg64 (Reg.gpr 0#5)) ↦₁₆ 1#16) =
          gf16SliceAt (sf_1.readReg64 (Reg.gpr 0#5)) (lagrangePreparePure a.pts).coefficients := by
      rw [hpts_nil]
      simp [lagrangePreparePure, prepareLoopPure, gf16SliceAt, CryptoVerification.RustHeap.arrayAt,
        CryptoVerification.SpqrV1.Poly.gf16At, GF16.ONE]
    have h176_nil :
        ((s0.sp - 176#64) ↦₆₄ 1#64) =
          ((s0.sp - 176#64) ↦₆₄ BitVec.ofNat 64 (a.pts.length + 1)) := by
      rw [hpts_nil]; rfl
    wp_conv_pre => rw [hslice_nil, h176_nil]
    refine epilogue_placed_sepWP M A lim st ext a R s0 _ (sf_1.readReg64 (Reg.gpr 0#5))
      _ _ _ a.ptsPtr _ _ _ _ _ _ _ _ hsp0 hptr0 ?_ ?_ ?_ ?_ ?_
    · wp_norm_lhs
    · simp only [arm64_norm, wp_norm]; exact hrun_sf_1
    · simp only [arm64_norm, wp_norm, hsp_sf1]
    · simp only [arm64_norm, wp_norm, htr_sf1]
    · simp only [arm64_norm, wp_norm, hvregs_sf1]
  · have hlen_pos : 0 < a.pts.length := List.length_pos_iff.mpr hpts_nil
    have hx20_ne0 : (BitVec.ofNat 64 a.pts.length == 0#64) = false := by
      rw [beq_eq_false_iff_ne]; intro h0
      have ht := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn_lt64] at ht
      exact Nat.ne_of_gt hlen_pos ht
    have hsub_shl :
        (BitVec.ofNat 64 (a.pts.length + 1) + 0xffffffff_ffffffff#64) <<< (1 : Nat) =
          BitVec.ofNat 64 (2 * a.pts.length) :=
      ofNat_succ_sub_one_shl_one a.pts.length
    have htoNat_len : (BitVec.ofNat 64 (2 * a.pts.length)).toNat = 2 * a.pts.length :=
      ofNat_two_mul_toNat a.pts.length hbound
    have hsplit_alloc :
        memRegion (sf_1.readReg64 (Reg.gpr 0#5)) (2 * (a.pts.length + 1)) =
          memRegion (sf_1.readReg64 (Reg.gpr 0#5)) (2 * a.pts.length) ∗
            (∃∗ v_last : BitVec 16,
              (sf_1.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 (2 * a.pts.length)) ↦₁₆ v_last) :=
      memRegion_alloc_split (sf_1.readReg64 (Reg.gpr 0#5)) a.pts.length halloc_le64
    wp_conv_pre => rw [hsplit_alloc]
    wp_pull_exists
    wp_steps_rw_pool (lsρ memsetName) st1
    simp only [State.setMem_setMem]
    wp_call hmemset
    have hsp_sf2 : sf_2.sp = s0.sp - 208#64 := hsp_sf_1.trans hsp_sf1
    have htr_sf2 : sf_2.trace = s0.trace := hpost_1.trans htr_sf1
    have hvregs_sf2 : calleeSavedVRegs sf_2 = calleeSavedVRegs s0 := hvregs_2.trans hvregs_sf1
    have hx20_sf2 : sf_2.readReg64 (Reg.gpr 20#5) = BitVec.ofNat 64 a.pts.length :=
      (h_30.trans h_18).trans h_8
    have hx29_sf2 : sf_2.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64 :=
      (hcs_sf_1.trans hcs_sf).trans hpost_sf
    have hp2 := (A.pool_transport lim st1 _ sf_2 h_39).symm
    wp_conv_pre => rw [hp2]
    clear hp2
    have hrep_zero :
        (sf_1.readReg64 (Reg.gpr 0#5) ↦ₛ
          List.replicate (BitVec.ofNat 64 (2 * (a.pts.length + 1)) - 2#64).toNat 0#8) =
          gf16SliceAt (sf_1.readReg64 (Reg.gpr 0#5)) (List.replicate a.pts.length GF16.ZERO) := by
      rw [sub_two_toNat_eq a.pts.length hbound, gf16SliceAt_replicate_zero]
    have hshl_len : BitVec.ofNat 64 a.pts.length <<< (1 : Nat) = BitVec.ofNat 64 (2 * a.pts.length) :=
      ofNat_shl_one_nat a.pts.length
    have hshl_len' : BitVec.ofNat 64 a.pts.length <<< 1#64 = BitVec.ofNat 64 (2 * a.pts.length) :=
      ofNat_shl_one a.pts.length
    have hal_last :
        MemWidth.isAligned .W16
          (sf_1.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 (2 * a.pts.length)) = true :=
      aligned16_add_mul_two (sf_1.readReg64 (Reg.gpr 0#5)) hptr_al a.pts.length
    wp_steps_rw_pool ((blkPl_372).base + 132#64) st1
    simp only [State.setMem_setMem]
    wp_conv_pre => rw [hrep_zero, combine_init_slice, outerLoop_frame_eq]
    have hx19_init :
        sf_1.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 (2 * a.pts.length) - 2#64 =
          sf_1.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 (2 * (a.pts.length - 1)) := by
      have hlen_eq : a.pts.length = (a.pts.length - 1) + 1 := (Nat.sub_add_cancel hlen_pos).symm
      conv => lhs; arg 1; arg 2; rw [hlen_eq]
      exact ptr_sub_two_succ (sf_1.readReg64 (Reg.gpr 0#5)) (a.pts.length - 1)
    apply sepWP_seg_ls_vm
      (Q := (blkPC_372).rebase (blkPl_372).base (hooksException (Rust.withPanics ext)))
      blkLib_eq_372 (mid := (blkPl_372).base + 608#64)
    intro m_strip
    apply outerLoop_placed_tp (hooksException (Rust.withPanics ext))
      s0.sp (sf_1.readReg64 (Reg.gpr 0#5)) a.ptsPtr
      hsp0 hptr_al a.pts hn_bound ((blkPl_372).base + 608#64) _
      (a.pts.length - 1) 0 ⟨List.replicate a.pts.length GF16.ZERO ++ [GF16.ONE]⟩
      (by rw [Nat.zero_add]; exact Nat.sub_add_cancel hlen_pos) (by simp)
      _ _ _ _ _ _ _ _ _ _
      (by wp_norm_lhs)
      (by wp_norm_lhs)
      (by simp only [arm64_norm, wp_norm, hsp_sf2])
      (by wp_norm_lhs)
      (by simpa [arm64_norm, wp_norm] using hx19_init)
      (by simp only [arm64_norm, wp_norm]; exact hx20_sf2)
      (by wp_norm_lhs)
      (by wp_norm_lhs)
      (by simp only [arm64_norm, wp_norm]; exact hx29_sf2)
    intro v160' v152' v144' w132' w128' w124' w120' w116' sf_loop
      hpc_loop hrun_loop hsp_loop htr_loop htp_loop hvregs_loop
    refine SepWP.done hpc_loop hrun_loop fun m_real hnsp_loop => ?_
    have hvm_loop :=
      hnsp_loop.toVmPreserved (by simp only [arm64_norm, wp_norm, htp_loop])
    have hloop_eq :
        prepareLoopPure a.pts a.pts.length 0 (a.pts.length - 1 + 1)
          ⟨List.replicate a.pts.length GF16.ZERO ++ [GF16.ONE]⟩ =
          lagrangePreparePure a.pts := by
      rw [Nat.sub_add_cancel hlen_pos]; rfl
    have hp_loop := (A.pool_transport lim st1 _ _ hvm_loop).symm
    wp_conv_pre => rw [hp_loop, hloop_eq, ← outerLoop_frame_eq]
    exact epilogue_placed_sepWP M A lim st ext a R s0 (sf_loop.setMem m_real)
      (sf_1.readReg64 (Reg.gpr 0#5))
      _ _ _ a.ptsPtr v160' v152' v144' w132' w128' w124' w120' w116' hsp0 hptr0
      (by simp only [arm64_norm, wp_norm, hpc_loop])
      (by simp only [arm64_norm, wp_norm, hrun_loop])
      (by simp only [arm64_norm, wp_norm, hsp_loop])
      (by simp only [arm64_norm, wp_norm, htr_loop, htr_sf2])
      (by simp only [arm64_norm, wp_norm, hvregs_loop, hvregs_sf2])

theorem lagrangePrepare_placed_ok_of_hookSat [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionBudgetSpec) :
    subroutine_ok ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext))
      (blkPl_372).base (lagrangePreparePlacedSpec M A lim) :=
  lagrangePrepare_placed_ok M A lim ext
    (spqr_hook_ok_of_mem hshim)
    (spqr_hook_ok_of_mem halloc)
    (spqr_hook_ok_of_mem hmemset)

end LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.ProofBudget

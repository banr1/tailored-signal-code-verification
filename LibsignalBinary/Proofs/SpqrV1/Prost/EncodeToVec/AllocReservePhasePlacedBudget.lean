/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhasePlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# `PqRatchetState::encode_to_vec` (Block `426`): Budget-Threaded Placed Allocation and Epilogue

Relocatable `[LibsignalPlacement]` epilogue (`+1808..+1856` preserving `VmPreserved`) and initial
`Vec<u8>` buffer allocation (`+516..+580` / `+1212`) threading `RustCliAllocBudget M` across
`pqRatchetStateEncodeToVecEvents`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhasePlacedBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits FitsEvents RustCliAllocBudget VmPreserved rustAllocEvents)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.RustHeap (RustAlloc vecU8 vecU8At)
open CryptoVerification.LibsignalSpqrV1 (PqRatchetState)
open CryptoVerification.SpqrV1.ProtoRepr (optChainPBPinnedAt)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (noneCap_add_one_beq_zero noneCap_add_one_bne_zero
   ofNat_countLeadingZeros_32 ofNat_countLeadingZeros_64
   ule_self_64 ule_zero_64 ult_self_64 ult_zero_64
   zeroExtend64_beq_zero32 zext64_truncate32
   hwVarintLen_bvShift_eq_ofNat_varintLen_norm hwVarintLen_eq_ofNat_varintLen_norm)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (PqRatchetStatePBGhost StepInv blkPC_426 blkPl_426 calleeSavedPreserved_writeLr_setPC
   encodeToVecCalleeStackOf encodeToVecLocalSlots encodeToVecSavedRegs encodeToVecStackOf
   memRegion_24_eq noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
   optChainCap optPqRatchetInnerCap optPqRatchetInnerPBPinnedAt optVersionNegCap
   optVersionNegRest optVersionNegRest_cap_bounds optVersionNegotiationPBPinnedAt_eq
   pqRatchetStatePBEncodedLen pqRatchetStatePBPinnedAt
   pqRatchetState_fields_none_of_encodedLen_zero
   stackAt_encodeToVec_recombine vecU8At_empty_of_alloc vecU8At_empty_zero
   vecU8At_expose_header withStepInv)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget
  (pqRatchetStateEncodeToVecEvents)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
  (sepWP_done_tpidr sepWP_done_vm sepWPp_call_cs_noPanic sepWPp_of_sepWP_cs_vm)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
  (authEncodeExactSpecOf encodeChainParamsExactSpecOf encodeEpochDirectionExactSpecOf
   encodeVarintExactSpecOf epochEncLenStackSpecOf etvMemcpyRegionSpec
   rustAllocStackSpecOf shimStackSpecOf)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (lsRetAddr624_blockPlacement_base_add)

private theorem sepWPp_extract_pure {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp} (φ : Prop)
    (hφ : ∀ R : SepProp, s.mem ⊨ P ∗ R → φ)
    (hnext : φ → SepWPp prog ret s P Q Qp oom) :
    SepWPp prog ret s P Q Qp oom :=
  fun R hm hL => hnext (hφ R hm) R hm hL

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm zext64_truncate32
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  ule_zero_64 ult_zero_64 ule_self_64 ult_self_64

@[local simp, local arm64_norm, local wp_norm]
private theorem extractLsb_lo_append64 (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 0 64 = lo := by
  bv_kernel

@[local simp, local arm64_norm, local wp_norm]
private theorem extractLsb_hi_append64 (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 64 64 = hi := by
  bv_kernel

/-! ## 1. Epilogue (`+1808..+1856`) -/

theorem step_encodeToVec_epilogue_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State))
    {s0 s : State} (sret sp cap ptr v0 v1 v2 : BitVec 64) (bs : List (BitVec 8))
    {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_426).base + 1808#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx27 : s.readReg64 .x27 = sret)
    (hinv0 : StepInv s0 s)
    (hP : P = (vecU8At A (sp - 120#64) cap ptr bs ∗
      memRegion sret 24 ∗
      ((sp - 144#64) ↦₆₄ v0) ∗ ((sp - 136#64) ↦₆₄ v1) ∗ ((sp - 128#64) ↦₆₄ v2) ∗
      encodeToVecSavedRegs sp s0 ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hret : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf →
      StepInv s0 sf →
      VmPreserved s sf →
      Q sf ((vecU8 A sret bs ∗ stackAt sp (encodeToVecStackOf resStack)) ∗ F)) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) (s0.readReg64 .lr) s P Q Qp oom := by
  subst hP
  unfold encodeToVecSavedRegs
  rw [vecU8At_expose_header A (sp - 120#64) cap ptr bs, memRegion_24_eq sret]
  have h112 : (sp - 120#64) + 8#64 = sp - 112#64 := by bv_omega
  have h104 : (sp - 120#64) + 16#64 = sp - 104#64 := by bv_omega
  rw [h112, h104]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun s2_v => SepWPp.exists_elim fun s1_v =>
    SepWPp.exists_elim fun s0_v => ?_
  apply sepWPp_of_sepWP_cs_vm (mid := s0.readReg64 .lr)
  by_vm_steps
    wp_steps
    apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv1
    refine SepWPp.weaken_pre ?_
      (SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hret _ (by simp only [arm64_norm])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
           by simp only [arm64_norm, *], by simp only [arm64_norm, *],
           by simp only [arm64_norm, *], by simp only [arm64_norm, *],
           by simp only [arm64_norm, *], by simp only [arm64_norm, *],
           by simp only [arm64_norm, *], by simp only [arm64_norm, *],
           by simp only [arm64_norm, *], (hinv0.trans hinv1.1).2.2⟩
          (hinv0.trans hinv1.1) hinv1.2))
    refine sepConj_mono_left ?_
    refine Entails.trans ?_
      (sepConj_mono_right
        (stackAt_encodeToVec_recombine hres sp v0 v1 v2 cap ptr (BitVec.ofNat 64 bs.length) s0))
    unfold vecU8 encodeToVecLocalSlots encodeToVecSavedRegs
    refine Entails.trans ?_
      (sepConj_mono_left
        (Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))))
    rw [vecU8At_expose_header A sret cap ptr bs]
    exact Entails.of_eq (by sep_ac_rfl)

/-- Convenience epilogue stepper directly transporting `A.pool lim st` across `+1808..+1856`. -/
theorem step_encodeToVec_epilogue_pool_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (H : String → Option (State → State))
    {s0 s : State} (sret sp cap ptr v0 v1 v2 : BitVec 64) (bs : List (BitVec 8))
    {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_426).base + 1808#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx27 : s.readReg64 .x27 = sret)
    (hinv0 : StepInv s0 s)
    (hP : P = (vecU8At A.repAlloc (sp - 120#64) cap ptr bs ∗
      memRegion sret 24 ∗
      ((sp - 144#64) ↦₆₄ v0) ∗ ((sp - 136#64) ↦₆₄ v1) ∗ ((sp - 128#64) ↦₆₄ v2) ∗
      encodeToVecSavedRegs sp s0 ∗
      A.pool lim st s ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hret : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf →
      StepInv s0 sf →
      Q sf ((vecU8 A.repAlloc sret bs ∗ A.pool lim st sf ∗
        stackAt sp (encodeToVecStackOf resStack)) ∗ F)) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) (s0.readReg64 .lr) s P Q Qp oom := by
  refine step_encodeToVec_epilogue_placed hres A.repAlloc H sret sp cap ptr v0 v1 v2 bs
    (F := A.pool lim st s ∗ F)
    hpc hrun hsp halign htr hx27 hinv0 (by rw [hP]; sep_ac_rfl) ?_
  intro sf hpcf hrunf hspf htrf hcsf hinvf hvm
  have hpool : A.pool lim st s = A.pool lim st sf := (A.pool_of_vmPreserved hvm).symm
  have hframe :
      ((vecU8 A.repAlloc sret bs ∗ stackAt sp (encodeToVecStackOf resStack)) ∗
        (A.pool lim st s ∗ F)) =
      ((vecU8 A.repAlloc sret bs ∗ A.pool lim st sf ∗
        stackAt sp (encodeToVecStackOf resStack)) ∗ F) := by
    rw [hpool]; sep_ac_rfl
  rw [hframe]
  exact hret sf hpcf hrunf hspf htrf hcsf hinvf

/-! ## 2. Initial Buffer Allocation (`+516..+580` / `+1212`) -/

private theorem getLsbD_63_ofNat_eq_false {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n).getLsbD 63 = false := by
  have htoNat : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat, htoNat]
  exact Nat.testBit_lt_two_pow h

private theorem getElem_63_ofNat_eq_false {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n)[63] = false := by
  have htoNat : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.getElem_eq_testBit_toNat, htoNat]
  exact Nat.testBit_lt_two_pow h

private theorem ofNat_beq_zero_false_of_pos {n : Nat} (hpos : 0 < n) (hlt : n < 2 ^ 63) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  change n = 0 at ht
  omega

theorem step_encodeToVec_alloc_placed [LibsignalPlacement] {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (H : String → Option (State → State))
    {s0 s : State}
    (hshim : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      ((blkPl_426).ρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStepInv s0 (shimStackSpecOf resStack)))
    (halloc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      ((blkPl_426).ρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (withStepInv s0 (rustAllocStackSpecOf resStack A lim)))
    (sret a sp v0 v1 v2 v3 v4 v5 : BitVec 64) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63)
    (hfits : FitsEvents M lim st0 (pqRatchetStateEncodeToVecEvents st))
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_426).base + 516#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = optChainCap g.chain st.chain)
    (hx20 : s.readReg64 .x20 = a)
    (hx21 : s.readReg64 .x21 = a + 128#64)
    (hx22 : s.readReg64 .x22 = a + 48#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st))
    (hx25 : s.readReg64 .x25 = optVersionNegCap g.vn st.versionNegotiation)
    (hx27 : s.readReg64 .x27 = sret)
    (hx28 : s.readReg64 .x28 = optPqRatchetInnerCap g.inner st.inner)
    (hfp : s.readReg64 .fp = sp - 96#64)
    (hinv0 : StepInv s0 s)
    (hP : P = (pqRatchetStatePBPinnedAt A.repAlloc g a st ∗
      A.pool lim st0 s ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
      encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5 ∗
      encodeToVecSavedRegs sp s0) ∗ F)
    (hnext : ∀ (sm : State) (ptr : BitVec 64),
      sm.pc = (if st.versionNegotiation.isSome then (blkPl_426).base + 580#64
               else (blkPl_426).base + 1212#64) →
      sm.status = .Running →
      sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      (st.versionNegotiation.isSome → sm.readReg64 .x0 = ptr) →
      sm.readReg64 .x19 = optChainCap g.chain st.chain →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = a + 128#64 →
      sm.readReg64 .x22 = a + 48#64 →
      sm.readReg64 .x25 = optVersionNegCap g.vn st.versionNegotiation →
      sm.readReg64 .x27 = sret →
      sm.readReg64 .x28 = optPqRatchetInnerCap g.inner st.inner →
      sm.readReg64 .fp = sp - 96#64 →
      StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm
        ((pqRatchetStatePBPinnedAt A.repAlloc g a st ∗
          vecU8At A.repAlloc (sp - 120#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr [] ∗
          A.pool lim (M.stepEvents (pqRatchetStateEncodeToVecEvents st) st0) sm ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
          ((sp - 144#64) ↦₆₄ v0) ∗ ((sp - 136#64) ↦₆₄ v1) ∗ ((sp - 128#64) ↦₆₄ v2) ∗
          encodeToVecSavedRegs sp s0) ∗ F)
        Q Qp oom) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q Qp oom := by
  subst hP
  have hbit63 := getLsbD_63_ofNat_eq_false hlen
  have helem63 := getElem_63_ofNat_eq_false hlen
  refine sepWPp_extract_pure
    ((optVersionNegCap g.vn st.versionNegotiation + 1#64 == 0#64) = !st.versionNegotiation.isSome ∧
     (optVersionNegCap g.vn st.versionNegotiation + 1#64 != 0#64) = st.versionNegotiation.isSome)
    (fun R' hm => by
      unfold pqRatchetStatePBPinnedAt at hm
      rw [optVersionNegotiationPBPinnedAt_eq] at hm
      have hm' : s.mem ⊨ optVersionNegRest A.repAlloc g.vn a st.versionNegotiation ∗
          ((a ↦₆₄ optVersionNegCap g.vn st.versionNegotiation) ∗
           optChainPBPinnedAt A.repAlloc g.chain (a + 48#64) st.chain ∗
           optPqRatchetInnerPBPinnedAt A.repAlloc g.inner (a + 128#64) st.inner ∗
           A.pool lim st0 s ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
           encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5 ∗
           encodeToVecSavedRegs sp s0 ∗ F ∗ R') := by
        convert hm using 1; sep_ac_rfl
      exact optVersionNegRest_cap_bounds hm')
    fun ⟨hvn_eq, hvn_ne⟩ => ?_
  by_cases hzero : pqRatchetStatePBEncodedLen st = 0
  · obtain ⟨hvn_none, _, _, _⟩ := pqRatchetState_fields_none_of_encodedLen_zero hzero
    have hevs0 : pqRatchetStateEncodeToVecEvents st = [] := by
      simp [pqRatchetStateEncodeToVecEvents, hzero]
    have hx23_0 : s.readReg64 .x23 = 0#64 := by rw [hx23, hzero]
    rw [hvn_none] at hvn_eq hvn_ne
    simp only [Option.isSome_none, Bool.not_false] at hvn_eq hvn_ne
    unfold encodeToVecLocalSlots
    apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 1212#64)
    by_vm_steps
      wp_steps
      apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv1
      refine SepWPp.weaken_pre ?_
        (hnext _ 1#64
          (by rw [hvn_none]; simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (fun h => by rw [hvn_none] at h; cases h)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1))
      rw [hevs0, M.stepEvents_nil, ← A.pool_of_vmPreserved hinv1.2, hzero,
        ← vecU8At_empty_zero A.repAlloc (sp - 120#64)]
      have h112 : (sp - 120#64) + 8#64 = sp - 112#64 := by bv_omega
      have h104 : (sp - 120#64) + 16#64 = sp - 104#64 := by bv_omega
      rw [h112, h104]
      exact Entails.of_eq (by sep_ac_rfl)
  · have hpos : 0 < pqRatchetStatePBEncodedLen st := Nat.pos_of_ne_zero hzero
    have hevs_pos : pqRatchetStateEncodeToVecEvents st =
        rustAllocEvents (pqRatchetStatePBEncodedLen st) 1 := by
      simp [pqRatchetStateEncodeToVecEvents, hzero]
    have hfits_alloc : FitsEvents M lim st0 (rustAllocEvents (pqRatchetStatePBEncodedLen st) 1) := by
      rwa [hevs_pos] at hfits
    have hcbz_f := ofNat_beq_zero_false_of_pos hpos hlen
    apply sepWPp_of_sepWP_cs_vm
      (mid := (blkPl_426).ρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
    wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv1
    refine sepWPp_call_cs_noPanic (x := ())
      (F := pqRatchetStatePBPinnedAt A.repAlloc g a st ∗ A.pool lim st0 s ∗
        encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5 ∗ encodeToVecSavedRegs sp s0 ∗ F)
      hshim (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
      (by simp only [State.spAligned, arm64_norm, hsp, beq_iff_eq]; exact halign)
      (ret_pc := (blkPl_426).base + 544#64) (by simp only [arm64_norm]) ?_ ?_ ?_ ?_ ?_
    · intro R' hm
      simp only [arm64_norm] at hm
      simp only [withStepInv, shimStackSpecOf, arm64_norm, hsp, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hinv0.trans hinv1.1, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
    · intro sf code R' _ hm
      simp only [withStepInv, shimStackSpecOf, satisfies_pure_sepConj] at hm
      exact hm.1.elim
    · intro sf R' _ hm
      simp only [withStepInv, shimStackSpecOf, satisfies_pure_sepConj] at hm
      exact hm.1.elim
    · intro sf R' _ hm
      simp only [withStepInv, shimStackSpecOf, satisfies_pure_sepConj] at hm
      exact hm.1.elim
    · intro s1 hpcs1 hruns1 hsps1 hcss1 hinv_s1
      simp only [arm64_norm, hsp] at hsps1
      obtain ⟨hs1_19, hs1_20, hs1_21, hs1_22, hs1_23, hs1_24, hs1_25, hs1_26, hs1_27, hs1_28, hs1_fp, _⟩ :=
        calleeSavedPreserved_writeLr_setPC hcss1
      rw [hx19] at hs1_19; rw [hx20] at hs1_20; rw [hx21] at hs1_21
      rw [hx22] at hs1_22; rw [hx23] at hs1_23
      rw [hx25] at hs1_25; rw [hx27] at hs1_27; rw [hx28] at hs1_28; rw [hfp] at hs1_fp
      dsimp only [withStepInv, shimStackSpecOf]
      simp only [arm64_norm, hsp, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hvm_s1, htrs1⟩ => ?_
      have htrs1' : s1.trace = s0.trace := htrs1.trans htr
      rw [← A.pool_of_vmPreserved (hinv1.2.trans hvm_s1)]
      apply sepWPp_of_sepWP_cs_vm
        (mid := (blkPl_426).ρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv2
      rw [← A.pool_of_vmPreserved hinv2.2]
      have htoNat_len :
          (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)).toNat = pqRatchetStatePBEncodedLen st := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine sepWPp_call_cs_noPanic (x := (pqRatchetStatePBEncodedLen st, st0))
        (F := pqRatchetStatePBPinnedAt A.repAlloc g a st ∗
          encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5 ∗ encodeToVecSavedRegs sp s0 ∗ F)
        halloc (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (by simp only [State.spAligned, arm64_norm, hsps1, beq_iff_eq]; exact halign)
        (ret_pc := (blkPl_426).base + 560#64) (by simp only [arm64_norm]) ?_ ?_ ?_ ?_ ?_
      · intro R' hm
        simp only [arm64_norm] at hm
        simp only [withStepInv, rustAllocStackSpecOf, arm64_norm, hsps1, htoNat_len,
          sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨⟨(hinv0.trans hinv1.1).trans (hinv_s1.trans hinv2.1), hpos, hlen, hfits_alloc, ?_⟩, ?_⟩
        · simp only [wp_norm, arm64_norm, blkPl_426]
          apply lsRetAddr624_blockPlacement_base_add <;> decide
        exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
      · intro sf code R' _ hm
        simp only [withStepInv, rustAllocStackSpecOf, satisfies_pure_sepConj] at hm
        exact hm.1.elim
      · intro sf R' _ hm
        simp only [withStepInv, rustAllocStackSpecOf, satisfies_pure_sepConj] at hm
        exact hm.1.elim
      · intro sf R' _ hm
        simp only [withStepInv, rustAllocStackSpecOf, satisfies_pure_sepConj] at hm
        exact hm.1.elim
      · intro s2 hpcs2 hruns2 hsps2 hcss2 hinv_s2
        simp only [arm64_norm, hsps1] at hsps2
        obtain ⟨hs2_19, hs2_20, hs2_21, hs2_22, hs2_23, hs2_24, hs2_25, hs2_26, hs2_27, hs2_28, hs2_fp, _⟩ :=
          calleeSavedPreserved_writeLr_setPC hcss2
        simp only [arm64_norm, hs1_19, hs1_20, hs1_21, hs1_22, hs1_23, hs1_25, hs1_27, hs1_28, hs1_fp]
          at hs2_19 hs2_20 hs2_21 hs2_22 hs2_23 hs2_25 hs2_27 hs2_28 hs2_fp
        have hinv_s2' : StepInv s0 s2 :=
          ((hinv0.trans hinv1.1).trans (hinv_s1.trans hinv2.1)).trans hinv_s2
        dsimp only [withStepInv, rustAllocStackSpecOf]
        simp only [arm64_norm, hsps1, sepConj_assoc]
        refine SepWPp.pure_elim fun ⟨hoom, htrs2⟩ => ?_
        have hoom_f : (s2.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
        have htrs2' : s2.trace = s0.trace := htrs2.trans htrs1'
        unfold encodeToVecLocalSlots
        cases hvn_case : st.versionNegotiation with
        | none =>
          rw [hvn_case] at hvn_eq hvn_ne
          simp only [Option.isSome_none, Bool.not_false] at hvn_eq hvn_ne
          apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 1212#64)
          by_vm_steps
            wp_steps
            apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, wp_norm, *])
            intro hinv3
            refine SepWPp.weaken_pre ?_
              (hnext _ (s2.readReg64 .x0)
                (by rw [hvn_case]; simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *])
                (fun h => by rw [hvn_case] at h; cases h)
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_s2'.trans hinv3.1))
            rw [hevs_pos, ← A.pool_of_vmPreserved hinv3.2,
              ← vecU8At_empty_of_alloc A.repAlloc (sp - 120#64) (s2.readReg64 .x0)
                (pqRatchetStatePBEncodedLen st) hpos hlen hoom]
            have h112 : (sp - 120#64) + 8#64 = sp - 112#64 := by bv_omega
            have h104 : (sp - 120#64) + 16#64 = sp - 104#64 := by bv_omega
            rw [h112, h104]
            dsimp only [RustCliAllocBudget.repAlloc, Reg.x0]
            exact Entails.of_eq (by sep_ac_rfl)
        | some vn =>
          rw [hvn_case] at hvn_eq hvn_ne
          simp only [Option.isSome_some, Bool.not_true] at hvn_eq hvn_ne
          apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 580#64)
          by_vm_steps
            wp_steps
            apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, wp_norm, *])
            intro hinv3
            refine SepWPp.weaken_pre ?_
              (hnext _ (s2.readReg64 .x0)
                (by rw [hvn_case]; simp only [↓reduceIte, arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *])
                (fun _ => by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_s2'.trans hinv3.1))
            rw [hevs_pos, ← A.pool_of_vmPreserved hinv3.2,
              ← vecU8At_empty_of_alloc A.repAlloc (sp - 120#64) (s2.readReg64 .x0)
                (pqRatchetStatePBEncodedLen st) hpos hlen hoom]
            have h112 : (sp - 120#64) + 8#64 = sp - 112#64 := by bv_omega
            have h104 : (sp - 120#64) + 16#64 = sp - 104#64 := by bv_omega
            rw [h112, h104]
            dsimp only [RustCliAllocBudget.repAlloc, Reg.x0]
            exact Entails.of_eq (by sep_ac_rfl)

/-! ## 3. Exact-Capacity Callee Call Wrappers Re-Exported from `AllocReservePhaseBudget` -/

abbrev step_etv_encode_varint_call_prog := @AllocReservePhaseBudget.step_etv_encode_varint_call_prog
abbrev step_etv_memcpy_call_prog := @AllocReservePhaseBudget.step_etv_memcpy_call_prog
abbrev step_etv_encode_chainParams_call_prog := @AllocReservePhaseBudget.step_etv_encode_chainParams_call_prog
abbrev step_etv_epoch_encLen_call_prog := @AllocReservePhaseBudget.step_etv_epoch_encLen_call_prog
abbrev step_etv_encode_epochDirection_call_prog := @AllocReservePhaseBudget.step_etv_encode_epochDirection_call_prog
abbrev step_etv_encode_auth_call_prog := @AllocReservePhaseBudget.step_etv_encode_auth_call_prog

end LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhasePlacedBudget

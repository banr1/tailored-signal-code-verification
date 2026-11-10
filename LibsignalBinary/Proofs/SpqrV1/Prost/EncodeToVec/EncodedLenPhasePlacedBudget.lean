/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenPhase
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodeToVecCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsV1StateBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
import ProofLib.SepLogic.WPp

/-!
# `PqRatchetState::encode_to_vec` (Block `426`): `StepInvVm` Placed `encoded_len` Phase (`+0..+516`)

Relocatable `[LibsignalPlacement]` verification of Phase 1 (`+0..+516`) of
`PqRatchetState::encode_to_vec` threading `StepInvVm` (`StepInv ∧ VmPreserved`) with zero allocator
events.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenPhasePlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification
  (LibsignalPlacement LibsignalCodeLoaded LibsignalRoLoaded lsmpl lsρ)
open CryptoVerification.LibsignalSpqrV1
  (PqRatchetState VersionNegotiationPB ChainPB ChainParamsPB V1State)
open CryptoVerification.SpqrV1.ProtoRepr
  (VersionNegotiationPBGhost ChainPBGhost V1StatePBGhost PinnedEncLenGhost
   ChainEncodedLenPinnedGhost V1StateEncodedLenPinnedGhost
   bytesFieldEncodedLen i32VarintFieldEncodedLen u32VarintFieldEncodedLen varintLen
   optVersionNegotiationPBPinnedAt optChainPBPinnedAt optChainParamsPBAt chainParamsPBAt
   chainPBPinnedAt chainPBEncodedLen v1StatePBPinnedAt v1StatePBEncodedLen
   optChainParamsPBFieldEncodedLen chainParamsPBEncodedLen v1StateJumpTableBytes)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (vecU8Buf ule_self_64 ult_self_64 ule_zero_64 ult_zero_64
   zeroExtend64_beq_zero32 ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
   hwVarintLen_eq_ofNat_varintLen_norm hwVarintLen_bvShift_eq_ofNat_varintLen_norm
   zext64_truncate32 noneCap_add_one_beq_zero noneCap_add_one_bne_zero
   ofNat_length_beq_zero_of_lt bv_u32VarintField_nonzero bv_bytesField_nonempty
   bv_add_ofNat_comm bv_add_ofNat_eq adds_no_overflow_of_eq cmp_ls_false_of_lt)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (blkPC_426 blkPl_426 PqRatchetStatePBGhost
   pqRatchetStatePBPinnedAt pqRatchetStatePBEncodedLen
   optVersionNegotiationPBPinnedAt_eq optVersionNegotiationPBFieldEncodedLen
   optVersionNegCap optVersionNegRest optVersionNegRest_cap_bounds versionNegotiationRest
   optChainPBPinnedAt_eq optChainPBFieldEncodedLen
   optChainCap optChainRest optChainRest_cap_bounds
   optPqRatchetInnerPBPinnedAt optPqRatchetInnerPBPinnedAt_eq
   optPqRatchetInnerPBFieldEncodedLen
   optPqRatchetInnerCap optPqRatchetInnerPBPinnedAt_cap_bounds
   encodeToVecStackOf encodeToVecCalleeStackOf encodeToVecLocalSlots encodeToVecSavedRegs
   sp_sub_144_aligned stackAt_encodeToVec_split cells_12_sub_96_eq
   stackAt_callee_eq_chainEncodedLen stackAt_callee_eq_v1StateEncodedLen
   noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
   bv_i32VarintField_nonzero bv_chainParams_maxJump_nonzero bv_optChainParams_some_combine
   bv_vn_sum_eq bv_optVN_some_eq bv_optChain_some_eq bv_optInner_some_eq
   chainPBEncodedLen_lt_of_state v1StatePBEncodedLen_lt_of_state vn_authKey_len_lt_of_state)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget
  (withVmPreserved chainEncodedLenPinnedSpec)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsV1StateBudget
  (v1StateEncodedLenRoPinnedSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
  (StepInvVm withStepInvVm sepWPp_of_sepWP_cs_vm sepWP_done_vm sepWP_done_tpidr
   sepWPp_call_cs_noPanic step_encodeToVec_vn_authKey_placed)

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

/-! ## Step 1a: `VersionNegotiation::encoded_len` Sub-Blocks (`+52 .. +368`) -/

theorem step_encodeToVec_vn_dir_minVer_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (a : BitVec 64) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_426).base + 88#64) (hrun : s.status = .Running)
    (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInvVm s0 s)
    (hP : P = versionNegotiationRest A g a vn ∗ F)
    (hnext : ∀ s1 : State,
      (s1.pc = (blkPl_426).base + 160#64 ∨ s1.pc = (blkPl_426).base + 288#64) →
      s1.status = .Running → s1.sp = s.sp → s1.trace = s.trace →
      s1.readReg64 .x8 = s.readReg64 .x8 →
      s1.readReg64 .x9 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.direction) →
      s1.readReg64 .x10 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.minVersion) →
      s1.readReg64 .x20 = a → s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .fp = s.readReg64 .fp →
      StepInvVm s0 s1 →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s1 (versionNegotiationRest A g a vn ∗ F) Q Qp oom) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q Qp oom := by
  subst hP
  dsimp only [versionNegotiationRest]
  by_cases hmv : vn.minVersion = 0#32
  · have hmv_eq : i32VarintFieldEncodedLen vn.minVersion = 0 := by simp [i32VarintFieldEncodedLen, hmv]
    have hbeq_mv : (vn.minVersion == 0#32) = true := beq_iff_eq.mpr hmv
    have hbne_mv : (vn.minVersion != 0#32) = false := by simp [hmv]
    by_cases hdir : vn.direction = 0#32
    · have hdir_eq : i32VarintFieldEncodedLen vn.direction = 0 := by simp [i32VarintFieldEncodedLen, hdir]
      have hbeq_d : (vn.direction == 0#32) = true := beq_iff_eq.mpr hdir
      have hbne_d : (vn.direction != 0#32) = false := by simp [hdir]
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 288#64); wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *]); intro hinv
      exact hnext _ (Or.inr (by simp only [arm64_norm, *]))
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv)
    · have hbeq_d : (vn.direction == 0#32) = false := beq_eq_false_iff_ne.mpr hdir
      have hbne_d : (vn.direction != 0#32) = true := bne_iff_ne.mpr hdir
      have hstep_d := bv_i32VarintField_nonzero hdir
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 288#64); wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *]); intro hinv
      exact hnext _ (Or.inr (by simp only [arm64_norm, *]))
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv)
  · have hbeq_mv : (vn.minVersion == 0#32) = false := beq_eq_false_iff_ne.mpr hmv
    have hbne_mv : (vn.minVersion != 0#32) = true := bne_iff_ne.mpr hmv
    have hstep_mv := bv_i32VarintField_nonzero hmv
    suffices h132 : ∀ s_mid : State,
        s_mid.pc = (blkPl_426).base + 132#64 → s_mid.status = .Running → s_mid.sp = s.sp → s_mid.trace = s.trace →
        s_mid.readReg64 .x8 = s.readReg64 .x8 →
        s_mid.readReg64 .x9 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.direction) →
        s_mid.readReg64 .x10 = vn.minVersion.signExtend 64 →
        s_mid.readReg64 .x20 = a → s_mid.readReg64 .x25 = s.readReg64 .x25 →
        s_mid.readReg64 .x27 = s.readReg64 .x27 → s_mid.readReg64 .fp = s.readReg64 .fp →
        StepInvVm s0 s_mid →
        SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s_mid (versionNegotiationRest A g a vn ∗ F) Q Qp oom by
      by_cases hdir : vn.direction = 0#32
      · have hdir_eq : i32VarintFieldEncodedLen vn.direction = 0 := by simp [i32VarintFieldEncodedLen, hdir]
        have hbeq_d : (vn.direction == 0#32) = true := beq_iff_eq.mpr hdir
        have hbne_d : (vn.direction != 0#32) = false := by simp [hdir]
        apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 132#64); wp_steps
        apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *]); intro hinv
        exact h132 _
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv0.trans hinv)
      · have hbeq_d : (vn.direction == 0#32) = false := beq_eq_false_iff_ne.mpr hdir
        have hbne_d : (vn.direction != 0#32) = true := bne_iff_ne.mpr hdir
        have hstep_d := bv_i32VarintField_nonzero hdir
        apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 132#64); wp_steps
        apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *]); intro hinv
        exact h132 _
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv0.trans hinv)
    intro s_mid hpc_m hrun_m hsp_m htr_m hx8_m hx9_m hx10_m hx20_m hx25_m hx27_m hfp_m hinv_m
    apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 160#64); wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hinv
    exact hnext _ (Or.inl (by simp only [arm64_norm, *]))
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m.trans hinv)

theorem step_encodeToVec_vn_chainParams_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (a : BitVec 64) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_426).base + 160#64 ∨ s.pc = (blkPl_426).base + 288#64) (hrun : s.status = .Running)
    (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInvVm s0 s)
    (hP : P = versionNegotiationRest A g a vn ∗ F)
    (hnext : ∀ s1 : State,
      s1.pc = (blkPl_426).base + 324#64 → s1.status = .Running → s1.sp = s.sp → s1.trace = s.trace →
      s1.readReg64 .x8 = s.readReg64 .x8 → s1.readReg64 .x9 = s.readReg64 .x9 →
      s1.readReg64 .x10 = s.readReg64 .x10 →
      s1.readReg64 .x11 = BitVec.ofNat 64 (optChainParamsPBFieldEncodedLen vn.chainParams) →
      s1.readReg64 .x20 = a → s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .fp = s.readReg64 .fp →
      StepInvVm s0 s1 →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s1 (versionNegotiationRest A g a vn ∗ F) Q Qp oom) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q Qp oom := by
  subst hP
  dsimp only [versionNegotiationRest]
  cases hcp : vn.chainParams with
  | none =>
    dsimp only [optChainParamsPBAt, optChainParamsPBFieldEncodedLen]
    rcases hpc with hpc | hpc <;>
      (apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 324#64); wp_steps;
       apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, wp_norm, *]); intro hinv;
       refine SepWPp.weaken_pre
         (by dsimp only [versionNegotiationRest]; rw [hcp]; dsimp only [optChainParamsPBAt]
             simp only [BitVec.add_assoc, BitVec.reduceAdd]; exact Entails.of_eq (by sep_ac_rfl))
         (hnext _
           (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
           (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
           (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
           (by simp only [arm64_norm, *])
           (by rw [hcp]; simp only [arm64_norm, optChainParamsPBFieldEncodedLen, *])
           (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
           (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv)))
  | some cp =>
    simp only [optChainParamsPBAt, chainParamsPBAt, BitVec.add_assoc, BitVec.reduceAdd]
    suffices h172 : ∀ s_mid : State,
        s_mid.pc = (blkPl_426).base + 172#64 → s_mid.status = .Running → s_mid.sp = s.sp → s_mid.trace = s.trace →
        s_mid.readReg64 .x8 = s.readReg64 .x8 → s_mid.readReg64 .x9 = s.readReg64 .x9 →
        s_mid.readReg64 .x10 = s.readReg64 .x10 → s_mid.readReg64 .x20 = a →
        s_mid.readReg64 .x25 = s.readReg64 .x25 → s_mid.readReg64 .x27 = s.readReg64 .x27 →
        s_mid.readReg64 .fp = s.readReg64 .fp → StepInvVm s0 s_mid →
        SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s_mid
          (((a + 8#64) ↦₆₄ g.authKey.ptr) ∗
           ((a + 16#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
           vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey ∗
           ((a + 24#64) ↦₃₂ 1#32) ∗ ((a + 28#64) ↦₃₂ cp.maxJump) ∗ ((a + 32#64) ↦₃₂ cp.maxOooKeys) ∗
           ((a + 36#64) ↦₃₂ vn.direction) ∗ ((a + 40#64) ↦₃₂ vn.minVersion) ∗
           memRegion (a + 44#64) 4 ∗ F) Q Qp oom by
      rcases hpc with hpc | hpc <;>
        (apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 172#64); wp_steps;
         apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
           (by simp only [arm64_norm, wp_norm, *]); intro hinv;
         refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
           (h172 _
             (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
             (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
             (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
             (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
             (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
             (by simp only [arm64_norm, *]) (hinv0.trans hinv)))
    intro s_mid hpc_m hrun_m hsp_m htr_m hx8_m hx9_m hx10_m hx20_m hx25_m hx27_m hfp_m hinv_m
    by_cases hmj : cp.maxJump = 0#32 <;> by_cases hmo : cp.maxOooKeys = 0#32
    · have hmj_eq : u32VarintFieldEncodedLen cp.maxJump = 0 := by simp [u32VarintFieldEncodedLen, hmj]
      have hmo_eq : u32VarintFieldEncodedLen cp.maxOooKeys = 0 := by simp [u32VarintFieldEncodedLen, hmo]
      have hbeq_mj : (cp.maxJump == 0#32) = true := beq_iff_eq.mpr hmj
      have hbne_mj : (cp.maxJump != 0#32) = false := by simp [hmj]
      have hbeq_mo : (cp.maxOooKeys == 0#32) = true := beq_iff_eq.mpr hmo
      have hbne_mo : (cp.maxOooKeys != 0#32) = false := by simp [hmo]
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 324#64); wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *]); intro hinv
      refine SepWPp.weaken_pre
        (by dsimp only [versionNegotiationRest]; rw [hcp]
            simp only [optChainParamsPBAt, chainParamsPBAt, BitVec.add_assoc, BitVec.reduceAdd]
            exact Entails.of_eq (by sep_ac_rfl))
        (hnext _
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by rw [hcp, ← bv_optChainParams_some_combine]; simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m.trans hinv))
    · have hmj_eq : u32VarintFieldEncodedLen cp.maxJump = 0 := by simp [u32VarintFieldEncodedLen, hmj]
      have hbeq_mj : (cp.maxJump == 0#32) = true := beq_iff_eq.mpr hmj
      have hbne_mj : (cp.maxJump != 0#32) = false := by simp [hmj]
      have hbeq_mo : (cp.maxOooKeys == 0#32) = false := beq_eq_false_iff_ne.mpr hmo
      have hbne_mo : (cp.maxOooKeys != 0#32) = true := bne_iff_ne.mpr hmo
      have hstep_mo := bv_u32VarintField_nonzero hmo
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 324#64); wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *]); intro hinv
      refine SepWPp.weaken_pre
        (by dsimp only [versionNegotiationRest]; rw [hcp]
            simp only [optChainParamsPBAt, chainParamsPBAt, BitVec.add_assoc, BitVec.reduceAdd]
            exact Entails.of_eq (by sep_ac_rfl))
        (hnext _
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by rw [hcp, ← bv_optChainParams_some_combine]; simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m.trans hinv))
    · have hmo_eq : u32VarintFieldEncodedLen cp.maxOooKeys = 0 := by simp [u32VarintFieldEncodedLen, hmo]
      have hbeq_mj : (cp.maxJump == 0#32) = false := beq_eq_false_iff_ne.mpr hmj
      have hbne_mj : (cp.maxJump != 0#32) = true := bne_iff_ne.mpr hmj
      have hstep_mj := bv_chainParams_maxJump_nonzero hmj
      have hbeq_mo : (cp.maxOooKeys == 0#32) = true := beq_iff_eq.mpr hmo
      have hbne_mo : (cp.maxOooKeys != 0#32) = false := by simp [hmo]
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 324#64); wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *]); intro hinv
      refine SepWPp.weaken_pre
        (by dsimp only [versionNegotiationRest]; rw [hcp]
            simp only [optChainParamsPBAt, chainParamsPBAt, BitVec.add_assoc, BitVec.reduceAdd]
            exact Entails.of_eq (by sep_ac_rfl))
        (hnext _
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by rw [hcp, ← bv_optChainParams_some_combine]; simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m.trans hinv))
    · have hbeq_mj : (cp.maxJump == 0#32) = false := beq_eq_false_iff_ne.mpr hmj
      have hbne_mj : (cp.maxJump != 0#32) = true := bne_iff_ne.mpr hmj
      have hstep_mj := bv_chainParams_maxJump_nonzero hmj
      have hbeq_mo : (cp.maxOooKeys == 0#32) = false := beq_eq_false_iff_ne.mpr hmo
      have hbne_mo : (cp.maxOooKeys != 0#32) = true := bne_iff_ne.mpr hmo
      have hstep_mo := bv_u32VarintField_nonzero hmo
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 324#64); wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *]); intro hinv
      refine SepWPp.weaken_pre
        (by dsimp only [versionNegotiationRest]; rw [hcp]
            simp only [optChainParamsPBAt, chainParamsPBAt, BitVec.add_assoc, BitVec.reduceAdd]
            exact Entails.of_eq (by sep_ac_rfl))
        (hnext _
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by rw [hcp, ← bv_optChainParams_some_combine]; simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m.trans hinv))

theorem step_encodeToVec_prologue_and_vn_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State))
    (sret a sp : BitVec 64) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {s0 : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s0.pc = (blkPl_426).base) (hrun : s0.status = .Running) (hsp : s0.sp = sp)
    (hx0 : s0.readReg64 .x0 = sret) (hx1 : s0.readReg64 .x1 = a)
    (hP : P = (pqRatchetStatePBPinnedAt A g a st ∗ stackAt sp (encodeToVecStackOf resStack)) ∗ F)
    (hnext : ∀ (s1 : State) (v0 v1 v2 v3 v4 v5 : BitVec 64),
      s1.pc = (if st.chain.isSome then (blkPl_426).base + 380#64 else (blkPl_426).base + 428#64) →
      s1.status = .Running → s1.sp = sp - 144#64 → s1.trace = s0.trace →
      (st.chain = none → s1.readReg64 .x8 = 0#64) →
      s1.readReg64 .x19 = optChainCap g.chain st.chain → s1.readReg64 .x20 = a →
      s1.readReg64 .x21 =
        BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen st.versionNegotiation) →
      s1.readReg64 .x22 = a + 48#64 →
      s1.readReg64 .x25 = optVersionNegCap g.vn st.versionNegotiation →
      s1.readReg64 .x27 = sret → s1.readReg64 .fp = sp - 96#64 → StepInvVm s0 s1 →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s1
        ((pqRatchetStatePBPinnedAt A g a st ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
          encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5 ∗
          encodeToVecSavedRegs sp s0) ∗ F) Q Qp oom) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s0 P Q Qp oom := by
  subst hP
  have hsp_sub_align : (sp - 144#64) &&& 15#64 = 0#64 := sp_sub_144_aligned halign
  have hx0' : s0.readReg64 (Reg.gpr 0#5) = sret := hx0
  have hx1' : s0.readReg64 (Reg.gpr 1#5) = a := hx1
  rw [stackAt_encodeToVec_split hres sp, pqRatchetStatePBPinnedAt,
    optVersionNegotiationPBPinnedAt_eq, optChainPBPinnedAt_eq]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun v0 => SepWPp.exists_elim fun v1 => SepWPp.exists_elim fun v2 =>
    SepWPp.exists_elim fun v3 => SepWPp.exists_elim fun v4 => SepWPp.exists_elim fun v5 => ?_
  rw [cells_12_sub_96_eq sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun r0 => SepWPp.exists_elim fun r1 => SepWPp.exists_elim fun r2 =>
    SepWPp.exists_elim fun r3 => SepWPp.exists_elim fun r4 => SepWPp.exists_elim fun r5 =>
    SepWPp.exists_elim fun r6 => SepWPp.exists_elim fun r7 => SepWPp.exists_elim fun r8 =>
    SepWPp.exists_elim fun r9 => SepWPp.exists_elim fun r10 => SepWPp.exists_elim fun r11 => ?_
  refine sepWPp_extract_pure
    (((optVersionNegCap g.vn st.versionNegotiation + 1#64 == 0#64) = !st.versionNegotiation.isSome ∧
       (optVersionNegCap g.vn st.versionNegotiation + 1#64 != 0#64) = st.versionNegotiation.isSome) ∧
     ((optChainCap g.chain st.chain + 1#64 == 0#64) = !st.chain.isSome ∧
       (optChainCap g.chain st.chain + 1#64 != 0#64) = st.chain.isSome))
    (fun R hm => ⟨?_, ?_⟩) (fun ⟨hvn_cap, hch_cap⟩ => ?_)
  · apply optVersionNegRest_cap_bounds (A := A) (p := a)
      (R := (a ↦₆₄ optVersionNegCap g.vn st.versionNegotiation) ∗
        ((a + 0x30#64) ↦₆₄ optChainCap g.chain st.chain) ∗
        optChainRest A g.chain (a + 0x30#64) st.chain ∗
        optPqRatchetInnerPBPinnedAt A g.inner (a + 0x80#64) st.inner ∗
        stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
        encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5 ∗
        ((sp - 96#64) ↦₆₄ r0) ∗ ((sp - 88#64) ↦₆₄ r1) ∗ ((sp - 80#64) ↦₆₄ r2) ∗
        ((sp - 72#64) ↦₆₄ r3) ∗ ((sp - 64#64) ↦₆₄ r4) ∗ ((sp - 56#64) ↦₆₄ r5) ∗
        ((sp - 48#64) ↦₆₄ r6) ∗ ((sp - 40#64) ↦₆₄ r7) ∗ ((sp - 32#64) ↦₆₄ r8) ∗
        ((sp - 24#64) ↦₆₄ r9) ∗ ((sp - 16#64) ↦₆₄ r10) ∗ ((sp - 8#64) ↦₆₄ r11) ∗ F ∗ R)
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  · apply optChainRest_cap_bounds (A := A) (p := a + 0x30#64)
      (R := (a ↦₆₄ optVersionNegCap g.vn st.versionNegotiation) ∗
        optVersionNegRest A g.vn a st.versionNegotiation ∗
        ((a + 0x30#64) ↦₆₄ optChainCap g.chain st.chain) ∗
        optPqRatchetInnerPBPinnedAt A g.inner (a + 0x80#64) st.inner ∗
        stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
        encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5 ∗
        ((sp - 96#64) ↦₆₄ r0) ∗ ((sp - 88#64) ↦₆₄ r1) ∗ ((sp - 80#64) ↦₆₄ r2) ∗
        ((sp - 72#64) ↦₆₄ r3) ∗ ((sp - 64#64) ↦₆₄ r4) ∗ ((sp - 56#64) ↦₆₄ r5) ∗
        ((sp - 48#64) ↦₆₄ r6) ∗ ((sp - 40#64) ↦₆₄ r7) ∗ ((sp - 32#64) ↦₆₄ r8) ∗
        ((sp - 24#64) ↦₆₄ r9) ∗ ((sp - 16#64) ↦₆₄ r10) ∗ ((sp - 8#64) ↦₆₄ r11) ∗ F ∗ R)
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  suffices h44 : ∀ s_pro : State,
      s_pro.pc = (blkPl_426).base + 44#64 → s_pro.status = .Running →
      s_pro.sp = sp - 144#64 → s_pro.trace = s0.trace →
      s_pro.readReg64 .x20 = a →
      s_pro.readReg64 .x25 = optVersionNegCap g.vn st.versionNegotiation →
      s_pro.readReg64 .x27 = sret → s_pro.readReg64 .fp = sp - 96#64 →
      StepInvVm s0 s_pro →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s_pro
        (((a ↦₆₄ optVersionNegCap g.vn st.versionNegotiation) ∗
          optVersionNegRest A g.vn a st.versionNegotiation ∗
          ((a + 0x30#64) ↦₆₄ optChainCap g.chain st.chain) ∗
          optChainRest A g.chain (a + 0x30#64) st.chain ∗
          optPqRatchetInnerPBPinnedAt A g.inner (a + 0x80#64) st.inner ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
          encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5 ∗
          encodeToVecSavedRegs sp s0) ∗ F) Q Qp oom by
    apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 44#64)
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv_pro
      refine SepWPp.weaken_pre
        (by rw [encodeToVecSavedRegs]; exact Entails.of_eq (by sep_ac_rfl))
        (h44 _
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          hinv_pro))
  intro s_pro hpc_pro hrun_pro hsp_pro htr_pro hx20_pro hx25_pro hx27_pro hfp_pro hinv_pro
  cases hvn : st.versionNegotiation with
  | none =>
    rw [hvn] at hvn_cap hx25_pro
    simp only [Option.isSome_none, Bool.not_false] at hvn_cap
    cases hch : st.chain with
    | none =>
      rw [hch] at hch_cap
      simp only [Option.isSome_none, Bool.not_false] at hch_cap
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 428#64); wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *]); intro hinv
      refine SepWPp.weaken_pre ?_
        (hnext _ v0 v1 v2 v3 v4 v5
          (by simp only [arm64_norm, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (fun _ => by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, optVersionNegotiationPBFieldEncodedLen, *])
          (by simp only [arm64_norm, *]) (by rw [hvn]; simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_pro.trans hinv))
      rw [pqRatchetStatePBPinnedAt, optVersionNegotiationPBPinnedAt_eq, optChainPBPinnedAt_eq,
        hvn, hch]
      exact Entails.of_eq (by sep_ac_rfl)
    | some ch =>
      rw [hch] at hch_cap
      simp only [Option.isSome_some, Bool.not_true] at hch_cap
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 380#64); wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *]); intro hinv
      refine SepWPp.weaken_pre ?_
        (hnext _ v0 v1 v2 v3 v4 v5
          (by simp only [arm64_norm, Option.isSome_some, ↓reduceIte, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (fun h => by rw [hch] at h; cases h)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, optVersionNegotiationPBFieldEncodedLen, *])
          (by simp only [arm64_norm, *]) (by rw [hvn]; simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_pro.trans hinv))
      rw [pqRatchetStatePBPinnedAt, optVersionNegotiationPBPinnedAt_eq, optChainPBPinnedAt_eq,
        hvn, hch]
      exact Entails.of_eq (by sep_ac_rfl)
  | some vn =>
    have hauth_lt := vn_authKey_len_lt_of_state hvn hlen
    rw [hvn] at hvn_cap hx25_pro
    simp only [Option.isSome_some, Bool.not_true] at hvn_cap
    dsimp only [optVersionNegRest]
    apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 52#64); wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hinv0
    let F_vn : SepProp :=
      ((a ↦₆₄ optVersionNegCap g.vn (some vn)) ∗
       ((a + 0x30#64) ↦₆₄ optChainCap g.chain st.chain) ∗
       optChainRest A g.chain (a + 0x30#64) st.chain ∗
       optPqRatchetInnerPBPinnedAt A g.inner (a + 0x80#64) st.inner ∗
       stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
       encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5 ∗
       encodeToVecSavedRegs sp s0) ∗ F
    refine SepWPp.weaken_pre (P' := versionNegotiationRest A g.vn a vn ∗ F_vn)
      (Entails.of_eq (by dsimp only [F_vn]; sep_ac_rfl)) ?_
    refine step_encodeToVec_vn_authKey_placed A H a g.vn vn hauth_lt
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hinv_pro.trans hinv0) rfl ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hx8_1 hx20_1 hx25_1 hx27_1 hfp1 hinv1
    refine step_encodeToVec_vn_dir_minVer_placed A H a g.vn vn
      hpc1 hrun1 hx20_1 hinv1 rfl ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hx8_2 hx9_2 hx10_2 hx20_2 hx25_2 hx27_2 hfp2 hinv2
    refine step_encodeToVec_vn_chainParams_placed A H a g.vn vn
      hpc2 hrun2 hx20_2 hinv2 rfl ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx8_3 hx9_3 hx10_3 hx11_3 hx20_3 hx25_3 hx27_3 hfp3 hinv3
    have hvn_sum := bv_vn_sum_eq vn
    have hopt_vn := bv_optVN_some_eq vn
    cases hch : st.chain with
    | none =>
      rw [hch] at hch_cap
      simp only [Option.isSome_none, Bool.not_false] at hch_cap
      dsimp only [F_vn]; rw [hch]
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 428#64); wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *]); intro hinv4
      refine SepWPp.weaken_pre ?_
        (hnext _ v0 v1 v2 v3 v4 v5
          (by simp only [arm64_norm, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (fun _ => by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by rw [hvn]; simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv3.trans hinv4))
      rw [pqRatchetStatePBPinnedAt, optVersionNegotiationPBPinnedAt_eq, optChainPBPinnedAt_eq,
        hvn, hch]
      dsimp only [optVersionNegRest]
      exact Entails.of_eq (by sep_ac_rfl)
    | some ch =>
      rw [hch] at hch_cap
      simp only [Option.isSome_some, Bool.not_true] at hch_cap
      dsimp only [F_vn]; rw [hch]
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 380#64); wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *]); intro hinv4
      refine SepWPp.weaken_pre ?_
        (hnext _ v0 v1 v2 v3 v4 v5
          (by simp only [arm64_norm, Option.isSome_some, ↓reduceIte, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (fun h => by rw [hch] at h; cases h)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by rw [hvn]; simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv3.trans hinv4))
      rw [pqRatchetStatePBPinnedAt, optVersionNegotiationPBPinnedAt_eq, optChainPBPinnedAt_eq,
        hvn, hch]
      dsimp only [optVersionNegRest]
      exact Entails.of_eq (by sep_ac_rfl)

/-! ## Step 1b: `Option<Chain>::encoded_len` (`+380/+428 .. +436`) -/

theorem step_encodeToVec_chain_len_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State))
    {s0 s1 : State}
    (hChainLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 406)
      (withStepInvVm s0 (chainEncodedLenPinnedSpec A)))
    (sret a sp v0 v1 v2 v3 v4 v5 : BitVec 64) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s1.pc = (if st.chain.isSome then (blkPl_426).base + 380#64 else (blkPl_426).base + 428#64))
    (hrun : s1.status = .Running) (hsp : s1.sp = sp - 144#64) (htr : s1.trace = s0.trace)
    (hx8_none : st.chain = none → s1.readReg64 .x8 = 0#64)
    (hx19 : s1.readReg64 .x19 = optChainCap g.chain st.chain) (hx20 : s1.readReg64 .x20 = a)
    (hx21 : s1.readReg64 .x21 =
      BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen st.versionNegotiation))
    (hx22 : s1.readReg64 .x22 = a + 48#64)
    (hx25 : s1.readReg64 .x25 = optVersionNegCap g.vn st.versionNegotiation)
    (hx27 : s1.readReg64 .x27 = sret) (hfp : s1.readReg64 .fp = sp - 96#64)
    (hinv1 : StepInvVm s0 s1)
    (hP : P = (pqRatchetStatePBPinnedAt A g a st ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
      encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5 ∗
      encodeToVecSavedRegs sp s0) ∗ F)
    (hnext : ∀ s2 : State,
      s2.pc = (blkPl_426).base + 436#64 → s2.status = .Running → s2.sp = sp - 144#64 →
      s2.trace = s0.trace → s2.readReg64 .x19 = optChainCap g.chain st.chain →
      s2.readReg64 .x20 = a → s2.readReg64 .x22 = a + 48#64 →
      s2.readReg64 .x23 =
        BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen st.versionNegotiation +
          optChainPBFieldEncodedLen st.chain) →
      s2.readReg64 .x25 = optVersionNegCap g.vn st.versionNegotiation →
      s2.readReg64 .x27 = sret → s2.readReg64 .fp = sp - 96#64 → StepInvVm s0 s2 →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s2
        ((pqRatchetStatePBPinnedAt A g a st ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
          encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5 ∗
          encodeToVecSavedRegs sp s0) ∗ F)
        Q Qp oom) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s1 P Q Qp oom := by
  subst hP
  cases hch : st.chain with
  | none =>
    rw [hch] at hpc
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc
    have hx8 := hx8_none hch
    have ⟨hadd1, hadd2⟩ := adds_no_overflow_of_eq (a := 0)
      (b := optVersionNegotiationPBFieldEncodedLen st.versionNegotiation)
      (c := optVersionNegotiationPBFieldEncodedLen st.versionNegotiation +
        optChainPBFieldEncodedLen none)
      (by dsimp [optChainPBFieldEncodedLen])
      (by unfold pqRatchetStatePBEncodedLen at hlen; dsimp [optChainPBFieldEncodedLen]; omega)
    apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 436#64); wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hinv
    exact hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by rw [hch]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (hinv1.trans hinv)
  | some ch =>
    rw [hch] at hpc
    simp only [Option.isSome_some, ↓reduceIte] at hpc
    have ⟨hfit, hopt_lt, hvar_lt⟩ := chainPBEncodedLen_lt_of_state hch hlen
    have hls := cmp_ls_false_of_lt hvar_lt hopt_lt
    have hopt_ch := bv_optChain_some_eq ch
    have ⟨hadd1, hadd2⟩ := adds_no_overflow_of_eq
      (a := optChainPBFieldEncodedLen (some ch))
      (b := optVersionNegotiationPBFieldEncodedLen st.versionNegotiation)
      (c := optVersionNegotiationPBFieldEncodedLen st.versionNegotiation +
        optChainPBFieldEncodedLen (some ch))
      rfl
      (by unfold pqRatchetStatePBEncodedLen at hlen; rw [hch] at hlen; omega)
    apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 406)
    wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hinv_bl
    refine sepWPp_call_cs_noPanic (x := ChainEncodedLenPinnedGhost.mk (a + 0x30#64) g.chain ch)
      (F := optVersionNegotiationPBPinnedAt A g.vn a st.versionNegotiation ∗
        optPqRatchetInnerPBPinnedAt A g.inner (a + 0x80#64) st.inner ∗
        memRegion (sp - 144#64 - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) (80 + resStack) ∗
        encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5 ∗
        encodeToVecSavedRegs sp s0 ∗ F)
      hChainLen (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
      (by simp only [State.spAligned, arm64_norm, hsp, beq_iff_eq]; exact halign)
      (ret_pc := (blkPl_426).base + 388#64) (by simp only [arm64_norm]) ?_ ?_ ?_ ?_ ?_
    · intro R' hm
      rw [pqRatchetStatePBPinnedAt, hch, optChainPBPinnedAt,
        stackAt_callee_eq_chainEncodedLen (by omega) (sp - 144#64)] at hm
      simp only [arm64_norm] at hm
      simp only [withStepInvVm, chainEncodedLenPinnedSpec, withVmPreserved,
        CryptoVerification.SpqrV1.ProtoRepr.chainEncodedLenPinnedSpec, arm64_norm, hsp,
        sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hinv1.trans hinv_bl, hfit⟩, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
    · intro sf code R' _ hm; exact allowPanic_not_exited hm
    · intro sf R' _ hm; exact allowPanic_not_exited hm
    · intro sf R' _ hm; exact allowPanic_not_exited hm
    · intro sm hpcm hrunm hspm hcsm hinv_call
      simp only [arm64_norm, hsp] at hspm
      dsimp only [withStepInvVm, chainEncodedLenPinnedSpec, withVmPreserved,
        CryptoVerification.SpqrV1.ProtoRepr.chainEncodedLenPinnedSpec]
      rw [sepConj_assoc]
      refine SepWPp.pure_elim fun hvm_call => ?_
      rw [sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
      simp only [arm64_norm, htr] at htrm
      have hinv_sm : StepInvVm s0 sm :=
        (hinv1.trans hinv_bl).trans ⟨hinv_call, hvm_call⟩
      have hx19m : sm.readReg64 .x19 = optChainCap g.chain st.chain :=
        hcsm.1.trans (by simpa only [arm64_norm] using hx19)
      have hx20m : sm.readReg64 .x20 = a := hcsm.2.1.trans (by simpa only [arm64_norm] using hx20)
      have hx21m : sm.readReg64 .x21 =
          BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen st.versionNegotiation) :=
        hcsm.2.2.1.trans (by simpa only [arm64_norm] using hx21)
      have hx22m : sm.readReg64 .x22 = a + 48#64 := hcsm.2.2.2.1.trans (by simpa only [arm64_norm] using hx22)
      have hx25m : sm.readReg64 .x25 = optVersionNegCap g.vn st.versionNegotiation :=
        hcsm.2.2.2.2.2.2.1.trans (by simpa only [arm64_norm] using hx25)
      have hx27m : sm.readReg64 .x27 = sret :=
        hcsm.2.2.2.2.2.2.2.2.1.trans (by simpa only [arm64_norm] using hx27)
      have hfpm : sm.readReg64 .fp = sp - 96#64 :=
        hcsm.2.2.2.2.2.2.2.2.2.2.1.trans (by simpa only [arm64_norm] using hfp)
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 436#64); wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *]); intro hinv_post
      refine SepWPp.weaken_pre ?_
        (hnext _
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by rw [hch]; simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (hinv_sm.trans hinv_post))
      rw [pqRatchetStatePBPinnedAt, hch, optChainPBPinnedAt,
        stackAt_callee_eq_chainEncodedLen (by omega) (sp - 144#64)]
      simp only [arm64_norm, hsp]
      exact Entails.of_eq (by sep_ac_rfl)

/-! ## Step 1c: `Option<pq_ratchet_state::Inner>::encoded_len` (`+436 .. +516`) -/

theorem step_encodeToVec_inner_len_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State)) (roV1 : BitVec 64)
    {s0 s2 : State}
    (hV1StateLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 405)
      (withStepInvVm s0 (v1StateEncodedLenRoPinnedSpec A roV1)))
    (sret a sp v0 v1 v2 v3 v4 v5 : BitVec 64) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s2.pc = (blkPl_426).base + 436#64) (hrun : s2.status = .Running)
    (hsp : s2.sp = sp - 144#64) (htr : s2.trace = s0.trace)
    (hx19 : s2.readReg64 .x19 = optChainCap g.chain st.chain) (hx20 : s2.readReg64 .x20 = a)
    (hx22 : s2.readReg64 .x22 = a + 48#64)
    (hx23 : s2.readReg64 .x23 =
      BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen st.versionNegotiation +
        optChainPBFieldEncodedLen st.chain))
    (hx25 : s2.readReg64 .x25 = optVersionNegCap g.vn st.versionNegotiation)
    (hx27 : s2.readReg64 .x27 = sret) (hfp : s2.readReg64 .fp = sp - 96#64)
    (hinv2 : StepInvVm s0 s2)
    (hP : P = (pqRatchetStatePBPinnedAt A g a st ∗
      (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
      encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5 ∗
      encodeToVecSavedRegs sp s0) ∗ F)
    (hnext : ∀ s3 : State,
      s3.pc = (blkPl_426).base + 516#64 → s3.status = .Running → s3.sp = sp - 144#64 →
      s3.trace = s0.trace → s3.readReg64 .x19 = optChainCap g.chain st.chain →
      s3.readReg64 .x20 = a → s3.readReg64 .x21 = a + 128#64 →
      s3.readReg64 .x22 = a + 48#64 →
      s3.readReg64 .x23 = BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st) →
      s3.readReg64 .x25 = optVersionNegCap g.vn st.versionNegotiation →
      s3.readReg64 .x27 = sret → s3.readReg64 .x28 = optPqRatchetInnerCap g.inner st.inner →
      s3.readReg64 .fp = sp - 96#64 → StepInvVm s0 s3 →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s3
        ((pqRatchetStatePBPinnedAt A g a st ∗
          (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
          encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5 ∗
          encodeToVecSavedRegs sp s0) ∗ F)
        Q Qp oom) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s2 P Q Qp oom := by
  subst hP
  refine sepWPp_extract_pure
    ((optPqRatchetInnerCap g.inner st.inner + 3#64 == 0#64) = !st.inner.isSome ∧
     (optPqRatchetInnerCap g.inner st.inner + 3#64 != 0#64) = st.inner.isSome)
    (fun R' hm => ?_) (fun hin_cap => ?_)
  · apply optPqRatchetInnerPBPinnedAt_cap_bounds (A := A) (p := a + 0x80#64)
      (R := optVersionNegotiationPBPinnedAt A g.vn a st.versionNegotiation ∗
        optChainPBPinnedAt A g.chain (a + 0x30#64) st.chain ∗
        (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
        stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
        encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5 ∗
        encodeToVecSavedRegs sp s0 ∗ F ∗ R')
    rw [pqRatchetStatePBPinnedAt] at hm
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  · rw [pqRatchetStatePBPinnedAt, optPqRatchetInnerPBPinnedAt_eq]
    cases hin : st.inner with
    | none =>
      rw [hin] at hin_cap
      simp only [Option.isSome_none, Bool.not_false] at hin_cap
      have ⟨hadd1, hadd2⟩ := adds_no_overflow_of_eq (a := 0)
        (b := optVersionNegotiationPBFieldEncodedLen st.versionNegotiation +
          optChainPBFieldEncodedLen st.chain)
        (c := pqRatchetStatePBEncodedLen st)
        (by unfold pqRatchetStatePBEncodedLen; rw [hin]; dsimp [optPqRatchetInnerPBFieldEncodedLen])
        (by omega)
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 516#64); wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *]); intro hinv
      refine SepWPp.weaken_pre ?_
        (hnext _
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, hin, *]) (by simp only [arm64_norm, *])
          (hinv2.trans hinv))
      rw [pqRatchetStatePBPinnedAt, optPqRatchetInnerPBPinnedAt_eq, hin]
      exact Entails.of_eq (by sep_ac_rfl)
    | some innerVal =>
      cases innerVal with
      | v1 v1s =>
        rw [hin] at hin_cap
        simp only [Option.isSome_some, Bool.not_true] at hin_cap
        have ⟨hfit, hopt_lt, hvar_lt⟩ := v1StatePBEncodedLen_lt_of_state hin hlen
        have hls := cmp_ls_false_of_lt hvar_lt hopt_lt
        have hopt_in := bv_optInner_some_eq v1s
        have ⟨hadd1, hadd2⟩ := adds_no_overflow_of_eq
          (a := optPqRatchetInnerPBFieldEncodedLen (some (.v1 v1s)))
          (b := optVersionNegotiationPBFieldEncodedLen st.versionNegotiation +
            optChainPBFieldEncodedLen st.chain)
          (c := pqRatchetStatePBEncodedLen st)
          (by unfold pqRatchetStatePBEncodedLen; rw [hin])
          (by omega)
        apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 405)
        wp_steps
        apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *]); intro hinv_bl
        refine sepWPp_call_cs_noPanic (x := PinnedEncLenGhost.mk (a + 0x80#64) g.inner v1s)
          (F := optVersionNegotiationPBPinnedAt A g.vn a st.versionNegotiation ∗
            optChainPBPinnedAt A g.chain (a + 0x30#64) st.chain ∗
            memRegion (sp - 144#64 - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) (96 + resStack) ∗
            encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5 ∗
            encodeToVecSavedRegs sp s0 ∗ F)
          hV1StateLen (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
          (by simp only [State.spAligned, arm64_norm, hsp, beq_iff_eq]; exact halign)
          (ret_pc := (blkPl_426).base + 468#64) (by simp only [arm64_norm]) ?_ ?_ ?_ ?_ ?_
        · intro R' hm
          rw [← optPqRatchetInnerPBPinnedAt_eq A g.inner (a + 0x80#64) (some (.v1 v1s)),
            optPqRatchetInnerPBPinnedAt,
            stackAt_callee_eq_v1StateEncodedLen (by omega) (sp - 144#64)] at hm
          simp only [arm64_norm] at hm
          simp only [withStepInvVm, v1StateEncodedLenRoPinnedSpec, withVmPreserved,
            CryptoVerification.SpqrV1.ProtoRepr.v1StateEncodedLenRoPinnedSpec, arm64_norm, hsp,
            sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨hinv2.trans hinv_bl, hfit⟩, ?_⟩
          exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
        · intro sf code R' _ hm; exact allowPanic_not_exited hm
        · intro sf R' _ hm; exact allowPanic_not_exited hm
        · intro sf R' _ hm; exact allowPanic_not_exited hm
        · intro sm hpcm hrunm hspm hcsm hinv_call
          simp only [arm64_norm, hsp] at hspm
          dsimp only [withStepInvVm, v1StateEncodedLenRoPinnedSpec, withVmPreserved,
            CryptoVerification.SpqrV1.ProtoRepr.v1StateEncodedLenRoPinnedSpec]
          rw [sepConj_assoc]
          refine SepWPp.pure_elim fun hvm_call => ?_
          rw [sepConj_assoc]
          refine SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
          simp only [arm64_norm, htr] at htrm
          have hinv_sm : StepInvVm s0 sm :=
            (hinv2.trans hinv_bl).trans ⟨hinv_call, hvm_call⟩
          have hx19m : sm.readReg64 .x19 = optChainCap g.chain st.chain :=
            hcsm.1.trans (by simpa only [arm64_norm] using hx19)
          have hx20m : sm.readReg64 .x20 = a := hcsm.2.1.trans (by simpa only [arm64_norm] using hx20)
          have hx21m : sm.readReg64 .x21 = a + 128#64 :=
            hcsm.2.2.1.trans (by simp only [arm64_norm])
          have hx22m : sm.readReg64 .x22 = a + 48#64 := hcsm.2.2.2.1.trans (by simpa only [arm64_norm] using hx22)
          have hx23m : sm.readReg64 .x23 =
              BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen st.versionNegotiation +
                optChainPBFieldEncodedLen st.chain) :=
            hcsm.2.2.2.2.1.trans (by simpa only [arm64_norm] using hx23)
          have hx25m : sm.readReg64 .x25 = optVersionNegCap g.vn st.versionNegotiation :=
            hcsm.2.2.2.2.2.2.1.trans (by simpa only [arm64_norm] using hx25)
          have hx27m : sm.readReg64 .x27 = sret :=
            hcsm.2.2.2.2.2.2.2.2.1.trans (by simpa only [arm64_norm] using hx27)
          have hx28m : sm.readReg64 .x28 = optPqRatchetInnerCap g.inner st.inner := by
            rw [hin]; exact hcsm.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm])
          have hfpm : sm.readReg64 .fp = sp - 96#64 :=
            hcsm.2.2.2.2.2.2.2.2.2.2.1.trans (by simpa only [arm64_norm] using hfp)
          apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 516#64); wp_steps
          apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, wp_norm, *]); intro hinv_post
          refine SepWPp.weaken_pre ?_
            (hnext _
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (hinv_sm.trans hinv_post))
          rw [pqRatchetStatePBPinnedAt, hin, optPqRatchetInnerPBPinnedAt,
            stackAt_callee_eq_v1StateEncodedLen (by omega) (sp - 144#64)]
          simp only [arm64_norm, hsp]
          exact Entails.of_eq (by sep_ac_rfl)

/-! ## Master Phase 1 Theorem (`+0 .. +516`) -/

theorem step_encodeToVec_phase1_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State)) (roV1 : BitVec 64)
    {s0 : State}
    (hChainLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 406)
      (withStepInvVm s0 (chainEncodedLenPinnedSpec A)))
    (hV1StateLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 405)
      (withStepInvVm s0 (v1StateEncodedLenRoPinnedSpec A roV1)))
    (sret a sp : BitVec 64) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s0.pc = (blkPl_426).base) (hrun : s0.status = .Running) (hsp : s0.sp = sp)
    (hx0 : s0.readReg64 .x0 = sret) (hx1 : s0.readReg64 .x1 = a)
    (hP : P = (pqRatchetStatePBPinnedAt A g a st ∗
      (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
      stackAt sp (encodeToVecStackOf resStack)) ∗ F)
    (hnext : ∀ (s3 : State) (v0 v1 v2 v3 v4 v5 : BitVec 64),
      s3.pc = (blkPl_426).base + 516#64 → s3.status = .Running → s3.sp = sp - 144#64 →
      s3.trace = s0.trace → s3.readReg64 .x19 = optChainCap g.chain st.chain →
      s3.readReg64 .x20 = a → s3.readReg64 .x21 = a + 128#64 →
      s3.readReg64 .x22 = a + 48#64 →
      s3.readReg64 .x23 = BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st) →
      s3.readReg64 .x25 = optVersionNegCap g.vn st.versionNegotiation →
      s3.readReg64 .x27 = sret → s3.readReg64 .x28 = optPqRatchetInnerCap g.inner st.inner →
      s3.readReg64 .fp = sp - 96#64 → StepInvVm s0 s3 →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s3
        ((pqRatchetStatePBPinnedAt A g a st ∗
          (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
          encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5 ∗
          encodeToVecSavedRegs sp s0) ∗ F)
        Q Qp oom) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s0 P Q Qp oom := by
  subst hP
  refine step_encodeToVec_prologue_and_vn_placed hres A H sret a sp g st hlen halign
    hpc hrun hsp hx0 hx1 (F := (roV1 ↦ᵣ v1StateJumpTableBytes) ∗ F) (by sep_ac_rfl) ?_
  intro s1 v0 v1 v2 v3 v4 v5 hpc1 hrun1 hsp1 htr1 hx8_1 hx19_1 hx20_1 hx21_1 hx22_1 hx25_1 hx27_1 hfp1 hinv1
  refine step_encodeToVec_chain_len_placed hres A H hChainLen sret a sp v0 v1 v2 v3 v4 v5 g st hlen halign
    hpc1 hrun1 hsp1 htr1 hx8_1 hx19_1 hx20_1 hx21_1 hx22_1 hx25_1 hx27_1 hfp1 hinv1
    (F := (roV1 ↦ᵣ v1StateJumpTableBytes) ∗ F) rfl ?_
  intro s2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx22_2 hx23_2 hx25_2 hx27_2 hfp2 hinv2
  refine step_encodeToVec_inner_len_placed hres A H roV1 hV1StateLen sret a sp v0 v1 v2 v3 v4 v5 g st hlen halign
    hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx22_2 hx23_2 hx25_2 hx27_2 hfp2 hinv2
    (F := F) (by sep_ac_rfl) ?_
  intro s3 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx25_3 hx27_3 hx28_3 hfp3 hinv3
  exact hnext s3 v0 v1 v2 v3 v4 v5 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx25_3 hx27_3 hx28_3 hfp3 hinv3

end LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenPhasePlacedBudget

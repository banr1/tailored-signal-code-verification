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
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodeToVecCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.VersionNegPhase
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhase
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `[LibsignalPlacement]` Phase 2b Sub-Steps (`Block 426`, `+580 .. +1212`): `VersionNegotiationPB`

Proves polymorphic `SepWPp` split/merge helpers, the 6 pure `VersionNegotiationPB` sub-steps
(`+580 .. +972`) exposing `VmPreserved`, and the 4 budget-threaded field-encoding sub-steps
(`+972/+1088 .. +1212`) threading `A.pool lim σ0`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.VersionNegPhasePlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (RustAlloc vecU8At)
open CryptoVerification.LibsignalSpqrV1 (ChainParamsPB VersionNegotiationPB)
open CryptoVerification.LibsignalSpqrV1.Proto
  (encodeBytesField encodeInt32Field encodeMessage encodeOptMessage encodeVarint)
open CryptoVerification.SpqrV1.ProtoRepr
  (VersionNegotiationPBGhost bytesFieldEncodedLen chainParamsPBAt
   i32VarintFieldEncodedLen optChainParamsPBAt u32VarintFieldEncodedLen
   versionNegotiationPBEncodedLen)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (bv_bytesField_nonempty bv_u32VarintField_nonzero
   hwVarintLen_bvShift_eq_ofNat_varintLen_norm hwVarintLen_eq_ofNat_varintLen_norm
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero
   ofNat_countLeadingZeros_32 ofNat_countLeadingZeros_64
   ofNat_length_beq_zero_of_lt
   ule_self_64 ule_zero_64 ult_self_64 ult_zero_64
   vecU8Buf vecU8Buf_bounds zeroExtend64_beq_zero32 zext64_truncate32)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (StepInv blkPC_426 blkPl_426
   bv_chainParams_maxJump_nonzero bv_i32VarintField_nonzero
   bv_optChainParams_some_combine bv_versionNegLen_none_combine bv_versionNegLen_some_combine
   cap_beq_len_false_of_lt elem_len_ult_spare_false_of_le
   encodeBytesField_1_eq encodeInt32Field_2_eq encodeInt32Field_3_eq
   encodeToVecCalleeStackOf encodeVarint_length_pos
   noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
   optChainParamsTag
   pointsTo32_pair_entails_exists_pointsTo64 pointsTo64_entails_pointsTo32_pair
   sext64_truncate32 sp_sub_144_aligned
   vecU8At_expose_header vecU8At_expose_one vecU8At_expose_slice
   vecU8At_pack_one vecU8At_pack_slice vecU8Buf_eq_of_nonempty
   versionNegotiationRest withStepInv)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
  (sepWP_done_tpidr sepWP_done_vm sepWPp_of_sepWP_cs_vm)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
  (encodeChainParamsExactSpecOf encodeVarintExactSpecOf etvMemcpyRegionSpec
   step_etv_encode_chainParams_call_prog step_etv_encode_varint_call_prog
   step_etv_memcpy_call_prog)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm zext64_truncate32
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  ule_zero_64 ult_zero_64 ule_self_64 ult_self_64

/-! ## 1. Polymorphic `SepWPp` Extraction & Split/Merge Helpers -/

theorem sepWPp_extract_pure {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp} (φ : Prop)
    (hφ : ∀ R : SepProp, s.mem ⊨ P ∗ R → φ)
    (hnext : φ → SepWPp prog ret s P Q Qp oom) :
    SepWPp prog ret s P Q Qp oom :=
  fun R hm hL => hnext (hφ R hm) R hm hL

theorem sepWPp_extract_vecU8At_bounds {prog : Program} {ret : BitVec 64} {s : State}
    {A : RustAlloc} {v cap ptr : BitVec 64} {bs : List (BitVec 8)}
    {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hP : P = vecU8At A v cap ptr bs ∗ F)
    (hnext : bs.length ≤ cap.toNat → cap.toNat < 2 ^ 63 → ptr ≠ 0 →
      SepWPp prog ret s P Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  have hhm : s.mem ⊨
      (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ : SepProp) ∗
        ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (if cap = 0 then emp
           else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
             memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗ F ∗ R) := by
    rw [hP, vecU8At_expose_header] at hm
    convert hm using 1; sep_ac_rfl
  rw [satisfies_pure_sepConj] at hhm
  exact hnext hhm.1.1 hhm.1.2.1 hhm.1.2.2 R hm hL

theorem sepWPp_split_pointsTo64 {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (a v : BitVec 64) (F : SepProp)
    (hP : P = (a ↦₆₄ v) ∗ F)
    (h : ∀ v_lo v_hi : BitVec 32,
      SepWPp prog ret s ((a ↦₃₂ v_lo) ∗ ((a + 4#64) ↦₃₂ v_hi) ∗ F) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  subst hP
  refine SepWPp.weaken_pre (sepConj_mono_left (pointsTo64_entails_pointsTo32_pair a v)) ?_
  simp only [sepExists_sepConj_left]
  exact SepWPp.exists_elim fun v_hi => SepWPp.exists_elim fun v_lo =>
    SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (h v_lo v_hi)

theorem sepWPp_merge_pointsTo32 {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (a : BitVec 64) (v_lo v_hi : BitVec 32) (F : SepProp)
    (hP : P = (a ↦₃₂ v_lo) ∗ ((a + 4#64) ↦₃₂ v_hi) ∗ F)
    (h : ∀ v : BitVec 64, SepWPp prog ret s ((a ↦₆₄ v) ∗ F) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  subst hP
  have hent : (a ↦₃₂ v_lo) ∗ ((a + 4#64) ↦₃₂ v_hi) ∗ F ⊢ (∃∗ v : BitVec 64, a ↦₆₄ v) ∗ F := by
    rw [← sepConj_assoc]
    exact sepConj_mono_left (pointsTo32_pair_entails_exists_pointsTo64 a v_lo v_hi)
  refine SepWPp.weaken_pre hent ?_
  simp only [sepExists_sepConj_left]
  exact SepWPp.exists_elim h

/-! ## 2. Pure Sub-Steps (`+580 .. +972`) with `VmPreserved` -/

theorem step_encodeToVec_vn_push_tag_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (a sp cap ptr : BitVec 64) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB)
    (hpos : 0 < cap.toNat) (halign : sp &&& 15#64 = 0#64)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_426).base + 580#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (hx0 : s.readReg64 .x0 = ptr)
    (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInv s0 s)
    (hP : P = (versionNegotiationRest A g a vn ∗ vecU8At A (sp - 120#64) cap ptr []) ∗ F)
    (hnext : ∀ s1 : State,
      s1.pc = (blkPl_426).base + 604#64 → s1.status = .Running → s1.sp = sp - 144#64 → s1.trace = s.trace →
      s1.readReg64 .x19 = s.readReg64 .x19 → s1.readReg64 .x20 = a →
      s1.readReg64 .x21 = s.readReg64 .x21 → s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x25 = BitVec.ofNat 64 vn.authKey.length →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .fp = s.readReg64 .fp → StepInv s0 s1 → VmPreserved s s1 →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s1
        ((versionNegotiationRest A g a vn ∗ vecU8At A (sp - 120#64) cap ptr [0x0a#8]) ∗ F) Q Qp oom) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q Qp oom := by
  subst hP
  have hsp_align : (sp - 144#64) &&& 15#64 = 0#64 := sp_sub_144_aligned halign
  refine sepWPp_extract_vecU8At_bounds (v := sp - 120#64) (cap := cap) (ptr := ptr) (bs := [])
    (F := versionNegotiationRest A g a vn ∗ F) (by sep_ac_rfl) fun _ hcap hptr => ?_
  rw [vecU8At_expose_one A (sp - 120#64) cap ptr [] (by simpa using hpos) hcap hptr]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun b0 => ?_
  dsimp only [versionNegotiationRest, List.length_nil, BitVec.ofNat_eq_ofNat]
  have h112 : (sp - 120#64) + 8#64 = sp - 112#64 := by bv_omega
  have h104 : (sp - 120#64) + 16#64 = sp - 104#64 := by bv_omega
  have hptr0 : ptr + 0#64 = ptr := by bv_omega
  rw [h112, h104, hptr0]
  apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 604#64)
  by_vm_steps
    wp_steps
    apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv
    refine SepWPp.weaken_pre ?_
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hinv0.trans hinv.1) hinv.2)
    have hpack := vecU8At_pack_one A (sp - 120#64) cap ptr [] 0x0a#8 (by simpa using hpos) hcap hptr
    dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat, List.nil_append] at hpack
    have h01 : (0#64 : BitVec 64) + 1#64 = 1#64 := rfl
    rw [h112, h104, hptr0, h01] at hpack; rw [← hpack]
    dsimp only [versionNegotiationRest]; exact Entails.of_eq (by sep_ac_rfl)

theorem step_encodeToVec_vn_authKey_len_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (a : BitVec 64) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB)
    (hlen : vn.authKey.length < 2 ^ 64)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_426).base + 604#64) (hrun : s.status = .Running)
    (hx20 : s.readReg64 .x20 = a) (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 vn.authKey.length)
    (hinv0 : StepInv s0 s) (hP : P = versionNegotiationRest A g a vn ∗ F)
    (hnext : ∀ s1 : State,
      (s1.pc = (blkPl_426).base + 640#64 ∨ s1.pc = (blkPl_426).base + 872#64) →
      s1.status = .Running → s1.sp = s.sp → s1.trace = s.trace →
      s1.readReg64 .x8 = BitVec.ofNat 64 (bytesFieldEncodedLen vn.authKey) →
      s1.readReg64 .x19 = s.readReg64 .x19 → s1.readReg64 .x20 = a →
      s1.readReg64 .x21 = s.readReg64 .x21 → s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x24 = vn.direction.signExtend 64 →
      s1.readReg64 .x25 = BitVec.ofNat 64 vn.authKey.length →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .fp = s.readReg64 .fp → StepInv s0 s1 → VmPreserved s s1 →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s1 (versionNegotiationRest A g a vn ∗ F) Q Qp oom) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q Qp oom := by
  subst hP; dsimp only [versionNegotiationRest]
  obtain ⟨hbeqz, hbnez⟩ := ofNat_length_beq_zero_of_lt hlen
  cases hemp : vn.authKey.isEmpty
  · have hstep := bv_bytesField_nonempty hemp
    simp only [hemp, Bool.not_false] at hbeqz hbnez
    apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 640#64); wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv
    exact hnext _ (Or.inl (by simp only [arm64_norm, *]))
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (hinv0.trans hinv.1) hinv.2
  · simp only [hemp, Bool.not_true] at hbeqz hbnez
    have hzero : bytesFieldEncodedLen vn.authKey = 0 := by unfold bytesFieldEncodedLen; simp [hemp]
    apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 872#64); wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv
    exact hnext _ (Or.inr (by simp only [arm64_norm, *]))
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, hzero, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (hinv0.trans hinv.1) hinv.2

theorem step_encodeToVec_vn_dir_len_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (a : BitVec 64) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_426).base + 640#64 ∨ s.pc = (blkPl_426).base + 872#64) (hrun : s.status = .Running)
    (hx20 : s.readReg64 .x20 = a) (hx24 : s.readReg64 .x24 = vn.direction.signExtend 64)
    (hinv0 : StepInv s0 s) (hP : P = versionNegotiationRest A g a vn ∗ F)
    (hnext : ∀ s1 : State,
      (s1.pc = (blkPl_426).base + 676#64 ∨ s1.pc = (blkPl_426).base + 884#64) →
      s1.status = .Running → s1.sp = s.sp → s1.trace = s.trace →
      s1.readReg64 .x8 = s.readReg64 .x8 →
      s1.readReg64 .x9 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.direction) →
      s1.readReg64 .x19 = s.readReg64 .x19 → s1.readReg64 .x20 = a →
      s1.readReg64 .x21 = s.readReg64 .x21 → s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = vn.minVersion.signExtend 64 →
      s1.readReg64 .x24 = vn.direction.signExtend 64 → s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .fp = s.readReg64 .fp → StepInv s0 s1 → VmPreserved s s1 →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s1 (versionNegotiationRest A g a vn ∗ F) Q Qp oom) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q Qp oom := by
  subst hP; dsimp only [versionNegotiationRest]
  have hw24 : s.readReg32 .x24 = vn.direction := by simp only [State.readReg32, hx24, sext64_truncate32]
  by_cases hdir : vn.direction = 0#32
  · have hdir_eq : i32VarintFieldEncodedLen vn.direction = 0 := by simp [i32VarintFieldEncodedLen, hdir]
    have hbeq_d : (vn.direction == 0#32) = true := beq_iff_eq.mpr hdir
    have hbne_d : (vn.direction != 0#32) = false := by simp [hdir]
    rcases hpc with hpc | hpc <;>
      (apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 884#64); wp_steps;
       apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, wp_norm, *]); intro hinv;
       exact hnext _ (Or.inr (by simp only [arm64_norm, *]))
         (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hdir_eq, *])
         (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, *]) (hinv0.trans hinv.1) hinv.2)
  · have hbeq_d : (vn.direction == 0#32) = false := beq_eq_false_iff_ne.mpr hdir
    have hbne_d : (vn.direction != 0#32) = true := bne_iff_ne.mpr hdir
    have hstep_d := bv_i32VarintField_nonzero hdir
    rcases hpc with hpc | hpc <;>
      (apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 676#64); wp_steps;
       apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, wp_norm, *]); intro hinv;
       exact hnext _ (Or.inl (by simp only [arm64_norm, *]))
         (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, *]) (hinv0.trans hinv.1) hinv.2)

theorem step_encodeToVec_vn_minVer_len_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (a : BitVec 64) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_426).base + 676#64 ∨ s.pc = (blkPl_426).base + 884#64) (hrun : s.status = .Running)
    (hx20 : s.readReg64 .x20 = a) (hx23 : s.readReg64 .x23 = vn.minVersion.signExtend 64)
    (hinv0 : StepInv s0 s) (hP : P = versionNegotiationRest A g a vn ∗ F)
    (hnext : ∀ s1 : State,
      (s1.pc = (blkPl_426).base + 708#64 ∨ s1.pc = (blkPl_426).base + 892#64) →
      s1.status = .Running → s1.sp = s.sp → s1.trace = s.trace →
      s1.readReg64 .x8 = s.readReg64 .x8 → s1.readReg64 .x9 = s.readReg64 .x9 →
      s1.readReg64 .x10 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.minVersion) →
      s1.readReg64 .x19 = s.readReg64 .x19 → s1.readReg64 .x20 = a →
      s1.readReg64 .x21 = s.readReg64 .x21 → s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = vn.minVersion.signExtend 64 →
      s1.readReg64 .x24 = s.readReg64 .x24 → s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .fp = s.readReg64 .fp → StepInv s0 s1 → VmPreserved s s1 →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s1 (versionNegotiationRest A g a vn ∗ F) Q Qp oom) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q Qp oom := by
  subst hP; dsimp only [versionNegotiationRest]
  have hw23 : s.readReg32 .x23 = vn.minVersion := by simp only [State.readReg32, hx23, sext64_truncate32]
  by_cases hmv : vn.minVersion = 0#32
  · have hmv_eq : i32VarintFieldEncodedLen vn.minVersion = 0 := by simp [i32VarintFieldEncodedLen, hmv]
    have hbeq_m : (vn.minVersion == 0#32) = true := beq_iff_eq.mpr hmv
    have hbne_m : (vn.minVersion != 0#32) = false := by simp [hmv]
    rcases hpc with hpc | hpc <;>
      (apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 892#64); wp_steps;
       apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, wp_norm, *]); intro hinv;
       exact hnext _ (Or.inr (by simp only [arm64_norm, *]))
         (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hmv_eq, *])
         (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, *]) (hinv0.trans hinv.1) hinv.2)
  · have hbeq_m : (vn.minVersion == 0#32) = false := beq_eq_false_iff_ne.mpr hmv
    have hbne_m : (vn.minVersion != 0#32) = true := bne_iff_ne.mpr hmv
    have hstep_m := bv_i32VarintField_nonzero hmv
    rcases hpc with hpc | hpc <;>
      (apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 708#64); wp_steps;
       apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, wp_norm, *]); intro hinv;
       exact hnext _ (Or.inl (by simp only [arm64_norm, *]))
         (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, *]) (hinv0.trans hinv.1) hinv.2)

theorem step_encodeToVec_vn_chainParams_len_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (a sp : BitVec 64) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_426).base + 708#64 ∨ s.pc = (blkPl_426).base + 892#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (bytesFieldEncodedLen vn.authKey))
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.direction))
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.minVersion))
    (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInv s0 s)
    (hP : P = versionNegotiationRest A g a vn ∗ F)
    (hnext : ∀ s1 : State,
      s1.pc = lsmpl.base 292 →
      s1.status = .Running → s1.sp = sp - 144#64 → s1.trace = s.trace →
      s1.readReg64 .x0 = BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn) →
      s1.readReg64 .x1 = sp - 120#64 →
      s1.readReg64 .lr = (if vn.chainParams.isSome then (blkPl_426).base + 968#64 else (blkPl_426).base + 924#64) →
      s1.readReg64 .x19 = s.readReg64 .x19 → s1.readReg64 .x20 = a →
      s1.readReg64 .x21 = s.readReg64 .x21 → s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = s.readReg64 .x23 → s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = (optChainParamsTag vn.chainParams).zeroExtend 64 →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .fp = s.readReg64 .fp → StepInv s0 s1 → VmPreserved s s1 →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s1 (versionNegotiationRest A g a vn ∗ F) Q Qp oom) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q Qp oom := by
  subst hP; dsimp only [versionNegotiationRest]
  cases hcp : vn.chainParams with
  | none =>
    dsimp only [optChainParamsPBAt, optChainParamsTag, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    have hcomb := bv_versionNegLen_none_combine vn hcp
    rcases hpc with hpc | hpc <;>
      (apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 292); wp_steps;
       apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, wp_norm, *]); intro hinv;
       refine SepWPp.weaken_pre
         (by dsimp only [versionNegotiationRest]; rw [hcp]; dsimp only [optChainParamsPBAt]
             simp only [BitVec.add_assoc, BitVec.reduceAdd]; exact Entails.of_eq (by sep_ac_rfl))
         (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
           (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
           (by rw [← hcomb]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
           (by rw [hcp]; simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
           (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
           (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
           (by simp only [arm64_norm, *]) (by rw [hcp]; simp only [optChainParamsTag, arm64_norm, *])
           (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
           (hinv0.trans hinv.1) hinv.2))
  | some cp =>
    simp only [optChainParamsPBAt, chainParamsPBAt, BitVec.add_assoc, BitVec.reduceAdd]
    suffices h720 : ∀ s_mid : State,
        s_mid.pc = (blkPl_426).base + 720#64 → s_mid.status = .Running → s_mid.sp = sp - 144#64 → s_mid.trace = s.trace →
        s_mid.readReg64 .x8 = BitVec.ofNat 64 (bytesFieldEncodedLen vn.authKey) →
        s_mid.readReg64 .x9 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.direction) →
        s_mid.readReg64 .x10 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.minVersion) →
        s_mid.readReg64 .x19 = s.readReg64 .x19 → s_mid.readReg64 .x20 = a →
        s_mid.readReg64 .x21 = s.readReg64 .x21 → s_mid.readReg64 .x22 = s.readReg64 .x22 →
        s_mid.readReg64 .x23 = s.readReg64 .x23 → s_mid.readReg64 .x24 = s.readReg64 .x24 →
        s_mid.readReg64 .x25 = s.readReg64 .x25 → s_mid.readReg64 .x26 = 1#64 →
        s_mid.readReg64 .x27 = s.readReg64 .x27 → s_mid.readReg64 .x28 = s.readReg64 .x28 →
        s_mid.readReg64 .fp = s.readReg64 .fp → StepInv s0 s_mid → VmPreserved s s_mid →
        SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s_mid
          (((a + 8#64) ↦₆₄ g.authKey.ptr) ∗
           ((a + 16#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
           vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey ∗
           ((a + 24#64) ↦₃₂ 1#32) ∗ ((a + 28#64) ↦₃₂ cp.maxJump) ∗ ((a + 32#64) ↦₃₂ cp.maxOooKeys) ∗
           ((a + 36#64) ↦₃₂ vn.direction) ∗ ((a + 40#64) ↦₃₂ vn.minVersion) ∗
           memRegion (a + 44#64) 4 ∗ F) Q Qp oom by
      rcases hpc with hpc | hpc <;>
        (apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 720#64); wp_steps;
         apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
           (by simp only [arm64_norm, wp_norm, *]); intro hinv;
         refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
           (h720 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
             (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
             (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
             (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
             (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
             (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
             (by simp only [arm64_norm, *]) (hinv0.trans hinv.1) hinv.2))
    intro s_mid hpc_m hrun_m hsp_m htr_m hx8_m hx9_m hx10_m hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hinv_m hvm_m
    have hcomb := bv_versionNegLen_some_combine vn
    by_cases hmj : cp.maxJump = 0#32 <;> by_cases hmo : cp.maxOooKeys = 0#32
    · have hmj_eq : u32VarintFieldEncodedLen cp.maxJump = 0 := by simp [u32VarintFieldEncodedLen, hmj]
      have hmo_eq : u32VarintFieldEncodedLen cp.maxOooKeys = 0 := by simp [u32VarintFieldEncodedLen, hmo]
      have hbeq_mj : (cp.maxJump == 0#32) = true := beq_iff_eq.mpr hmj
      have hbne_mj : (cp.maxJump != 0#32) = false := by simp [hmj]
      have hbeq_mo : (cp.maxOooKeys == 0#32) = true := beq_iff_eq.mpr hmo
      have hbne_mo : (cp.maxOooKeys != 0#32) = false := by simp [hmo]
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 292); wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *]); intro hinv
      refine SepWPp.weaken_pre
        (by dsimp only [versionNegotiationRest]; rw [hcp]
            simp only [optChainParamsPBAt, chainParamsPBAt, BitVec.add_assoc, BitVec.reduceAdd]
            exact Entails.of_eq (by sep_ac_rfl))
        (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by rw [← hcomb, hcp, ← bv_optChainParams_some_combine]; simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by rw [hcp]; simp only [Option.isSome_some, ↓reduceIte, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by rw [hcp]; simp only [optChainParamsTag, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_m.trans hinv.1) (hvm_m.trans hinv.2))
    · have hmj_eq : u32VarintFieldEncodedLen cp.maxJump = 0 := by simp [u32VarintFieldEncodedLen, hmj]
      have hbeq_mj : (cp.maxJump == 0#32) = true := beq_iff_eq.mpr hmj
      have hbne_mj : (cp.maxJump != 0#32) = false := by simp [hmj]
      have hbeq_mo : (cp.maxOooKeys == 0#32) = false := beq_eq_false_iff_ne.mpr hmo
      have hbne_mo : (cp.maxOooKeys != 0#32) = true := bne_iff_ne.mpr hmo
      have hstep_mo := bv_u32VarintField_nonzero hmo
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 292); wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *]); intro hinv
      refine SepWPp.weaken_pre
        (by dsimp only [versionNegotiationRest]; rw [hcp]
            simp only [optChainParamsPBAt, chainParamsPBAt, BitVec.add_assoc, BitVec.reduceAdd]
            exact Entails.of_eq (by sep_ac_rfl))
        (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by rw [← hcomb, hcp, ← bv_optChainParams_some_combine]; simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by rw [hcp]; simp only [Option.isSome_some, ↓reduceIte, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by rw [hcp]; simp only [optChainParamsTag, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_m.trans hinv.1) (hvm_m.trans hinv.2))
    · have hmo_eq : u32VarintFieldEncodedLen cp.maxOooKeys = 0 := by simp [u32VarintFieldEncodedLen, hmo]
      have hbeq_mj : (cp.maxJump == 0#32) = false := beq_eq_false_iff_ne.mpr hmj
      have hbne_mj : (cp.maxJump != 0#32) = true := bne_iff_ne.mpr hmj
      have hstep_mj := bv_chainParams_maxJump_nonzero hmj
      have hbeq_mo : (cp.maxOooKeys == 0#32) = true := beq_iff_eq.mpr hmo
      have hbne_mo : (cp.maxOooKeys != 0#32) = false := by simp [hmo]
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 292); wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *]); intro hinv
      refine SepWPp.weaken_pre
        (by dsimp only [versionNegotiationRest]; rw [hcp]
            simp only [optChainParamsPBAt, chainParamsPBAt, BitVec.add_assoc, BitVec.reduceAdd]
            exact Entails.of_eq (by sep_ac_rfl))
        (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by rw [← hcomb, hcp, ← bv_optChainParams_some_combine]; simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by rw [hcp]; simp only [Option.isSome_some, ↓reduceIte, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by rw [hcp]; simp only [optChainParamsTag, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_m.trans hinv.1) (hvm_m.trans hinv.2))
    · have hbeq_mj : (cp.maxJump == 0#32) = false := beq_eq_false_iff_ne.mpr hmj
      have hbne_mj : (cp.maxJump != 0#32) = true := bne_iff_ne.mpr hmj
      have hstep_mj := bv_chainParams_maxJump_nonzero hmj
      have hbeq_mo : (cp.maxOooKeys == 0#32) = false := beq_eq_false_iff_ne.mpr hmo
      have hbne_mo : (cp.maxOooKeys != 0#32) = true := bne_iff_ne.mpr hmo
      have hstep_mo := bv_u32VarintField_nonzero hmo
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 292); wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *]); intro hinv
      refine SepWPp.weaken_pre
        (by dsimp only [versionNegotiationRest]; rw [hcp]
            simp only [optChainParamsPBAt, chainParamsPBAt, BitVec.add_assoc, BitVec.reduceAdd]
            exact Entails.of_eq (by sep_ac_rfl))
        (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by rw [← hcomb, hcp, ← bv_optChainParams_some_combine]; simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by rw [hcp]; simp only [Option.isSome_some, ↓reduceIte, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by rw [hcp]; simp only [optChainParamsTag, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_m.trans hinv.1) (hvm_m.trans hinv.2))

theorem step_encodeToVec_vn_branch_authKey_placed [LibsignalPlacement]
    (H : String → Option (State → State))
    (vn : VersionNegotiationPB) (hlen : vn.authKey.length < 2 ^ 64)
    {s0 s : State} {ret : BitVec 64} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = if vn.chainParams.isSome then (blkPl_426).base + 968#64 else (blkPl_426).base + 924#64)
    (hrun : s.status = .Running) (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 vn.authKey.length)
    (hinv0 : StepInv s0 s)
    (hnext : ∀ s1 : State,
      s1.pc = (if vn.authKey.isEmpty then (blkPl_426).base + 1088#64 else (blkPl_426).base + 972#64) →
      s1.status = .Running → s1.sp = s.sp → s1.trace = s.trace →
      s1.readReg64 .x19 = s.readReg64 .x19 → s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = s.readReg64 .x21 → s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = s.readReg64 .x23 → s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 → s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .fp = s.readReg64 .fp → StepInv s0 s1 → VmPreserved s s1 →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s1 P Q Qp oom) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q Qp oom := by
  obtain ⟨hbeqz, hbnez⟩ := ofNat_length_beq_zero_of_lt hlen
  cases hcp : vn.chainParams.isSome <;> rw [hcp] at hpc <;>
    simp only [Bool.false_eq_true, ↓reduceIte] at hpc <;>
    cases hemp : vn.authKey.isEmpty <;>
    simp only [hemp, Bool.not_false, Bool.not_true, ↓reduceIte] at hbeqz hbnez ⊢ <;>
    (apply sepWPp_of_sepWP_cs_vm (mid := if vn.authKey.isEmpty then (blkPl_426).base + 1088#64 else (blkPl_426).base + 972#64);
     rw [hemp]; simp only [Bool.false_eq_true, ↓reduceIte]; wp_steps;
     apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
       (by simp only [arm64_norm, wp_norm, *]); intro hinv;
     exact hnext _
       (by rw [hemp]; simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
       (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
       (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
       (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
       (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
       (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
       (hinv0.trans hinv.1) hinv.2)

/-! ## 3. Budget-Threaded Field-Encoding Sub-Steps (`+972/+1088 .. +1212`) -/

theorem step_encodeToVec_vn_encode_authKey_placed [LibsignalPlacement] {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (σ0 : M.σ)
    (H : String → Option (State → State))
    {s0 s : State}
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      ((blkPl_426).ρ "memcpy")
      etvMemcpyRegionSpec)
    (a sp cap ptr v1 v2 : BitVec 64) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB)
    (bs : List (BitVec 8))
    (hfit : bs.length + (encodeBytesField 1#32 vn.authKey).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (if vn.authKey.isEmpty then (blkPl_426).base + 1088#64 else (blkPl_426).base + 972#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = a)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 vn.authKey.length)
    (hx26 : s.readReg64 .x26 = (optChainParamsTag vn.chainParams).zeroExtend 64)
    (hinv0 : StepInv s0 s)
    (hP : P = (versionNegotiationRest A.repAlloc g a vn ∗
      vecU8At A.repAlloc (sp - 120#64) cap ptr bs ∗ A.pool lim σ0 s ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
      ((sp - 136#64) ↦₆₄ v1) ∗ ((sp - 128#64) ↦₆₄ v2)) ∗ F)
    (hnext : ∀ (sm : State) (w1 w2 : BitVec 64),
      sm.pc = (blkPl_426).base + 1088#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x24 = s.readReg64 .x24 →
      sm.readReg64 .x26 = (optChainParamsTag vn.chainParams).zeroExtend 64 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm
        ((versionNegotiationRest A.repAlloc g a vn ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr (bs ++ encodeBytesField 1#32 vn.authKey) ∗
          A.pool lim σ0 sm ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
          ((sp - 136#64) ↦₆₄ w1) ∗ ((sp - 128#64) ↦₆₄ w2)) ∗ F)
        Q Qp oom) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q Qp oom := by
  subst hP
  cases hemp : vn.authKey.isEmpty
  · rw [hemp] at hpc; simp only [Bool.false_eq_true, ↓reduceIte] at hpc
    have hsp_align : (sp - 144#64) &&& 15#64 = 0#64 := sp_sub_144_aligned halign
    have h112 : (sp - 120#64) + 8#64 = sp - 112#64 := by bv_omega
    have h104 : (sp - 120#64) + 16#64 = sp - 104#64 := by bv_omega
    have h132 : (sp - 136#64) + 4#64 = sp - 132#64 := by bv_omega
    have hpos_ak : 0 < vn.authKey.length := List.length_pos_of_ne_nil (List.isEmpty_eq_false_iff.mp hemp)
    have hne_ak : vn.authKey ≠ [] := List.isEmpty_eq_false_iff.mp hemp
    have henc_eq : encodeBytesField 1#32 vn.authKey =
        [0x0a#8] ++ encodeVarint (BitVec.ofNat 64 vn.authKey.length) ++ vn.authKey := by
      rw [encodeBytesField_1_eq, hemp]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hfit_all :
        bs.length + 1 + (encodeVarint (BitVec.ofNat 64 vn.authKey.length)).length +
          vn.authKey.length ≤ cap.toNat := by
      rw [henc_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit; omega
    have hlt_tag : bs.length < cap.toNat := by omega
    refine sepWPp_extract_vecU8At_bounds (v := sp - 120#64) (cap := cap) (ptr := ptr) (bs := bs)
      (F := versionNegotiationRest A.repAlloc g a vn ∗ A.pool lim σ0 s ∗
        stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
        ((sp - 136#64) ↦₆₄ v1) ∗ ((sp - 128#64) ↦₆₄ v2) ∗ F) (by sep_ac_rfl) fun _ hcap hptr => ?_
    refine sepWPp_extract_pure
      (vn.authKey.length ≤ g.authKey.cap.toNat ∧ g.authKey.cap.toNat < 2 ^ 63)
      (fun R' hm => by
        dsimp only [versionNegotiationRest] at hm
        have hm' : s.mem ⊨ vecU8Buf A.repAlloc g.authKey.cap g.authKey.ptr vn.authKey ∗
            (((a + 8#64) ↦₆₄ g.authKey.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
             optChainParamsPBAt (a + 24#64) vn.chainParams ∗
             ((a + 36#64) ↦₃₂ vn.direction) ∗ ((a + 40#64) ↦₃₂ vn.minVersion) ∗
             memRegion (a + 44#64) 4 ∗ vecU8At A.repAlloc (sp - 120#64) cap ptr bs ∗ A.pool lim σ0 s ∗
             stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
             ((sp - 136#64) ↦₆₄ v1) ∗ ((sp - 128#64) ↦₆₄ v2) ∗ F ∗ R') := by
          convert hm using 1; sep_ac_rfl
        exact vecU8Buf_bounds hm')
      fun ⟨hak_le, hak_cap⟩ => ?_
    have hcmp_tag := cap_beq_len_false_of_lt hlt_tag hcap
    refine sepWPp_split_pointsTo64 (sp - 136#64) v1
      (vecU8At A.repAlloc (sp - 120#64) cap ptr bs ∗ versionNegotiationRest A.repAlloc g a vn ∗ A.pool lim σ0 s ∗
        stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ ((sp - 128#64) ↦₆₄ v2) ∗ F)
      (by sep_ac_rfl) fun v1_lo v1_hi => ?_
    rw [h132, vecU8At_expose_one A.repAlloc (sp - 120#64) cap ptr bs hlt_tag hcap hptr, h112, h104]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    dsimp only [versionNegotiationRest]
    apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 292)
    by_vm_steps
      wp_steps
      apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv1
      have hpack_tag := vecU8At_pack_one A.repAlloc (sp - 120#64) cap ptr bs 0x0a#8 hlt_tag hcap hptr
      rw [h112, h104] at hpack_tag
      refine step_etv_encode_varint_call_prog A lim σ0 hvarint
        (BitVec.ofNat 64 vn.authKey.length) (sp - 120#64) cap ptr sp ((blkPl_426).base + 1032#64) (bs ++ [0x0a#8])
        (by simp only [List.length_append, List.length_singleton]; omega)
        (F := versionNegotiationRest A.repAlloc g a vn ∗ ((sp - 136#64) ↦₃₂ v1_lo) ∗
          ((sp - 132#64) ↦₃₂ optChainParamsTag vn.chainParams) ∗
          ((sp - 128#64) ↦₆₄ s.readReg64 .x27) ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1)
        (by rw [A.pool_of_vmPreserved hinv1.2, ← hpack_tag]; dsimp only [versionNegotiationRest]; sep_ac_rfl) ?_
      intro s1 hpcs1 hruns1 hsps1 htrs1 hcss1 hinv_s1
      rcases hcss1 with ⟨hs1_19, hs1_20, hs1_21, hs1_22, hs1_23, hs1_24, hs1_25, hs1_26, hs1_27, hs1_28, hs1_fp, _⟩
      simp only [arm64_norm, hx20, hx25] at hs1_19 hs1_20 hs1_21 hs1_22 hs1_23 hs1_24 hs1_25 hs1_26 hs1_27 hs1_28 hs1_fp
      let bs1 := (bs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 vn.authKey.length)
      have hfit_mc : bs1.length + vn.authKey.length ≤ cap.toNat := by
        dsimp only [bs1]; simp only [List.length_append, List.length_singleton]; omega
      have hcmp_mc := elem_len_ult_spare_false_of_le hfit_mc hcap
      rw [vecU8At_expose_slice A.repAlloc (sp - 120#64) cap ptr bs1 vn.authKey.length hfit_mc hcap hptr hpos_ak, h112, h104]
      dsimp only [versionNegotiationRest]
      rw [vecU8Buf_eq_of_nonempty A.repAlloc g.authKey.cap g.authKey.ptr vn.authKey hemp hak_le]
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).ρ "memcpy")
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv2
      have hlen_ak_toNat : (BitVec.ofNat 64 vn.authKey.length).toNat = vn.authKey.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine step_etv_memcpy_call_prog A lim σ0 hmemcpy
        (ptr + BitVec.ofNat 64 bs1.length) g.authKey.ptr sp ((blkPl_426).base + 1072#64) vn.authKey
        (F := ((sp - 120#64) ↦₆₄ cap) ∗ ((sp - 112#64) ↦₆₄ ptr) ∗
          ((sp - 104#64) ↦₆₄ BitVec.ofNat 64 bs1.length) ∗
          A.repAlloc.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs1) ∗
          memRegion (ptr + BitVec.ofNat 64 bs1.length + BitVec.ofNat 64 vn.authKey.length)
            (cap.toNat - bs1.length - vn.authKey.length) ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
          ((a + 8#64) ↦₆₄ g.authKey.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
          (⌜vn.authKey.length ≤ g.authKey.cap.toNat ∧ g.authKey.cap.toNat < 2 ^ 63 ∧ g.authKey.ptr ≠ 0⌝ ∗
            A.repAlloc.live g.authKey.ptr g.authKey.cap.toNat 1 ∗
            memRegion (g.authKey.ptr + BitVec.ofNat 64 vn.authKey.length)
              (g.authKey.cap.toNat - vn.authKey.length)) ∗
          optChainParamsPBAt (a + 24#64) vn.chainParams ∗
          ((a + 36#64) ↦₃₂ vn.direction) ∗ ((a + 40#64) ↦₃₂ vn.minVersion) ∗
          memRegion (a + 44#64) 4 ∗
          ((sp - 136#64) ↦₃₂ v1_lo) ∗ ((sp - 132#64) ↦₃₂ optChainParamsTag vn.chainParams) ∗
          ((sp - 128#64) ↦₆₄ s.readReg64 .x27) ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, hlen_ak_toNat, *]) (hinv_s1.trans hinv2.1)
        (by rw [A.pool_of_vmPreserved hinv2.2]; sep_ac_rfl) ?_
      intro s2 hpcs2 hruns2 hsps2 htrs2 hvms2 hcss2 hinv_s2
      rcases hcss2 with ⟨hs2_19, hs2_20, hs2_21, hs2_22, hs2_23, hs2_24, hs2_25, hs2_26, hs2_27, hs2_28, hs2_fp, _⟩
      simp only [arm64_norm, hs1_19, hs1_20, hs1_21, hs1_22, hs1_23, hs1_24, hs1_25, hs1_26, hs1_28, hs1_fp]
        at hs2_19 hs2_20 hs2_21 hs2_22 hs2_23 hs2_24 hs2_25 hs2_26 hs2_27 hs2_28 hs2_fp
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 1088#64)
      by_vm_steps
        wp_steps
        apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv3
        have hpack_mc := vecU8At_pack_slice A.repAlloc (sp - 120#64) cap ptr bs1 vn.authKey hfit_mc hcap hptr hne_ak
        have hbs_eq : bs1 ++ vn.authKey = bs ++ encodeBytesField 1#32 vn.authKey := by
          dsimp only [bs1]; rw [henc_eq]; simp only [List.append_assoc]
        rw [h112, h104, hbs_eq] at hpack_mc
        refine sepWPp_merge_pointsTo32 (sp - 136#64) v1_lo (optChainParamsTag vn.chainParams)
          (versionNegotiationRest A.repAlloc g a vn ∗
            vecU8At A.repAlloc (sp - 120#64) cap ptr (bs ++ encodeBytesField 1#32 vn.authKey) ∗
            A.pool lim σ0 s2 ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
            ((sp - 128#64) ↦₆₄ s.readReg64 .x27) ∗ F)
          (by rw [h132, ← hpack_mc]; dsimp only [versionNegotiationRest]
              rw [vecU8Buf_eq_of_nonempty A.repAlloc g.authKey.cap g.authKey.ptr vn.authKey hemp hak_le]
              sep_ac_rfl)
          fun w1 => ?_
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (hnext _ w1 (s.readReg64 .x27)
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_s2.trans hinv3.1))
        rw [A.pool_of_vmPreserved hinv3.2]; sep_ac_rfl
  · rw [hemp] at hpc; simp only [↓reduceIte] at hpc
    have henc_nil : encodeBytesField 1#32 vn.authKey = [] := by
      rw [encodeBytesField_1_eq, hemp]; simp only [↓reduceIte]
    refine SepWPp.weaken_pre
      (by rw [henc_nil, List.append_nil]; exact Entails.of_eq (by sep_ac_rfl))
      (hnext s v1 v2 hpc hrun hsp htr rfl hx20 rfl rfl rfl rfl hx26 rfl rfl rfl hinv0)

theorem step_encodeToVec_vn_encode_dir_placed [LibsignalPlacement] {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (σ0 : M.σ)
    (H : String → Option (State → State))
    {s0 s : State}
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (sp cap ptr : BitVec 64) (vn : VersionNegotiationPB) (bs : List (BitVec 8))
    (hfit : bs.length + (encodeInt32Field 2#32 vn.direction).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_426).base + 1088#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx24 : s.readReg64 .x24 = vn.direction.signExtend 64) (hinv0 : StepInv s0 s)
    (hP : P = (vecU8At A.repAlloc (sp - 120#64) cap ptr bs ∗ A.pool lim σ0 s ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 1140#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x26 = s.readReg64 .x26 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm
        ((vecU8At A.repAlloc (sp - 120#64) cap ptr (bs ++ encodeInt32Field 2#32 vn.direction) ∗
          A.pool lim σ0 sm ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q Qp oom := by
  subst hP
  have hsp_align : (sp - 144#64) &&& 15#64 = 0#64 := sp_sub_144_aligned halign
  have h112 : (sp - 120#64) + 8#64 = sp - 112#64 := by bv_omega
  have h104 : (sp - 120#64) + 16#64 = sp - 104#64 := by bv_omega
  have hw24 : s.readReg32 .x24 = vn.direction := by simp only [State.readReg32, hx24, sext64_truncate32]
  by_cases hdir : vn.direction = 0#32
  · have hbeq_d : (vn.direction == 0#32) = true := beq_iff_eq.mpr hdir
    have hbne_d : (vn.direction != 0#32) = false := by simp [hdir]
    have henc_nil : encodeInt32Field 2#32 vn.direction = [] := by
      rw [encodeInt32Field_2_eq, hbeq_d]; simp only [↓reduceIte]
    apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 1140#64); wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv
    refine SepWPp.weaken_pre (Entails.of_eq ?_)
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hinv0.trans hinv.1))
    rw [henc_nil, List.append_nil, A.pool_of_vmPreserved hinv.2]
  · have hbeq_d : (vn.direction == 0#32) = false := beq_eq_false_iff_ne.mpr hdir
    have hbne_d : (vn.direction != 0#32) = true := bne_iff_ne.mpr hdir
    have henc_eq : encodeInt32Field 2#32 vn.direction =
        [0x10#8] ++ encodeVarint (vn.direction.signExtend 64) := by
      rw [encodeInt32Field_2_eq, hbeq_d]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hvpos := encodeVarint_length_pos (vn.direction.signExtend 64)
    have hfit' : bs.length + 1 + (encodeVarint (vn.direction.signExtend 64)).length ≤ cap.toNat := by
      rw [henc_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit; omega
    have hlt : bs.length < cap.toNat := by omega
    refine sepWPp_extract_vecU8At_bounds (v := sp - 120#64) (cap := cap) (ptr := ptr) (bs := bs)
      (F := A.pool lim σ0 s ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F) (by sep_ac_rfl)
      fun _ hcap hptr => ?_
    have hcmp := cap_beq_len_false_of_lt hlt hcap
    rw [vecU8At_expose_one A.repAlloc (sp - 120#64) cap ptr bs hlt hcap hptr, h112, h104]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 292)
    by_vm_steps
      wp_steps
      apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv1
      have hpack := vecU8At_pack_one A.repAlloc (sp - 120#64) cap ptr bs 0x10#8 hlt hcap hptr
      rw [h112, h104] at hpack
      refine step_etv_encode_varint_call_prog A lim σ0 hvarint
        (vn.direction.signExtend 64) (sp - 120#64) cap ptr sp ((blkPl_426).base + 1140#64) (bs ++ [0x10#8])
        (by simp only [List.length_append, List.length_singleton]; omega) (F := F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1)
        (by rw [A.pool_of_vmPreserved hinv1.2, ← hpack]) ?_
      intro sm hpcm hrunm hspm htrm hcsm hinv_m
      rcases hcsm with ⟨hm19, hm20, hm21, hm22, hm23, _, _, hm26, hm27, hm28, hmfp, _⟩
      simp only [arm64_norm] at hm19 hm20 hm21 hm22 hm23 hm26 hm27 hm28 hmfp
      refine SepWPp.weaken_pre
        (by rw [henc_eq, ← List.append_assoc]; exact Entails.of_eq (by sep_ac_rfl))
        (hnext sm hpcm hrunm hspm htrm hm19 hm20 hm21 hm22 hm23 hm26 hm27 hm28 hmfp hinv_m)

theorem step_encodeToVec_vn_encode_minVer_placed [LibsignalPlacement] {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (σ0 : M.σ)
    (H : String → Option (State → State))
    {s0 s : State}
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (sp cap ptr : BitVec 64) (vn : VersionNegotiationPB) (bs : List (BitVec 8))
    (hfit : bs.length + (encodeInt32Field 3#32 vn.minVersion).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_426).base + 1140#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx23 : s.readReg64 .x23 = vn.minVersion.signExtend 64) (hinv0 : StepInv s0 s)
    (hP : P = (vecU8At A.repAlloc (sp - 120#64) cap ptr bs ∗ A.pool lim σ0 s ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 1192#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .x26 = s.readReg64 .x26 → sm.readReg64 .x27 = s.readReg64 .x27 →
      sm.readReg64 .x28 = s.readReg64 .x28 → sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm
        ((vecU8At A.repAlloc (sp - 120#64) cap ptr (bs ++ encodeInt32Field 3#32 vn.minVersion) ∗
          A.pool lim σ0 sm ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q Qp oom := by
  subst hP
  have hsp_align : (sp - 144#64) &&& 15#64 = 0#64 := sp_sub_144_aligned halign
  have h112 : (sp - 120#64) + 8#64 = sp - 112#64 := by bv_omega
  have h104 : (sp - 120#64) + 16#64 = sp - 104#64 := by bv_omega
  have hw23 : s.readReg32 .x23 = vn.minVersion := by simp only [State.readReg32, hx23, sext64_truncate32]
  by_cases hmv : vn.minVersion = 0#32
  · have hbeq_m : (vn.minVersion == 0#32) = true := beq_iff_eq.mpr hmv
    have hbne_m : (vn.minVersion != 0#32) = false := by simp [hmv]
    have henc_nil : encodeInt32Field 3#32 vn.minVersion = [] := by
      rw [encodeInt32Field_3_eq, hbeq_m]; simp only [↓reduceIte]
    apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 1192#64); wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv
    refine SepWPp.weaken_pre (Entails.of_eq ?_)
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hinv0.trans hinv.1))
    rw [henc_nil, List.append_nil, A.pool_of_vmPreserved hinv.2]
  · have hbeq_m : (vn.minVersion == 0#32) = false := beq_eq_false_iff_ne.mpr hmv
    have hbne_m : (vn.minVersion != 0#32) = true := bne_iff_ne.mpr hmv
    have henc_eq : encodeInt32Field 3#32 vn.minVersion =
        [0x18#8] ++ encodeVarint (vn.minVersion.signExtend 64) := by
      rw [encodeInt32Field_3_eq, hbeq_m]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hvpos := encodeVarint_length_pos (vn.minVersion.signExtend 64)
    have hfit' : bs.length + 1 + (encodeVarint (vn.minVersion.signExtend 64)).length ≤ cap.toNat := by
      rw [henc_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit; omega
    have hlt : bs.length < cap.toNat := by omega
    refine sepWPp_extract_vecU8At_bounds (v := sp - 120#64) (cap := cap) (ptr := ptr) (bs := bs)
      (F := A.pool lim σ0 s ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F) (by sep_ac_rfl)
      fun _ hcap hptr => ?_
    have hcmp := cap_beq_len_false_of_lt hlt hcap
    rw [vecU8At_expose_one A.repAlloc (sp - 120#64) cap ptr bs hlt hcap hptr, h112, h104]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 292)
    by_vm_steps
      wp_steps
      apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv1
      have hpack := vecU8At_pack_one A.repAlloc (sp - 120#64) cap ptr bs 0x18#8 hlt hcap hptr
      rw [h112, h104] at hpack
      refine step_etv_encode_varint_call_prog A lim σ0 hvarint
        (vn.minVersion.signExtend 64) (sp - 120#64) cap ptr sp ((blkPl_426).base + 1192#64) (bs ++ [0x18#8])
        (by simp only [List.length_append, List.length_singleton]; omega) (F := F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1)
        (by rw [A.pool_of_vmPreserved hinv1.2, ← hpack]) ?_
      intro sm hpcm hrunm hspm htrm hcsm hinv_m
      rcases hcsm with ⟨hm19, hm20, hm21, hm22, _, _, _, hm26, hm27, hm28, hmfp, _⟩
      simp only [arm64_norm] at hm19 hm20 hm21 hm22 hm26 hm27 hm28 hmfp
      refine SepWPp.weaken_pre
        (by rw [henc_eq, ← List.append_assoc]; exact Entails.of_eq (by sep_ac_rfl))
        (hnext sm hpcm hrunm hspm htrm hm19 hm20 hm21 hm22 hm26 hm27 hm28 hmfp hinv_m)

theorem step_encodeToVec_vn_encode_chainParams_placed [LibsignalPlacement] {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (σ0 : M.σ)
    (H : String → Option (State → State))
    {s0 s : State}
    (hcp_call : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 313)
      (withStepInv s0 (encodeChainParamsExactSpecOf resStack A lim)))
    (a sp cap ptr : BitVec 64) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB)
    (bs : List (BitVec 8))
    (hfit : bs.length + (encodeOptMessage ChainParamsPB.encodeRaw 4#32 vn.chainParams).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_426).base + 1192#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = a)
    (hx26 : s.readReg64 .x26 = (optChainParamsTag vn.chainParams).zeroExtend 64)
    (hinv0 : StepInv s0 s)
    (hP : P = (versionNegotiationRest A.repAlloc g a vn ∗
      vecU8At A.repAlloc (sp - 120#64) cap ptr bs ∗ A.pool lim σ0 s ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 1212#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm
        ((versionNegotiationRest A.repAlloc g a vn ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr
            (bs ++ encodeOptMessage ChainParamsPB.encodeRaw 4#32 vn.chainParams) ∗
          A.pool lim σ0 sm ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q Qp oom := by
  subst hP; dsimp only [versionNegotiationRest]
  cases hcp : vn.chainParams with
  | none =>
    rw [hcp] at hx26
    dsimp only [optChainParamsTag, optChainParamsPBAt, encodeOptMessage] at hx26 ⊢
    apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 1212#64); wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv
    refine SepWPp.weaken_pre (Entails.of_eq ?_)
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hinv0.trans hinv.1))
    dsimp only [versionNegotiationRest]
    rw [hcp]
    dsimp only [optChainParamsPBAt, encodeOptMessage]
    rw [List.append_nil, A.pool_of_vmPreserved hinv.2]
  | some cp =>
    rw [hcp] at hx26 hfit
    dsimp only [optChainParamsTag, encodeOptMessage] at hx26 hfit
    simp only [optChainParamsPBAt, chainParamsPBAt, BitVec.add_assoc, BitVec.reduceAdd]
    apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 313); wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv1
    refine step_etv_encode_chainParams_call_prog A lim σ0 hcp_call
      4#32 cp (sp - 120#64) cap ptr sp ((blkPl_426).base + 1212#64) bs
      (by decide) (by decide) hfit
      (F := ((a + 8#64) ↦₆₄ g.authKey.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
        vecU8Buf A.repAlloc g.authKey.cap g.authKey.ptr vn.authKey ∗
        ((a + 24#64) ↦₃₂ 1#32) ∗ ((a + 28#64) ↦₃₂ cp.maxJump) ∗ ((a + 32#64) ↦₃₂ cp.maxOooKeys) ∗
        ((a + 36#64) ↦₃₂ vn.direction) ∗ ((a + 40#64) ↦₃₂ vn.minVersion) ∗
        memRegion (a + 44#64) 4 ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1)
      (by rw [A.pool_of_vmPreserved hinv1.2]; sep_ac_rfl) ?_
    intro sm hpcm hrunm hspm htrm hcsm hinv_m
    rcases hcsm with ⟨hm19, hm20, hm21, hm22, _, _, _, _, hm27, hm28, hmfp, _⟩
    simp only [arm64_norm, hx20] at hm19 hm20 hm21 hm22 hm27 hm28 hmfp
    refine SepWPp.weaken_pre
      (by dsimp only [versionNegotiationRest]; rw [hcp]
          simp only [optChainParamsPBAt, chainParamsPBAt, encodeOptMessage,
            BitVec.add_assoc, BitVec.reduceAdd]
          exact Entails.of_eq (by sep_ac_rfl))
      (hnext sm hpcm hrunm hspm htrm hm19 hm20 hm21 hm22 hm27 hm28 hmfp hinv_m)

end LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.VersionNegPhasePlacedBudgetAux

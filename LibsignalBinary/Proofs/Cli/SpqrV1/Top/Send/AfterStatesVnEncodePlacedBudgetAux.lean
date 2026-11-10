/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesVnEncodePlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.VersionNegPhasePlacedBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhasePlaced
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ChainEncodedLenBase
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesVnEncode
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Sub-Steps for Relocatable Phase 3c (`+4996..+5604`)

Proves `VmPreserved` `encode_varint` call helpers and sub-steps (`+4996..+5348`) for
inlined `Option<VersionNegotiation>` encoding in Block `427`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesVnEncodePlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open CryptoVerification (LibsignalPlacement libsignalSessionCode lsmpl lsρ)
open CryptoVerification.Cli.SpqrV1.Top.Send (spqrSendPlacedEntry spqrSendPlacedProg)
open CryptoVerification.RustHeap (RustAlloc vecU8At)
open CryptoVerification.LibsignalSpqrV1 (ChainParamsPB VersionNegotiationPB)
open CryptoVerification.LibsignalSpqrV1.Proto
  (encodeBytesField encodeInt32Field encodeMessage encodeOptMessage encodeVarint)
open CryptoVerification.LibsignalTripleRatchet (sessionMemcpyRegionSpec withStack)
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
  (StepInv bv_chainParams_maxJump_nonzero bv_i32VarintField_nonzero
   bv_optChainParams_some_combine bv_versionNegLen_none_combine bv_versionNegLen_some_combine
   cap_beq_len_false_of_lt elem_len_ult_spare_false_of_le
   encodeBytesField_1_eq encodeInt32Field_2_eq encodeInt32Field_3_eq
   encodeToVecCalleeStackOf encodeVarint_length_pos
   noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
   optChainParamsTag sext64_truncate32 subroutine_ok_withStepInv
   vecU8At_expose_one vecU8At_expose_slice vecU8At_pack_one vecU8At_pack_slice
   vecU8Buf_eq_of_nonempty versionNegotiationRest withStepInv)
open CryptoVerification.SpqrV1.Top.Send (sp_add_144_aligned sp_add_144_sub_144)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
  (sepWP_done_tpidr sepWP_done_vm sepWPp_call_cs_noPanic sepWPp_of_sepWP_cs_vm)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
  (encodeChainParamsExactSpecOf encodeVarintExactSpecOf etvMemcpyRegionSpec
   step_etv_encode_chainParams_call_prog step_etv_encode_varint_call_prog
   step_etv_memcpy_call_prog)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.VersionNegPhasePlacedBudgetAux
  (sepWPp_extract_pure sepWPp_extract_vecU8At_bounds
   sepWPp_merge_pointsTo32 sepWPp_split_pointsTo64)

variable [LibsignalPlacement]

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm zext64_truncate32
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  ule_zero_64 ult_zero_64 ule_self_64 ult_self_64
  spqrSendPlacedEntry

/-! ## 1. `s.sp = sp` Budget-Threaded Call Wrappers (`prog`-generic) -/

omit [LibsignalPlacement] in
/-- Execute `bl encode_varint` at `s.sp = sp` on any `prog : Program`. -/
theorem step_send_encode_varint_call_placed {resStack : Nat} {M : AllocCostModel}
    {prog : Program} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {call_pc : BitVec 64} {s0 s : State}
    (henc : subroutine_ok prog call_pc
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (val v cap ptr sp ret_pc : BitVec 64) (bs : List (BitVec 8))
    (hfit : bs.length + (encodeVarint val).length ≤ cap.toNat)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hinv0 : StepInv s0 s)
    (hP : P = (vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc v cap ptr (bs ++ encodeVarint val) ∗ A.pool lim st sm ∗
          stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp' : s.sp = (sp + 144#64) - 144#64 := by rw [sp_add_144_sub_144, hsp]
  have hP' : P = (vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s ∗
      stackAt ((sp + 144#64) - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F := by
    rw [sp_add_144_sub_144]; exact hP
  refine step_etv_encode_varint_call_prog A lim st henc val v cap ptr (sp + 144#64) ret_pc bs hfit
    hpc hrun hsp' (sp_add_144_aligned halign) htr hlr hx0 hx1 hinv0 hP' ?_
  intro sm hpcm hrunm hspm htrm hcsm hinvm
  rw [sp_add_144_sub_144] at hspm
  refine SepWPp.weaken_pre (by rw [sp_add_144_sub_144]; exact Entails.refl _)
    (hnext sm hpcm hrunm hspm htrm hcsm hinvm)

omit [LibsignalPlacement] in
/-- Execute `bl memcpy` at `s.sp = sp` on any `prog : Program`. -/
theorem step_send_memcpy_call_placed {M : AllocCostModel}
    {prog : Program} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {call_pc : BitVec 64} {s0 s : State}
    (hmemcpy : subroutine_ok prog call_pc etvMemcpyRegionSpec)
    (dst src sp ret_pc : BitVec 64) (bs : List (BitVec 8))
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hinv0 : StepInv s0 s)
    (hP : P = (memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ A.pool lim st s) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp →
      sm.trace = s0.trace →
      VmPreserved s sm →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      SepWPp prog ret sm
        (((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ A.pool lim st sm) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp' : s.sp = (sp + 144#64) - 144#64 := by rw [sp_add_144_sub_144, hsp]
  refine step_etv_memcpy_call_prog A lim st hmemcpy dst src (sp + 144#64) ret_pc bs
    hpc hrun hsp' (sp_add_144_aligned halign) htr hlr hx0 hx1 hx2 hinv0 hP ?_
  intro sm hpcm hrunm hspm htrm hvmm hcsm hinvm
  rw [sp_add_144_sub_144] at hspm
  exact hnext sm hpcm hrunm hspm htrm hvmm hcsm hinvm

omit [LibsignalPlacement] in
/-- Execute `bl encode<ChainParams>` at `s.sp = sp` on any `prog : Program`. -/
theorem step_send_encode_chainParams_call_placed {resStack : Nat} {M : AllocCostModel}
    {prog : Program} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {call_pc : BitVec 64} {s0 s : State}
    (hcp : subroutine_ok prog call_pc
      (withStepInv s0 (encodeChainParamsExactSpecOf resStack A lim)))
    (tag : BitVec 32) (p : ChainParamsPB) (v cap ptr sp ret_pc : BitVec 64) (bs : List (BitVec 8))
    (htag1 : 1 ≤ tag.toNat) (htag2 : tag.toNat < 2 ^ 29)
    (hfit : bs.length + (encodeMessage ChainParamsPB.encodeRaw tag p).length ≤ cap.toNat)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hw0 : s.readReg32 .x0 = tag)
    (hw1 : s.readReg32 .x1 = p.maxJump)
    (hw2 : s.readReg32 .x2 = p.maxOooKeys)
    (hx3 : s.readReg64 .x3 = v)
    (hinv0 : StepInv s0 s)
    (hP : P = (vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc v cap ptr (bs ++ encodeMessage ChainParamsPB.encodeRaw tag p) ∗
          A.pool lim st sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp' : s.sp = (sp + 144#64) - 144#64 := by rw [sp_add_144_sub_144, hsp]
  have hP' : P = (vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s ∗
      stackAt ((sp + 144#64) - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F := by
    rw [sp_add_144_sub_144]; exact hP
  refine step_etv_encode_chainParams_call_prog A lim st hcp tag p v cap ptr (sp + 144#64) ret_pc bs
    htag1 htag2 hfit hpc hrun hsp' (sp_add_144_aligned halign) htr hlr hw0 hw1 hw2 hx3 hinv0 hP' ?_
  intro sm hpcm hrunm hspm htrm hcsm hinvm
  rw [sp_add_144_sub_144] at hspm
  refine SepWPp.weaken_pre (by rw [sp_add_144_sub_144]; exact Entails.refl _)
    (hnext sm hpcm hrunm hspm htrm hcsm hinvm)

omit [LibsignalPlacement] in
theorem step_send_memcpy_call_cs_placed {resStack : Nat} {M : AllocCostModel}
    {prog : Program} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {call_pc : BitVec 64} {s0 s : State}
    (hmemcpy : subroutine_ok prog call_pc
      (withStepInv s0 (withStack etvMemcpyRegionSpec (encodeToVecCalleeStackOf resStack))))
    (dst src sp ret_pc : BitVec 64) (bs : List (BitVec 8))
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length) (hinv0 : StepInv s0 s)
    (hP : P = (memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ A.pool lim st s ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      VmPreserved s sm → CalleeSavedPreserved s sm → StepInv s0 sm →
      SepWPp prog ret sm
        (((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ A.pool lim st sm ∗
          stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact halign
  refine sepWPp_call_cs_noPanic (x := (dst, src, bs)) (F := A.pool lim st s ∗ F)
    hmemcpy hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    dsimp only [withStepInv, withStack, etvMemcpyRegionSpec, sessionMemcpyRegionBudgetSpec,
      sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [hsp, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm⟩
  · intro sf code R' _ hm
    dsimp only [withStepInv, withStack, etvMemcpyRegionSpec, sessionMemcpyRegionBudgetSpec,
      sessionMemcpyRegionSpec, memcpyRegionSpec] at hm
    exact (not_satisfies_false_sepConj hm).elim
  · intro sf R' _ hm
    dsimp only [withStepInv, withStack, etvMemcpyRegionSpec, sessionMemcpyRegionBudgetSpec,
      sessionMemcpyRegionSpec, memcpyRegionSpec] at hm
    exact (not_satisfies_false_sepConj hm).elim
  · intro sf R' _ hm
    dsimp only [withStepInv, withStack, etvMemcpyRegionSpec, sessionMemcpyRegionBudgetSpec,
      sessionMemcpyRegionSpec, memcpyRegionSpec] at hm
    exact (not_satisfies_false_sepConj hm).elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, withStack, etvMemcpyRegionSpec, sessionMemcpyRegionBudgetSpec,
      sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [hsp, sepConj_assoc, sepConj_assoc, sepConj_assoc]
    refine SepWPp.pure_elim fun hvm => SepWPp.pure_elim fun ⟨_, htrm⟩ => ?_
    have hpool : A.pool lim st s = A.pool lim st sm := (A.pool_of_vmPreserved hvm).symm
    rw [hpool]
    exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hvm hcsm (hinv0.trans hinv_call))

omit [LibsignalPlacement] in
theorem etvMemcpy_to_withStack_placed {prog : Program} {pc : BitVec 64} (stk : Nat)
    (h : subroutine_ok prog pc etvMemcpyRegionSpec) :
    subroutine_ok prog pc (withStack etvMemcpyRegionSpec stk) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hal => ?_
  have hpre' : s.mem ⊨ etvMemcpyRegionSpec.pre x s ∗ (stackAt s.sp stk ∗ R) := by
    dsimp only [withStack, etvMemcpyRegionSpec] at hpre ⊢
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  refine h.mono_outcome x (stackAt s.sp stk ∗ R) s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack, etvMemcpyRegionSpec] at hpost ⊢
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
  · dsimp only [etvMemcpyRegionSpec, sessionMemcpyRegionBudgetSpec,
      sessionMemcpyRegionSpec, memcpyRegionSpec] at hpan
    exact (not_satisfies_false_sepConj hpan).elim
  · dsimp only [etvMemcpyRegionSpec, sessionMemcpyRegionBudgetSpec,
      sessionMemcpyRegionSpec, memcpyRegionSpec] at hex
    exact (not_satisfies_false_sepConj hex).elim
  · dsimp only [etvMemcpyRegionSpec, sessionMemcpyRegionBudgetSpec,
      sessionMemcpyRegionSpec, memcpyRegionSpec] at hoom
    exact (not_satisfies_false_sepConj hoom).elim

/-! ## 2. Pure Sub-Steps for `VersionNegotiationPB` Encoding (`+4996 .. +5348`) with `VmPreserved` -/

/-- Step `spqrSendPlacedEntry + 4996#64 .. spqrSendPlacedEntry + 5020#64`: writes outer
`VersionNegotiation` tag `0x0a#8` into `vecU8At A (sp + 1424#64) cap ptr []` and loads
`x26 = BitVec.ofNat 64 vn.authKey.length`. -/
theorem step_send_vn_push_tag_31be0_placed (A : RustAlloc)
    (ext : String → Option (State → State))
    (sp cap ptr : BitVec 64) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB)
    (hpos : 0 < cap.toNat) (halign : sp &&& 15#64 = 0#64)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 4996#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hx0 : s.readReg64 .x0 = ptr) (hinv0 : StepInv s0 s)
    (hP : P = (versionNegotiationRest A g (sp + 4704#64) vn ∗
      vecU8At A (sp + 1424#64) cap ptr []) ∗ F)
    (hnext : ∀ s1 : State,
      s1.pc = spqrSendPlacedEntry + 5020#64 → s1.status = .Running → s1.sp = sp →
      s1.trace = s.trace →
      s1.readReg64 .x19 = s.readReg64 .x19 → s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = s.readReg64 .x21 → s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = s.readReg64 .x23 → s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = BitVec.ofNat 64 vn.authKey.length →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .fp = s.readReg64 .fp → StepInv s0 s1 → VmPreserved s s1 →
      SepWPp (spqrSendPlacedProg ext) ret s1
        ((versionNegotiationRest A g (sp + 4704#64) vn ∗
          vecU8At A (sp + 1424#64) cap ptr [0x0a#8]) ∗ F) Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP
  refine sepWPp_extract_vecU8At_bounds (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := [])
    (F := versionNegotiationRest A g (sp + 4704#64) vn ∗ F) (by sep_ac_rfl) fun _ hcap hptr => ?_
  rw [vecU8At_expose_one A (sp + 1424#64) cap ptr [] (by simpa using hpos) hcap hptr]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun b0 => ?_
  dsimp only [versionNegotiationRest, List.length_nil, BitVec.ofNat_eq_ofNat]
  have h1432 : (sp + 1424#64) + 8#64 = sp + 1432#64 := by bv_omega
  have h1440 : (sp + 1424#64) + 16#64 = sp + 1440#64 := by bv_omega
  have h4720 : (sp + 4704#64) + 16#64 = sp + 4720#64 := by bv_omega
  have hptr0 : ptr + 0#64 = ptr := by bv_omega
  rw [h1432, h1440, h4720, hptr0]
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at hpc ⊢
  apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 5020#64)
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
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hinv0.trans hinv.1) hinv.2)
    have hpack := vecU8At_pack_one A (sp + 1424#64) cap ptr [] 0x0a#8 (by simpa using hpos) hcap hptr
    dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat, List.nil_append] at hpack
    have h01 : (0#64 : BitVec 64) + 1#64 = 1#64 := rfl
    rw [h1432, h1440, hptr0, h01] at hpack; rw [← hpack]
    dsimp only [versionNegotiationRest]; rw [h4720]; exact Entails.of_eq (by sep_ac_rfl)

/-- Step `spqrSendPlacedEntry + 5020#64 .. spqrSendPlacedEntry + 5136#64`: computes
`x8 = BitVec.ofNat 64 (bytesFieldEncodedLen vn.authKey)` and loads `x25 = vn.direction.signExtend 64`. -/
theorem step_send_vn_authKey_len_31bf8_placed (A : RustAlloc)
    (ext : String → Option (State → State))
    (sp : BitVec 64) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB)
    (hlen : vn.authKey.length < 2 ^ 64) (halign : sp &&& 15#64 = 0#64)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 5020#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 vn.authKey.length)
    (hinv0 : StepInv s0 s) (hP : P = versionNegotiationRest A g (sp + 4704#64) vn ∗ F)
    (hnext : ∀ s1 : State,
      s1.pc = spqrSendPlacedEntry + 5136#64 → s1.status = .Running → s1.sp = sp →
      s1.trace = s.trace →
      s1.readReg64 .x8 = BitVec.ofNat 64 (bytesFieldEncodedLen vn.authKey) →
      s1.readReg64 .x19 = s.readReg64 .x19 → s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = s.readReg64 .x21 → s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = s.readReg64 .x23 → s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = vn.direction.signExtend 64 →
      s1.readReg64 .x26 = BitVec.ofNat 64 vn.authKey.length →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .fp = s.readReg64 .fp → StepInv s0 s1 → VmPreserved s s1 →
      SepWPp (spqrSendPlacedProg ext) ret s1
        (versionNegotiationRest A g (sp + 4704#64) vn ∗ F) Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP; dsimp only [versionNegotiationRest]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  obtain ⟨hbeqz, hbnez⟩ := ofNat_length_beq_zero_of_lt hlen
  cases hemp : vn.authKey.isEmpty
  · have hstep := bv_bytesField_nonempty hemp
    simp only [hemp, Bool.not_false] at hbeqz hbnez
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 5136#64); wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hinv
    refine SepWPp.weaken_pre
      (by dsimp only [versionNegotiationRest]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
          exact Entails.of_eq (by sep_ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv.1) hinv.2)
  · simp only [hemp, Bool.not_true] at hbeqz hbnez
    have hzero : bytesFieldEncodedLen vn.authKey = 0 := by unfold bytesFieldEncodedLen; simp [hemp]
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 5136#64); wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hinv
    refine SepWPp.weaken_pre
      (by dsimp only [versionNegotiationRest]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
          exact Entails.of_eq (by sep_ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, hzero, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv.1) hinv.2)

/-- Step `spqrSendPlacedEntry + 5136#64 .. spqrSendPlacedEntry + 5180#64`: computes
`x9 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.direction)` and loads `x24 = vn.minVersion.signExtend 64`. -/
theorem step_send_vn_dir_len_31c6c_placed (A : RustAlloc)
    (ext : String → Option (State → State))
    (sp : BitVec 64) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB)
    (halign : sp &&& 15#64 = 0#64)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 5136#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hx25 : s.readReg64 .x25 = vn.direction.signExtend 64)
    (hinv0 : StepInv s0 s) (hP : P = versionNegotiationRest A g (sp + 4704#64) vn ∗ F)
    (hnext : ∀ s1 : State,
      s1.pc = spqrSendPlacedEntry + 5180#64 → s1.status = .Running → s1.sp = sp →
      s1.trace = s.trace →
      s1.readReg64 .x8 = s.readReg64 .x8 →
      s1.readReg64 .x9 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.direction) →
      s1.readReg64 .x19 = s.readReg64 .x19 → s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = s.readReg64 .x21 → s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = vn.minVersion.signExtend 64 →
      s1.readReg64 .x25 = vn.direction.signExtend 64 →
      s1.readReg64 .x26 = s.readReg64 .x26 → s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 → s1.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 s1 → VmPreserved s s1 →
      SepWPp (spqrSendPlacedProg ext) ret s1
        (versionNegotiationRest A g (sp + 4704#64) vn ∗ F) Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP; dsimp only [versionNegotiationRest]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hw25 : s.readReg32 .x25 = vn.direction := by
    simp only [State.readReg32, hx25, sext64_truncate32]
  by_cases hdir : vn.direction = 0#32
  · have hdir_eq : i32VarintFieldEncodedLen vn.direction = 0 := by
      simp [i32VarintFieldEncodedLen, hdir]
    have hbeq_d : (vn.direction == 0#32) = true := beq_iff_eq.mpr hdir
    have hbne_d : (vn.direction != 0#32) = false := by simp [hdir]
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 5180#64); wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hinv
    refine SepWPp.weaken_pre
      (by dsimp only [versionNegotiationRest]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
          exact Entails.of_eq (by sep_ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, hdir_eq, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hinv0.trans hinv.1) hinv.2)
  · have hbeq_d : (vn.direction == 0#32) = false := beq_eq_false_iff_ne.mpr hdir
    have hbne_d : (vn.direction != 0#32) = true := bne_iff_ne.mpr hdir
    have hstep_d := bv_i32VarintField_nonzero hdir
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 5180#64); wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hinv
    refine SepWPp.weaken_pre
      (by dsimp only [versionNegotiationRest]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
          exact Entails.of_eq (by sep_ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hinv0.trans hinv.1) hinv.2)

/-- Step `spqrSendPlacedEntry + 5180#64 .. spqrSendPlacedEntry + 5220#64`: computes
`x10 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.minVersion)`. -/
theorem step_send_vn_minVer_len_31c98_placed
    (ext : String → Option (State → State))
    (vn : VersionNegotiationPB)
    {s0 s : State} {ret : BitVec 64} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 5180#64) (hrun : s.status = .Running)
    (hx24 : s.readReg64 .x24 = vn.minVersion.signExtend 64)
    (hinv0 : StepInv s0 s)
    (hnext : ∀ s1 : State,
      s1.pc = spqrSendPlacedEntry + 5220#64 → s1.status = .Running → s1.sp = s.sp →
      s1.trace = s.trace →
      s1.readReg64 .x8 = s.readReg64 .x8 → s1.readReg64 .x9 = s.readReg64 .x9 →
      s1.readReg64 .x10 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.minVersion) →
      s1.readReg64 .x19 = s.readReg64 .x19 → s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = s.readReg64 .x21 → s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = vn.minVersion.signExtend 64 →
      s1.readReg64 .x25 = s.readReg64 .x25 → s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .fp = s.readReg64 .fp → StepInv s0 s1 → VmPreserved s s1 →
      SepWPp (spqrSendPlacedProg ext) ret s1 P Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  have hw24 : s.readReg32 .x24 = vn.minVersion := by
    simp only [State.readReg32, hx24, sext64_truncate32]
  by_cases hmv : vn.minVersion = 0#32
  · have hmv_eq : i32VarintFieldEncodedLen vn.minVersion = 0 := by
      simp [i32VarintFieldEncodedLen, hmv]
    have hbeq_m : (vn.minVersion == 0#32) = true := beq_iff_eq.mpr hmv
    have hbne_m : (vn.minVersion != 0#32) = false := by simp [hmv]
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 5220#64); wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hinv
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hmv_eq, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv.1) hinv.2
  · have hbeq_m : (vn.minVersion == 0#32) = false := beq_eq_false_iff_ne.mpr hmv
    have hbne_m : (vn.minVersion != 0#32) = true := bne_iff_ne.mpr hmv
    have hstep_m := bv_i32VarintField_nonzero hmv
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 5220#64); wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hinv
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv.1) hinv.2

/-- Step `spqrSendPlacedEntry + 5220#64 .. spqrSendPlacedEntry + 5348#64`: computes
`x0 = BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn)`, sets `x1 = sp + 1424#64` and
`x22 = (optChainParamsTag vn.chainParams).zeroExtend 64`, and steps `bl encode_varint [local#4]` to
`lsmpl.base 451` with `lr = spqrSendPlacedEntry + 5352#64`. -/
theorem step_send_vn_chainParams_len_31cc0_placed (A : RustAlloc)
    (ext : String → Option (State → State))
    (sp : BitVec 64) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB)
    (halign : sp &&& 15#64 = 0#64)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 5220#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (bytesFieldEncodedLen vn.authKey))
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.direction))
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.minVersion))
    (hinv0 : StepInv s0 s)
    (hP : P = versionNegotiationRest A g (sp + 4704#64) vn ∗ F)
    (hnext : ∀ s1 : State,
      s1.pc = lsmpl.base 451 → s1.status = .Running → s1.sp = sp → s1.trace = s.trace →
      s1.readReg64 .x0 = BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn) →
      s1.readReg64 .x1 = sp + 1424#64 →
      s1.readReg64 .lr = spqrSendPlacedEntry + 5352#64 →
      s1.readReg64 .x19 = s.readReg64 .x19 → s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = (optChainParamsTag vn.chainParams).zeroExtend 64 →
      s1.readReg64 .x23 = s.readReg64 .x23 → s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 → s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .fp = s.readReg64 .fp → StepInv s0 s1 → VmPreserved s s1 →
      SepWPp (spqrSendPlacedProg ext) ret s1
        (versionNegotiationRest A g (sp + 4704#64) vn ∗ F) Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP; dsimp only [versionNegotiationRest]
  cases hcp : vn.chainParams with
  | none =>
    dsimp only [optChainParamsPBAt, optChainParamsTag]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    have hcomb := bv_versionNegLen_none_combine vn hcp
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 451); wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hinv
    refine SepWPp.weaken_pre
      (by dsimp only [versionNegotiationRest]; rw [hcp]; dsimp only [optChainParamsPBAt]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]; exact Entails.of_eq (by sep_ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by rw [← hcomb]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by rw [hcp]; simp only [optChainParamsTag, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hinv0.trans hinv.1) hinv.2)
  | some cp =>
    simp only [optChainParamsPBAt, chainParamsPBAt, BitVec.add_assoc, BitVec.reduceAdd]
    have hcomb := bv_versionNegLen_some_combine vn
    by_cases hmj : cp.maxJump = 0#32 <;> by_cases hmo : cp.maxOooKeys = 0#32
    · have hmj_eq : u32VarintFieldEncodedLen cp.maxJump = 0 := by
        simp [u32VarintFieldEncodedLen, hmj]
      have hmo_eq : u32VarintFieldEncodedLen cp.maxOooKeys = 0 := by
        simp [u32VarintFieldEncodedLen, hmo]
      have hbeq_mj : (cp.maxJump == 0#32) = true := beq_iff_eq.mpr hmj
      have hbne_mj : (cp.maxJump != 0#32) = false := by simp [hmj]
      have hbeq_mo : (cp.maxOooKeys == 0#32) = true := beq_iff_eq.mpr hmo
      have hbne_mo : (cp.maxOooKeys != 0#32) = false := by simp [hmo]
      dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 451); wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *]); intro hinv
      refine SepWPp.weaken_pre
        (by dsimp only [versionNegotiationRest]; rw [hcp]
            simp only [optChainParamsPBAt, chainParamsPBAt, BitVec.add_assoc, BitVec.reduceAdd]
            exact Entails.of_eq (by sep_ac_rfl))
        (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by rw [← hcomb, hcp, ← bv_optChainParams_some_combine]; simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by rw [hcp]; simp only [optChainParamsTag, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv0.trans hinv.1) hinv.2)
    · have hmj_eq : u32VarintFieldEncodedLen cp.maxJump = 0 := by
        simp [u32VarintFieldEncodedLen, hmj]
      have hbeq_mj : (cp.maxJump == 0#32) = true := beq_iff_eq.mpr hmj
      have hbne_mj : (cp.maxJump != 0#32) = false := by simp [hmj]
      have hbeq_mo : (cp.maxOooKeys == 0#32) = false := beq_eq_false_iff_ne.mpr hmo
      have hbne_mo : (cp.maxOooKeys != 0#32) = true := bne_iff_ne.mpr hmo
      have hstep_mo := bv_u32VarintField_nonzero hmo
      dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 451); wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *]); intro hinv
      refine SepWPp.weaken_pre
        (by dsimp only [versionNegotiationRest]; rw [hcp]
            simp only [optChainParamsPBAt, chainParamsPBAt, BitVec.add_assoc, BitVec.reduceAdd]
            exact Entails.of_eq (by sep_ac_rfl))
        (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by rw [← hcomb, hcp, ← bv_optChainParams_some_combine]; simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by rw [hcp]; simp only [optChainParamsTag, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv0.trans hinv.1) hinv.2)
    · have hmo_eq : u32VarintFieldEncodedLen cp.maxOooKeys = 0 := by
        simp [u32VarintFieldEncodedLen, hmo]
      have hbeq_mj : (cp.maxJump == 0#32) = false := beq_eq_false_iff_ne.mpr hmj
      have hbne_mj : (cp.maxJump != 0#32) = true := bne_iff_ne.mpr hmj
      have hstep_mj := bv_chainParams_maxJump_nonzero hmj
      have hbeq_mo : (cp.maxOooKeys == 0#32) = true := beq_iff_eq.mpr hmo
      have hbne_mo : (cp.maxOooKeys != 0#32) = false := by simp [hmo]
      dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 451); wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *]); intro hinv
      refine SepWPp.weaken_pre
        (by dsimp only [versionNegotiationRest]; rw [hcp]
            simp only [optChainParamsPBAt, chainParamsPBAt, BitVec.add_assoc, BitVec.reduceAdd]
            exact Entails.of_eq (by sep_ac_rfl))
        (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by rw [← hcomb, hcp, ← bv_optChainParams_some_combine]; simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by rw [hcp]; simp only [optChainParamsTag, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv0.trans hinv.1) hinv.2)
    · have hbeq_mj : (cp.maxJump == 0#32) = false := beq_eq_false_iff_ne.mpr hmj
      have hbne_mj : (cp.maxJump != 0#32) = true := bne_iff_ne.mpr hmj
      have hstep_mj := bv_chainParams_maxJump_nonzero hmj
      have hbeq_mo : (cp.maxOooKeys == 0#32) = false := beq_eq_false_iff_ne.mpr hmo
      have hbne_mo : (cp.maxOooKeys != 0#32) = true := bne_iff_ne.mpr hmo
      have hstep_mo := bv_u32VarintField_nonzero hmo
      dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 451); wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *]); intro hinv
      refine SepWPp.weaken_pre
        (by dsimp only [versionNegotiationRest]; rw [hcp]
            simp only [optChainParamsPBAt, chainParamsPBAt, BitVec.add_assoc, BitVec.reduceAdd]
            exact Entails.of_eq (by sep_ac_rfl))
        (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by rw [← hcomb, hcp, ← bv_optChainParams_some_combine]; simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by rw [hcp]; simp only [optChainParamsTag, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv0.trans hinv.1) hinv.2)

/-! ## 3. Budget-Threaded `authKey` Field-Encoding Sub-Steps (`+5352 .. +5472`) -/

/-- Step `spqrSendPlacedEntry + 5352#64 .. spqrSendPlacedEntry + 5472#64`: encodes `vn.authKey`
(`encodeBytesField 1#32 vn.authKey`) under stack-bounded `memcpy`. -/
theorem step_send_vn_encode_authKey_31d44_4k_placed {resStack : Nat} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (σ0 : M.σ)
    (ext : String → Option (State → State))
    {s0 s : State}
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy")
      (withStepInv s0 (withStack etvMemcpyRegionSpec (encodeToVecCalleeStackOf resStack))))
    (sp cap ptr v0 : BitVec 64) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB)
    (bs : List (BitVec 8))
    (hlen : vn.authKey.length < 2 ^ 64)
    (hfit : bs.length + (encodeBytesField 1#32 vn.authKey).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 5352#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (htr : s.trace = s0.trace)
    (hx22 : s.readReg64 .x22 = (optChainParamsTag vn.chainParams).zeroExtend 64)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 vn.authKey.length)
    (hx28 : s.readReg64 .x28 = sp + 4192#64)
    (hinv0 : StepInv s0 s)
    (hP : P = (versionNegotiationRest A.repAlloc g (sp + 4704#64) vn ∗
      vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗ A.pool lim σ0 s ∗
      stackAt sp (encodeToVecCalleeStackOf resStack) ∗
      (sp ↦₆₄ v0)) ∗ F)
    (hnext : ∀ (sm : State) (w0 : BitVec 64),
      sm.pc = spqrSendPlacedEntry + 5472#64 → sm.status = .Running → sm.sp = sp →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x22 = (optChainParamsTag vn.chainParams).zeroExtend 64 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x24 = s.readReg64 .x24 →
      sm.readReg64 .x25 = s.readReg64 .x25 → sm.readReg64 .x27 = s.readReg64 .x27 →
      sm.readReg64 .x28 = sp + 4192#64 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((versionNegotiationRest A.repAlloc g (sp + 4704#64) vn ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ encodeBytesField 1#32 vn.authKey) ∗
          A.pool lim σ0 sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗
          (sp ↦₆₄ w0)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP
  obtain ⟨hbeqz, hbnez⟩ := ofNat_length_beq_zero_of_lt hlen
  cases hemp : vn.authKey.isEmpty
  · simp only [hemp, Bool.not_false] at hbeqz hbnez
    have h1432 : (sp + 1424#64) + 8#64 = sp + 1432#64 := by bv_omega
    have h1440 : (sp + 1424#64) + 16#64 = sp + 1440#64 := by bv_omega
    have h4712 : (sp + 4704#64) + 8#64 = sp + 4712#64 := by bv_omega
    have h4720 : (sp + 4704#64) + 16#64 = sp + 4720#64 := by bv_omega
    have h4192 : (sp + 4096#64) + 96#64 = sp + 4192#64 := by bv_omega
    have hw22 : s.readReg32 .x22 = optChainParamsTag vn.chainParams := by
      simp only [State.readReg32, hx22, zext64_truncate32]
    have hpos_ak : 0 < vn.authKey.length :=
      List.length_pos_of_ne_nil (List.isEmpty_eq_false_iff.mp hemp)
    have hne_ak : vn.authKey ≠ [] := List.isEmpty_eq_false_iff.mp hemp
    have henc_eq : encodeBytesField 1#32 vn.authKey =
        [0x0a#8] ++ encodeVarint (BitVec.ofNat 64 vn.authKey.length) ++ vn.authKey := by
      rw [encodeBytesField_1_eq, hemp]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hfit_all :
        bs.length + 1 + (encodeVarint (BitVec.ofNat 64 vn.authKey.length)).length +
          vn.authKey.length ≤ cap.toNat := by
      rw [henc_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit; omega
    have hlt_tag : bs.length < cap.toNat := by omega
    refine sepWPp_extract_vecU8At_bounds (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := bs)
      (F := versionNegotiationRest A.repAlloc g (sp + 4704#64) vn ∗ A.pool lim σ0 s ∗
        stackAt sp (encodeToVecCalleeStackOf resStack) ∗
        (sp ↦₆₄ v0) ∗ F) (by sep_ac_rfl) fun _ hcap hptr => ?_
    refine sepWPp_extract_pure
      (vn.authKey.length ≤ g.authKey.cap.toNat ∧ g.authKey.cap.toNat < 2 ^ 63)
      (fun R' hm => by
        dsimp only [versionNegotiationRest] at hm
        have hm' : s.mem ⊨ vecU8Buf A.repAlloc g.authKey.cap g.authKey.ptr vn.authKey ∗
            (((sp + 4704#64 + 8#64) ↦₆₄ g.authKey.ptr) ∗
             ((sp + 4704#64 + 16#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
             optChainParamsPBAt (sp + 4704#64 + 24#64) vn.chainParams ∗
             ((sp + 4704#64 + 36#64) ↦₃₂ vn.direction) ∗
             ((sp + 4704#64 + 40#64) ↦₃₂ vn.minVersion) ∗
             memRegion (sp + 4704#64 + 44#64) 4 ∗
             vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗ A.pool lim σ0 s ∗
             stackAt sp (encodeToVecCalleeStackOf resStack) ∗
             (sp ↦₆₄ v0) ∗ F ∗ R') := by
          convert hm using 1; sep_ac_rfl
        exact vecU8Buf_bounds hm')
      fun ⟨hak_le, hak_cap⟩ => ?_
    have hcmp_tag := cap_beq_len_false_of_lt hlt_tag hcap
    refine sepWPp_split_pointsTo64 sp v0
      (vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗
        versionNegotiationRest A.repAlloc g (sp + 4704#64) vn ∗ A.pool lim σ0 s ∗
        stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
      (by sep_ac_rfl) fun v0_lo v0_hi => ?_
    rw [vecU8At_expose_one A.repAlloc (sp + 1424#64) cap ptr bs hlt_tag hcap hptr, h1432, h1440]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    dsimp only [versionNegotiationRest]
    rw [h4712, h4720]
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 451)
    by_vm_steps
      wp_steps
      apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv1
      have hpack_tag := vecU8At_pack_one A.repAlloc (sp + 1424#64) cap ptr bs 0x0a#8
        hlt_tag hcap hptr
      simp only [arm64_norm, h1432, h1440] at hpack_tag
      refine step_send_encode_varint_call_placed A lim σ0 hvarint
        (BitVec.ofNat 64 vn.authKey.length) (sp + 1424#64) cap ptr sp
        (spqrSendPlacedEntry + 5412#64) (bs ++ [0x0a#8])
        (by simp only [List.length_append, List.length_singleton]; omega)
        (F := versionNegotiationRest A.repAlloc g (sp + 4704#64) vn ∗ (sp ↦₃₂ v0_lo) ∗
          ((sp + 4#64) ↦₃₂ optChainParamsTag vn.chainParams) ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1)
        (by rw [A.pool_of_vmPreserved hinv1.2, ← hpack_tag]
            dsimp only [versionNegotiationRest]; rw [h4712, h4720]; sep_ac_rfl) ?_
      intro s1 hpcs1 hruns1 hsps1 htrs1 hcss1 hinv_s1
      rcases hcss1 with ⟨hs1_19, hs1_20, hs1_21, hs1_22, hs1_23, hs1_24, hs1_25,
        hs1_26, hs1_27, hs1_28, hs1_fp, _⟩
      simp only [arm64_norm, hx26]
        at hs1_19 hs1_20 hs1_21 hs1_22 hs1_23 hs1_24 hs1_25 hs1_26 hs1_27 hs1_28 hs1_fp
      let bs1 := (bs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 vn.authKey.length)
      have hfit_mc : bs1.length + vn.authKey.length ≤ cap.toNat := by
        dsimp only [bs1]; simp only [List.length_append, List.length_singleton]; omega
      have hcmp_mc := elem_len_ult_spare_false_of_le hfit_mc hcap
      rw [vecU8At_expose_slice A.repAlloc (sp + 1424#64) cap ptr bs1 vn.authKey.length
        hfit_mc hcap hptr hpos_ak, h1432, h1440]
      dsimp only [versionNegotiationRest]; rw [h4712, h4720]
      rw [vecU8Buf_eq_of_nonempty A.repAlloc g.authKey.cap g.authKey.ptr vn.authKey hemp hak_le]
      dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
      apply sepWPp_of_sepWP_cs_vm (mid := lsρ "memcpy"); wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv2
      have hlen_ak_toNat : (BitVec.ofNat 64 vn.authKey.length).toNat = vn.authKey.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine step_send_memcpy_call_cs_placed A lim σ0 hmemcpy
        (ptr + BitVec.ofNat 64 bs1.length) g.authKey.ptr sp
        (spqrSendPlacedEntry + 5452#64) vn.authKey
        (F := ((sp + 1424#64) ↦₆₄ cap) ∗ ((sp + 1432#64) ↦₆₄ ptr) ∗
          ((sp + 1440#64) ↦₆₄ BitVec.ofNat 64 bs1.length) ∗
          A.repAlloc.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs1) ∗
          memRegion (ptr + BitVec.ofNat 64 bs1.length + BitVec.ofNat 64 vn.authKey.length)
            (cap.toNat - bs1.length - vn.authKey.length) ∗
          ((sp + 4712#64) ↦₆₄ g.authKey.ptr) ∗
          ((sp + 4720#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
          (⌜vn.authKey.length ≤ g.authKey.cap.toNat ∧
            g.authKey.cap.toNat < 2 ^ 63 ∧ g.authKey.ptr ≠ 0⌝ ∗
            A.repAlloc.live g.authKey.ptr g.authKey.cap.toNat 1 ∗
            memRegion (g.authKey.ptr + BitVec.ofNat 64 vn.authKey.length)
              (g.authKey.cap.toNat - vn.authKey.length)) ∗
          optChainParamsPBAt (sp + 4704#64 + 24#64) vn.chainParams ∗
          ((sp + 4704#64 + 36#64) ↦₃₂ vn.direction) ∗
          ((sp + 4704#64 + 40#64) ↦₃₂ vn.minVersion) ∗
          memRegion (sp + 4704#64 + 44#64) 4 ∗
          (sp ↦₃₂ v0_lo) ∗ ((sp + 4#64) ↦₃₂ optChainParamsTag vn.chainParams) ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, hlen_ak_toNat, *]) (hinv_s1.trans hinv2.1)
        (by rw [A.pool_of_vmPreserved hinv2.2]; sep_ac_rfl) ?_
      intro s2 hpcs2 hruns2 hsps2 htrs2 hvms2 hcss2 hinv_s2
      rcases hcss2 with ⟨hs2_19, hs2_20, hs2_21, hs2_22, hs2_23, hs2_24, hs2_25,
        hs2_26, hs2_27, hs2_28, hs2_fp, _⟩
      simp only [arm64_norm,
        hs1_19, hs1_20, hs1_21, hs1_22, hs1_23, hs1_24, hs1_25, hs1_26, hs1_27, hs1_fp]
        at hs2_19 hs2_20 hs2_21 hs2_22 hs2_23 hs2_24 hs2_25 hs2_26 hs2_27 hs2_28 hs2_fp
      dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
      apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 5472#64)
      by_vm_steps
        wp_steps
        apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv3
        have hpack_mc := vecU8At_pack_slice A.repAlloc (sp + 1424#64) cap ptr bs1 vn.authKey
          hfit_mc hcap hptr hne_ak
        have hbs_eq : bs1 ++ vn.authKey = bs ++ encodeBytesField 1#32 vn.authKey := by
          dsimp only [bs1]; rw [henc_eq]; simp only [List.append_assoc]
        rw [h1432, h1440, hbs_eq] at hpack_mc
        refine sepWPp_merge_pointsTo32 sp v0_lo (optChainParamsTag vn.chainParams)
          (versionNegotiationRest A.repAlloc g (sp + 4704#64) vn ∗
            vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ encodeBytesField 1#32 vn.authKey) ∗
            A.pool lim σ0 s2 ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
          (by rw [← hpack_mc]; dsimp only [versionNegotiationRest]; rw [h4712, h4720]
              rw [vecU8Buf_eq_of_nonempty A.repAlloc g.authKey.cap g.authKey.ptr vn.authKey
                hemp hak_le]
              sep_ac_rfl)
          fun w0 => ?_
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (hnext _ w0
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, h4192, *]) (by simp only [arm64_norm, *])
            (hinv_s2.trans hinv3.1))
        rw [A.pool_of_vmPreserved hinv3.2]; sep_ac_rfl
  · simp only [hemp, Bool.not_true] at hbeqz hbnez
    have henc_nil : encodeBytesField 1#32 vn.authKey = [] := by
      rw [encodeBytesField_1_eq, hemp]; simp only [↓reduceIte]
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 5472#64); wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv
    refine SepWPp.weaken_pre
      (Entails.of_eq (by rw [henc_nil, List.append_nil, A.pool_of_vmPreserved hinv.2]))
      (hnext _ v0
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv.1))

/-- Step `spqrSendPlacedEntry + 5352#64 .. spqrSendPlacedEntry + 5472#64`: encodes `vn.authKey`
(`encodeBytesField 1#32 vn.authKey`). -/
theorem step_send_vn_encode_authKey_31d44_placed {resStack : Nat} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (σ0 : M.σ)
    (ext : String → Option (State → State))
    {s0 s : State}
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") etvMemcpyRegionSpec)
    (sp cap ptr v0 : BitVec 64) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB)
    (bs : List (BitVec 8))
    (hlen : vn.authKey.length < 2 ^ 64)
    (hfit : bs.length + (encodeBytesField 1#32 vn.authKey).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 5352#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (htr : s.trace = s0.trace)
    (hx22 : s.readReg64 .x22 = (optChainParamsTag vn.chainParams).zeroExtend 64)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 vn.authKey.length)
    (hx28 : s.readReg64 .x28 = sp + 4192#64)
    (hinv0 : StepInv s0 s)
    (hP : P = (versionNegotiationRest A.repAlloc g (sp + 4704#64) vn ∗
      vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗ A.pool lim σ0 s ∗
      stackAt sp (encodeToVecCalleeStackOf resStack) ∗
      (sp ↦₆₄ v0)) ∗ F)
    (hnext : ∀ (sm : State) (w0 : BitVec 64),
      sm.pc = spqrSendPlacedEntry + 5472#64 → sm.status = .Running → sm.sp = sp →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x22 = (optChainParamsTag vn.chainParams).zeroExtend 64 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x24 = s.readReg64 .x24 →
      sm.readReg64 .x25 = s.readReg64 .x25 → sm.readReg64 .x27 = s.readReg64 .x27 →
      sm.readReg64 .x28 = sp + 4192#64 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((versionNegotiationRest A.repAlloc g (sp + 4704#64) vn ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ encodeBytesField 1#32 vn.authKey) ∗
          A.pool lim σ0 sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗
          (sp ↦₆₄ w0)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom :=
  step_send_vn_encode_authKey_31d44_4k_placed A lim σ0 ext hvarint
    (subroutine_ok_withStepInv s0 (etvMemcpy_to_withStack_placed _ hmemcpy))
    sp cap ptr v0 g vn bs hlen hfit halign hpc hrun hsp htr hx22 hx26 hx28 hinv0 hP hnext

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesVnEncodePlacedBudgetAux

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesVnEncodePlacedBudgetAux
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhasePlaced
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ChainEncodedLenBase
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesVnEncode
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Phase 3c (`+4996..+5604`): `Option<VersionNegotiation>` Encoding

Threads `RustCliAllocBudget` and `VmPreserved` through the inlined `Option<VersionNegotiation>`
encoding phase (`+4996..+5604`) in Block `427`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesVnEncodePlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open CryptoVerification (LibsignalPlacement libsignalSessionCode lsmpl lsρ)
open CryptoVerification.Cli.SpqrV1.Top.Send (spqrSendPlacedEntry spqrSendPlacedProg)
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalTripleRatchet (withStack)
open CryptoVerification.LibsignalSpqrV1 (ChainParamsPB PqRatchetState VersionNegotiationPB)
open CryptoVerification.LibsignalSpqrV1.Proto
  (encodeBytesField encodeInt32Field encodeMessage encodeOptMessage encodeVarint)
open CryptoVerification.SpqrV1.ProtoRepr
  (VersionNegotiationPBGhost bytesFieldEncodedLen chainParamsPBAt i32VarintFieldEncodedLen
   optChainPBPinnedAt optChainParamsPBAt versionNegotiationPBEncodedLen)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (hwVarintLen_bvShift_eq_ofNat_varintLen_norm hwVarintLen_eq_ofNat_varintLen_norm
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero
   ofNat_countLeadingZeros_32 ofNat_countLeadingZeros_64
   ule_self_64 ule_zero_64 ult_self_64 ult_zero_64
   vecU8Buf zeroExtend64_beq_zero32 zext64_truncate32)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (PqRatchetStatePBGhost StepInv cap_beq_len_false_of_lt
   encodeInt32Field_2_eq encodeInt32Field_3_eq encodeOptMessage_versionNeg_some
   encodeToVecCalleeStackOf encodeVarint_length_pos
   noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
   optChainCap optChainParamsTag optPqRatchetInnerPBPinnedAt
   optVersionNegCap optVersionNegRest optVersionNegotiationPBPinnedAt_eq
   optVersionNegotiationPB_encode_len_le pqRatchetStatePBEncodedLen pqRatchetStatePBPinnedAt
   sext64_truncate32 subroutine_ok_withStepInv vecU8At_expose_one vecU8At_pack_one
   versionNegotiationRest vn_authKey_len_lt_of_state withStepInv)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
  (sepWP_done_tpidr sepWP_done_vm sepWPp_of_sepWP_cs_vm)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
  (encodeChainParamsExactSpecOf encodeVarintExactSpecOf etvMemcpyRegionSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.VersionNegPhasePlacedBudgetAux
  (sepWPp_extract_vecU8At_bounds)

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

/-! ## 1. Re-Exports from `AfterStatesVnEncodePlacedBudgetAux` -/

abbrev step_send_encode_varint_call_placed :=
  @AfterStatesVnEncodePlacedBudgetAux.step_send_encode_varint_call_placed

abbrev step_send_memcpy_call_placed :=
  @AfterStatesVnEncodePlacedBudgetAux.step_send_memcpy_call_placed

abbrev step_send_encode_chainParams_call_placed :=
  @AfterStatesVnEncodePlacedBudgetAux.step_send_encode_chainParams_call_placed

abbrev step_send_memcpy_call_cs_placed :=
  @AfterStatesVnEncodePlacedBudgetAux.step_send_memcpy_call_cs_placed

abbrev etvMemcpy_to_withStack_placed :=
  @AfterStatesVnEncodePlacedBudgetAux.etvMemcpy_to_withStack_placed

abbrev step_send_vn_push_tag_31be0_placed :=
  @AfterStatesVnEncodePlacedBudgetAux.step_send_vn_push_tag_31be0_placed

abbrev step_send_vn_authKey_len_31bf8_placed :=
  @AfterStatesVnEncodePlacedBudgetAux.step_send_vn_authKey_len_31bf8_placed

abbrev step_send_vn_dir_len_31c6c_placed :=
  @AfterStatesVnEncodePlacedBudgetAux.step_send_vn_dir_len_31c6c_placed

abbrev step_send_vn_minVer_len_31c98_placed :=
  @AfterStatesVnEncodePlacedBudgetAux.step_send_vn_minVer_len_31c98_placed

abbrev step_send_vn_chainParams_len_31cc0_placed :=
  @AfterStatesVnEncodePlacedBudgetAux.step_send_vn_chainParams_len_31cc0_placed

abbrev step_send_vn_encode_authKey_31d44_4k_placed :=
  @AfterStatesVnEncodePlacedBudgetAux.step_send_vn_encode_authKey_31d44_4k_placed

abbrev step_send_vn_encode_authKey_31d44_placed :=
  @AfterStatesVnEncodePlacedBudgetAux.step_send_vn_encode_authKey_31d44_placed

/-! ## 2. Remaining Field-Encoding Sub-Steps (`+5472 .. +5604`) -/

/-- Step `spqrSendPlacedEntry + 5472#64 .. spqrSendPlacedEntry + 5524#64`: encodes `vn.direction`
(`encodeInt32Field 2#32 vn.direction`). -/
theorem step_send_vn_encode_dir_31dbc_placed {resStack : Nat} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (σ0 : M.σ)
    (ext : String → Option (State → State))
    {s0 s : State}
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (sp cap ptr : BitVec 64) (vn : VersionNegotiationPB) (bs : List (BitVec 8))
    (hfit : bs.length + (encodeInt32Field 2#32 vn.direction).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 5472#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx25 : s.readReg64 .x25 = vn.direction.signExtend 64) (hinv0 : StepInv s0 s)
    (hP : P = (vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗ A.pool lim σ0 s ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 5524#64 → sm.status = .Running → sm.sp = sp →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x24 = s.readReg64 .x24 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ encodeInt32Field 2#32 vn.direction) ∗
          A.pool lim σ0 sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP
  have h1432 : (sp + 1424#64) + 8#64 = sp + 1432#64 := by bv_omega
  have h1440 : (sp + 1424#64) + 16#64 = sp + 1440#64 := by bv_omega
  have hw25 : s.readReg32 .x25 = vn.direction := by
    simp only [State.readReg32, hx25, sext64_truncate32]
  by_cases hdir : vn.direction = 0#32
  · have hbeq_d : (vn.direction == 0#32) = true := beq_iff_eq.mpr hdir
    have hbne_d : (vn.direction != 0#32) = false := by simp [hdir]
    have henc_nil : encodeInt32Field 2#32 vn.direction = [] := by
      rw [encodeInt32Field_2_eq, hbeq_d]; simp only [↓reduceIte]
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 5524#64); wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv
    refine SepWPp.weaken_pre
      (Entails.of_eq (by rw [henc_nil, List.append_nil, A.pool_of_vmPreserved hinv.2]))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hinv0.trans hinv.1))
  · have hbeq_d : (vn.direction == 0#32) = false := beq_eq_false_iff_ne.mpr hdir
    have hbne_d : (vn.direction != 0#32) = true := bne_iff_ne.mpr hdir
    have henc_eq : encodeInt32Field 2#32 vn.direction =
        [0x10#8] ++ encodeVarint (vn.direction.signExtend 64) := by
      rw [encodeInt32Field_2_eq, hbeq_d]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hvpos := encodeVarint_length_pos (vn.direction.signExtend 64)
    have hfit' : bs.length + 1 + (encodeVarint (vn.direction.signExtend 64)).length ≤ cap.toNat := by
      rw [henc_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit; omega
    have hlt : bs.length < cap.toNat := by omega
    refine sepWPp_extract_vecU8At_bounds (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := bs)
      (F := A.pool lim σ0 s ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F) (by sep_ac_rfl)
      fun _ hcap hptr => ?_
    have hcmp := cap_beq_len_false_of_lt hlt hcap
    rw [vecU8At_expose_one A.repAlloc (sp + 1424#64) cap ptr bs hlt hcap hptr, h1432, h1440]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 451)
    by_vm_steps
      wp_steps
      apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv1
      have hpack := vecU8At_pack_one A.repAlloc (sp + 1424#64) cap ptr bs 0x10#8 hlt hcap hptr
      simp only [arm64_norm, h1432, h1440] at hpack
      refine step_send_encode_varint_call_placed A lim σ0 hvarint
        (vn.direction.signExtend 64) (sp + 1424#64) cap ptr sp
        (spqrSendPlacedEntry + 5524#64) (bs ++ [0x10#8])
        (by simp only [List.length_append, List.length_singleton]; omega) (F := F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1)
        (by rw [A.pool_of_vmPreserved hinv1.2, ← hpack]; rfl) ?_
      intro sm hpcm hrunm hspm htrm hcsm hinv_m
      rcases hcsm with ⟨hm19, hm20, hm21, hm22, hm23, hm24, _, _, hm27, hm28, hmfp, _⟩
      simp only [arm64_norm] at hm19 hm20 hm21 hm22 hm23 hm24 hm27 hm28 hmfp
      refine SepWPp.weaken_pre
        (by rw [henc_eq, ← List.append_assoc]; exact Entails.of_eq (by sep_ac_rfl))
        (hnext sm hpcm hrunm hspm htrm hm19 hm20 hm21 hm22 hm23 hm24 hm27 hm28 hmfp hinv_m)

/-- Step `spqrSendPlacedEntry + 5524#64 .. spqrSendPlacedEntry + 5580#64`: reloads `x25 = v16`
from `[sp + 16#64]` and encodes `vn.minVersion` (`encodeInt32Field 3#32 vn.minVersion`). -/
theorem step_send_vn_encode_minVer_31df0_placed {resStack : Nat} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (σ0 : M.σ)
    (ext : String → Option (State → State))
    {s0 s : State}
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (sp cap ptr v16 : BitVec 64) (vn : VersionNegotiationPB) (bs : List (BitVec 8))
    (hfit : bs.length + (encodeInt32Field 3#32 vn.minVersion).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 5524#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx24 : s.readReg64 .x24 = vn.minVersion.signExtend 64) (hinv0 : StepInv s0 s)
    (hP : P = (vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗ A.pool lim σ0 s ∗
      stackAt sp (encodeToVecCalleeStackOf resStack) ∗
      ((sp + 16#64) ↦₆₄ v16)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 5580#64 → sm.status = .Running → sm.sp = sp →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = v16 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ encodeInt32Field 3#32 vn.minVersion) ∗
          A.pool lim σ0 sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗
          ((sp + 16#64) ↦₆₄ v16)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP
  have h1432 : (sp + 1424#64) + 8#64 = sp + 1432#64 := by bv_omega
  have h1440 : (sp + 1424#64) + 16#64 = sp + 1440#64 := by bv_omega
  have hw24 : s.readReg32 .x24 = vn.minVersion := by
    simp only [State.readReg32, hx24, sext64_truncate32]
  by_cases hmv : vn.minVersion = 0#32
  · have hbeq_m : (vn.minVersion == 0#32) = true := beq_iff_eq.mpr hmv
    have hbne_m : (vn.minVersion != 0#32) = false := by simp [hmv]
    have henc_nil : encodeInt32Field 3#32 vn.minVersion = [] := by
      rw [encodeInt32Field_3_eq, hbeq_m]; simp only [↓reduceIte]
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 5580#64); wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv
    refine SepWPp.weaken_pre
      (Entails.of_eq (by rw [henc_nil, List.append_nil, A.pool_of_vmPreserved hinv.2]))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hinv0.trans hinv.1))
  · have hbeq_m : (vn.minVersion == 0#32) = false := beq_eq_false_iff_ne.mpr hmv
    have hbne_m : (vn.minVersion != 0#32) = true := bne_iff_ne.mpr hmv
    have henc_eq : encodeInt32Field 3#32 vn.minVersion =
        [0x18#8] ++ encodeVarint (vn.minVersion.signExtend 64) := by
      rw [encodeInt32Field_3_eq, hbeq_m]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hvpos := encodeVarint_length_pos (vn.minVersion.signExtend 64)
    have hfit' : bs.length + 1 + (encodeVarint (vn.minVersion.signExtend 64)).length ≤ cap.toNat := by
      rw [henc_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit; omega
    have hlt : bs.length < cap.toNat := by omega
    refine sepWPp_extract_vecU8At_bounds (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := bs)
      (F := A.pool lim σ0 s ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗
        ((sp + 16#64) ↦₆₄ v16) ∗ F) (by sep_ac_rfl)
      fun _ hcap hptr => ?_
    have hcmp := cap_beq_len_false_of_lt hlt hcap
    rw [vecU8At_expose_one A.repAlloc (sp + 1424#64) cap ptr bs hlt hcap hptr, h1432, h1440]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 451)
    by_vm_steps
      wp_steps
      apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv1
      have hpack := vecU8At_pack_one A.repAlloc (sp + 1424#64) cap ptr bs 0x18#8 hlt hcap hptr
      simp only [arm64_norm, h1432, h1440] at hpack
      refine step_send_encode_varint_call_placed A lim σ0 hvarint
        (vn.minVersion.signExtend 64) (sp + 1424#64) cap ptr sp
        (spqrSendPlacedEntry + 5580#64) (bs ++ [0x18#8])
        (by simp only [List.length_append, List.length_singleton]; omega)
        (F := ((sp + 16#64) ↦₆₄ v16) ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1)
        (by rw [A.pool_of_vmPreserved hinv1.2, ← hpack]; sep_ac_rfl) ?_
      intro sm hpcm hrunm hspm htrm hcsm hinv_m
      rcases hcsm with ⟨hm19, hm20, hm21, hm22, hm23, _, hm25, _, hm27, hm28, hmfp, _⟩
      simp only [arm64_norm] at hm19 hm20 hm21 hm22 hm23 hm25 hm27 hm28 hmfp
      refine SepWPp.weaken_pre
        (by rw [henc_eq, ← List.append_assoc]; exact Entails.of_eq (by sep_ac_rfl))
        (hnext sm hpcm hrunm hspm htrm hm19 hm20 hm21 hm22 hm23 hm25 hm27 hm28 hmfp hinv_m)

/-- Step `spqrSendPlacedEntry + 5580#64 .. spqrSendPlacedEntry + 5604#64`: encodes `vn.chainParams`
(`encodeOptMessage ChainParamsPB.encodeRaw 4#32 vn.chainParams`). -/
theorem step_send_vn_encode_chainParams_31e28_placed {resStack : Nat} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (σ0 : M.σ)
    (ext : String → Option (State → State))
    {s0 s : State}
    (hcp_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 453)
      (withStepInv s0 (encodeChainParamsExactSpecOf resStack A lim)))
    (sp cap ptr : BitVec 64) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB)
    (bs : List (BitVec 8))
    (hfit : bs.length + (encodeOptMessage ChainParamsPB.encodeRaw 4#32 vn.chainParams).length ≤
      cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 5580#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx22 : s.readReg64 .x22 = (optChainParamsTag vn.chainParams).zeroExtend 64)
    (hinv0 : StepInv s0 s)
    (hP : P = (versionNegotiationRest A.repAlloc g (sp + 4704#64) vn ∗
      vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗ A.pool lim σ0 s ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 5604#64 → sm.status = .Running → sm.sp = sp →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x25 = s.readReg64 .x25 → sm.readReg64 .x27 = s.readReg64 .x27 →
      sm.readReg64 .x28 = s.readReg64 .x28 → sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((versionNegotiationRest A.repAlloc g (sp + 4704#64) vn ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr
            (bs ++ encodeOptMessage ChainParamsPB.encodeRaw 4#32 vn.chainParams) ∗
          A.pool lim σ0 sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP; dsimp only [versionNegotiationRest]
  cases hcp : vn.chainParams with
  | none =>
    rw [hcp] at hx22
    dsimp only [optChainParamsTag, optChainParamsPBAt, encodeOptMessage] at hx22 ⊢
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 5604#64); wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv
    refine SepWPp.weaken_pre (Entails.of_eq ?_)
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv.1))
    dsimp only [versionNegotiationRest]
    rw [hcp]
    dsimp only [optChainParamsPBAt, encodeOptMessage]
    rw [List.append_nil, A.pool_of_vmPreserved hinv.2]
  | some cp =>
    rw [hcp] at hx22 hfit
    dsimp only [optChainParamsTag, encodeOptMessage] at hx22 hfit
    simp only [optChainParamsPBAt, chainParamsPBAt, BitVec.add_assoc, BitVec.reduceAdd]
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 453); wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv1
    refine step_send_encode_chainParams_call_placed A lim σ0 hcp_call
      4#32 cp (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 5604#64) bs
      (by decide) (by decide) hfit
      (F := ((sp + 4712#64) ↦₆₄ g.authKey.ptr) ∗
        ((sp + 4720#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
        vecU8Buf A.repAlloc g.authKey.cap g.authKey.ptr vn.authKey ∗
        ((sp + 4728#64) ↦₃₂ 1#32) ∗ ((sp + 4732#64) ↦₃₂ cp.maxJump) ∗
        ((sp + 4736#64) ↦₃₂ cp.maxOooKeys) ∗
        ((sp + 4740#64) ↦₃₂ vn.direction) ∗ ((sp + 4744#64) ↦₃₂ vn.minVersion) ∗
        memRegion (sp + 4748#64) 4 ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1)
      (by rw [A.pool_of_vmPreserved hinv1.2]; sep_ac_rfl) ?_
    intro sm hpcm hrunm hspm htrm hcsm hinv_m
    rcases hcsm with ⟨hm19, hm20, hm21, _, hm23, _, hm25, _, hm27, hm28, hmfp, _⟩
    simp only [arm64_norm] at hm19 hm20 hm21 hm23 hm25 hm27 hm28 hmfp
    refine SepWPp.weaken_pre
      (by dsimp only [versionNegotiationRest]; rw [hcp]
          simp only [optChainParamsPBAt, chainParamsPBAt, encodeOptMessage,
            BitVec.add_assoc, BitVec.reduceAdd]
          exact Entails.of_eq (by sep_ac_rfl))
      (hnext sm hpcm hrunm hspm htrm hm19 hm20 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m)

/-! ## 3. Full Phase 3c Theorems (`+4996..+5604`) -/

/-- Step `spqrSendPlacedEntry + 4996#64 / spqrSendPlacedEntry + 5604#64 .. spqrSendPlacedEntry + 5604#64`:
encodes `st.versionNegotiation` under stack-bounded `memcpy` while threading `A.pool lim σ0`. -/
theorem step_send_versionNeg_31be0_4k_placed {resStack : Nat} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (σ0 : M.σ)
    (ext : String → Option (State → State))
    {s0 s : State}
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy")
      (withStepInv s0 (withStack etvMemcpyRegionSpec (encodeToVecCalleeStackOf resStack))))
    (hcp_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 453)
      (withStepInv s0 (encodeChainParamsExactSpecOf resStack A lim)))
    (sp ptr v0 : BitVec 64) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc =
      (if st.versionNegotiation.isSome then spqrSendPlacedEntry + 4996#64
       else spqrSendPlacedEntry + 5604#64))
    (hrun : s.status = .Running) (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx0 : st.versionNegotiation.isSome → s.readReg64 .x0 = ptr)
    (hx25 : s.readReg64 .x25 = optChainCap g.chain st.chain)
    (hx28 : s.readReg64 .x28 = sp + 4192#64)
    (hinv0 : StepInv s0 s)
    (hP : P = (pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) st ∗
      vecU8At A.repAlloc (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr [] ∗
      A.pool lim σ0 s ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗
      (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain)) ∗ F)
    (hnext : ∀ (sm : State) (w0 : BitVec 64),
      sm.pc = spqrSendPlacedEntry + 5604#64 → sm.status = .Running → sm.sp = sp →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x25 = optChainCap g.chain st.chain →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = sp + 4192#64 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) st ∗
          vecU8At A.repAlloc (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr
            (encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 st.versionNegotiation) ∗
          A.pool lim σ0 sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗
          (sp ↦₆₄ w0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP
  cases hvn : st.versionNegotiation with
  | none =>
    rw [hvn] at hpc; simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc
    refine SepWPp.weaken_pre (by rw [hvn]; exact Entails.refl _)
      (hnext s v0 hpc hrun hsp htr rfl rfl rfl rfl hx25 rfl hx28 rfl hinv0)
  | some vn =>
    rw [hvn] at hpc hx0; simp only [Option.isSome_some, ↓reduceIte] at hpc hx0
    have hx0' := hx0 trivial
    let cap := BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)
    have hcap_toNat : cap.toNat = pqRatchetStatePBEncodedLen st := by
      dsimp only [cap]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hvn_len_le :
        (encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 (some vn)).length ≤ cap.toNat := by
      rw [hcap_toNat, ← hvn]; exact optVersionNegotiationPB_encode_len_le st
    rw [encodeOptMessage_versionNeg_some vn] at hvn_len_le
    simp only [List.length_append, List.length_singleton] at hvn_len_le
    have hpos : 0 < cap.toNat := by
      have := encodeVarint_length_pos (BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn)); omega
    have hak_lt : vn.authKey.length < 2 ^ 64 := vn_authKey_len_lt_of_state hvn hlen
    let F_rest : SepProp :=
      ((sp + 4704#64) ↦₆₄ g.vn.authKey.cap) ∗
        optChainPBPinnedAt A.repAlloc g.chain (sp + 4704#64 + 48#64) st.chain ∗
        optPqRatchetInnerPBPinnedAt A.repAlloc g.inner (sp + 4704#64 + 128#64) st.inner ∗ F
    refine step_send_vn_push_tag_31be0_placed A.repAlloc ext sp cap ptr g.vn vn hpos halign
      (F := A.pool lim σ0 s ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗
        (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain) ∗ F_rest)
      hpc hrun hsp hx0' hinv0
      (by unfold pqRatchetStatePBPinnedAt
          rw [hvn, optVersionNegotiationPBPinnedAt_eq A.repAlloc g.vn (sp + 4704#64) (some vn)]
          dsimp only [optVersionNegCap, optVersionNegRest, cap, F_rest]; sep_ac_rfl) ?_
    intro s1 hpcs1 hruns1 hsps1 htrs1 hs1_19 hs1_20 hs1_21 hs1_22 hs1_23 hs1_24 hs1_25 hs1_26
      hs1_27 hs1_28 hs1_fp hinv1 hvm1
    refine step_send_vn_authKey_len_31bf8_placed A.repAlloc ext sp g.vn vn hak_lt halign
      (F := vecU8At A.repAlloc (sp + 1424#64) cap ptr [0x0a#8] ∗ A.pool lim σ0 s ∗
        stackAt sp (encodeToVecCalleeStackOf resStack) ∗
        (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain) ∗ F_rest)
      hpcs1 hruns1 hsps1 hs1_26 hinv1 (by sep_ac_rfl) ?_
    intro s2 hpcs2 hruns2 hsps2 htrs2 hs2_8 hs2_19 hs2_20 hs2_21 hs2_22 hs2_23 hs2_24 hs2_25
      hs2_26 hs2_27 hs2_28 hs2_fp hinv2 hvm2
    refine step_send_vn_dir_len_31c6c_placed A.repAlloc ext sp g.vn vn halign
      (F := vecU8At A.repAlloc (sp + 1424#64) cap ptr [0x0a#8] ∗ A.pool lim σ0 s ∗
        stackAt sp (encodeToVecCalleeStackOf resStack) ∗
        (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain) ∗ F_rest)
      hpcs2 hruns2 hsps2 hs2_25 hinv2 (by sep_ac_rfl) ?_
    intro s3 hpcs3 hruns3 hsps3 htrs3 hs3_8 hs3_9 hs3_19 hs3_20 hs3_21 hs3_22 hs3_23 hs3_24
      hs3_25 hs3_26 hs3_27 hs3_28 hs3_fp hinv3 hvm3
    refine step_send_vn_minVer_len_31c98_placed ext vn hpcs3 hruns3 hs3_24 hinv3 ?_
    intro s4 hpcs4 hruns4 hsps4 htrs4 hs4_8 hs4_9 hs4_10 hs4_19 hs4_20 hs4_21 hs4_22 hs4_23
      hs4_24 hs4_25 hs4_26 hs4_27 hs4_28 hs4_fp hinv4 hvm4
    have hsps4' : s4.sp = sp := by rw [hsps4, hsps3]
    have hs4_8' : s4.readReg64 .x8 = BitVec.ofNat 64 (bytesFieldEncodedLen vn.authKey) := by
      rw [hs4_8, hs3_8, hs2_8]
    have hs4_9' : s4.readReg64 .x9 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.direction) := by
      rw [hs4_9, hs3_9]
    refine step_send_vn_chainParams_len_31cc0_placed A.repAlloc ext sp g.vn vn halign
      (F := vecU8At A.repAlloc (sp + 1424#64) cap ptr [0x0a#8] ∗ A.pool lim σ0 s ∗
        stackAt sp (encodeToVecCalleeStackOf resStack) ∗
        (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain) ∗ F_rest)
      hpcs4 hruns4 hsps4' hs4_8' hs4_9' hs4_10 hinv4 (by sep_ac_rfl) ?_
    intro s5 hpcs5 hruns5 hsps5 htrs5 hs5_0 hs5_1 hs5_lr hs5_19 hs5_20 hs5_21 hs5_22 hs5_23
      hs5_24 hs5_25 hs5_26 hs5_27 hs5_28 hs5_fp hinv5 hvm5
    have htrs5' : s5.trace = s0.trace := by rw [htrs5, htrs4, htrs3, htrs2, htrs1, htr]
    have hvm05 : VmPreserved s s5 := (((hvm1.trans hvm2).trans hvm3).trans hvm4).trans hvm5
    refine step_send_encode_varint_call_placed A lim σ0 hvarint
      (BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn)) (sp + 1424#64) cap ptr sp
      (spqrSendPlacedEntry + 5352#64) [0x0a#8]
      (by simp only [List.length_singleton]; omega)
      (F := versionNegotiationRest A.repAlloc g.vn (sp + 4704#64) vn ∗
        (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain) ∗ F_rest)
      hpcs5 hruns5 hsps5 halign htrs5' hs5_lr hs5_0 hs5_1 hinv5
      (by rw [A.pool_of_vmPreserved hvm05]; sep_ac_rfl) ?_
    intro s6 hpcs6 hruns6 hsps6 htrs6 hcsm6 hinv6
    have hs6_19 : s6.readReg64 .x19 = s.readReg64 .x19 := by
      rw [hcsm6.1, hs5_19, hs4_19, hs3_19, hs2_19, hs1_19]
    have hs6_20 : s6.readReg64 .x20 = s.readReg64 .x20 := by
      rw [hcsm6.2.1, hs5_20, hs4_20, hs3_20, hs2_20, hs1_20]
    have hs6_21 : s6.readReg64 .x21 = s.readReg64 .x21 := by
      rw [hcsm6.2.2.1, hs5_21, hs4_21, hs3_21, hs2_21, hs1_21]
    have hs6_22 : s6.readReg64 .x22 = (optChainParamsTag vn.chainParams).zeroExtend 64 := by
      rw [hcsm6.2.2.2.1, hs5_22]
    have hs6_23 : s6.readReg64 .x23 = s.readReg64 .x23 := by
      rw [hcsm6.2.2.2.2.1, hs5_23, hs4_23, hs3_23, hs2_23, hs1_23]
    have hs6_24 : s6.readReg64 .x24 = vn.minVersion.signExtend 64 := by
      rw [hcsm6.2.2.2.2.2.1, hs5_24, hs4_24]
    have hs6_25 : s6.readReg64 .x25 = vn.direction.signExtend 64 := by
      rw [hcsm6.2.2.2.2.2.2.1, hs5_25, hs4_25, hs3_25]
    have hs6_26 : s6.readReg64 .x26 = BitVec.ofNat 64 vn.authKey.length := by
      rw [hcsm6.2.2.2.2.2.2.2.1, hs5_26, hs4_26, hs3_26, hs2_26]
    have hs6_27 : s6.readReg64 .x27 = s.readReg64 .x27 := by
      rw [hcsm6.2.2.2.2.2.2.2.2.1, hs5_27, hs4_27, hs3_27, hs2_27, hs1_27]
    have hs6_28 : s6.readReg64 .x28 = sp + 4192#64 := by
      rw [hcsm6.2.2.2.2.2.2.2.2.2.1, hs5_28, hs4_28, hs3_28, hs2_28, hs1_28, hx28]
    have hs6_fp : s6.readReg64 .fp = s.readReg64 .fp := by
      rw [hcsm6.2.2.2.2.2.2.2.2.2.2.1, hs5_fp, hs4_fp, hs3_fp, hs2_fp, hs1_fp]
    refine step_send_vn_encode_authKey_31d44_4k_placed A lim σ0 ext hvarint hmemcpy
      sp cap ptr v0 g.vn vn
      ([0x0a#8] ++ encodeVarint (BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn)))
      hak_lt (by simp only [List.length_append, List.length_singleton]; omega) halign
      (F := ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain) ∗ F_rest)
      hpcs6 hruns6 hsps6 htrs6 hs6_22 hs6_26 hs6_28 hinv6 (by sep_ac_rfl) ?_
    intro s7 w0 hpcs7 hruns7 hsps7 htrs7 hs7_19 hs7_20 hs7_21 hs7_22 hs7_23 hs7_24 hs7_25
      hs7_27 hs7_28 hs7_fp hinv7
    rw [hs6_19] at hs7_19; rw [hs6_20] at hs7_20; rw [hs6_21] at hs7_21
    rw [hs6_23] at hs7_23; rw [hs6_24] at hs7_24; rw [hs6_25] at hs7_25
    rw [hs6_27] at hs7_27; rw [hs6_fp] at hs7_fp
    refine step_send_vn_encode_dir_31dbc_placed A lim σ0 ext hvarint sp cap ptr vn
      (([0x0a#8] ++ encodeVarint (BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn))) ++
        encodeBytesField 1#32 vn.authKey)
      (by simp only [List.length_append, List.length_singleton]; omega) halign
      (F := versionNegotiationRest A.repAlloc g.vn (sp + 4704#64) vn ∗ (sp ↦₆₄ w0) ∗
        ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain) ∗ F_rest)
      hpcs7 hruns7 hsps7 htrs7 hs7_25 hinv7 (by sep_ac_rfl) ?_
    intro s8 hpcs8 hruns8 hsps8 htrs8 hs8_19 hs8_20 hs8_21 hs8_22 hs8_23 hs8_24 hs8_27 hs8_28
      hs8_fp hinv8
    rw [hs7_19] at hs8_19; rw [hs7_20] at hs8_20; rw [hs7_21] at hs8_21; rw [hs7_22] at hs8_22
    rw [hs7_23] at hs8_23; rw [hs7_24] at hs8_24; rw [hs7_27] at hs8_27
    rw [hs7_28] at hs8_28; rw [hs7_fp] at hs8_fp
    refine step_send_vn_encode_minVer_31df0_placed A lim σ0 ext hvarint
      sp cap ptr (optChainCap g.chain st.chain) vn
      ((([0x0a#8] ++ encodeVarint (BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn))) ++
        encodeBytesField 1#32 vn.authKey) ++ encodeInt32Field 2#32 vn.direction)
      (by simp only [List.length_append, List.length_singleton]; omega) halign
      (F := versionNegotiationRest A.repAlloc g.vn (sp + 4704#64) vn ∗ (sp ↦₆₄ w0) ∗ F_rest)
      hpcs8 hruns8 hsps8 htrs8 hs8_24 hinv8 (by sep_ac_rfl) ?_
    intro s9 hpcs9 hruns9 hsps9 htrs9 hs9_19 hs9_20 hs9_21 hs9_22 hs9_23 hs9_25 hs9_27 hs9_28
      hs9_fp hinv9
    rw [hs8_19] at hs9_19; rw [hs8_20] at hs9_20; rw [hs8_21] at hs9_21; rw [hs8_22] at hs9_22
    rw [hs8_23] at hs9_23; rw [hs8_27] at hs9_27; rw [hs8_28] at hs9_28; rw [hs8_fp] at hs9_fp
    refine step_send_vn_encode_chainParams_31e28_placed A lim σ0 ext hcp_call sp cap ptr g.vn vn
      (((([0x0a#8] ++ encodeVarint (BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn))) ++
        encodeBytesField 1#32 vn.authKey) ++
        encodeInt32Field 2#32 vn.direction) ++ encodeInt32Field 3#32 vn.minVersion)
      (by simp only [List.length_append, List.length_singleton]; omega) halign
      (F := (sp ↦₆₄ w0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain) ∗ F_rest)
      hpcs9 hruns9 hsps9 htrs9 hs9_22 hinv9 (by sep_ac_rfl) ?_
    intro s10 hpcs10 hruns10 hsps10 htrs10 hs10_19 hs10_20 hs10_21 hs10_23 hs10_25 hs10_27
      hs10_28 hs10_fp hinv10
    rw [hs9_19] at hs10_19; rw [hs9_20] at hs10_20; rw [hs9_21] at hs10_21; rw [hs9_23] at hs10_23
    rw [hs9_25] at hs10_25; rw [hs9_27] at hs10_27; rw [hs9_28] at hs10_28; rw [hs9_fp] at hs10_fp
    refine SepWPp.weaken_pre ?_
      (hnext s10 w0 hpcs10 hruns10 hsps10 htrs10
        hs10_19 hs10_20 hs10_21 hs10_23 hs10_25 hs10_27 hs10_28 hs10_fp hinv10)
    unfold pqRatchetStatePBPinnedAt
    rw [hvn, optVersionNegotiationPBPinnedAt_eq A.repAlloc g.vn (sp + 4704#64) (some vn),
      encodeOptMessage_versionNeg_some vn]
    dsimp only [optVersionNegCap, optVersionNegRest, cap, F_rest]
    simp only [List.append_assoc]
    exact Entails.of_eq (by sep_ac_rfl)

theorem step_send_versionNeg_31be0_ext_placed {resStack : Nat} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (σ0 : M.σ)
    (ext : String → Option (State → State))
    {s0 s : State}
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy")
      (withStack etvMemcpyRegionSpec (encodeToVecCalleeStackOf resStack)))
    (hcp_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 453)
      (withStepInv s0 (encodeChainParamsExactSpecOf resStack A lim)))
    (sp ptr v0 : BitVec 64) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc =
      (if st.versionNegotiation.isSome then spqrSendPlacedEntry + 4996#64
       else spqrSendPlacedEntry + 5604#64))
    (hrun : s.status = .Running) (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx0 : st.versionNegotiation.isSome → s.readReg64 .x0 = ptr)
    (hx25 : s.readReg64 .x25 = optChainCap g.chain st.chain)
    (hx28 : s.readReg64 .x28 = sp + 4192#64)
    (hinv0 : StepInv s0 s)
    (hP : P = (pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) st ∗
      vecU8At A.repAlloc (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr [] ∗
      A.pool lim σ0 s ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗
      (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain)) ∗ F)
    (hnext : ∀ (sm : State) (w0 : BitVec 64),
      sm.pc = spqrSendPlacedEntry + 5604#64 → sm.status = .Running → sm.sp = sp →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x25 = optChainCap g.chain st.chain →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = sp + 4192#64 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) st ∗
          vecU8At A.repAlloc (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr
            (encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 st.versionNegotiation) ∗
          A.pool lim σ0 sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗
          (sp ↦₆₄ w0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom :=
  step_send_versionNeg_31be0_4k_placed A lim σ0 ext hvarint
    (subroutine_ok_withStepInv s0 hmemcpy) hcp_call sp ptr v0 g st hlen halign
    hpc hrun hsp htr hx0 hx25 hx28 hinv0 hP hnext

/-- Step `spqrSendPlacedEntry + 4996#64 / spqrSendPlacedEntry + 5604#64 .. spqrSendPlacedEntry + 5604#64`:
encodes `st.versionNegotiation` into
`vecU8At A.repAlloc (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr
  (encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 st.versionNegotiation)`
while threading `A.pool lim σ0`. -/
theorem step_send_versionNeg_31be0_placed {resStack : Nat} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (σ0 : M.σ)
    (ext : String → Option (State → State))
    {s0 s : State}
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") etvMemcpyRegionSpec)
    (hcp_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 453)
      (withStepInv s0 (encodeChainParamsExactSpecOf resStack A lim)))
    (sp ptr v0 : BitVec 64) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc =
      (if st.versionNegotiation.isSome then spqrSendPlacedEntry + 4996#64
       else spqrSendPlacedEntry + 5604#64))
    (hrun : s.status = .Running) (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx0 : st.versionNegotiation.isSome → s.readReg64 .x0 = ptr)
    (hx25 : s.readReg64 .x25 = optChainCap g.chain st.chain)
    (hx28 : s.readReg64 .x28 = sp + 4192#64)
    (hinv0 : StepInv s0 s)
    (hP : P = (pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) st ∗
      vecU8At A.repAlloc (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr [] ∗
      A.pool lim σ0 s ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗
      (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain)) ∗ F)
    (hnext : ∀ (sm : State) (w0 : BitVec 64),
      sm.pc = spqrSendPlacedEntry + 5604#64 → sm.status = .Running → sm.sp = sp →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x25 = optChainCap g.chain st.chain →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = sp + 4192#64 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) st ∗
          vecU8At A.repAlloc (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr
            (encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 st.versionNegotiation) ∗
          A.pool lim σ0 sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗
          (sp ↦₆₄ w0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom :=
  step_send_versionNeg_31be0_ext_placed A lim σ0 ext hvarint
    (etvMemcpy_to_withStack_placed _ hmemcpy) hcp_call sp ptr v0 g st hlen halign
    hpc hrun hsp htr hx0 hx25 hx28 hinv0 hP hnext

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesVnEncodePlacedBudget

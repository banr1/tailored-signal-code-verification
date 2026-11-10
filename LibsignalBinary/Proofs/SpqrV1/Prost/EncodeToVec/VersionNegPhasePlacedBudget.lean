/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.VersionNegPhasePlacedBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `[LibsignalPlacement]` Phase 2b (`Block 426`, `+580 .. +1212`): `Option<VersionNegotiation>` Encoding

Re-exports the `VersionNegotiationPB` sub-steps from `VersionNegPhasePlacedBudgetAux` and proves
`step_encodeToVec_versionNeg_placed` (`+580/+1212 .. +1212`), threading `A.pool lim σ0`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.VersionNegPhasePlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalSpqrV1 (PqRatchetState VersionNegotiationPB)
open CryptoVerification.LibsignalSpqrV1.Proto
  (encodeBytesField encodeInt32Field encodeOptMessage encodeVarint)
open CryptoVerification.SpqrV1.ProtoRepr
  (bytesFieldEncodedLen i32VarintFieldEncodedLen optChainPBPinnedAt
   versionNegotiationPBEncodedLen)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (PqRatchetStatePBGhost StepInv blkPC_426 blkPl_426
   encodeOptMessage_versionNeg_some encodeToVecCalleeStackOf encodeToVecSavedRegs
   encodeVarint_length_pos optChainCap optChainParamsTag optPqRatchetInnerCap
   optPqRatchetInnerPBPinnedAt optVersionNegCap optVersionNegRest
   optVersionNegotiationPBPinnedAt_eq optVersionNegotiationPB_encode_len_le
   pqRatchetStatePBEncodedLen pqRatchetStatePBPinnedAt
   versionNegotiationRest vn_authKey_len_lt_of_state withStepInv)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
  (encodeChainParamsExactSpecOf encodeVarintExactSpecOf etvMemcpyRegionSpec
   step_etv_encode_varint_call_prog)

/-! ## 1. Re-Exports from `VersionNegPhasePlacedBudgetAux` -/

abbrev step_encodeToVec_vn_push_tag_placed :=
  @VersionNegPhasePlacedBudgetAux.step_encodeToVec_vn_push_tag_placed

abbrev step_encodeToVec_vn_authKey_len_placed :=
  @VersionNegPhasePlacedBudgetAux.step_encodeToVec_vn_authKey_len_placed

abbrev step_encodeToVec_vn_dir_len_placed :=
  @VersionNegPhasePlacedBudgetAux.step_encodeToVec_vn_dir_len_placed

abbrev step_encodeToVec_vn_minVer_len_placed :=
  @VersionNegPhasePlacedBudgetAux.step_encodeToVec_vn_minVer_len_placed

abbrev step_encodeToVec_vn_chainParams_len_placed :=
  @VersionNegPhasePlacedBudgetAux.step_encodeToVec_vn_chainParams_len_placed

abbrev step_encodeToVec_vn_branch_authKey_placed :=
  @VersionNegPhasePlacedBudgetAux.step_encodeToVec_vn_branch_authKey_placed

abbrev step_encodeToVec_vn_encode_authKey_placed :=
  @VersionNegPhasePlacedBudgetAux.step_encodeToVec_vn_encode_authKey_placed

abbrev step_encodeToVec_vn_encode_dir_placed :=
  @VersionNegPhasePlacedBudgetAux.step_encodeToVec_vn_encode_dir_placed

abbrev step_encodeToVec_vn_encode_minVer_placed :=
  @VersionNegPhasePlacedBudgetAux.step_encodeToVec_vn_encode_minVer_placed

abbrev step_encodeToVec_vn_encode_chainParams_placed :=
  @VersionNegPhasePlacedBudgetAux.step_encodeToVec_vn_encode_chainParams_placed

/-! ## 2. Full Phase 2b Theorem: `step_encodeToVec_versionNeg_placed` (`+580/+1212 .. +1212`) -/

theorem step_encodeToVec_versionNeg_placed [LibsignalPlacement] {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (σ0 : M.σ)
    (H : String → Option (State → State))
    {s0 s : State}
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      ((blkPl_426).ρ "memcpy")
      etvMemcpyRegionSpec)
    (hcp_call : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 313)
      (withStepInv s0 (encodeChainParamsExactSpecOf resStack A lim)))
    (sret a sp ptr v0 v1 v2 : BitVec 64) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (if st.versionNegotiation.isSome then (blkPl_426).base + 580#64 else (blkPl_426).base + 1212#64))
    (hrun : s.status = .Running) (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx0 : st.versionNegotiation.isSome → s.readReg64 .x0 = ptr)
    (hx19 : s.readReg64 .x19 = optChainCap g.chain st.chain)
    (hx20 : s.readReg64 .x20 = a) (hx21 : s.readReg64 .x21 = a + 128#64)
    (hx22 : s.readReg64 .x22 = a + 48#64) (hx27 : s.readReg64 .x27 = sret)
    (hx28 : s.readReg64 .x28 = optPqRatchetInnerCap g.inner st.inner)
    (hfp : s.readReg64 .fp = sp - 96#64) (hinv0 : StepInv s0 s)
    (hP : P = (pqRatchetStatePBPinnedAt A.repAlloc g a st ∗
      vecU8At A.repAlloc (sp - 120#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr [] ∗
      A.pool lim σ0 s ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
      ((sp - 144#64) ↦₆₄ v0) ∗ ((sp - 136#64) ↦₆₄ v1) ∗ ((sp - 128#64) ↦₆₄ v2) ∗
      encodeToVecSavedRegs sp s0) ∗ F)
    (hnext : ∀ (sm : State) (w1 w2 : BitVec 64),
      sm.pc = (blkPl_426).base + 1212#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = optChainCap g.chain st.chain → sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = a + 128#64 → sm.readReg64 .x22 = a + 48#64 →
      sm.readReg64 .x27 = sret → sm.readReg64 .x28 = optPqRatchetInnerCap g.inner st.inner →
      sm.readReg64 .fp = sp - 96#64 → StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm
        ((pqRatchetStatePBPinnedAt A.repAlloc g a st ∗
          vecU8At A.repAlloc (sp - 120#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr
            (encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 st.versionNegotiation) ∗
          A.pool lim σ0 sm ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
          ((sp - 144#64) ↦₆₄ v0) ∗ ((sp - 136#64) ↦₆₄ w1) ∗ ((sp - 128#64) ↦₆₄ w2) ∗
          encodeToVecSavedRegs sp s0) ∗ F)
        Q Qp oom) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q Qp oom := by
  subst hP
  cases hvn : st.versionNegotiation with
  | none =>
    rw [hvn] at hpc; simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc
    refine SepWPp.weaken_pre (by rw [hvn]; exact Entails.refl _)
      (hnext s v1 v2 hpc hrun hsp htr hx19 hx20 hx21 hx22 hx27 hx28 hfp hinv0)
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
      (a ↦₆₄ g.vn.authKey.cap) ∗ optChainPBPinnedAt A.repAlloc g.chain (a + 48#64) st.chain ∗
        optPqRatchetInnerPBPinnedAt A.repAlloc g.inner (a + 128#64) st.inner ∗
        ((sp - 144#64) ↦₆₄ v0) ∗ encodeToVecSavedRegs sp s0 ∗ F
    refine step_encodeToVec_vn_push_tag_placed A.repAlloc H a sp cap ptr g.vn vn hpos halign
      (F := A.pool lim σ0 s ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
        ((sp - 136#64) ↦₆₄ v1) ∗ ((sp - 128#64) ↦₆₄ v2) ∗ F_rest)
      hpc hrun hsp hx0' hx20 hinv0
      (by unfold pqRatchetStatePBPinnedAt
          rw [hvn, optVersionNegotiationPBPinnedAt_eq A.repAlloc g.vn a (some vn)]
          dsimp only [optVersionNegCap, optVersionNegRest, cap, F_rest]; sep_ac_rfl) ?_
    intro s1 hpcs1 hruns1 hsps1 htrs1 hs1_19 hs1_20 hs1_21 hs1_22 hs1_25 hs1_27 hs1_28 hs1_fp hinv1 hvm1
    refine step_encodeToVec_vn_authKey_len_placed A.repAlloc H a g.vn vn hak_lt
      (F := vecU8At A.repAlloc (sp - 120#64) cap ptr [0x0a#8] ∗ A.pool lim σ0 s ∗
        stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
        ((sp - 136#64) ↦₆₄ v1) ∗ ((sp - 128#64) ↦₆₄ v2) ∗ F_rest)
      hpcs1 hruns1 hs1_20 hs1_25 hinv1 (by sep_ac_rfl) ?_
    intro s2 hpcs2 hruns2 hsps2 htrs2 hs2_8 hs2_19 hs2_20 hs2_21 hs2_22 hs2_24 hs2_25 hs2_27 hs2_28 hs2_fp hinv2 hvm2
    refine step_encodeToVec_vn_dir_len_placed A.repAlloc H a g.vn vn
      (F := vecU8At A.repAlloc (sp - 120#64) cap ptr [0x0a#8] ∗ A.pool lim σ0 s ∗
        stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
        ((sp - 136#64) ↦₆₄ v1) ∗ ((sp - 128#64) ↦₆₄ v2) ∗ F_rest)
      hpcs2 hruns2 hs2_20 hs2_24 hinv2 (by sep_ac_rfl) ?_
    intro s3 hpcs3 hruns3 hsps3 htrs3 hs3_8 hs3_9 hs3_19 hs3_20 hs3_21 hs3_22 hs3_23 hs3_24 hs3_25 hs3_27 hs3_28 hs3_fp hinv3 hvm3
    refine step_encodeToVec_vn_minVer_len_placed A.repAlloc H a g.vn vn
      (F := vecU8At A.repAlloc (sp - 120#64) cap ptr [0x0a#8] ∗ A.pool lim σ0 s ∗
        stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
        ((sp - 136#64) ↦₆₄ v1) ∗ ((sp - 128#64) ↦₆₄ v2) ∗ F_rest)
      hpcs3 hruns3 hs3_20 hs3_23 hinv3 (by sep_ac_rfl) ?_
    intro s4 hpcs4 hruns4 hsps4 htrs4 hs4_8 hs4_9 hs4_10 hs4_19 hs4_20 hs4_21 hs4_22 hs4_23 hs4_24 hs4_25 hs4_27 hs4_28 hs4_fp hinv4 hvm4
    have hsps4' : s4.sp = sp - 144#64 := by rw [hsps4, hsps3, hsps2, hsps1]
    have hs4_8' : s4.readReg64 .x8 = BitVec.ofNat 64 (bytesFieldEncodedLen vn.authKey) := by rw [hs4_8, hs3_8, hs2_8]
    have hs4_9' : s4.readReg64 .x9 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.direction) := by rw [hs4_9, hs3_9]
    refine step_encodeToVec_vn_chainParams_len_placed A.repAlloc H a sp g.vn vn
      (F := vecU8At A.repAlloc (sp - 120#64) cap ptr [0x0a#8] ∗ A.pool lim σ0 s ∗
        stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
        ((sp - 136#64) ↦₆₄ v1) ∗ ((sp - 128#64) ↦₆₄ v2) ∗ F_rest)
      hpcs4 hruns4 hsps4' hs4_8' hs4_9' hs4_10 hs4_20 hinv4 (by sep_ac_rfl) ?_
    intro s5 hpcs5 hruns5 hsps5 htrs5 hs5_0 hs5_1 hs5_lr hs5_19 hs5_20 hs5_21 hs5_22 hs5_23 hs5_24 hs5_25 hs5_26 hs5_27 hs5_28 hs5_fp hinv5 hvm5
    have htrs5' : s5.trace = s0.trace := by rw [htrs5, htrs4, htrs3, htrs2, htrs1, htr]
    have hvm05 : VmPreserved s s5 := (((hvm1.trans hvm2).trans hvm3).trans hvm4).trans hvm5
    refine step_etv_encode_varint_call_prog A lim σ0 hvarint
      (BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn)) (sp - 120#64) cap ptr sp
      (if vn.chainParams.isSome then (blkPl_426).base + 968#64 else (blkPl_426).base + 924#64) [0x0a#8]
      (by simp only [List.length_singleton]; omega)
      (F := versionNegotiationRest A.repAlloc g.vn a vn ∗
        ((sp - 136#64) ↦₆₄ v1) ∗ ((sp - 128#64) ↦₆₄ v2) ∗ F_rest)
      hpcs5 hruns5 hsps5 halign htrs5' hs5_lr hs5_0 hs5_1 hinv5
      (by rw [A.pool_of_vmPreserved hvm05]; sep_ac_rfl) ?_
    intro s6 hpcs6 hruns6 hsps6 htrs6 hcsm6 hinv6
    have hs6_19 : s6.readReg64 .x19 = optChainCap g.chain st.chain := by
      rw [hcsm6.1, hs5_19, hs4_19, hs3_19, hs2_19, hs1_19, hx19]
    have hs6_20 : s6.readReg64 .x20 = a := by rw [hcsm6.2.1, hs5_20]
    have hs6_21 : s6.readReg64 .x21 = a + 128#64 := by
      rw [hcsm6.2.2.1, hs5_21, hs4_21, hs3_21, hs2_21, hs1_21, hx21]
    have hs6_22 : s6.readReg64 .x22 = a + 48#64 := by
      rw [hcsm6.2.2.2.1, hs5_22, hs4_22, hs3_22, hs2_22, hs1_22, hx22]
    have hs6_23 : s6.readReg64 .x23 = vn.minVersion.signExtend 64 := by rw [hcsm6.2.2.2.2.1, hs5_23, hs4_23]
    have hs6_24 : s6.readReg64 .x24 = vn.direction.signExtend 64 := by rw [hcsm6.2.2.2.2.2.1, hs5_24, hs4_24, hs3_24]
    have hs6_25 : s6.readReg64 .x25 = BitVec.ofNat 64 vn.authKey.length := by
      rw [hcsm6.2.2.2.2.2.2.1, hs5_25, hs4_25, hs3_25, hs2_25]
    have hs6_26 : s6.readReg64 .x26 = (optChainParamsTag vn.chainParams).zeroExtend 64 := by
      rw [hcsm6.2.2.2.2.2.2.2.1, hs5_26]
    have hs6_27 : s6.readReg64 .x27 = sret := by
      rw [hcsm6.2.2.2.2.2.2.2.2.1, hs5_27, hs4_27, hs3_27, hs2_27, hs1_27, hx27]
    have hs6_28 : s6.readReg64 .x28 = optPqRatchetInnerCap g.inner st.inner := by
      rw [hcsm6.2.2.2.2.2.2.2.2.2.1, hs5_28, hs4_28, hs3_28, hs2_28, hs1_28, hx28]
    have hs6_fp : s6.readReg64 .fp = sp - 96#64 := by
      rw [hcsm6.2.2.2.2.2.2.2.2.2.2.1, hs5_fp, hs4_fp, hs3_fp, hs2_fp, hs1_fp, hfp]
    refine step_encodeToVec_vn_branch_authKey_placed H vn hak_lt hpcs6 hruns6 hs6_25 hinv6 ?_
    intro s7 hpcs7 hruns7 hsps7 htrs7 hs7_19 hs7_20 hs7_21 hs7_22 hs7_23 hs7_24 hs7_25 hs7_26 hs7_27 hs7_28 hs7_fp hinv7 hvm7
    rw [hsps6] at hsps7; rw [htrs6] at htrs7
    rw [hs6_19] at hs7_19; rw [hs6_20] at hs7_20; rw [hs6_21] at hs7_21; rw [hs6_22] at hs7_22
    rw [hs6_23] at hs7_23; rw [hs6_24] at hs7_24; rw [hs6_25] at hs7_25
    rw [hs6_26] at hs7_26; rw [hs6_27] at hs7_27; rw [hs6_28] at hs7_28; rw [hs6_fp] at hs7_fp
    refine step_encodeToVec_vn_encode_authKey_placed A lim σ0 H hvarint hmemcpy
      a sp cap ptr v1 v2 g.vn vn
      ([0x0a#8] ++ encodeVarint (BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn)))
      (by simp only [List.length_append, List.length_singleton]; omega) halign
      (F := F_rest) hpcs7 hruns7 hsps7 htrs7 hs7_20 hs7_25 hs7_26 hinv7
      (by rw [A.pool_of_vmPreserved hvm7]; sep_ac_rfl) ?_
    intro s8 w1 w2 hpcs8 hruns8 hsps8 htrs8 hs8_19 hs8_20 hs8_21 hs8_22 hs8_23 hs8_24 hs8_26 hs8_27 hs8_28 hs8_fp hinv8
    rw [hs7_19] at hs8_19; rw [hs7_21] at hs8_21; rw [hs7_22] at hs8_22; rw [hs7_23] at hs8_23
    rw [hs7_24] at hs8_24; rw [hs7_27] at hs8_27; rw [hs7_28] at hs8_28; rw [hs7_fp] at hs8_fp
    refine step_encodeToVec_vn_encode_dir_placed A lim σ0 H hvarint sp cap ptr vn
      (([0x0a#8] ++ encodeVarint (BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn))) ++
        encodeBytesField 1#32 vn.authKey)
      (by simp only [List.length_append, List.length_singleton]; omega) halign
      (F := versionNegotiationRest A.repAlloc g.vn a vn ∗ ((sp - 136#64) ↦₆₄ w1) ∗ ((sp - 128#64) ↦₆₄ w2) ∗ F_rest)
      hpcs8 hruns8 hsps8 htrs8 hs8_24 hinv8 (by sep_ac_rfl) ?_
    intro s9 hpcs9 hruns9 hsps9 htrs9 hs9_19 hs9_20 hs9_21 hs9_22 hs9_23 hs9_26 hs9_27 hs9_28 hs9_fp hinv9
    rw [hs8_19] at hs9_19; rw [hs8_20] at hs9_20; rw [hs8_21] at hs9_21; rw [hs8_22] at hs9_22
    rw [hs8_23] at hs9_23; rw [hs8_26] at hs9_26; rw [hs8_27] at hs9_27
    rw [hs8_28] at hs9_28; rw [hs8_fp] at hs9_fp
    refine step_encodeToVec_vn_encode_minVer_placed A lim σ0 H hvarint sp cap ptr vn
      ((([0x0a#8] ++ encodeVarint (BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn))) ++
        encodeBytesField 1#32 vn.authKey) ++ encodeInt32Field 2#32 vn.direction)
      (by simp only [List.length_append, List.length_singleton]; omega) halign
      (F := versionNegotiationRest A.repAlloc g.vn a vn ∗ ((sp - 136#64) ↦₆₄ w1) ∗ ((sp - 128#64) ↦₆₄ w2) ∗ F_rest)
      hpcs9 hruns9 hsps9 htrs9 hs9_23 hinv9 (by sep_ac_rfl) ?_
    intro s10 hpcs10 hruns10 hsps10 htrs10 hs10_19 hs10_20 hs10_21 hs10_22 hs10_26 hs10_27 hs10_28 hs10_fp hinv10
    rw [hs9_19] at hs10_19; rw [hs9_20] at hs10_20; rw [hs9_21] at hs10_21; rw [hs9_22] at hs10_22
    rw [hs9_26] at hs10_26; rw [hs9_27] at hs10_27; rw [hs9_28] at hs10_28; rw [hs9_fp] at hs10_fp
    refine step_encodeToVec_vn_encode_chainParams_placed A lim σ0 H hcp_call a sp cap ptr g.vn vn
      (((([0x0a#8] ++ encodeVarint (BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn))) ++
        encodeBytesField 1#32 vn.authKey) ++
        encodeInt32Field 2#32 vn.direction) ++ encodeInt32Field 3#32 vn.minVersion)
      (by simp only [List.length_append, List.length_singleton]; omega) halign
      (F := ((sp - 136#64) ↦₆₄ w1) ∗ ((sp - 128#64) ↦₆₄ w2) ∗ F_rest)
      hpcs10 hruns10 hsps10 htrs10 hs10_20 hs10_26 hinv10 (by sep_ac_rfl) ?_
    intro s11 hpcs11 hruns11 hsps11 htrs11 hs11_19 hs11_20 hs11_21 hs11_22 hs11_27 hs11_28 hs11_fp hinv11
    rw [hs10_19] at hs11_19; rw [hs10_21] at hs11_21; rw [hs10_22] at hs11_22; rw [hs10_27] at hs11_27
    rw [hs10_28] at hs11_28; rw [hs10_fp] at hs11_fp
    refine SepWPp.weaken_pre ?_
      (hnext s11 w1 w2 hpcs11 hruns11 hsps11 htrs11 hs11_19 hs11_20 hs11_21 hs11_22 hs11_27 hs11_28 hs11_fp hinv11)
    unfold pqRatchetStatePBPinnedAt
    rw [hvn, optVersionNegotiationPBPinnedAt_eq A.repAlloc g.vn a (some vn), encodeOptMessage_versionNeg_some vn]
    dsimp only [optVersionNegCap, optVersionNegRest, cap, F_rest]
    simp only [List.append_assoc]
    exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.VersionNegPhasePlacedBudget

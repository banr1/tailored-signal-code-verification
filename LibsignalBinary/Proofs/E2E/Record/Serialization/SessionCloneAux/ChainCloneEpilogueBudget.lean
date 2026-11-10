/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.ChainCloneBaseBudget
public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.ChainCloneEpilogue
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Placed.GenLsBlock
import ProofLib.SepLogic.WPp

/-!
# Budget-threaded epilogue and specification lifts for `<Chain as Clone>::clone`

Relocatable `[LibsignalPlacement]` epilogue (`+736..ret`) and lifts from `protoChainCloneSpec` to
`chainCloneSpec` and `senderChainCloneSpec` on block `82`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.ChainCloneEpilogueBudget

open Arm64 ProofLib SepProp
open CryptoGames.Ratchet (clampScalar)
open CryptoGames.LibsignalSession (Crypto PublicKey ReceiverChain SenderChain maxMessageKeys)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E.Record.Placed (blkPl_82 lsProg_82)
open CryptoVerification.RustHeap (allocHookStack vecBuf vecU8Buf)
open CryptoVerification.LibsignalSessionRepr (
  ChainGhost MessageKeyGhost VecPin chainAt messageKeyAt
)
open CryptoVerification.LibsignalTripleRatchetRepr (SenderChainGhost optSenderChainAt)
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone (
  ChainCloneGhost chainCloneStack
)
open CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1 (
  chainAt_eq_protoChainAt clonedChainGhost clonedOptChainKeyBuf
  fold_chainAt_dst fold_stackAt_chainClone
  fp_neg_8 fp_neg_12 fp_neg_24 fp_neg_32 fp_neg_40 fp_neg_48
  fp_neg_8_int fp_neg_12_int fp_neg_24_int fp_neg_32_int fp_neg_40_int fp_neg_48_int
  memRegion_104_eq_slots104 optSenderChainAt_some_eq_chainAt
  protoChainAt savedRegsOnStack spillSlotsExist
)
open CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1.ChainCloneStateSimp (
  readReg32_setMem_setPC_pre readReg32_setPC_pre
  readReg64_setMem_setPC_pre readReg64_setPC_pre
  readReg_setMem_setPC_pre readReg_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget (
  ChainCloneEnv SenderChainCloneEnv chainCloneEvents chainCloneSpec
  senderChainAsProtoGhost senderChainCloneSpec
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.ChainCloneBaseBudget (
  ChainCloneLocal1Ok ChainCloneLocal1Ok_trap
  ProtoChainCloneLocal1Ok ProtoChainCloneLocal1Ok_trap
  SenderChainCloneLocal1Ok SenderChainCloneLocal1Ok_trap
  protoChainCloneSpec
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-! ## Lifts from `protoChainCloneSpec` to `chainCloneSpec` and `senderChainCloneSpec` -/

theorem chainClone_of_protoChainClone_local1_gen
    {M : AllocCostModel} {prog : Program} {entry : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hclone : subroutine_ok prog entry (protoChainCloneSpec M A lim)) :
    subroutine_ok prog entry (chainCloneSpec M A lim) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [chainCloneSpec, chainAt_eq_protoChainAt, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hfits⟩, hmem⟩
  set P_rc : Prop := x.gc.1.srk.bytes.length = 33 ∧ x.gc.1.priv.bytes = []
  change s0.mem ⊨ memRegion x.dst 104 ∗ ⌜P_rc⌝ ∗ protoChainAt A.repAlloc x.gc x.src ∗
    A.pool lim st s0 ∗ stackAt s0.sp chainCloneStack ∗ R at hmem
  have hmem_rearr :
      s0.mem ⊨
        memRegion x.dst 104 ∗ protoChainAt A.repAlloc x.gc x.src ∗
        A.pool lim st s0 ∗ stackAt s0.sp chainCloneStack ∗ (⌜P_rc⌝ ∗ R) := by
    have heq :
        (memRegion x.dst 104 ∗ ⌜P_rc⌝ ∗ protoChainAt A.repAlloc x.gc x.src ∗
          A.pool lim st s0 ∗ stackAt s0.sp chainCloneStack ∗ R) =
        (memRegion x.dst 104 ∗ protoChainAt A.repAlloc x.gc x.src ∗
          A.pool lim st s0 ∗ stackAt s0.sp chainCloneStack ∗ (⌜P_rc⌝ ∗ R)) := by
      ac_rfl
    rwa [← heq]
  have hpre_clone :
      s0.mem ⊨ (protoChainCloneSpec M A lim).pre (x, st) s0 ∗ (⌜P_rc⌝ ∗ R) := by
    simp only [protoChainCloneSpec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hfits⟩, hmem_rearr⟩
  refine hclone.mono_outcome (x, st) (⌜P_rc⌝ ∗ R) s0 hpc hrun hpre_clone hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [protoChainCloneSpec] at hpost
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨htrace, hevs⟩, hmem_f⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hmem_f
    rcases hmem_f with ⟨g', hmem_f⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hmem_f
    rcases hmem_f with ⟨⟨hsrk', hpriv', hkeys'⟩, hmem_f⟩
    have hpure_front :
        sf.mem ⊨
          ⌜P_rc⌝ ∗
          (protoChainAt A.repAlloc (g', x.gc.2) x.dst ∗ protoChainAt A.repAlloc x.gc x.src ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainCloneStack ∗ R) := by
      have heq :
          (protoChainAt A.repAlloc (g', x.gc.2) x.dst ∗ protoChainAt A.repAlloc x.gc x.src ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainCloneStack ∗ ⌜P_rc⌝ ∗ R) =
          (⌜P_rc⌝ ∗
            (protoChainAt A.repAlloc (g', x.gc.2) x.dst ∗ protoChainAt A.repAlloc x.gc x.src ∗
              A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainCloneStack ∗ R)) := by
        ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj] at hpure_front
    rcases hpure_front with ⟨⟨hsrk33, hpriv_nil⟩, hrest_f⟩
    dsimp only [chainCloneSpec]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨evs, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htrace, hevs⟩, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨g', ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hsrk', hpriv', hkeys'⟩, ?_⟩
    rw [chainAt_eq_protoChainAt A.repAlloc (g', x.gc.2) x.dst,
        chainAt_eq_protoChainAt A.repAlloc x.gc x.src]
    have hsrk33' : g'.srk.bytes.length = 33 := by rw [hsrk', hsrk33]
    have hpriv_nil' : g'.priv.bytes = [] := hpriv'.trans hpriv_nil
    set P_rc' : Prop := g'.srk.bytes.length = 33 ∧ g'.priv.bytes = []
    change sf.mem ⊨
      (⌜P_rc'⌝ ∗ protoChainAt A.repAlloc (g', x.gc.2) x.dst) ∗
      (⌜P_rc⌝ ∗ protoChainAt A.repAlloc x.gc x.src) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainCloneStack ∗ R
    have heq2 :
        ((⌜P_rc'⌝ ∗ protoChainAt A.repAlloc (g', x.gc.2) x.dst) ∗
          (⌜P_rc⌝ ∗ protoChainAt A.repAlloc x.gc x.src) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainCloneStack ∗ R) =
        (⌜P_rc'⌝ ∗ (⌜P_rc⌝ ∗
          (protoChainAt A.repAlloc (g', x.gc.2) x.dst ∗ protoChainAt A.repAlloc x.gc x.src ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainCloneStack ∗ R))) := by
      ac_rfl
    rw [heq2, satisfies_pure_sepConj, satisfies_pure_sepConj]
    exact ⟨⟨hsrk33', hpriv_nil'⟩, ⟨hsrk33, hpriv_nil⟩, hrest_f⟩
  · simp only [protoChainCloneSpec, sepConj_assoc] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · simp only [protoChainCloneSpec, sepConj_assoc] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · simp only [protoChainCloneSpec, sepConj_assoc] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

theorem chainClone_of_protoChainClone_trap
    {M : AllocCostModel} {b : BitVec 64} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {abs : String → Option (State → State)}
    (hclone : ProtoChainCloneLocal1Ok_trap M b C A lim abs) :
    ChainCloneLocal1Ok_trap M b C A lim abs :=
  chainClone_of_protoChainClone_local1_gen hclone

theorem chainClone_of_protoChainClone
    {M : AllocCostModel} {b : BitVec 64} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hclone : ProtoChainCloneLocal1Ok M b C A lim ctl abs) :
    ChainCloneLocal1Ok M b C A lim ctl abs :=
  chainClone_of_protoChainClone_local1_gen hclone

theorem senderChainClone_of_chainClone_local1_gen
    {M : AllocCostModel} {prog : Program} {entry : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hclone : subroutine_ok prog entry (protoChainCloneSpec M A lim)) :
    subroutine_ok prog entry (senderChainCloneSpec M A lim) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [senderChainCloneSpec, optSenderChainAt_some_eq_chainAt, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hfits⟩, hmem⟩
  let P_sc : Prop :=
    x.g.priv.bytes = x.sc.ratchetKey.privateKey.bytes.toList ∧
      clampScalar x.sc.ratchetKey.privateKey.bytes = x.sc.ratchetKey.privateKey.bytes ∧
      x.g.srk.bytes.length = 33
  let gc0 : ChainGhost × ReceiverChain := senderChainAsProtoGhost x.g x.sc
  change s0.mem ⊨ memRegion x.dst 104 ∗ ⌜P_sc⌝ ∗ protoChainAt A.repAlloc gc0 x.src ∗
    A.pool lim st s0 ∗ stackAt s0.sp chainCloneStack ∗ R at hmem
  have hmem_rearr :
      s0.mem ⊨
        memRegion x.dst 104 ∗ protoChainAt A.repAlloc gc0 x.src ∗
        A.pool lim st s0 ∗ stackAt s0.sp chainCloneStack ∗ (⌜P_sc⌝ ∗ R) := by
    have heq :
        (memRegion x.dst 104 ∗ ⌜P_sc⌝ ∗ protoChainAt A.repAlloc gc0 x.src ∗
          A.pool lim st s0 ∗ stackAt s0.sp chainCloneStack ∗ R) =
        (memRegion x.dst 104 ∗ protoChainAt A.repAlloc gc0 x.src ∗
          A.pool lim st s0 ∗ stackAt s0.sp chainCloneStack ∗ (⌜P_sc⌝ ∗ R)) := by
      ac_rfl
    rwa [← heq]
  have hpre_clone :
      s0.mem ⊨ (protoChainCloneSpec M A lim).pre (⟨x.dst, x.src, gc0⟩, st) s0 ∗ (⌜P_sc⌝ ∗ R) := by
    simp only [protoChainCloneSpec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hfits⟩, hmem_rearr⟩
  refine hclone.mono_outcome (⟨x.dst, x.src, gc0⟩, st) (⌜P_sc⌝ ∗ R) s0 hpc hrun hpre_clone hsp
    fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [protoChainCloneSpec] at hpost
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨htrace, hevs⟩, hmem_f⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hmem_f
    rcases hmem_f with ⟨g', hmem_f⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hmem_f
    rcases hmem_f with ⟨⟨hsrk', hpriv', hkeys'⟩, hmem_f⟩
    have hkeys_nil : g'.keys = [] := List.eq_nil_of_length_eq_zero hkeys'
    have hpure_front :
        sf.mem ⊨
          ⌜P_sc⌝ ∗
          (protoChainAt A.repAlloc (g', gc0.2) x.dst ∗ protoChainAt A.repAlloc gc0 x.src ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainCloneStack ∗ R) := by
      have heq :
          (protoChainAt A.repAlloc (g', gc0.2) x.dst ∗ protoChainAt A.repAlloc gc0 x.src ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainCloneStack ∗ ⌜P_sc⌝ ∗ R) =
          (⌜P_sc⌝ ∗
            (protoChainAt A.repAlloc (g', gc0.2) x.dst ∗ protoChainAt A.repAlloc gc0 x.src ∗
              A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainCloneStack ∗ R)) := by
        ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj] at hpure_front
    rcases hpure_front with ⟨⟨hpriv_eq, hclamp, hsrk33⟩, hrest_f⟩
    let sg' : SenderChainGhost := ⟨g'.srk, g'.priv, g'.mkCap, g'.mkPtr, g'.ck⟩
    have hg'_eq : g' = ⟨sg'.srk, sg'.priv, sg'.mkCap, sg'.mkPtr, [], sg'.ck⟩ := by
      cases g'; dsimp [sg'] at hkeys_nil ⊢; subst hkeys_nil; rfl
    rw [hg'_eq] at hrest_f
    dsimp only [senderChainCloneSpec]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨evs, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htrace, hevs⟩, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨sg', ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hsrk', hpriv'⟩, ?_⟩
    rw [optSenderChainAt_some_eq_chainAt A.repAlloc x.dst sg' x.sc,
        optSenderChainAt_some_eq_chainAt A.repAlloc x.src x.g x.sc]
    have hpriv'_eq : sg'.priv.bytes = x.sc.ratchetKey.privateKey.bytes.toList :=
      hpriv'.trans hpriv_eq
    have hsrk33' : sg'.srk.bytes.length = 33 :=
      (congrArg List.length hsrk').trans hsrk33
    let P_sc' : Prop :=
      sg'.priv.bytes = x.sc.ratchetKey.privateKey.bytes.toList ∧
        clampScalar x.sc.ratchetKey.privateKey.bytes = x.sc.ratchetKey.privateKey.bytes ∧
        sg'.srk.bytes.length = 33
    let gc' : ChainGhost × ReceiverChain :=
      (⟨sg'.srk, sg'.priv, sg'.mkCap, sg'.mkPtr, [], sg'.ck⟩, gc0.2)
    change sf.mem ⊨
      (⌜P_sc'⌝ ∗ protoChainAt A.repAlloc gc' x.dst) ∗
      (⌜P_sc⌝ ∗ protoChainAt A.repAlloc gc0 x.src) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainCloneStack ∗ R
    have heq2 :
        ((⌜P_sc'⌝ ∗ protoChainAt A.repAlloc gc' x.dst) ∗
          (⌜P_sc⌝ ∗ protoChainAt A.repAlloc gc0 x.src) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainCloneStack ∗ R) =
        (⌜P_sc'⌝ ∗ (⌜P_sc⌝ ∗
          (protoChainAt A.repAlloc gc' x.dst ∗ protoChainAt A.repAlloc gc0 x.src ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainCloneStack ∗ R))) := by
      ac_rfl
    rw [heq2, satisfies_pure_sepConj, satisfies_pure_sepConj]
    exact ⟨⟨hpriv'_eq, hclamp, hsrk33'⟩, ⟨hpriv_eq, hclamp, hsrk33⟩, hrest_f⟩
  · simp only [protoChainCloneSpec, sepConj_assoc] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · simp only [protoChainCloneSpec, sepConj_assoc] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · simp only [protoChainCloneSpec, sepConj_assoc] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

theorem senderChainClone_of_chainClone_trap
    {M : AllocCostModel} {b : BitVec 64} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {abs : String → Option (State → State)}
    (hclone : ProtoChainCloneLocal1Ok_trap M b C A lim abs) :
    SenderChainCloneLocal1Ok_trap M b C A lim abs :=
  senderChainClone_of_chainClone_local1_gen hclone

theorem senderChainClone_of_chainClone
    {M : AllocCostModel} {b : BitVec 64} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hclone : ProtoChainCloneLocal1Ok M b C A lim ctl abs) :
    SenderChainCloneLocal1Ok M b C A lim ctl abs :=
  senderChainClone_of_chainClone_local1_gen hclone

/-! ## Relocatable `[LibsignalPlacement]` epilogue (block `82`) -/

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  fp_neg_48 fp_neg_40 fp_neg_32 fp_neg_24 fp_neg_12 fp_neg_8
  fp_neg_48_int fp_neg_40_int fp_neg_32_int fp_neg_24_int fp_neg_12_int fp_neg_8_int
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
attribute [local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite
  calleeSavedVRegs_writeVReg32_ite isCalleeSavedVReg updateCalleeSavedVRegs

private theorem sepWPp_of_sepWP_vm {prog : Program} {mid ret : BitVec 64}
    {s : State} {Pre : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWP prog mid s Pre
      (fun sm Pm => VmPreserved s sm ∧ (VmPreserved s sm → SepWPp prog ret sm Pm Q Qp))) :
    SepWPp prog ret s Pre Q Qp :=
  SepWPp.of_sepWP (mid := mid) (SepWP.mono h (fun _ _ _ _ ⟨hvm, hk⟩ => hk hvm))

theorem epilogue_post_entails {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (x : ChainCloneGhost) (s0 sf : State)
    (srkPtr' privPtr' mkPtr' x25 x28 v9 v10 v13 : BitVec 64)
    (w27 : BitVec 32) (keys' : List MessageKeyGhost) (ckPin' : VecPin)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : keys'.length = x.gc.2.messageKeys.length)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (htrace : sf.trace = s0.trace) :
    ((x.dst ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
      ((x.dst + 8#64) ↦₆₄ srkPtr') ∗
      ((x.dst + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
      ((x.dst + 24#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
      ((x.dst + 32#64) ↦₆₄ privPtr') ∗
      ((x.dst + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
      ((x.dst + 48#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
      ((x.dst + 56#64) ↦₆₄ mkPtr') ∗
      ((x.dst + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
      ((x.dst + 72#64) ↦₆₄ x25) ∗
      ((x.dst + 80#64) ↦₆₄ x28) ∗
      ((x.dst + 88#64) ↦₆₄ x25) ∗
      ((x.dst + 96#64) ↦₃₂ w27) ∗
      memRegion (x.dst + 100#64) 4 ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
      vecBuf A.repAlloc 104 8 (messageKeyAt A.repAlloc) (BitVec.ofNat 64 x.gc.2.messageKeys.length)
        mkPtr' (keys'.zip x.gc.2.messageKeys) ∗
      clonedOptChainKeyBuf A.repAlloc ckPin' x25 x28 w27 x.gc.2.chainKey ∗
      protoChainAt A.repAlloc x.gc x.src ∗
      A.pool lim (M.stepEvents (chainCloneEvents x.gc) st) sf ∗
      stackAt (s0.sp - 208#64) allocHookStack ∗
      spillSlotsExist s0.sp ∗
      ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
      ((s0.sp - 136#64) ↦₆₄ v9) ∗
      ((s0.sp - 128#64) ↦₆₄ v10) ∗
      ((s0.sp - 104#64) ↦₆₄ v13) ∗
      savedRegsOnStack s0) ⊢
      (protoChainCloneSpec M A lim).post (x, st) s0 sf := by
  unfold protoChainCloneSpec
  dsimp only
  apply Entails.sepExists_right (chainCloneEvents x.gc)
  apply Entails.pure_right ⟨htrace, rfl⟩
  let g' := clonedChainGhost x.gc srkPtr' privPtr'
    (BitVec.ofNat 64 x.gc.2.messageKeys.length) mkPtr' keys' ckPin'
  have hg' :
      ((x.dst ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
        ((x.dst + 8#64) ↦₆₄ srkPtr') ∗
        ((x.dst + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
        ((x.dst + 24#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        ((x.dst + 32#64) ↦₆₄ privPtr') ∗
        ((x.dst + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        ((x.dst + 48#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.dst + 56#64) ↦₆₄ mkPtr') ∗
        ((x.dst + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.dst + 72#64) ↦₆₄ x25) ∗
        ((x.dst + 80#64) ↦₆₄ x28) ∗
        ((x.dst + 88#64) ↦₆₄ x25) ∗
        ((x.dst + 96#64) ↦₃₂ w27) ∗
        memRegion (x.dst + 100#64) 4 ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        vecBuf A.repAlloc 104 8 (messageKeyAt A.repAlloc)
          (BitVec.ofNat 64 x.gc.2.messageKeys.length) mkPtr' (keys'.zip x.gc.2.messageKeys) ∗
        clonedOptChainKeyBuf A.repAlloc ckPin' x25 x28 w27 x.gc.2.chainKey) ⊢
      (∃∗ g' : ChainGhost,
        ⌜g'.srk.bytes = x.gc.1.srk.bytes ∧ g'.priv.bytes = x.gc.1.priv.bytes ∧
          g'.keys.length = x.gc.1.keys.length⌝ ∗
        protoChainAt A.repAlloc (g', x.gc.2) x.dst) := by
    refine Entails.trans
      (fold_chainAt_dst A.repAlloc x.gc x.dst srkPtr' privPtr' mkPtr' x25 x28 w27 keys' ckPin'
        hsrk hmax hklen) ?_
    apply Entails.sepExists_right g'
    exact Entails.pure_right ⟨rfl, rfl, hklen.trans hsrc_klen.symm⟩ (Entails.refl _)
  have hst := fold_stackAt_chainClone s0
    (BitVec.ofNat 64 x.gc.2.messageKeys.length) v9 v10 v13
  have hgroup :
      ((x.dst ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
        ((x.dst + 8#64) ↦₆₄ srkPtr') ∗
        ((x.dst + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
        ((x.dst + 24#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        ((x.dst + 32#64) ↦₆₄ privPtr') ∗
        ((x.dst + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        ((x.dst + 48#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.dst + 56#64) ↦₆₄ mkPtr') ∗
        ((x.dst + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.dst + 72#64) ↦₆₄ x25) ∗
        ((x.dst + 80#64) ↦₆₄ x28) ∗
        ((x.dst + 88#64) ↦₆₄ x25) ∗
        ((x.dst + 96#64) ↦₃₂ w27) ∗
        memRegion (x.dst + 100#64) 4 ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        vecBuf A.repAlloc 104 8 (messageKeyAt A.repAlloc)
          (BitVec.ofNat 64 x.gc.2.messageKeys.length) mkPtr' (keys'.zip x.gc.2.messageKeys) ∗
        clonedOptChainKeyBuf A.repAlloc ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        protoChainAt A.repAlloc x.gc x.src ∗
        A.pool lim (M.stepEvents (chainCloneEvents x.gc) st) sf ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) =
      (((x.dst ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
        ((x.dst + 8#64) ↦₆₄ srkPtr') ∗
        ((x.dst + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
        ((x.dst + 24#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        ((x.dst + 32#64) ↦₆₄ privPtr') ∗
        ((x.dst + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        ((x.dst + 48#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.dst + 56#64) ↦₆₄ mkPtr') ∗
        ((x.dst + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.dst + 72#64) ↦₆₄ x25) ∗
        ((x.dst + 80#64) ↦₆₄ x28) ∗
        ((x.dst + 88#64) ↦₆₄ x25) ∗
        ((x.dst + 96#64) ↦₃₂ w27) ∗
        memRegion (x.dst + 100#64) 4 ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        vecBuf A.repAlloc 104 8 (messageKeyAt A.repAlloc)
          (BitVec.ofNat 64 x.gc.2.messageKeys.length) mkPtr' (keys'.zip x.gc.2.messageKeys) ∗
        clonedOptChainKeyBuf A.repAlloc ckPin' x25 x28 w27 x.gc.2.chainKey) ∗
       protoChainAt A.repAlloc x.gc x.src ∗
       A.pool lim (M.stepEvents (chainCloneEvents x.gc) st) sf ∗
       (stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)) := by
    ac_rfl
  rw [hgroup]
  exact sepConj_mono hg'
    (sepConj_mono_right (sepConj_mono_right hst))

set_option maxHeartbeats 1200000 in
theorem chain_clone_local1_placed_epilogue [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {Qp : State → SepProp → Prop}
    (x : ChainCloneGhost) (st : M.σ) (s0 s : State)
    (srkPtr' privPtr' mkPtr' x25 x28 v9 v10 v13 : BitVec 64)
    (w27 : BitVec 32) (keys' : List MessageKeyGhost) (ckPin' : VecPin)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : keys'.length = x.gc.2.messageKeys.length)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hpc : s.pc = (blkPl_82).base + 736#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr')
    (hx23 : s.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 x.gc.1.priv.bytes.length)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = privPtr')
    (hx9 : s.readReg64 (Reg.gpr 9#5) = mkPtr')
    (hx25 : s.readReg64 (Reg.gpr 25#5) = x25)
    (hx28 : s.readReg64 (Reg.gpr 28#5) = x28)
    (hw27 : s.readReg32 (Reg.gpr 27#5) = w27)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (lsProg_82 H) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        vecBuf A.repAlloc 104 8 (messageKeyAt A.repAlloc)
          (BitVec.ofNat 64 x.gc.2.messageKeys.length) mkPtr' (keys'.zip x.gc.2.messageKeys) ∗
        clonedOptChainKeyBuf A.repAlloc ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        protoChainAt A.repAlloc x.gc x.src ∗
        A.pool lim (M.stepEvents (chainCloneEvents x.gc) st) s ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpec M A lim).post (x, st) s0 sf))
      Qp := by
  rw [memRegion_104_eq_slots104 x.dst, sepExists_sepConj_left]
  refine SepWPp.exists_elim fun d => ?_
  unfold savedRegsOnStack
  simp only [sepConj_assoc]
  apply sepWPp_of_sepWP_vm (mid := s0.readReg64 (Reg.gpr 30#5))
  dsimp only [lsProg_82]
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp_all) (by simp_all) ⟨by simp_all, fun hvm => ?_⟩
    rw [← A.pool_of_vmPreserved (lim := lim) (st := M.stepEvents (chainCloneEvents x.gc) st) hvm]
    apply SepWPp.done (by simp_all) (by simp_all)
    refine ⟨by simp_all, ?_, ?_⟩
    · constructor <;> simp_all
    · rw [show BitVec.truncate 32 (s.readReg64 (Reg.gpr 27#5)) = w27 from hw27]
      refine Entails.trans ?_
        (epilogue_post_entails A lim st x s0 _ srkPtr' privPtr' mkPtr' x25 x28 v9 v10 v13
          w27 keys' ckPin' hsrk hmax hklen hsrc_klen (by simp_all))
      unfold savedRegsOnStack
      exact Entails.of_eq (by ac_rfl)

end LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.ChainCloneEpilogueBudget

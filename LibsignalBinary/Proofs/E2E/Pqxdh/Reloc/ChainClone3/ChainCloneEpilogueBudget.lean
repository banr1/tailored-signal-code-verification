/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneBaseBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneEpilogue
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Epilogue and Spec Lifts for `Chain::clone [local#3]` (Block `468`)

Lifts `protoChainCloneSpec` to `chainCloneSpec` and `senderChainCloneSpec` under
`RustCliAllocBudget M`, proves budget-threaded `epilogue_post_entails`, and provides
`VmPreserved`-strengthened `sessionShimSpec` and `sessionMemcpySpec` hook lemmas.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneEpilogueBudget

open Arm64 ProofLib SepProp
open CryptoGames.Ratchet (clampScalar)
open CryptoGames.LibsignalSession (Crypto PublicKey ReceiverChain SenderChain maxMessageKeys)
open CryptoVerification.RustHeap (RustAlloc allocHookStack vecBuf vecU8Buf)
open CryptoVerification.LibsignalSessionRepr (
  ChainGhost MessageKeyGhost VecPin chainAt messageKeyAt
)
open CryptoVerification.LibsignalTripleRatchetRepr (SenderChainGhost optSenderChainAt)
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone (
  ChainCloneGhost chainCloneStack
)
open CryptoVerification.LibsignalTripleRatchet.ChainClone3 (
  chainAt_eq_protoChainAt clonedChainGhost clonedOptChainKeyBuf
  fold_chainAt_dst fold_stackAt_chainClone optSenderChainAt_some_eq_chainAt
  protoChainAt savedRegsOnStack spillSlotsExist
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  noAllocShimBudgetSpec noAllocShim_hookOk
  framelessMemcpyBudgetSpec framelessMemcpy_hookOk
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget (
  ChainCloneEnv SenderChainCloneEnv chainCloneEvents chainCloneSpec
  senderChainAsProtoGhost senderChainCloneSpec
)
open LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneBaseBudget (
  ChainClone3Ok ChainClone3Ok_trap
  ProtoChainClone3Ok ProtoChainClone3Ok_trap
  SenderChainClone3Ok SenderChainClone3Ok_trap
  protoChainCloneSpec
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## 1. `protoChainCloneSpec` → `chainCloneSpec` / `senderChainCloneSpec` Lifts -/

theorem chainClone_of_protoChainClone_gen
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
      sep_ac_rfl
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
        sep_ac_rfl
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
      sep_ac_rfl
    rw [heq2, satisfies_pure_sepConj, satisfies_pure_sepConj]
    exact ⟨⟨hsrk33', hpriv_nil'⟩, ⟨hsrk33, hpriv_nil⟩, hrest_f⟩
  · simp only [protoChainCloneSpec] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · simp only [protoChainCloneSpec] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · simp only [protoChainCloneSpec] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

theorem chainClone_of_protoChainClone_trap
    {M : AllocCostModel} {b : BitVec 64} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {abs : String → Option (State → State)}
    (hclone : ProtoChainClone3Ok_trap M b C A lim abs) :
    ChainClone3Ok_trap M b C A lim abs :=
  chainClone_of_protoChainClone_gen hclone

theorem chainClone_of_protoChainClone
    {M : AllocCostModel} {b : BitVec 64} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hclone : ProtoChainClone3Ok M b C A lim ctl abs) :
    ChainClone3Ok M b C A lim ctl abs :=
  chainClone_of_protoChainClone_gen hclone

theorem senderChainClone_of_chainClone_gen_of_bridge
    {M : AllocCostModel} {prog : Program} {entry : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hbridge : ∀ (B : RustAlloc) a g sc, optSenderChainAt B a (some g) (some sc) =
      ⌜g.priv.bytes = sc.ratchetKey.privateKey.bytes.toList ∧
        clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes ∧
        g.srk.bytes.length = 33⌝ ∗
      protoChainAt B (⟨g.srk, g.priv, g.mkCap, g.mkPtr, [], g.ck⟩,
        ⟨sc.ratchetKey.publicKey, some sc.chainKey, []⟩) a)
    (hclone : subroutine_ok prog entry (protoChainCloneSpec M A lim)) :
    subroutine_ok prog entry (senderChainCloneSpec M A lim) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [senderChainCloneSpec, hbridge, sepConj_assoc, satisfies_pure_sepConj] at hpre
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
      sep_ac_rfl
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
        sep_ac_rfl
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
    rw [hbridge A.repAlloc x.dst sg' x.sc, hbridge A.repAlloc x.src x.g x.sc]
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
      sep_ac_rfl
    rw [heq2, satisfies_pure_sepConj, satisfies_pure_sepConj]
    exact ⟨⟨hpriv'_eq, hclamp, hsrk33'⟩, ⟨hpriv_eq, hclamp, hsrk33⟩, hrest_f⟩
  · simp only [protoChainCloneSpec] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · simp only [protoChainCloneSpec] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · simp only [protoChainCloneSpec] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

theorem senderChainClone_of_chainClone_gen
    {M : AllocCostModel} {prog : Program} {entry : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hclone : subroutine_ok prog entry (protoChainCloneSpec M A lim)) :
    subroutine_ok prog entry (senderChainCloneSpec M A lim) :=
  senderChainClone_of_chainClone_gen_of_bridge optSenderChainAt_some_eq_chainAt hclone

theorem senderChainClone_of_chainClone_trap
    {M : AllocCostModel} {b : BitVec 64} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {abs : String → Option (State → State)}
    (hclone : ProtoChainClone3Ok_trap M b C A lim abs) :
    SenderChainClone3Ok_trap M b C A lim abs :=
  senderChainClone_of_chainClone_gen hclone

theorem senderChainClone_of_chainClone
    {M : AllocCostModel} {b : BitVec 64} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hclone : ProtoChainClone3Ok M b C A lim ctl abs) :
    SenderChainClone3Ok M b C A lim ctl abs :=
  senderChainClone_of_chainClone_gen hclone

/-! ## 2. Budget-Threaded `epilogue_post_entails` -/

theorem epilogue_post_entails_of_env {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (evs : List AllocEvent) (x : ChainCloneGhost) (s0 sf : State)
    (srkPtr' privPtr' mkPtr' x25 x28 v9 v10 v13 : BitVec 64)
    (w27 : BitVec 32) (keys' : List MessageKeyGhost) (ckPin' : VecPin)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : keys'.length = x.gc.2.messageKeys.length)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (htrace : sf.trace = s0.trace)
    (hevs : ChainCloneEnv x.gc evs) :
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
      A.pool lim (M.stepEvents evs st) sf ∗
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
  apply Entails.sepExists_right evs
  apply Entails.pure_right ⟨htrace, hevs⟩
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
        A.pool lim (M.stepEvents evs st) sf ∗
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
       A.pool lim (M.stepEvents evs st) sf ∗
       (stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)) := by
    sep_ac_rfl
  rw [hgroup]
  exact sepConj_mono hg' (sepConj_mono_right (sepConj_mono_right hst))

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
      (protoChainCloneSpec M A lim).post (x, st) s0 sf :=
  epilogue_post_entails_of_env A lim st (chainCloneEvents x.gc) x s0 sf
    srkPtr' privPtr' mkPtr' x25 x28 v9 v10 v13 w27 keys' ckPin'
    hsrk hmax hklen hsrc_klen htrace rfl

/-! ## 3. `VmPreserved`-Strengthened `sessionShimSpec` and `sessionMemcpySpec` -/

abbrev sessionShimSpec : Spec Unit := noAllocShimBudgetSpec

theorem sessionShim_hookOk : HookOk hookNoop sessionShimSpec := noAllocShim_hookOk

abbrev sessionMemcpySpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  framelessMemcpyBudgetSpec

theorem sessionMemcpy_hookOk : HookOk hookMemcpy sessionMemcpySpec := framelessMemcpy_hookOk

end LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneEpilogueBudget

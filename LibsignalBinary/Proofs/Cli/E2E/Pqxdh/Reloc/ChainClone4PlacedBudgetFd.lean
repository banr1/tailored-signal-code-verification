/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.ChainClone4PlacedBudget
public import LibsignalBinary.Proofs.Placed.PlacedCallSym
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# `FdsGe3Closed`-Threaded `Chain::clone` Seams (Block `524`)

Conversion seams from `withFds A` (`lim.enforced = true`) to `withFdsGe3Closed` for
`protoChainCloneSpec`, `chainCloneSpec`, and `senderChainCloneSpec`, plus closed Block `524`
and caller-block `subroutine_ok` wrappers.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.ChainClone4PlacedBudgetFd

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoVerification (
  IsLsBlockProg LibsignalPlacement LsBlockBound
  lsMemcpySym lsRustAllocSym lsRustNoAllocShimSym
  ls_hook_ok_of_mem ls_subroutine_ok_of_block lsmpl
  subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded
)
open CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainCloneDefs (protoChainAt)
open CryptoVerification.CliHandshake.Placed (blkPC_524 blkPl_524)
open CryptoVerification.LibsignalSessionRepr (ChainGhost chainAt)
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone (
  ChainCloneGhost SenderChainCloneGhost chainCloneStack
)
open CryptoVerification.LibsignalTripleRatchetRepr (SenderChainGhost optSenderChainAt)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget
  allocMemcpyVmSpec rustCliAllocBudgetSpec
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.ChainClone4PlacedBudget (
  chain_clone_placed_ok chain_clone_placed_ok_of_vmHooks
  protoChain_clone_placed_ok protoChain_clone_placed_ok_of_hooks
  senderChain_clone_placed_ok senderChain_clone_placed_ok_of_vmHooks
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordChainClone.ClonePlacedDefsBudget (
  protoChainCloneSpec
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (
  FdsGe3Closed withFdsGe3Closed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds (
  hookOk_allocBudget_withFds withFds withFds_pool_enforced withFds_repAlloc
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget (
  ChainCloneEnv SenderChainCloneEnv chainCloneSpec senderChainCloneSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec
  subroutine_ok_sessionMemcpyRegionBudget_of_allocMemcpyVm
  subroutine_ok_sessionShimBudget_of_rustAllocShimVm
)

private theorem subroutine_ok_of_pre_post {α : Type} {P : Program} {entry : BitVec 64}
    {spec1 spec2 : Spec α}
    (hok : subroutine_ok P entry spec1)
    (hpan : spec2.onPanic = spec1.onPanic)
    (hexc : spec2.onExit = spec1.onExit)
    (hoom : spec2.onOom = spec1.onOom)
    (hpre : ∀ x R s0, (s0.mem ⊨ spec2.pre x s0 ∗ R) → (s0.mem ⊨ spec1.pre x s0 ∗ R))
    (hpost : ∀ x R s0 sf, (sf.mem ⊨ spec1.post x s0 sf ∗ R) →
      (sf.mem ⊨ spec2.post x s0 sf ∗ R)) :
    subroutine_ok P entry spec2 := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre2 hsp => ?_
  refine hok.mono_outcome x R s0 hpc hrun (hpre x R s0 hpre2) hsp ?_
  rintro sf (⟨hret, hcc, hp1⟩ | ⟨hp, hpan1⟩ | ⟨c, hc, hexc1⟩ | ⟨ho, hoom1⟩)
  · exact Or.inl ⟨hret, hcc, hpost x R s0 sf hp1⟩
  · exact Or.inr (Or.inl ⟨hp, hpan ▸ hpan1⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hexc ▸ hexc1⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom ▸ hoom1⟩))

private structure SpecImp {α : Type} (spec1 spec2 : Spec α) : Prop where
  onPanic_eq : spec2.onPanic = spec1.onPanic
  onExit_eq : spec2.onExit = spec1.onExit
  onOom_eq : spec2.onOom = spec1.onOom
  pre_eq : ∀ x s0, spec2.pre x s0 = spec1.pre x s0
  post_imp : ∀ x R s0 sf,
    (sf.mem ⊨ spec1.post x s0 sf ∗ R) → (sf.mem ⊨ spec2.post x s0 sf ∗ R)

private theorem SpecImp.to_subroutine_ok {α : Type} {P : Program} {entry : BitVec 64}
    {spec1 spec2 : Spec α} (h : SpecImp spec1 spec2)
    (hok : subroutine_ok P entry spec1) :
    subroutine_ok P entry spec2 :=
  subroutine_ok_of_pre_post hok h.onPanic_eq h.onExit_eq h.onOom_eq
    (fun x _ s0 hp => by rwa [← h.pre_eq x s0]) h.post_imp

private theorem SpecImp.withLsCodeLoaded {α : Type} (pl : MultiPlacement)
    {spec1 spec2 : Spec α} (h : SpecImp spec1 spec2) :
    SpecImp (CryptoVerification.withLsCodeLoaded pl spec1)
      (CryptoVerification.withLsCodeLoaded pl spec2) where
  onPanic_eq := h.onPanic_eq
  onExit_eq := h.onExit_eq
  onOom_eq := h.onOom_eq
  pre_eq := fun x s0 => by
    dsimp only [CryptoVerification.withLsCodeLoaded]
    rw [h.pre_eq x s0]
  post_imp := h.post_imp

private theorem hookSat_allocBudget_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {zeroed : Bool}
    {H : String → Option (State → State)} {sym : String}
    (hsat : HookSat H sym (rustCliAllocBudgetSpec M A lim zeroed)) :
    HookSat H sym (rustCliAllocBudgetSpec M (withFds A) lim zeroed) :=
  let ⟨f, hf, hok⟩ := hsat
  ⟨f, hf, hookOk_allocBudget_withFds hok⟩

/-! ## 1. Spec-Level `withFds` → `withFdsGe3Closed` Conversions -/

private theorem specImp_protoChainClone
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true) :
    SpecImp (protoChainCloneSpec M (withFds A) lim)
      (withFdsGe3Closed (protoChainCloneSpec M A lim)) where
  onPanic_eq := rfl
  onExit_eq := rfl
  onOom_eq := rfl
  pre_eq := by
    rintro ⟨x, st⟩ s0
    dsimp only [withFdsGe3Closed, protoChainCloneSpec, withFds_repAlloc]
    rw [withFds_pool_enforced A henf]
    sep_ac_rfl
  post_imp := by
    rintro ⟨x, st⟩ R s0 sf hpost
    dsimp only [withFdsGe3Closed, protoChainCloneSpec, withFds_repAlloc] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hevs⟩
    rw [withFds_pool_enforced A henf] at hevs
    let Cloned : SepProp :=
      ∃∗ g' : ChainGhost,
        ⌜g'.srk.bytes = x.gc.1.srk.bytes ∧ g'.priv.bytes = x.gc.1.priv.bytes ∧
          g'.keys.length = x.gc.1.keys.length⌝ ∗
        protoChainAt A.repAlloc (g', x.gc.2) x.dst
    have hpull :
        (⌜sf.trace = s0.trace ∧ ChainCloneEnv x.gc evs⌝ ∗
          Cloned ∗
          protoChainAt A.repAlloc x.gc x.src ∗
          (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
          stackAt s0.sp chainCloneStack) ∗ R =
        ⌜FdsGe3Closed sf.fs⌝ ∗
          ((⌜sf.trace = s0.trace ∧ ChainCloneEnv x.gc evs⌝ ∗
            Cloned ∗
            protoChainAt A.repAlloc x.gc x.src ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp chainCloneStack) ∗ R) := by
      sep_ac_rfl
    change sf.mem ⊨
      (⌜sf.trace = s0.trace ∧ ChainCloneEnv x.gc evs⌝ ∗
        Cloned ∗
        protoChainAt A.repAlloc x.gc x.src ∗
        (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
        stackAt s0.sp chainCloneStack) ∗ R at hevs
    rw [hpull, satisfies_pure_sepConj] at hevs
    rcases hevs with ⟨hClosedF, hbody⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hClosedF, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    exact ⟨evs, hbody⟩

private theorem specImp_chainClone
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true) :
    SpecImp (chainCloneSpec M (withFds A) lim)
      (withFdsGe3Closed (chainCloneSpec M A lim)) where
  onPanic_eq := rfl
  onExit_eq := rfl
  onOom_eq := rfl
  pre_eq := by
    rintro ⟨x, st⟩ s0
    dsimp only [withFdsGe3Closed, chainCloneSpec, withFds_repAlloc]
    rw [withFds_pool_enforced A henf]
    sep_ac_rfl
  post_imp := by
    rintro ⟨x, st⟩ R s0 sf hpost
    dsimp only [withFdsGe3Closed, chainCloneSpec, withFds_repAlloc] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hevs⟩
    rw [withFds_pool_enforced A henf] at hevs
    let Cloned : SepProp :=
      ∃∗ g' : ChainGhost,
        ⌜g'.srk.bytes = x.gc.1.srk.bytes ∧ g'.priv.bytes = x.gc.1.priv.bytes ∧
          g'.keys.length = x.gc.1.keys.length⌝ ∗
        chainAt A.repAlloc (g', x.gc.2) x.dst
    have hpull :
        (⌜sf.trace = s0.trace ∧ ChainCloneEnv x.gc evs⌝ ∗
          Cloned ∗
          chainAt A.repAlloc x.gc x.src ∗
          (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
          stackAt s0.sp chainCloneStack) ∗ R =
        ⌜FdsGe3Closed sf.fs⌝ ∗
          ((⌜sf.trace = s0.trace ∧ ChainCloneEnv x.gc evs⌝ ∗
            Cloned ∗
            chainAt A.repAlloc x.gc x.src ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp chainCloneStack) ∗ R) := by
      sep_ac_rfl
    change sf.mem ⊨
      (⌜sf.trace = s0.trace ∧ ChainCloneEnv x.gc evs⌝ ∗
        Cloned ∗
        chainAt A.repAlloc x.gc x.src ∗
        (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
        stackAt s0.sp chainCloneStack) ∗ R at hevs
    rw [hpull, satisfies_pure_sepConj] at hevs
    rcases hevs with ⟨hClosedF, hbody⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hClosedF, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    exact ⟨evs, hbody⟩

private theorem specImp_senderChainClone
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true) :
    SpecImp (senderChainCloneSpec M (withFds A) lim)
      (withFdsGe3Closed (senderChainCloneSpec M A lim)) where
  onPanic_eq := rfl
  onExit_eq := rfl
  onOom_eq := rfl
  pre_eq := by
    rintro ⟨x, st⟩ s0
    dsimp only [withFdsGe3Closed, senderChainCloneSpec, withFds_repAlloc]
    rw [withFds_pool_enforced A henf]
    sep_ac_rfl
  post_imp := by
    rintro ⟨x, st⟩ R s0 sf hpost
    dsimp only [withFdsGe3Closed, senderChainCloneSpec, withFds_repAlloc] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hevs⟩
    rw [withFds_pool_enforced A henf] at hevs
    let Cloned : SepProp :=
      ∃∗ g' : SenderChainGhost,
        ⌜g'.srk.bytes = x.g.srk.bytes ∧ g'.priv.bytes = x.g.priv.bytes⌝ ∗
        optSenderChainAt A.repAlloc x.dst (some g') (some x.sc)
    have hpull :
        (⌜sf.trace = s0.trace ∧ SenderChainCloneEnv x.g x.sc evs⌝ ∗
          Cloned ∗
          optSenderChainAt A.repAlloc x.src (some x.g) (some x.sc) ∗
          (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
          stackAt s0.sp chainCloneStack) ∗ R =
        ⌜FdsGe3Closed sf.fs⌝ ∗
          ((⌜sf.trace = s0.trace ∧ SenderChainCloneEnv x.g x.sc evs⌝ ∗
            Cloned ∗
            optSenderChainAt A.repAlloc x.src (some x.g) (some x.sc) ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp chainCloneStack) ∗ R) := by
      sep_ac_rfl
    change sf.mem ⊨
      (⌜sf.trace = s0.trace ∧ SenderChainCloneEnv x.g x.sc evs⌝ ∗
        Cloned ∗
        optSenderChainAt A.repAlloc x.src (some x.g) (some x.sc) ∗
        (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
        stackAt s0.sp chainCloneStack) ∗ R at hevs
    rw [hpull, satisfies_pure_sepConj] at hevs
    rcases hevs with ⟨hClosedF, hbody⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hClosedF, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    exact ⟨evs, hbody⟩

theorem subroutine_ok_protoChainClone_withFdsGe3Closed_of_withFds
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    (henf : lim.enforced = true)
    (hok : subroutine_ok P entry (protoChainCloneSpec M (withFds A) lim)) :
    subroutine_ok P entry (withFdsGe3Closed (protoChainCloneSpec M A lim)) :=
  (specImp_protoChainClone henf).to_subroutine_ok hok

theorem subroutine_ok_withLsCodeLoaded_protoChainClone_withFdsGe3Closed_of_withFds
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    (henf : lim.enforced = true)
    (hok : subroutine_ok P entry
      (withLsCodeLoaded lsmpl (protoChainCloneSpec M (withFds A) lim))) :
    subroutine_ok P entry
      (withLsCodeLoaded lsmpl (withFdsGe3Closed (protoChainCloneSpec M A lim))) :=
  ((specImp_protoChainClone henf).withLsCodeLoaded lsmpl).to_subroutine_ok hok

theorem subroutine_ok_chainClone_withFdsGe3Closed_of_withFds
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    (henf : lim.enforced = true)
    (hok : subroutine_ok P entry (chainCloneSpec M (withFds A) lim)) :
    subroutine_ok P entry (withFdsGe3Closed (chainCloneSpec M A lim)) :=
  (specImp_chainClone henf).to_subroutine_ok hok

theorem subroutine_ok_withLsCodeLoaded_chainClone_withFdsGe3Closed_of_withFds
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    (henf : lim.enforced = true)
    (hok : subroutine_ok P entry (withLsCodeLoaded lsmpl (chainCloneSpec M (withFds A) lim))) :
    subroutine_ok P entry
      (withLsCodeLoaded lsmpl (withFdsGe3Closed (chainCloneSpec M A lim))) :=
  ((specImp_chainClone henf).withLsCodeLoaded lsmpl).to_subroutine_ok hok

theorem subroutine_ok_senderChainClone_withFdsGe3Closed_of_withFds
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    (henf : lim.enforced = true)
    (hok : subroutine_ok P entry (senderChainCloneSpec M (withFds A) lim)) :
    subroutine_ok P entry (withFdsGe3Closed (senderChainCloneSpec M A lim)) :=
  (specImp_senderChainClone henf).to_subroutine_ok hok

theorem subroutine_ok_withLsCodeLoaded_senderChainClone_withFdsGe3Closed_of_withFds
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    (henf : lim.enforced = true)
    (hok : subroutine_ok P entry
      (withLsCodeLoaded lsmpl (senderChainCloneSpec M (withFds A) lim))) :
    subroutine_ok P entry
      (withLsCodeLoaded lsmpl (withFdsGe3Closed (senderChainCloneSpec M A lim))) :=
  ((specImp_senderChainClone henf).withLsCodeLoaded lsmpl).to_subroutine_ok hok

/-! ## 2. Closed Block `524` & Caller-Block `subroutine_ok` Wrappers -/

theorem protoChain_clone_placed_ok_withFdsGe3Closed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (henf : lim.enforced = true)
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_524).rebase (blkPl_524).base H) (blkPl_524).base
      (withFdsGe3Closed (protoChainCloneSpec M A lim)) :=
  subroutine_ok_protoChainClone_withFdsGe3Closed_of_withFds henf
    (protoChain_clone_placed_ok hshim (hookSat_allocBudget_withFds halloc) hmemcpy)

set_option maxRecDepth 200000 in
theorem protoChain_clone_placed_ok_of_vmHooks_withFdsGe3Closed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (henf : lim.enforced = true)
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok ((blkPC_524).rebase (blkPl_524).base H) (blkPl_524).base
      (withFdsGe3Closed (protoChainCloneSpec M A lim)) :=
  subroutine_ok_protoChainClone_withFdsGe3Closed_of_withFds henf
    (protoChain_clone_placed_ok_of_hooks
      (subroutine_ok_sessionShimBudget_of_rustAllocShimVm (ls_hook_ok_of_mem hshim))
      (ls_hook_ok_of_mem (hookSat_allocBudget_withFds halloc))
      (subroutine_ok_sessionMemcpyRegionBudget_of_allocMemcpyVm (ls_hook_ok_of_mem hmemcpy)))

theorem protoChain_clone_placed_ok_withFdsGe3Closed_at [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {callerProg : Program} {i bi : Nat} [IsLsBlockProg callerProg i H] [LsBlockBound bi]
    (henf : lim.enforced = true)
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hi : i < bi := by decide) :
    subroutine_ok callerProg (lsmpl.base 524)
      (withLsCodeLoaded lsmpl (withFdsGe3Closed (protoChainCloneSpec M A lim))) :=
  ls_subroutine_ok_of_block
    (subroutine_ok_withLsCodeLoaded_of_plain
      (protoChain_clone_placed_ok_withFdsGe3Closed henf hshim halloc hmemcpy)) hi

theorem chain_clone_placed_ok_withFdsGe3Closed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (henf : lim.enforced = true)
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_524).rebase (blkPl_524).base H) (blkPl_524).base
      (withFdsGe3Closed (chainCloneSpec M A lim)) :=
  subroutine_ok_chainClone_withFdsGe3Closed_of_withFds henf
    (chain_clone_placed_ok hshim (hookSat_allocBudget_withFds halloc) hmemcpy)

theorem chain_clone_placed_ok_of_vmHooks_withFdsGe3Closed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (henf : lim.enforced = true)
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok ((blkPC_524).rebase (blkPl_524).base H) (blkPl_524).base
      (withFdsGe3Closed (chainCloneSpec M A lim)) :=
  subroutine_ok_chainClone_withFdsGe3Closed_of_withFds henf
    (chain_clone_placed_ok_of_vmHooks hshim (hookSat_allocBudget_withFds halloc) hmemcpy)

theorem chain_clone_placed_ok_withFdsGe3Closed_at [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {callerProg : Program} {i bi : Nat} [IsLsBlockProg callerProg i H] [LsBlockBound bi]
    (henf : lim.enforced = true)
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hi : i < bi := by decide) :
    subroutine_ok callerProg (lsmpl.base 524)
      (withLsCodeLoaded lsmpl (withFdsGe3Closed (chainCloneSpec M A lim))) :=
  ls_subroutine_ok_of_block
    (subroutine_ok_withLsCodeLoaded_of_plain
      (chain_clone_placed_ok_withFdsGe3Closed henf hshim halloc hmemcpy)) hi

theorem senderChain_clone_placed_ok_withFdsGe3Closed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (henf : lim.enforced = true)
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_524).rebase (blkPl_524).base H) (blkPl_524).base
      (withFdsGe3Closed (senderChainCloneSpec M A lim)) :=
  subroutine_ok_senderChainClone_withFdsGe3Closed_of_withFds henf
    (senderChain_clone_placed_ok hshim (hookSat_allocBudget_withFds halloc) hmemcpy)

theorem senderChain_clone_placed_ok_of_vmHooks_withFdsGe3Closed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (henf : lim.enforced = true)
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok ((blkPC_524).rebase (blkPl_524).base H) (blkPl_524).base
      (withFdsGe3Closed (senderChainCloneSpec M A lim)) :=
  subroutine_ok_senderChainClone_withFdsGe3Closed_of_withFds henf
    (senderChain_clone_placed_ok_of_vmHooks hshim (hookSat_allocBudget_withFds halloc) hmemcpy)

theorem senderChain_clone_placed_ok_withFdsGe3Closed_at [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {callerProg : Program} {i bi : Nat} [IsLsBlockProg callerProg i H] [LsBlockBound bi]
    (henf : lim.enforced = true)
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hi : i < bi := by decide) :
    subroutine_ok callerProg (lsmpl.base 524)
      (withLsCodeLoaded lsmpl (withFdsGe3Closed (senderChainCloneSpec M A lim))) :=
  ls_subroutine_ok_of_block
    (subroutine_ok_withLsCodeLoaded_of_plain
      (senderChain_clone_placed_ok_withFdsGe3Closed henf hshim halloc hmemcpy)) hi

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.ChainClone4PlacedBudgetFd

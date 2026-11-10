/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserializeBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KitRelDetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded `SessionRecord::deserialize` Contracts at `scopeKit` (Placed)

Proves budget-threaded `sessDeserializeSpecPlaced` for Block `46` (`SessionRecord::deserialize`) at
`scopeKit` (and any `Scope ⊆ scopeKit`) under `[LibsignalPlacement]` and `[HasFineReallocCredit M]`,
with cross-block (`i < 619`) and `CliGhostAllocHooks` specializations.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KitRelDetPlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.E2E.Record (encodeRecord recDeserializeStack)
open CryptoVerification.E2E.Record.Placed (blkPl_46 instIsLsBlockProg_46 lsProg_46)
open CryptoVerification.E2E.Record.Serialization (CanonRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (extract_withLsCodeRoLoaded ls_subroutine_ok_rocl_of_block
   subroutine_ok_withLsCodeRoLoaded_of_rocl withLsCodeRoLoaded)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost sessionRecordAt)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks cliExternsPlaced_row cliGhostExterns cliGhostExterns_other cliGhostExterns_shim)
open CryptoVerification.SignalSession.Cli.Slots
  (cliGhostExterns_panic_handle_alloc_error cliGhostExterns_panic_handle_error
   scopeKit)
open Symbolic.Swarm.TRREF.B3Defs (DeserializeScopeP_Q NonEmptyV1Q)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEvents RustCliAllocBudget)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.HookLift (AllocContractsBudgetPlaced)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserializeBudget
  (sessDeserEvents sessDeserializeBudgetPlacedSpec sessDeserializeBudgetRawSpec
   sessDeserialize_budget_placed_ok_of_sub)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks cliExternsPlaced_alloc_budget_sat cliExternsPlaced_dealloc_budget_sat
   cliExternsPlaced_realloc_budget_sat cliExternsPlaced_sessionMemcpy_budget_sat
   cliExternsPlaced_shim_budget_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (sessDeserializeSpecPlaced)

/-- Discharges `AllocContractsBudgetPlaced` on `cliGhostExterns g (cliExternsPlaced mmpl W)` from
`CliGhostAllocHooks M A lim g`. -/
theorem allocContractsBudgetPlaced_cli [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) :
    AllocContractsBudgetPlaced M A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  AllocContractsBudgetPlaced.of_hooks
    (cliExternsPlaced_alloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_dealloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_realloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_shim_budget_sat mmpl g W hG.shim_eq)
    (cliExternsPlaced_sessionMemcpy_budget_sat mmpl g W hG extHookStack)
    (cliGhostExterns_panic_handle_error mmpl g W)
    (cliGhostExterns_panic_handle_alloc_error mmpl g W)

/-- Block `46` (`lsProg_46 H`) satisfies `sessDeserializeSpecPlaced` for any `DeserEnv` closed under
`sessDeserEvents` on `Scope ⊆ scopeKit`. -/
theorem sessDeserialize_of_sessDeserEvents_placed_ok [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hA : AllocContractsBudgetPlaced M A lim H)
    (hsub : ∀ r, Scope r → DeserializeScopeP_Q NonEmptyV1Q r)
    (hMem : ∀ r, Scope r → DeserEnv r (sessDeserEvents r)) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base
      (sessDeserializeSpecPlaced Scope A lim DeserEnv) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  obtain ⟨hcrl, hrest⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [sessDeserializeSpecPlaced] at hrest
  rw [sepConj_assoc, satisfies_pure_sepConj] at hrest
  obtain ⟨⟨hx0, hx1, hx8, hsc, hfitEnv⟩, hmem⟩ := hrest
  have hMemEvs : DeserEnv x.r (sessDeserEvents x.r) := hMem x.r hsc
  have hfitEvs : FitsEvents M lim st (sessDeserEvents x.r) := hfitEnv (sessDeserEvents x.r) hMemEvs
  have hpre_b : s0.mem ⊨ (sessDeserializeBudgetPlacedSpec Scope M A lim).pre (x, st) s0 ∗ R := by
    dsimp only [sessDeserializeBudgetPlacedSpec,
      CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded, sessDeserializeBudgetRawSpec]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨⟨hcrl.1, hcrl.2⟩, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8, hsc, hfitEvs⟩, hmem⟩
  refine (sessDeserialize_budget_placed_ok_of_sub hA hsub).mono_outcome
    (x, st) R s0 hpc hrun hpre_b hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [sessDeserializeBudgetPlacedSpec,
      CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
      sessDeserializeBudgetRawSpec] at hpost
    have hpost1 : sf.mem ⊨
        ⌜sf.trace = s0.trace⌝ ∗
        ((∃∗ g : RecordGhost,
            ⌜CanonRecord g x.r ∧
              (∀ G, g.cur = some G →
                (∀ s_sess, x.r.currentSession = some s_sess →
                  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential.ssStateLargeLive
                    M G s_sess.state =
                  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential.ssLargeLive M G) ∧
                (33 ≤ HasFineReallocCredit.smallMaxReq M →
                  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential.ssLargeLive M G =
                  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserializeBudget.sessDeserLargeLive
                    M x.r))⌝ ∗
            sessionRecordAt A.repAlloc x.out g x.r) ∗
          ((x.p ↦ₛ encodeRecord x.r) ∗
            A.pool lim (M.stepEvents (sessDeserEvents x.r) st) sf ∗
            stackAt s0.sp recDeserializeStack ∗ R)) :=
      Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hpost
    rw [satisfies_pure_sepConj] at hpost1
    obtain ⟨htr, hpost2⟩ := hpost1
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost2
    obtain ⟨g, hg⟩ := hpost2
    rw [sepConj_assoc, satisfies_pure_sepConj] at hg
    obtain ⟨⟨hcanon, _⟩, hspatial⟩ := hg
    dsimp only [sessDeserializeSpecPlaced, withLsCodeRoLoaded]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨sessDeserEvents x.r, ?_⟩
    have hgoal : sf.mem ⊨
        ⌜sf.trace = s0.trace ∧ DeserEnv x.r (sessDeserEvents x.r)⌝ ∗
        ((∃∗ g' : RecordGhost, ⌜CanonRecord g' x.r⌝ ∗
            CryptoVerification.E2E.Record.sessionRecordAt A.repAlloc x.out g' x.r) ∗
          ((x.p ↦ₛ encodeRecord x.r) ∗
            A.pool lim (M.stepEvents (sessDeserEvents x.r) st) sf ∗
            stackAt s0.sp recDeserializeStack ∗ R)) := by
      rw [satisfies_pure_sepConj]
      refine ⟨⟨htr, hMemEvs⟩, ?_⟩
      rw [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨g, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hcanon, hspatial⟩
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hgoal
  · dsimp only [sessDeserializeBudgetPlacedSpec,
      CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [sessDeserializeBudgetPlacedSpec,
      CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [sessDeserializeBudgetPlacedSpec,
      CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem sessDeserialize_of_sessDeserEvents_caller_ok [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {callerProg : Program} {callerBlk : Nat} [hcaller : IsLsBlockProg callerProg callerBlk H]
    (hA : AllocContractsBudgetPlaced M A lim H)
    (hsub : ∀ r, Scope r → DeserializeScopeP_Q NonEmptyV1Q r)
    (hMem : ∀ r, Scope r → DeserEnv r (sessDeserEvents r))
    (hCallerBlk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (blkPl_46).base
      (sessDeserializeSpecPlaced Scope A lim DeserEnv) := by
  have hrocl := @ls_subroutine_ok_rocl_of_block _ _ callerProg (lsProg_46 H) callerBlk 46 H
    hcaller (instIsLsBlockProg_46 H) (blkPl_46).base _
    (sessDeserialize_of_sessDeserEvents_placed_ok hA hsub hMem) _ _ _ _
    hCallerBlk (by decide) (by decide)
  exact subroutine_ok_withLsCodeRoLoaded_of_rocl hrocl

/-- Block `46` (`SessionRecord::deserialize`) satisfies `sessDeserializeSpecPlaced scopeKit A lim DeserEnv`
under `[HasFineReallocCredit M]` and `AllocContractsBudgetPlaced M A lim H`. -/
theorem sessDeserialize_scopeKit_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hA : AllocContractsBudgetPlaced M A lim H)
    (hMem : ∀ r, scopeKit r → DeserEnv r (sessDeserEvents r)) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv) :=
  sessDeserialize_of_sessDeserEvents_placed_ok hA (fun _ h => h) hMem

theorem sessDeserialize_of_sub_scopeKit_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hA : AllocContractsBudgetPlaced M A lim H)
    (hsub : ∀ r, Scope r → scopeKit r)
    (hMem : ∀ r, Scope r → DeserEnv r (sessDeserEvents r)) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base
      (sessDeserializeSpecPlaced Scope A lim DeserEnv) :=
  sessDeserialize_of_sessDeserEvents_placed_ok hA hsub hMem

/-- Transfers `sessDeserialize_of_sub_scopeKit_placed_ok` to any caller block `i < 619`. -/
theorem sessDeserialize_of_sub_scopeKit_placed_at_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hA : AllocContractsBudgetPlaced M A lim H)
    (hsub : ∀ r, Scope r → scopeKit r)
    (hMem : ∀ r, Scope r → DeserEnv r (sessDeserEvents r))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_46).base
      (sessDeserializeSpecPlaced Scope A lim DeserEnv) :=
  sessDeserialize_of_sessDeserEvents_caller_ok hA hsub hMem hi

theorem sessDeserialize_scopeKit_cli_placed_ok [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hG : CliGhostAllocHooks M A lim g)
    (hMem : ∀ r, scopeKit r → DeserEnv r (sessDeserEvents r)) :
    subroutine_ok (lsProg_46 (cliGhostExterns g (cliExternsPlaced mmpl W))) (blkPl_46).base
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv) :=
  sessDeserialize_scopeKit_placed_ok (allocContractsBudgetPlaced_cli mmpl g W hG) hMem

theorem sessDeserialize_of_sub_scopeKit_cli_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hG : CliGhostAllocHooks M A lim g)
    (hsub : ∀ r, Scope r → scopeKit r)
    (hMem : ∀ r, Scope r → DeserEnv r (sessDeserEvents r)) :
    subroutine_ok (lsProg_46 (cliGhostExterns g (cliExternsPlaced mmpl W))) (blkPl_46).base
      (sessDeserializeSpecPlaced Scope A lim DeserEnv) :=
  sessDeserialize_of_sub_scopeKit_placed_ok (allocContractsBudgetPlaced_cli mmpl g W hG) hsub hMem

theorem sessDeserialize_of_sub_scopeKit_cli_placed_at_block [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hG : CliGhostAllocHooks M A lim g)
    (hsub : ∀ r, Scope r → scopeKit r)
    (hMem : ∀ r, Scope r → DeserEnv r (sessDeserEvents r))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_46).base
      (sessDeserializeSpecPlaced Scope A lim DeserEnv) :=
  sessDeserialize_of_sub_scopeKit_placed_at_block (allocContractsBudgetPlaced_cli mmpl g W hG)
    hsub hMem hi

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KitRelDetPlacedBudget

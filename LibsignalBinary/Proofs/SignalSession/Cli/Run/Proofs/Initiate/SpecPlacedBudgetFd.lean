/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import Arm64.Trusted.Spec.SepLogic
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.AssemblyPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SpecPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd

import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced

/-!
# File-Descriptor-Guarded Tight Budget Contract for `initiate`

Lifts `SpecPlacedBudget`'s tight `Compose.SemPlacedBudget.initSlotSpecPlaced` contract on block `521`
and caller blocks `i < 619` to `withPreFdsGe3Closed` via `AllocWithFds.withFds A` when
`lim.enforced = true`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SpecPlacedBudgetFd

noncomputable section

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.SepLogic SepProp
open CryptoVerification (IsLsBlockProg LibsignalPlacement lsmpl)
open CryptoVerification.E2E (PreKeyBundleFields UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (extract_withLsCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (Params)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.RustHeap (allocFailedIn)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.RunCompose (InitGhost RunSem SlotCtx)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (InitOk₀ cliInitiateNeed initDef)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate (AtInitEntryPlaced initProgPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (satisfies_lscro_pre)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (FdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
  (withFds withFds_pool_enforced withFds_repAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
  (extract_withPreFdsGe3Closed withPreFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (initSlotSpecPlaced slotFramePlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.AssemblyPlacedBudget
  (CliInitiateBudgetFits Stage3PlacedOk)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
  (SubsetA4InitCalleesPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SpecPlacedBudget
  (cliInitiate_caller_tight_placed_ok cliInitiate_tight_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlacedBudget
  (ExistingStoreCalleesEnvs ExistingStoreCalleesPlaced)

/-- Under `lim.enforced = true`, `SemPlacedBudget.slotFramePlaced (withFds A)` equals `⌜FdsGe3Closed s.fs⌝ ∗ SemPlacedBudget.slotFramePlaced A`. -/
theorem semSlotFramePlaced_withFds_eq [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) {lim : BudgetLimits} (henf : lim.enforced = true)
    (st : M.σ) (x : SlotCtx) (s : State) :
    slotFramePlaced (withFds A) lim st x s =
      (⌜FdsGe3Closed s.fs⌝ ∗ slotFramePlaced A lim st x s) := by
  unfold slotFramePlaced
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.slotFramePlaced
  rw [withFds_repAlloc, withFds_pool_enforced A henf st s]
  sep_ac_rfl

private theorem push_pure_slot6 {Q : Prop} {P1 Slot P3 P4 P5 P6 R : SepProp} {m : Memory}
    (hq : Q) (h : m ⊨ (P1 ∗ Slot ∗ P3 ∗ P4 ∗ P5 ∗ P6) ∗ R) :
    m ⊨ (P1 ∗ (⌜Q⌝ ∗ Slot) ∗ P3 ∗ P4 ∗ P5 ∗ P6) ∗ R := by
  have h' : m ⊨ ⌜Q⌝ ∗ ((P1 ∗ Slot ∗ P3 ∗ P4 ∗ P5 ∗ P6) ∗ R) := by
    rw [satisfies_pure_sepConj]
    exact ⟨hq, h⟩
  exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) h'

private theorem drop_pure_10 {Q : Prop}
    {P1 P2 P3 P4 P5 P6 P7 P8 Pool P9 P10 R : SepProp} {m : Memory}
    (h : m ⊨ (P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ P6 ∗ P7 ∗ P8 ∗ (⌜Q⌝ ∗ Pool) ∗ P9 ∗ P10) ∗ R) :
    m ⊨ (P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ P6 ∗ P7 ∗ P8 ∗ Pool ∗ P9 ∗ P10) ∗ R := by
  have h' : m ⊨ ⌜Q⌝ ∗ ((P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ P6 ∗ P7 ∗ P8 ∗ Pool ∗ P9 ∗ P10) ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) h
  rw [satisfies_pure_sepConj] at h'
  exact h'.2

/-- Weakens `subroutine_ok` from `SemPlacedBudget.initSlotSpecPlaced (withFds A)` to `withPreFdsGe3Closed (SemPlacedBudget.initSlotSpecPlaced A)` when `lim.enforced = true`. -/
theorem subroutine_ok_semInitSlot_preFd_of_withFds [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (henf : lim.enforced = true)
    {InitEnv : InitGhost → List AllocEvent → Prop} {S : RunSem} {stk : Nat}
    (hok : subroutine_ok prog entry (initSlotSpecPlaced (withFds A) lim InitEnv S stk)) :
    subroutine_ok prog entry
      (withPreFdsGe3Closed (initSlotSpecPlaced A lim InitEnv S stk)) := by
  apply subroutine_ok.of_codeLoaded
  intro ⟨x, st⟩ R s0 hpc hrun hpre hsp _
  obtain ⟨hfds0, hpre0⟩ := extract_withPreFdsGe3Closed hpre
  obtain ⟨hcrl, hpre1⟩ := extract_withLsCodeRoLoaded hpre0
  have hpre_fds : s0.mem ⊨
      (initSlotSpecPlaced (withFds A) lim InitEnv S stk).pre (x, st) s0 ∗ R := by
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [initSlotSpecPlaced] at hpre1 ⊢
    rw [semSlotFramePlaced_withFds_eq A henf st x.toSlotCtx s0]
    exact push_pure_slot6 hfds0 hpre1
  refine subroutine_ok.mono_outcome hok (x, st) R s0 hpc hrun hpre_fds hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hexc⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withPreFdsGe3Closed, initSlotSpecPlaced, withLsCodeRoLoaded] at hpost ⊢
    rw [withFds_repAlloc] at hpost
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨g', hpost⟩
    refine ⟨g', ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨e, hpost⟩
    refine ⟨e, ?_⟩
    rw [withFds_pool_enforced A henf (M.stepEvents evs st) sf] at hpost
    exact drop_pure_10 hpost
  · exact Or.inr (Or.inl ⟨hp, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hexc⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))

/-- Block `521` `FdsGe3Closed`-guarded tight `initSlotSpecPlaced` theorem via `withFds A`. -/
theorem cliInitiate_tight_placed_ok_preFd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (henf : lim.enforced = true)
    {eEnvs : ExistingStoreCalleesEnvs}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {Stage3Fit : InitGhost → PreKeyBundleFields → IdentityKeyPair →
      List (BitVec 8) → List (BitVec 8) → BitVec 64 → BitVec 32 → State → M.σ → M.σ → Prop}
    {Stage3Out : InitGhost → PreKeyBundleFields → IdentityKeyPair →
      SignalPqxdh.DRKey → SignalPqxdh.HandshakeHdr → List AllocEvent → Prop}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (hh : RunHooksPlaced W (withFds A) lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hExist : ExistingStoreCalleesPlaced (withFds A) lim eEnvs
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) B)
    (ha4 : SubsetA4InitCalleesPlaced (withFds A) lim InitStateEnv mmpl gh W)
    (hStage3 : Stage3PlacedOk (withFds A) lim InitStateEnv InitEnv Stage3Fit Stage3Out
      mmpl gh W X B S)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hok : ∀ F peer me, S.filesOk F peer me → S.initOk F peer me → InitOk₀ ⟨W.C, W.Q⟩ F peer me)
    (stk : Nat) (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hFits : ∀ (x : InitGhost) (st0 : M.σ) (s0 : State),
      AtInitEntryPlaced x s0 →
      S.filesOk x.F x.peer.val x.me.val →
      S.initOk x.F x.peer.val x.me.val →
      InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val →
      x.coins.length < 2 ^ 63 →
      stk ≤ s0.sp.toNat →
      FitsEnv M lim st0 (InitEnv x) →
      CliInitiateBudgetFits M lim eEnvs InitStateEnv InitEnv Stage3Fit Stage3Out W X x s0 st0)
    (hNoAllocFail : ∀ (x : InitGhost) (st0 : M.σ) (R : SepProp) (s0 sf : State),
      s0.pc = lsmpl.base 521 →
      s0.status = .Running →
      (s0.mem ⊨ (initSlotSpecPlaced (withFds A) lim InitEnv S stk).pre (x, st0) s0 ∗ R) →
      s0.spAligned = true →
      (initProgPlaced mmpl gh W).CodeLoaded s0.mem →
      Steps (initProgPlaced mmpl gh W) s0 sf →
      sf.status = .Panicked →
      allocFailedIn s0 sf →
      S.initiate x.F x.peer.val x.me.val x.bundle x.coins = none) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 521)
      (withPreFdsGe3Closed (initSlotSpecPlaced A lim InitEnv S stk)) :=
  subroutine_ok_semInitSlot_preFd_of_withFds henf
    (cliInitiate_tight_placed_ok mmpl gh W X B S hh hExist ha4 hStage3
      hS hok stk hstk hstk64 hFits hNoAllocFail)

/-- Transfers `cliInitiate_tight_placed_ok_preFd` to any caller block `i < 619`. -/
theorem cliInitiate_caller_tight_placed_ok_preFd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (henf : lim.enforced = true)
    {eEnvs : ExistingStoreCalleesEnvs}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {Stage3Fit : InitGhost → PreKeyBundleFields → IdentityKeyPair →
      List (BitVec 8) → List (BitVec 8) → BitVec 64 → BitVec 32 → State → M.σ → M.σ → Prop}
    {Stage3Out : InitGhost → PreKeyBundleFields → IdentityKeyPair →
      SignalPqxdh.DRKey → SignalPqxdh.HandshakeHdr → List AllocEvent → Prop}
    {callerProg : Program} {i : Nat}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    [IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (hh : RunHooksPlaced W (withFds A) lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hExist : ExistingStoreCalleesPlaced (withFds A) lim eEnvs
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) B)
    (ha4 : SubsetA4InitCalleesPlaced (withFds A) lim InitStateEnv mmpl gh W)
    (hStage3 : Stage3PlacedOk (withFds A) lim InitStateEnv InitEnv Stage3Fit Stage3Out
      mmpl gh W X B S)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hok : ∀ F peer me, S.filesOk F peer me → S.initOk F peer me → InitOk₀ ⟨W.C, W.Q⟩ F peer me)
    (stk : Nat) (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hFits : ∀ (x : InitGhost) (st0 : M.σ) (s0 : State),
      AtInitEntryPlaced x s0 →
      S.filesOk x.F x.peer.val x.me.val →
      S.initOk x.F x.peer.val x.me.val →
      InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val →
      x.coins.length < 2 ^ 63 →
      stk ≤ s0.sp.toNat →
      FitsEnv M lim st0 (InitEnv x) →
      CliInitiateBudgetFits M lim eEnvs InitStateEnv InitEnv Stage3Fit Stage3Out W X x s0 st0)
    (hNoAllocFail : ∀ (x : InitGhost) (st0 : M.σ) (R : SepProp) (s0 sf : State),
      s0.pc = lsmpl.base 521 →
      s0.status = .Running →
      (s0.mem ⊨ (initSlotSpecPlaced (withFds A) lim InitEnv S stk).pre (x, st0) s0 ∗ R) →
      s0.spAligned = true →
      callerProg.CodeLoaded s0.mem →
      Steps callerProg s0 sf →
      sf.status = .Panicked →
      allocFailedIn s0 sf →
      S.initiate x.F x.peer.val x.me.val x.bundle x.coins = none)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 521)
      (withPreFdsGe3Closed (initSlotSpecPlaced A lim InitEnv S stk)) :=
  subroutine_ok_semInitSlot_preFd_of_withFds henf
    (cliInitiate_caller_tight_placed_ok (callerProg := callerProg) (i := i)
      mmpl gh W X B S hh hExist ha4 hStage3 hS hok stk hstk hstk64 hFits hNoAllocFail hi)

end

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SpecPlacedBudgetFd

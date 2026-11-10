/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.AssemblyPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SpecPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.RunCodeSym
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.MallocngBridge

/-!
# Budget-Threaded Relocatable Contract for `signal_session_handshake::initiate`

Exports budget-threaded `[LibsignalPlacement]` theorems on block `521` (`initProgPlaced mmpl gh W`)
and caller blocks `i < 619` over `RustCliAllocBudget M`, proving both
`DefsPlacedBudget.initSlotSpecPlaced` and the tight `Compose.SemPlacedBudget.initSlotSpecPlaced`
contract (`cliInitiate_slotOk_placed`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SpecPlacedBudget

noncomputable section

open Arm64 Arm64.Process ProofLib SepProp
open CryptoVerification (IsLsBlockProg LibsignalPlacement lsmpl)
open CryptoVerification.E2E
  (PEParams PreKeyBundleFields UnreachedPqxdhPrimitives initiateTapeLen)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (Params)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.RustHeap (allocFailedIn)
open CryptoVerification.SignalSession
  (CliHooks PqParty PqxdhPartyInSpecDomain cliExternsPlaced pqInitInputs)
open CryptoVerification.SignalSession.Cli.Run.Placed (instIsLsBlockProg_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (InitGhost RunNeeds RunSem mkSlot runFiles)
open CryptoVerification.SignalSession.Cli.RunProofs (InitOk₀ cliInitiateNeed initDef)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (AtInitEntryPlaced initProgPlaced transfer_withLsCodeRoLoaded)
open CryptoVerification.SignalSession.Cli.RunRefine (PqInitiateAgrees addrValE)
open CryptoVerification.SignalSession.Cli.RunSkeleton (CalleeSlot.OkPlaced RunBudgets)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.AssemblyPlacedBudget
  (CliInitiateBudgetFits Stage3PlacedOk cliInitiate_placed_ok_proof
   cliInitiate_placed_ok_proof_of_stage2)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
  (SubsetA4InitCalleesPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2PlacedBudget
  (Stage2PlacedOk)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlacedBudget
  (ExistingStoreCalleesEnvs ExistingStoreCalleesPlaced)
open Arm64.Obj (MultiPlacement)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

/-! ## `DefsPlacedBudget.initSlotSpecPlaced` entrypoints -/

/-- Budget-threaded `initSlotSpecPlaced` on block `521`, parameterized over `Stage2PlacedOk` and `Stage3PlacedOk`. -/
theorem cliInitiate_placed_ok_of_stage2 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {eEnvs : ExistingStoreCalleesEnvs}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {Stage3Fit : InitGhost → PreKeyBundleFields → IdentityKeyPair →
      List (BitVec 8) → List (BitVec 8) → BitVec 64 → BitVec 32 → State → M.σ → M.σ → Prop}
    {Stage3Out : InitGhost → PreKeyBundleFields → IdentityKeyPair →
      SignalPqxdh.DRKey → SignalPqxdh.HandshakeHdr → List AllocEvent → Prop}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hExist : ExistingStoreCalleesPlaced A lim eEnvs (cliGhostExterns gh (cliExternsPlaced mmpl W)) B)
    (ha4 : SubsetA4InitCalleesPlaced A lim InitStateEnv mmpl gh W)
    (hStage2 : Stage2PlacedOk A lim eEnvs InitStateEnv InitEnv mmpl gh W X B S)
    (hStage3 : Stage3PlacedOk A lim InitStateEnv InitEnv Stage3Fit Stage3Out mmpl gh W X B S)
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
      CliInitiateBudgetFits M lim eEnvs InitStateEnv InitEnv Stage3Fit Stage3Out W X x s0 st0) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 521)
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget.initSlotSpecPlaced
        A lim InitEnv S stk) :=
  cliInitiate_placed_ok_proof_of_stage2 mmpl gh W X B S hh hExist ha4 hStage2 hStage3 hS hok stk hstk hstk64
    hFits

/-- Budget-threaded `initSlotSpecPlaced` on block `521`, with Stage 2 discharged via `Stage2PlacedBudget.stage2Placed_ok`. -/
theorem cliInitiate_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {eEnvs : ExistingStoreCalleesEnvs}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {Stage3Fit : InitGhost → PreKeyBundleFields → IdentityKeyPair →
      List (BitVec 8) → List (BitVec 8) → BitVec 64 → BitVec 32 → State → M.σ → M.σ → Prop}
    {Stage3Out : InitGhost → PreKeyBundleFields → IdentityKeyPair →
      SignalPqxdh.DRKey → SignalPqxdh.HandshakeHdr → List AllocEvent → Prop}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hExist : ExistingStoreCalleesPlaced A lim eEnvs (cliGhostExterns gh (cliExternsPlaced mmpl W)) B)
    (ha4 : SubsetA4InitCalleesPlaced A lim InitStateEnv mmpl gh W)
    (hStage3 : Stage3PlacedOk A lim InitStateEnv InitEnv Stage3Fit Stage3Out mmpl gh W X B S)
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
      CliInitiateBudgetFits M lim eEnvs InitStateEnv InitEnv Stage3Fit Stage3Out W X x s0 st0) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 521)
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget.initSlotSpecPlaced
        A lim InitEnv S stk) :=
  cliInitiate_placed_ok_proof mmpl gh W X B S hh hExist ha4 hStage3 hS hok stk hstk hstk64 hFits

/-- Transfers `cliInitiate_placed_ok_of_stage2` to any caller block `i < 619`. -/
theorem cliInitiate_caller_placed_ok_of_stage2 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {eEnvs : ExistingStoreCalleesEnvs}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {Stage3Fit : InitGhost → PreKeyBundleFields → IdentityKeyPair →
      List (BitVec 8) → List (BitVec 8) → BitVec 64 → BitVec 32 → State → M.σ → M.σ → Prop}
    {Stage3Out : InitGhost → PreKeyBundleFields → IdentityKeyPair →
      SignalPqxdh.DRKey → SignalPqxdh.HandshakeHdr → List AllocEvent → Prop}
    {callerProg : Program} {i : Nat}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) [IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hExist : ExistingStoreCalleesPlaced A lim eEnvs (cliGhostExterns gh (cliExternsPlaced mmpl W)) B)
    (ha4 : SubsetA4InitCalleesPlaced A lim InitStateEnv mmpl gh W)
    (hStage2 : Stage2PlacedOk A lim eEnvs InitStateEnv InitEnv mmpl gh W X B S)
    (hStage3 : Stage3PlacedOk A lim InitStateEnv InitEnv Stage3Fit Stage3Out mmpl gh W X B S)
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
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 521)
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget.initSlotSpecPlaced
        A lim InitEnv S stk) :=
  transfer_withLsCodeRoLoaded (callerProg := callerProg) (hi := hi)
    (cliInitiate_placed_ok_of_stage2 mmpl gh W X B S hh hExist ha4 hStage2 hStage3 hS hok stk hstk hstk64
      hFits)

/-- Transfers `cliInitiate_placed_ok` to any caller block `i < 619`. -/
theorem cliInitiate_caller_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {eEnvs : ExistingStoreCalleesEnvs}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {Stage3Fit : InitGhost → PreKeyBundleFields → IdentityKeyPair →
      List (BitVec 8) → List (BitVec 8) → BitVec 64 → BitVec 32 → State → M.σ → M.σ → Prop}
    {Stage3Out : InitGhost → PreKeyBundleFields → IdentityKeyPair →
      SignalPqxdh.DRKey → SignalPqxdh.HandshakeHdr → List AllocEvent → Prop}
    {callerProg : Program} {i : Nat}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) [IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hExist : ExistingStoreCalleesPlaced A lim eEnvs (cliGhostExterns gh (cliExternsPlaced mmpl W)) B)
    (ha4 : SubsetA4InitCalleesPlaced A lim InitStateEnv mmpl gh W)
    (hStage3 : Stage3PlacedOk A lim InitStateEnv InitEnv Stage3Fit Stage3Out mmpl gh W X B S)
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
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 521)
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget.initSlotSpecPlaced
        A lim InitEnv S stk) :=
  AssemblyPlacedBudget.cliInitiate_caller_placed_ok mmpl gh W X B S hh hExist ha4 hStage3 hS hok stk hstk
    hstk64 hFits hi

/-- Instantiates `cliInitiate_caller_placed_ok` on block `579` (`lsProg_579`) for `DefsPlacedBudget.initSlotSpecPlaced`. -/
theorem cliInitiate_slotOk_defs_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {eEnvs : ExistingStoreCalleesEnvs}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {Stage3Fit : InitGhost → PreKeyBundleFields → IdentityKeyPair →
      List (BitVec 8) → List (BitVec 8) → BitVec 64 → BitVec 32 → State → M.σ → M.σ → Prop}
    {Stage3Out : InitGhost → PreKeyBundleFields → IdentityKeyPair →
      SignalPqxdh.DRKey → SignalPqxdh.HandshakeHdr → List AllocEvent → Prop}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (envs : RunSlotEnvs) (needs : RunNeeds)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hExist : ExistingStoreCalleesPlaced A lim eEnvs (cliGhostExterns gh (cliExternsPlaced mmpl W)) B)
    (ha4 : SubsetA4InitCalleesPlaced A lim InitStateEnv mmpl gh W)
    (hStage3 : Stage3PlacedOk A lim InitStateEnv InitEnv Stage3Fit Stage3Out mmpl gh W X B S)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hok : ∀ F peer me, S.filesOk F peer me → S.initOk F peer me → InitOk₀ ⟨W.C, W.Q⟩ F peer me)
    (hFits : ∀ {stk : Nat}, cliInitiateNeed B ≤ stk → stk ≤ 2 ^ 63 →
      ∀ (x : InitGhost) (st0 : M.σ) (s0 : State),
        AtInitEntryPlaced x s0 →
        S.filesOk x.F x.peer.val x.me.val →
        S.initOk x.F x.peer.val x.me.val →
        InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val →
        x.coins.length < 2 ^ 63 →
        stk ≤ s0.sp.toNat →
        FitsEnv M lim st0 (InitEnv x) →
        CliInitiateBudgetFits M lim eEnvs InitStateEnv InitEnv Stage3Fit Stage3Out W X x s0 st0)
    (henv : envs.initiate = InitEnv)
    (hneed : needs.initiate = cliInitiateNeed B) :
    ∀ stk, (slotsOfPlaced A lim envs S needs).initiate.need ≤ stk → stk ≤ 2 ^ 63 →
      subroutine_ok (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 521)
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget.initSlotSpecPlaced
          A lim envs.initiate S stk) := by
  intro stk h1 h2
  dsimp only [slotsOfPlaced, mkSlot] at h1
  have hstk : cliInitiateNeed B ≤ stk := hneed ▸ h1
  rw [henv]
  exact cliInitiate_caller_placed_ok (i := 579) mmpl gh W X B S hh hExist ha4 hStage3 hS hok stk hstk h2
    (hFits hstk h2)

/-! ## Bridge to `Compose.SemPlacedBudget.initSlotSpecPlaced` and `slotsOfPlaced` -/

/-- Lifts `subroutine_ok` from `DefsPlacedBudget.initSlotSpecPlaced` to `Compose.SemPlacedBudget.initSlotSpecPlaced` when panics with `allocFailedIn` imply `S.initiate = none`. -/
theorem subroutine_ok_semInitSlot_of_defsInitSlot [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {S : RunSem} {stk : Nat}
    (hok : subroutine_ok prog entry
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget.initSlotSpecPlaced
        A lim InitEnv S stk))
    (hNoAllocFail : ∀ (x : InitGhost) (st0 : M.σ) (R : SepProp) (s0 sf : State),
      s0.pc = entry →
      s0.status = .Running →
      (s0.mem ⊨
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.initSlotSpecPlaced
          A lim InitEnv S stk).pre (x, st0) s0 ∗ R) →
      s0.spAligned = true →
      prog.CodeLoaded s0.mem →
      Steps prog s0 sf →
      sf.status = .Panicked →
      allocFailedIn s0 sf →
      S.initiate x.F x.peer.val x.me.val x.bundle x.coins = none) :
    subroutine_ok prog entry
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.initSlotSpecPlaced
        A lim InitEnv S stk) := by
  refine subroutine_ok_of_steps_outcome fun ⟨x, st0⟩ R s0 hpc hrun hpre hsp hL => ?_
  have hpreDefs :
      s0.mem ⊨
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget.initSlotSpecPlaced
          A lim InitEnv S stk).pre (x, st0) s0 ∗ R := hpre
  obtain ⟨sf, hsteps, hout⟩ :=
    subroutine_ok_elim_steps_outcome hok (x, st0) R s0 hpc hrun hpreDefs hsp hL
  refine ⟨sf, hsteps, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpanMem⟩ | ⟨code, hex, hexMem⟩ | ⟨hoom, hoomMem⟩
  · exact Or.inl ⟨hret, hcc, hpost⟩
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget.initSlotSpecPlaced,
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.initSlotSpecPlaced,
      withLsCodeRoLoaded] at hpanMem ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpanMem ⊢
    exact ⟨hpanMem.1.elim id (hNoAllocFail x st0 R s0 sf hpc hrun hpre hsp hL hsteps hpan),
      hpanMem.2⟩
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hexMem⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hoomMem⟩))

/-- Specializes `subroutine_ok_semInitSlot_of_defsInitSlot` when `Steps prog` never emits `allocFailedEvent`. -/
theorem subroutine_ok_semInitSlot_of_noAllocFail [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {S : RunSem} {stk : Nat}
    (hok : subroutine_ok prog entry
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget.initSlotSpecPlaced
        A lim InitEnv S stk))
    (hNoAlloc : ∀ s0 sf : State, Steps prog s0 sf → ¬ allocFailedIn s0 sf) :
    subroutine_ok prog entry
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.initSlotSpecPlaced
        A lim InitEnv S stk) :=
  subroutine_ok_semInitSlot_of_defsInitSlot hok
    fun _ _ _ s0 sf _ _ _ _ _ hsteps _ hfail => False.elim (hNoAlloc s0 sf hsteps hfail)

/-- Block `521` tight `Compose.SemPlacedBudget.initSlotSpecPlaced` theorem. -/
theorem cliInitiate_tight_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {eEnvs : ExistingStoreCalleesEnvs}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {Stage3Fit : InitGhost → PreKeyBundleFields → IdentityKeyPair →
      List (BitVec 8) → List (BitVec 8) → BitVec 64 → BitVec 32 → State → M.σ → M.σ → Prop}
    {Stage3Out : InitGhost → PreKeyBundleFields → IdentityKeyPair →
      SignalPqxdh.DRKey → SignalPqxdh.HandshakeHdr → List AllocEvent → Prop}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hExist : ExistingStoreCalleesPlaced A lim eEnvs (cliGhostExterns gh (cliExternsPlaced mmpl W)) B)
    (ha4 : SubsetA4InitCalleesPlaced A lim InitStateEnv mmpl gh W)
    (hStage3 : Stage3PlacedOk A lim InitStateEnv InitEnv Stage3Fit Stage3Out mmpl gh W X B S)
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
      (s0.mem ⊨
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.initSlotSpecPlaced
          A lim InitEnv S stk).pre (x, st0) s0 ∗ R) →
      s0.spAligned = true →
      (initProgPlaced mmpl gh W).CodeLoaded s0.mem →
      Steps (initProgPlaced mmpl gh W) s0 sf →
      sf.status = .Panicked →
      allocFailedIn s0 sf →
      S.initiate x.F x.peer.val x.me.val x.bundle x.coins = none) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 521)
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.initSlotSpecPlaced
        A lim InitEnv S stk) :=
  subroutine_ok_semInitSlot_of_defsInitSlot
    (cliInitiate_placed_ok mmpl gh W X B S hh hExist ha4 hStage3 hS hok stk hstk hstk64 hFits)
    hNoAllocFail

/-- Transfers `cliInitiate_tight_placed_ok` to any caller block `i < 619`. -/
theorem cliInitiate_caller_tight_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {eEnvs : ExistingStoreCalleesEnvs}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {Stage3Fit : InitGhost → PreKeyBundleFields → IdentityKeyPair →
      List (BitVec 8) → List (BitVec 8) → BitVec 64 → BitVec 32 → State → M.σ → M.σ → Prop}
    {Stage3Out : InitGhost → PreKeyBundleFields → IdentityKeyPair →
      SignalPqxdh.DRKey → SignalPqxdh.HandshakeHdr → List AllocEvent → Prop}
    {callerProg : Program} {i : Nat}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) [IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hExist : ExistingStoreCalleesPlaced A lim eEnvs (cliGhostExterns gh (cliExternsPlaced mmpl W)) B)
    (ha4 : SubsetA4InitCalleesPlaced A lim InitStateEnv mmpl gh W)
    (hStage3 : Stage3PlacedOk A lim InitStateEnv InitEnv Stage3Fit Stage3Out mmpl gh W X B S)
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
      (s0.mem ⊨
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.initSlotSpecPlaced
          A lim InitEnv S stk).pre (x, st0) s0 ∗ R) →
      s0.spAligned = true →
      callerProg.CodeLoaded s0.mem →
      Steps callerProg s0 sf →
      sf.status = .Panicked →
      allocFailedIn s0 sf →
      S.initiate x.F x.peer.val x.me.val x.bundle x.coins = none)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 521)
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.initSlotSpecPlaced
        A lim InitEnv S stk) :=
  subroutine_ok_semInitSlot_of_defsInitSlot
    (cliInitiate_caller_placed_ok (callerProg := callerProg) (i := i) mmpl gh W X B S hh hExist ha4 hStage3
      hS hok stk hstk hstk64 hFits hi)
    hNoAllocFail

/-- Packages `cliInitiate_caller_tight_placed_ok` into `RunCalleesPlaced.initiate` on block `579`. -/
theorem cliInitiate_slotOk_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {eEnvs : ExistingStoreCalleesEnvs}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {Stage3Fit : InitGhost → PreKeyBundleFields → IdentityKeyPair →
      List (BitVec 8) → List (BitVec 8) → BitVec 64 → BitVec 32 → State → M.σ → M.σ → Prop}
    {Stage3Out : InitGhost → PreKeyBundleFields → IdentityKeyPair →
      SignalPqxdh.DRKey → SignalPqxdh.HandshakeHdr → List AllocEvent → Prop}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (envs : RunSlotEnvs) (needs : RunNeeds)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hExist : ExistingStoreCalleesPlaced A lim eEnvs (cliGhostExterns gh (cliExternsPlaced mmpl W)) B)
    (ha4 : SubsetA4InitCalleesPlaced A lim InitStateEnv mmpl gh W)
    (hStage3 : Stage3PlacedOk A lim InitStateEnv InitEnv Stage3Fit Stage3Out mmpl gh W X B S)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hok : ∀ F peer me, S.filesOk F peer me → S.initOk F peer me → InitOk₀ ⟨W.C, W.Q⟩ F peer me)
    (hFits : ∀ {stk : Nat}, cliInitiateNeed B ≤ stk → stk ≤ 2 ^ 63 →
      ∀ (x : InitGhost) (st0 : M.σ) (s0 : State),
        AtInitEntryPlaced x s0 →
        S.filesOk x.F x.peer.val x.me.val →
        S.initOk x.F x.peer.val x.me.val →
        InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val →
        x.coins.length < 2 ^ 63 →
        stk ≤ s0.sp.toNat →
        FitsEnv M lim st0 (InitEnv x) →
        CliInitiateBudgetFits M lim eEnvs InitStateEnv InitEnv Stage3Fit Stage3Out W X x s0 st0)
    (hNoAllocFail : ∀ {stk : Nat}, cliInitiateNeed B ≤ stk → stk ≤ 2 ^ 63 →
      ∀ (x : InitGhost) (st0 : M.σ) (R : SepProp) (s0 sf : State),
        s0.pc = lsmpl.base 521 →
        s0.status = .Running →
        (s0.mem ⊨
          (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.initSlotSpecPlaced
            A lim InitEnv S stk).pre (x, st0) s0 ∗ R) →
        s0.spAligned = true →
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))).CodeLoaded s0.mem →
        Steps (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 sf →
        sf.status = .Panicked →
        allocFailedIn s0 sf →
        S.initiate x.F x.peer.val x.me.val x.bundle x.coins = none)
    (henv : envs.initiate = InitEnv)
    (hneed : needs.initiate = cliInitiateNeed B) :
    (slotsOfPlaced A lim envs S needs).initiate.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 521) := by
  intro stk h1 h2
  dsimp only [slotsOfPlaced, mkSlot] at h1 ⊢
  have hstk : cliInitiateNeed B ≤ stk := hneed ▸ h1
  rw [henv]
  exact cliInitiate_caller_tight_placed_ok (i := 579) mmpl gh W X B S hh hExist ha4 hStage3 hS hok stk hstk
    h2 (hFits hstk h2) (hNoAllocFail hstk h2)

/-! ## Pure model agreement re-exports -/

theorem initOk₀_pqInit_placed (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) (hwf : PqxdhPartyInSpecDomain W st)
    (hs : st.session = none) :
    InitOk₀ W (runFiles (pqInitInputs W st b t)) (addrValE st.party.other) (addrValE st.party) :=
  CryptoVerification.SignalSession.Cli.RunProofs.initOk₀_pqInit_placed W st b t hwf hs

theorem pqInitiateAgrees_initDef_placed (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (hS : S.initiate = initDef X W) : PqInitiateAgrees S X W :=
  CryptoVerification.SignalSession.Cli.RunProofs.pqInitiateAgrees_initDef_placed S X W hS

end

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SpecPlacedBudget

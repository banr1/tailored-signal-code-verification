/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.M24.ArgvPad -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudgetSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.ProcessBridgeExec
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process

/-!
# SWAR-Padded Route-B2 `MainOkCliExt*PadPlacedAt` & Strict Whole-ELF Composers

- **Role**: `Role::Proof` (outside the TCB).
- **Overview**:
  Additive SWAR-padded sibling of the Route-B2 `NeedLocks` declarations in
  `MainOkCliExtB2NeedLocksInst` and `CliStrictPlaced`:
  - `MainOkCliExt{Pq,Over}B2NeedLocksPadPlacedAt` + `.ofUnpadded` + constructors;
  - `MuslHarnessFineNeedLocks{,Guarded}PadPerInput` + `*_of_startup` + `.toUnpadded`;
  - `outcome_of_main_strict_b2_needLocks_{guarded_,}pad_perInput_at` +
    `cliRunExtOnInputsSigAt_of_strict_b2_needLocks_pad_*` +
    `cliSpecPqxdh{,NoMatch}_ext_strict_of_b2_needLocks_pad`;
  - `CliElfExtB2NeedLocksPadAssumptions` and
    `cliPqxdhExtOnInputsElfCorrectStrictPlacedAt_of_b2NeedLocksPadAssumptions`, recovering the
    existing `CliPqxdh*ElfCorrect*Placed*` conclusions token-for-token.
-/

public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlacedPadSat

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames.LibsignalSession (GhostState)
open CryptoVerification
  (LibsignalPlacement libsignalMutatedBlocks libsignalSessionExterns lsmpl)
open CryptoVerification.E2E
  (Bytes PEParams PreKeyBundleFields PreKeyMessageFields RecordExtras UnreachedPqxdhPrimitives
   initiateTapeLen wirePrekey wireWhisper)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.RustHeap (allocFailedEvent allocFailedIn)
open CryptoVerification.SignalSession
  (CliHooks CliSpecPqxdh CliSpecPqxdhNoMatch Inputs Outcome OutcomeMatchesModelExceptPath PqParty
   PqSessionMatches PqxdhPartyInSpecDomain cliInputsOk_pqInitInputs cliInputsOk_pqRecvInputs
   cliInputsOk_pqSendInputs cliProcessInputs coinsReadable_pqInitInputs coinsReadable_pqRecvInputs
   coinsReadable_pqSendInputs filesOf inputsLoadable_pqInitInputs inputsLoadable_pqRecvInputs
   inputsLoadable_pqSendInputs isSendOverCap_pqSendInputs isStdinOverCap_pqRecvInputs
   isStdinOverCap_pqSendInputs libsignalSessionLib maxPlaintextBytes not_isSendOverCap_of_stdin_le
   not_isSendOverCap_pqInitInputs not_isSendOverCap_pqRecvInputs not_isStdinOverCap_of_stdin_le
   not_isStdinOverCap_pqInitInputs observe outcomeOf outcomeOf_eq_aborted outcomeOf_eq_exited
   partyAddress pqInitInputs pqInitModel pqInputs pqRecvInputs pqRecvPrekeyModel pqRecvWhisperModel
   pqSendInputs pqSendModel pqxdhExpectedOutcome sessionFile stdinCapBytes)
open CryptoVerification.SignalSession.Cli
  (CliInputsOk CoinsReadable CommitOk ElfStaticOk InputsLoadable IsSendOverCap IsStdinOverCap
   MainCaseB2 MainPost MainResult RunAnswer StoresGhost cliInputs fsView_congr
   fsView_writeAll_initFsState loadState_fs_trace signExtend_ofNat_small)
open CryptoVerification.SignalSession.Cli.MainHops
  (CallV LsCodeInv RunCall cliMainStk cliResStack cliWrOk mProgPlaced mainFrameSize)
open CryptoVerification.SignalSession.Cli.RunCompose (runRel)
open CryptoVerification.SignalSession.Placed (CliElfCodeMatchesPlaced)
open LibsignalBinary.Heap (AllocEvent BudgetLimits FitsEvents rustAllocEvents)
open LibsignalBinary.Heap.Fine
  (CliElfMallocngLayout FineBudget StartupVmPreserved fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.ArgvPad
  (argvAtROPad b2MainEntryPreFinePad b2MainFrameFinePad b2MainFrameFinePad_entails_frame
   b2MainSpecTightNeedLocksFineAtPad strlenSpecROSat
   subroutine_ok_b2MainSpecTightNeedLocksFineAtPad_of_unpadded)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudgetSat
  (b2MainSpecTightNeedLocksFineAtPad_of_pqScopedRunSem_placed_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CliElfMallocngHarness
  (CliElfTokenCellsPlacedAt CliStackShape b2FineHookPool_of_needLocks cliProgExtPlacedAt
   cliRunExtOnInputsSigAt cliRunExtOnInputsSigAt_eq_some cliRunsToExtOnInputsAt_of_outcomeOf_observed
   cliRunsToExtOnInputsAt_of_outcomeOf_usage elfStaticOk_patchElfTokensPlacedAt
   loadState_patchElfTokensPlacedAt patchElfTokensPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (runSpecTightPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsFsPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced
  (CliElfExtB2NeedLocksAssumptions CliPqxdhExtOnInputsElfCorrectStrictPlacedAt
   MainOkCliExtOverB2NeedLocksPlacedAt MainOkCliExtPqB2NeedLocksPlacedAt
   MuslHarnessFineNeedLocksPerInput b2MainEntryPreFine cliStaticsPlacedAt exit_frame_needLocks_n)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.M2ExternNoAllocFail
  (ExternPreservesNoAllocFailed externPreservesNoAllocFailed_none steps_preserves_no_allocFailed)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst
  (B2MainRemainingHops cliRunSemD2c_placed cliRunSemD2c_pqxdh_and_noMatch_clauses_placed
   initFsState_cliProcessInputs_eq pqScopedCliRunSemD2c_pqxdh_and_noMatch_clauses_placed pqScopedRun)
open VerifiedLibraries.Mallocng (MallocngAuxvAt mallocngAddrsOfPlacement)

/-! ## 1. SWAR-Padded `MainOkCliExt{Pq,Over}B2NeedLocksPadPlacedAt` & Top Constructors -/

/-- Route-B2 `NeedLocks` + `argvAtROPad` 5-clause PQXDH `main` specification. -/
def MainOkCliExtPqB2NeedLocksPadPlacedAt
    (mpl mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (inputsOf : Inputs → ProcessInputs) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) (lim : BudgetLimits) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → RunAnswer → Prop,
      (∀ (γ : GhostName) (tp : BitVec 64),
        subroutine_ok (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx)
          (b2MainSpecTightNeedLocksFineAtPad libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            lim fineCostModel.init stk (cliStaticsPlacedAt mpl) Run inputsOf)) ∧
      ∀ p : PqParty, PqxdhPartyInSpecDomain WP p →
        (∀ (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen),
          p.session = none →
          ∃ a, Run (pqInitInputs WP p b t) a ∧
            observe (pqInitInputs WP p b t).files a =
              pqxdhExpectedOutcome WP (pqInitInputs WP p b t) (pqInitModel X WP p b t) ∧
            CommitOk (pqInitInputs WP p b t) (MainResult.ofAnswer a)) ∧
        (∀ (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64), m.length < 2 ^ 32 →
          ∃ a, Run (pqSendInputs WP p m r) a ∧
            observe (pqSendInputs WP p m r).files a =
              pqxdhExpectedOutcome WP (pqSendInputs WP p m r) (pqSendModel WP p m r.toList) ∧
            CommitOk (pqSendInputs WP p m r) (MainResult.ofAnswer a)) ∧
        (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
          ∃ a, Run (pqRecvInputs WP p (wireWhisper :: c) rc) a ∧
            observe (pqRecvInputs WP p (wireWhisper :: c) rc).files a =
              pqxdhExpectedOutcome WP (pqRecvInputs WP p (wireWhisper :: c) rc)
                (pqRecvWhisperModel WP p c rc) ∧
            CommitOk (pqRecvInputs WP p (wireWhisper :: c) rc) (MainResult.ofAnswer a)) ∧
        (∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
          (∀ x g, p.session = some (x, g) → PqSessionMatches x g m) →
          ∃ a, Run (pqRecvInputs WP p (wirePrekey :: m.bytes) rc) a ∧
            observe (pqRecvInputs WP p (wirePrekey :: m.bytes) rc).files a =
              pqxdhExpectedOutcome WP (pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
                (pqRecvPrekeyModel X WP p m rc) ∧
            CommitOk (pqRecvInputs WP p (wirePrekey :: m.bytes) rc) (MainResult.ofAnswer a)) ∧
        (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
          c.head? ≠ some wireWhisper → c.head? ≠ some wirePrekey →
          ∃ a, Run (pqRecvInputs WP p c rc) a ∧
            observe (pqRecvInputs WP p c rc).files a =
              .exited 1 [] (filesOf (pqRecvInputs WP p c rc).files) ∧
            CommitOk (pqRecvInputs WP p c rc) (MainResult.ofAnswer a))

/-- Route-B2 `NeedLocks` + `argvAtROPad` `NoMatch` `main` specification. -/
def MainOkCliExtOverB2NeedLocksPadPlacedAt
    (mpl mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (inputsOf : Inputs → ProcessInputs) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) (lim : BudgetLimits) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → RunAnswer → Prop,
      (∀ (γ : GhostName) (tp : BitVec 64),
        subroutine_ok (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx)
          (b2MainSpecTightNeedLocksFineAtPad libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            lim fineCostModel.init stk (cliStaticsPlacedAt mpl) Run inputsOf)) ∧
      ∀ st : PqParty, PqxdhPartyInSpecDomain WP st →
        ∀ (x : RecordExtras) (g : GhostState Bytes), st.session = some (x, g) →
        ∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
          ¬ PqSessionMatches x g m →
          ∃ a, Run (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) a ∧
            OutcomeMatchesModelExceptPath WP (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
              (sessionFile (partyAddress st.party.other))
              (pqRecvPrekeyModel X WP { st with session := none } m rc)
              (observe (pqRecvInputs WP st (wirePrekey :: m.bytes) rc).files a) ∧
            CommitOk (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) (MainResult.ofAnswer a)

theorem MainOkCliExtPqB2NeedLocksPadPlacedAt.ofUnpadded
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)}
    {mainIdx : Nat} {inputsOf : Inputs → ProcessInputs} {CodeOk : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat} {lim : BudgetLimits}
    (h : MainOkCliExtPqB2NeedLocksPlacedAt mpl mmpl ext mainIdx inputsOf CodeOk
      libcAddr brkStart stk lim) :
    MainOkCliExtPqB2NeedLocksPadPlacedAt mpl mmpl ext mainIdx inputsOf CodeOk
      libcAddr brkStart stk lim := by
  intro hDropNz X W
  obtain ⟨Run, hsub, hclauses⟩ := h hDropNz X W
  exact ⟨Run, fun γ tp => subroutine_ok_b2MainSpecTightNeedLocksFineAtPad_of_unpadded (hsub γ tp),
    hclauses⟩

theorem MainOkCliExtOverB2NeedLocksPadPlacedAt.ofUnpadded
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)}
    {mainIdx : Nat} {inputsOf : Inputs → ProcessInputs} {CodeOk : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat} {lim : BudgetLimits}
    (h : MainOkCliExtOverB2NeedLocksPlacedAt mpl mmpl ext mainIdx inputsOf CodeOk
      libcAddr brkStart stk lim) :
    MainOkCliExtOverB2NeedLocksPadPlacedAt mpl mmpl ext mainIdx inputsOf CodeOk
      libcAddr brkStart stk lim := by
  intro hDropNz X W
  obtain ⟨Run, hsub, hclauses⟩ := h hDropNz X W
  exact ⟨Run, fun γ tp => subroutine_ok_b2MainSpecTightNeedLocksFineAtPad_of_unpadded (hsub γ tp),
    hclauses⟩

theorem mainOkCliExtPqB2NeedLocksPadPlacedAt_of_pqScopedMainSubroutine
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {ext : CliHooks → String → Option (State → State)}
    {mainIdx : Nat} {inputsOf : Inputs → ProcessInputs} {CodeOk : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat} {lim : BudgetLimits}
    (hmain_sub : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        subroutine_ok (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx)
          (b2MainSpecTightNeedLocksFineAtPad libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            lim fineCostModel.init stk (cliStaticsPlacedAt mpl)
            (pqScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD2c_placed X W)))
            inputsOf)) :
    MainOkCliExtPqB2NeedLocksPadPlacedAt mpl mmpl ext mainIdx inputsOf CodeOk
      libcAddr brkStart stk lim := by
  intro hDropNz X W
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  refine ⟨pqScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD2c_placed X W)), hmain_sub hDropNz X W,
    fun p hp => ?_⟩
  have h6 := pqScopedCliRunSemD2c_pqxdh_and_noMatch_clauses_placed X W p hp
  exact ⟨h6.1, h6.2.1, h6.2.2.1, h6.2.2.2.1, h6.2.2.2.2.1⟩

theorem mainOkCliExtOverB2NeedLocksPadPlacedAt_of_pqScopedMainSubroutine
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {ext : CliHooks → String → Option (State → State)}
    {mainIdx : Nat} {inputsOf : Inputs → ProcessInputs} {CodeOk : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat} {lim : BudgetLimits}
    (hmain_sub : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        subroutine_ok (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx)
          (b2MainSpecTightNeedLocksFineAtPad libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            lim fineCostModel.init stk (cliStaticsPlacedAt mpl)
            (pqScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD2c_placed X W)))
            inputsOf)) :
    MainOkCliExtOverB2NeedLocksPadPlacedAt mpl mmpl ext mainIdx inputsOf CodeOk
      libcAddr brkStart stk lim := by
  intro hDropNz X W
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  refine ⟨pqScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD2c_placed X W)), hmain_sub hDropNz X W,
    fun st hst x g hs m rc hm hnot => ?_⟩
  obtain ⟨a, hrun, _, hexcept, hcommit⟩ :=
    (pqScopedCliRunSemD2c_pqxdh_and_noMatch_clauses_placed X W st hst).2.2.2.2.2 x g m rc hs hm hnot
  exact ⟨a, hrun, hexcept, hcommit⟩

theorem mainOkCliExtPqB2NeedLocksPadPlacedAt_of_mainSubroutine
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {ext : CliHooks → String → Option (State → State)}
    {mainIdx : Nat} {inputsOf : Inputs → ProcessInputs} {CodeOk : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat} {lim : BudgetLimits}
    (hmain_sub : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        subroutine_ok (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx)
          (b2MainSpecTightNeedLocksFineAtPad libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            lim fineCostModel.init stk (cliStaticsPlacedAt mpl)
            (runRel (cliRunSemD2c_placed X W))
            inputsOf)) :
    MainOkCliExtPqB2NeedLocksPadPlacedAt mpl mmpl ext mainIdx inputsOf CodeOk
      libcAddr brkStart stk lim := by
  intro hDropNz X W
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  refine ⟨runRel (cliRunSemD2c_placed X W), hmain_sub hDropNz X W, fun p hp => ?_⟩
  have h6 := cliRunSemD2c_pqxdh_and_noMatch_clauses_placed X W p hp
  exact ⟨h6.1, h6.2.1, h6.2.2.1, h6.2.2.2.1, h6.2.2.2.2.1⟩

theorem mainOkCliExtOverB2NeedLocksPadPlacedAt_of_mainSubroutine
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {ext : CliHooks → String → Option (State → State)}
    {mainIdx : Nat} {inputsOf : Inputs → ProcessInputs} {CodeOk : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat} {lim : BudgetLimits}
    (hmain_sub : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        subroutine_ok (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx)
          (b2MainSpecTightNeedLocksFineAtPad libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            lim fineCostModel.init stk (cliStaticsPlacedAt mpl)
            (runRel (cliRunSemD2c_placed X W))
            inputsOf)) :
    MainOkCliExtOverB2NeedLocksPadPlacedAt mpl mmpl ext mainIdx inputsOf CodeOk
      libcAddr brkStart stk lim := by
  intro hDropNz X W
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  refine ⟨runRel (cliRunSemD2c_placed X W), hmain_sub hDropNz X W,
    fun st hst x g hs m rc hm hnot => ?_⟩
  obtain ⟨a, hrun, _, hexcept, hcommit⟩ :=
    (cliRunSemD2c_pqxdh_and_noMatch_clauses_placed X W st hst).2.2.2.2.2 x g m rc hs hm hnot
  exact ⟨a, hrun, hexcept, hcommit⟩

theorem mainOkCliExtPqB2NeedLocksPadPlacedAt_of_runTight_and_hops_sat
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits} {hookStack : Nat}
    (St0 : UnreachedPqxdhPrimitives → CliHooks → Inputs → FineBudget → Prop)
    (St1 : UnreachedPqxdhPrimitives → CliHooks → Inputs → FineBudget → Prop)
    (St2 : UnreachedPqxdhPrimitives → CliHooks → Inputs → CallV → FineBudget → Prop)
    (St3 : UnreachedPqxdhPrimitives → CliHooks → Inputs → CallV → FineBudget → Prop)
    (St4 : UnreachedPqxdhPrimitives → CliHooks → Inputs → CallV → StoresGhost → FineBudget → Prop)
    (St5 : UnreachedPqxdhPrimitives → CliHooks → Inputs → CallV → StoresGhost → Bool →
      FineBudget → Prop)
    (RunEnv : UnreachedPqxdhPrimitives → CliHooks → RunCall → List AllocEvent → Prop)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hstrlenRO : ∀ W : CliHooks, HookSat (ext W) "strlen" (strlenSpecROSat hookStack))
    (hc_alloc : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hSt0 : ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (i : Inputs),
      CliInputsOk i → St0 X W i fineCostModel.init)
    (hSt01 : ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) {i : Inputs},
      CliInputsOk i → St0 X W i fineCostModel.init → i.argv ≠ [] →
        FitsEvents fineCostModel lim fineCostModel.init (rustAllocEvents (16 * i.argv.length) 8) ∧
          St1 X W i
            (fineCostModel.stepEvents (rustAllocEvents (16 * i.argv.length) 8) fineCostModel.init))
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (RunEnv X W) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack))
    (hhops : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @B2MainRemainingHops (libsignalPlacementOf mpl hblk hext_nodup)
          CodeOk mmpl ext W brkStart lim γ tp
          (St1 X W) (St2 X W) (St3 X W) (St4 X W) (St5 X W) (RunEnv X W)
          (pqScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD2c_placed X W)))) :
    MainOkCliExtPqB2NeedLocksPadPlacedAt mpl mmpl ext 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk lim :=
  mainOkCliExtPqB2NeedLocksPadPlacedAt_of_pqScopedMainSubroutine hblk hext_nodup
    fun hDropNz X W γ tp =>
      b2MainSpecTightNeedLocksFineAtPad_of_pqScopedRunSem_placed_sat hblk hext_nodup hCI
        ⟨W.C, W.Q⟩ (cliRunSemD2c_placed X W) hlibc initFsState_cliProcessInputs_eq
        (hstrlenRO W) (hc_alloc W γ tp) hstk (hSt0 X W) (hSt01 X W)
        (hrun hDropNz X W γ tp) (hhops hDropNz X W γ tp)

theorem mainOkCliExtOverB2NeedLocksPadPlacedAt_of_runTight_and_hops_sat
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits} {hookStack : Nat}
    (St0 : UnreachedPqxdhPrimitives → CliHooks → Inputs → FineBudget → Prop)
    (St1 : UnreachedPqxdhPrimitives → CliHooks → Inputs → FineBudget → Prop)
    (St2 : UnreachedPqxdhPrimitives → CliHooks → Inputs → CallV → FineBudget → Prop)
    (St3 : UnreachedPqxdhPrimitives → CliHooks → Inputs → CallV → FineBudget → Prop)
    (St4 : UnreachedPqxdhPrimitives → CliHooks → Inputs → CallV → StoresGhost → FineBudget → Prop)
    (St5 : UnreachedPqxdhPrimitives → CliHooks → Inputs → CallV → StoresGhost → Bool →
      FineBudget → Prop)
    (RunEnv : UnreachedPqxdhPrimitives → CliHooks → RunCall → List AllocEvent → Prop)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hstrlenRO : ∀ W : CliHooks, HookSat (ext W) "strlen" (strlenSpecROSat hookStack))
    (hc_alloc : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hSt0 : ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (i : Inputs),
      CliInputsOk i → St0 X W i fineCostModel.init)
    (hSt01 : ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) {i : Inputs},
      CliInputsOk i → St0 X W i fineCostModel.init → i.argv ≠ [] →
        FitsEvents fineCostModel lim fineCostModel.init (rustAllocEvents (16 * i.argv.length) 8) ∧
          St1 X W i
            (fineCostModel.stepEvents (rustAllocEvents (16 * i.argv.length) 8) fineCostModel.init))
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (RunEnv X W) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack))
    (hhops : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @B2MainRemainingHops (libsignalPlacementOf mpl hblk hext_nodup)
          CodeOk mmpl ext W brkStart lim γ tp
          (St1 X W) (St2 X W) (St3 X W) (St4 X W) (St5 X W) (RunEnv X W)
          (pqScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD2c_placed X W)))) :
    MainOkCliExtOverB2NeedLocksPadPlacedAt mpl mmpl ext 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk lim :=
  mainOkCliExtOverB2NeedLocksPadPlacedAt_of_pqScopedMainSubroutine hblk hext_nodup
    fun hDropNz X W γ tp =>
      b2MainSpecTightNeedLocksFineAtPad_of_pqScopedRunSem_placed_sat hblk hext_nodup hCI
        ⟨W.C, W.Q⟩ (cliRunSemD2c_placed X W) hlibc initFsState_cliProcessInputs_eq
        (hstrlenRO W) (hc_alloc W γ tp) hstk (hSt0 X W) (hSt01 X W)
        (hrun hDropNz X W γ tp) (hhops hDropNz X W γ tp)

/-! ## 2. SWAR-Padded Route-B2 `MuslHarnessFineNeedLocks{,Guarded}PadPerInput` -/

/-- SWAR-padded sibling of `CliStrictPlaced.MuslHarnessFineNeedLocksPerInput`, supplying
`b2MainEntryPreFinePad` (`argvAtROPad`) at `mainPc`. -/
def MuslHarnessFineNeedLocksPadPerInput (exitStk : Nat) (libcAddr : BitVec 64)
    (elf : ElfImage) (P : Program) (mainPc : BitVec 64)
    (inputsOf : Inputs → ProcessInputs)
    (mmpl : Obj.MultiPlacement) (lim : BudgetLimits) (st : FineBudget)
    (stk : Nat) (CodeOk : Memory → Prop) (Statics : SepProp) : Prop :=
  ElfStaticOk elf →
    ∀ i : Inputs, CliInputsOk i ∧ InputsLoadable i →
      ∃ (s0 sm : State) (Fr : SepProp) (γ : GhostName),
        let A := fineHookRustCliAllocBudget γ mmpl sm.tpidrEl0 elf.brkStart
        elf.loadState (inputsOf i) = .ok s0 ∧
        Steps P s0 sm ∧ sm.pc = mainPc ∧ sm.status = .Running ∧ sm.spAligned = true ∧
        sm.fs = s0.fs ∧ sm.trace = s0.trace ∧
        (sm.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 (i.argv.length + 1) ∧
        (sm.mem ⊨ b2MainEntryPreFinePad CodeOk A lim st stk Statics i sm ∗ Fr) ∧
        ∀ sr : State, Steps P sm sr → Returned sm sr →
          (sr.mem ⊨ ((libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt sm.sp exitStk ∗ Fr ∗ anyHeap) →
          ∃ sx : State, Steps P sr sx ∧
            sx.status = .Exited (((sr.readReg64 .x0).setWidth 32).signExtend 64) ∧
            sx.fs = sr.fs ∧ sx.trace = sr.trace

/-- Forget the SWAR pad from `MuslHarnessFineNeedLocksPadPerInput` into `Fr`, recovering unpadded
`MuslHarnessFineNeedLocksPerInput`. -/
theorem MuslHarnessFineNeedLocksPadPerInput.toUnpadded
    {exitStk : Nat} {libcAddr : BitVec 64} {elf : ElfImage} {P : Program} {mainPc : BitVec 64}
    {inputsOf : Inputs → ProcessInputs} {mmpl : Obj.MultiPlacement} {lim : BudgetLimits}
    {st : FineBudget} {stk : Nat} {CodeOk : Memory → Prop} {Statics : SepProp}
    (hH : MuslHarnessFineNeedLocksPadPerInput exitStk libcAddr elf P mainPc inputsOf
      mmpl lim st stk CodeOk Statics) :
    MuslHarnessFineNeedLocksPerInput exitStk libcAddr elf P mainPc inputsOf
      mmpl lim st stk CodeOk Statics := by
  intro hE i hi
  obtain ⟨s0, sm, Fr, γ, hload, hsteps, hpc, hrun, hal, hfs, htr, hx0, hmem, hexit⟩ := hH hE i hi
  let A := fineHookRustCliAllocBudget γ mmpl sm.tpidrEl0 elf.brkStart
  simp only [b2MainEntryPreFinePad, sepConj_assoc, satisfies_pure_sepConj] at hmem
  obtain ⟨⟨hCO, hsp⟩, hmem⟩ := hmem
  have hm' :=
    Satisfies.mono (sepConj_mono_left (b2MainFrameFinePad_entails_frame A lim st stk Statics i sm))
      hmem
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm'
  obtain ⟨Rpad, hm'⟩ := hm'
  refine ⟨s0, sm, Rpad ∗ Fr, γ, hload, hsteps, hpc, hrun, hal, hfs, htr, hx0, ?_, ?_⟩
  · simp only [b2MainEntryPreFine, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hCO, hsp⟩, by simpa only [sepConj_assoc] using hm'⟩
  · intro sr hsr hret hsr_mem
    apply hexit sr hsr hret
    have heq :
        (((libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt sm.sp exitStk ∗ (Rpad ∗ Fr) ∗ anyHeap) =
        (((libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt sm.sp exitStk ∗ Fr ∗ (Rpad ∗ anyHeap)) := by
      sep_ac_rfl
    rw [heq] at hsr_mem
    exact Satisfies.mono
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (entails_anyHeap _)))) hsr_mem

/-- 1-step SWAR-padded `MuslHarnessFineNeedLocksPadPerInput` builder from a `NeedLocks` startup+exit
witness producing `argvAtROPad` (`argvTable_dup_argvAtROPad`). -/
theorem muslHarnessFineNeedLocksPadPerInput_of_startup
    {exitStk : Nat} {libcAddr : BitVec 64} {elf : ElfImage} {P : Program} {mainPc : BitVec 64}
    {inputsOf : Inputs → ProcessInputs} {mmpl : Obj.MultiPlacement} {lim : BudgetLimits}
    {stk : Nat} {CodeOk : Memory → Prop} {Statics : SepProp}
    (hsh : ∀ i : Inputs, CliStackShape (inputsOf i))
    (hLayout : CliElfMallocngLayout elf lim)
    (hlibc : (mallocngAddrsOfPlacement mmpl).libc = libcAddr)
    (hStartup : ElfStaticOk elf →
      ∀ i : Inputs, CliInputsOk i ∧ InputsLoadable i →
        ∃ (s0 sm : State) (Fr : SepProp) (auxvPtr : BitVec 64) (errnoVal : BitVec 32),
          elf.loadState (inputsOf i) = .ok s0 ∧
          Steps P s0 sm ∧ sm.pc = mainPc ∧ sm.status = .Running ∧ sm.spAligned = true ∧
          sm.fs = s0.fs ∧ sm.trace = s0.trace ∧
          (sm.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 (i.argv.length + 1) ∧
          StartupVmPreserved s0 sm ∧
          0xa4 ≤ sm.tpidrEl0.toNat ∧ sm.tpidrEl0.toNat ≤ 2 ^ 48 ∧
          CodeOk sm.mem ∧ VerifiedLibraries.mallocngLib.CodeLoaded mmpl sm.mem ∧
          stk ≤ sm.sp.toNat ∧
          (sm.mem ⊨
            VerifiedLibraries.mallocngLib.dataInit mmpl ∗
              ((sm.tpidrEl0 - 0xa4#64) ↦₃₂ errnoVal) ∗
              ((libcAddr + 3#64) ↦₈ 0#8) ∗
              ((libcAddr + 48#64) ↦₆₄ 4096#64) ∗
              ((libcAddr + 8#64) ↦₆₄ auxvPtr) ∗
              MallocngAuxvAt auxvPtr ∗
              (argvAtROPad (sm.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString) ∗
                stackAt sm.sp stk ∗ Statics ∗ Fr)) ∧
          ∀ sr : State, Steps P sm sr → Returned sm sr →
            (sr.mem ⊨ ((libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt sm.sp exitStk ∗ Fr ∗ anyHeap) →
            ∃ sx : State, Steps P sr sx ∧
              sx.status = .Exited (((sr.readReg64 .x0).setWidth 32).signExtend 64) ∧
              sx.fs = sr.fs ∧ sx.trace = sr.trace) :
    MuslHarnessFineNeedLocksPadPerInput exitStk libcAddr elf P mainPc inputsOf
      mmpl lim fineCostModel.init stk CodeOk Statics := by
  intro hE i hi
  obtain ⟨s0, sm, Fr, auxvPtr, errnoVal, hload, hsteps, hpc, hrun, hal, hfs, htr, hx0,
    hVm, htpLo, htpHi, hCO, hCL, hsp, hmem, hexit⟩ := hStartup hE i hi
  obtain ⟨γ, hPool⟩ :=
    b2FineHookPool_of_needLocks hCL (hsh i) hLayout hload hVm htpLo htpHi hlibc hmem
  let A := fineHookRustCliAllocBudget γ mmpl sm.tpidrEl0 elf.brkStart
  have hEntry : sm.mem ⊨ b2MainEntryPreFinePad CodeOk A lim fineCostModel.init stk Statics i sm ∗ Fr := by
    simp only [b2MainEntryPreFinePad, b2MainFrameFinePad, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hCO, hsp⟩, ?_⟩
    let Argv := argvAtROPad (sm.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString)
    let Stk := stackAt sm.sp stk
    have heq :
        (A.pool lim fineCostModel.init sm ∗ (Argv ∗ Stk ∗ Statics ∗ Fr)) =
        (Argv ∗ Stk ∗ A.pool lim fineCostModel.init sm ∗ Statics ∗ Fr) := by sep_ac_rfl
    exact heq ▸ hPool
  exact ⟨s0, sm, Fr, γ, hload, hsteps, hpc, hrun, hal, hfs, htr, hx0, hEntry, hexit⟩

/-- Guarded twin of `MuslHarnessFineNeedLocksPadPerInput`. -/
def MuslHarnessFineNeedLocksGuardedPadPerInput (exitStk : Nat) (libcAddr : BitVec 64)
    (elf : ElfImage) (P : Program) (mainPc : BitVec 64)
    (inputsOf : Inputs → ProcessInputs)
    (mmpl : Obj.MultiPlacement) (lim : BudgetLimits) (st : FineBudget)
    (stk : Nat) (CodeOk : Memory → Prop) (Statics : SepProp)
    (EntryGuard : State → Prop) : Prop :=
  ElfStaticOk elf →
    ∀ i : Inputs, CliInputsOk i ∧ InputsLoadable i →
      ∃ (s0 sm : State) (Fr : SepProp) (γ : GhostName),
        let A := fineHookRustCliAllocBudget γ mmpl sm.tpidrEl0 elf.brkStart
        elf.loadState (inputsOf i) = .ok s0 ∧
        Steps P s0 sm ∧ sm.pc = mainPc ∧ sm.status = .Running ∧ sm.spAligned = true ∧
        sm.fs = s0.fs ∧ sm.trace = s0.trace ∧
        EntryGuard sm ∧
        (sm.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 (i.argv.length + 1) ∧
        (sm.mem ⊨ b2MainEntryPreFinePad CodeOk A lim st stk Statics i sm ∗ Fr) ∧
        ∀ sr : State, Steps P sm sr → Returned sm sr →
          (sr.mem ⊨ ((libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt sm.sp exitStk ∗ Fr ∗ anyHeap) →
          ∃ sx : State, Steps P sr sx ∧
            sx.status = .Exited (((sr.readReg64 .x0).setWidth 32).signExtend 64) ∧
            sx.fs = sr.fs ∧ sx.trace = sr.trace

theorem muslHarnessFineNeedLocksGuardedPadPerInput_of_startup
    {exitStk : Nat} {libcAddr : BitVec 64} {elf : ElfImage} {P : Program} {mainPc : BitVec 64}
    {inputsOf : Inputs → ProcessInputs} {mmpl : Obj.MultiPlacement} {lim : BudgetLimits}
    {stk : Nat} {CodeOk : Memory → Prop} {Statics : SepProp} {EntryGuard : State → Prop}
    (hsh : ∀ i : Inputs, CliStackShape (inputsOf i))
    (hLayout : CliElfMallocngLayout elf lim)
    (hlibc : (mallocngAddrsOfPlacement mmpl).libc = libcAddr)
    (hStartup : ElfStaticOk elf →
      ∀ i : Inputs, CliInputsOk i ∧ InputsLoadable i →
        ∃ (s0 sm : State) (Fr : SepProp) (auxvPtr : BitVec 64) (errnoVal : BitVec 32),
          elf.loadState (inputsOf i) = .ok s0 ∧
          Steps P s0 sm ∧ sm.pc = mainPc ∧ sm.status = .Running ∧ sm.spAligned = true ∧
          sm.fs = s0.fs ∧ sm.trace = s0.trace ∧
          EntryGuard sm ∧
          (sm.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 (i.argv.length + 1) ∧
          StartupVmPreserved s0 sm ∧
          0xa4 ≤ sm.tpidrEl0.toNat ∧ sm.tpidrEl0.toNat ≤ 2 ^ 48 ∧
          CodeOk sm.mem ∧ VerifiedLibraries.mallocngLib.CodeLoaded mmpl sm.mem ∧
          stk ≤ sm.sp.toNat ∧
          (sm.mem ⊨
            VerifiedLibraries.mallocngLib.dataInit mmpl ∗
              ((sm.tpidrEl0 - 0xa4#64) ↦₃₂ errnoVal) ∗
              ((libcAddr + 3#64) ↦₈ 0#8) ∗
              ((libcAddr + 48#64) ↦₆₄ 4096#64) ∗
              ((libcAddr + 8#64) ↦₆₄ auxvPtr) ∗
              MallocngAuxvAt auxvPtr ∗
              (argvAtROPad (sm.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString) ∗
                stackAt sm.sp stk ∗ Statics ∗ Fr)) ∧
          ∀ sr : State, Steps P sm sr → Returned sm sr →
            (sr.mem ⊨ ((libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt sm.sp exitStk ∗ Fr ∗ anyHeap) →
            ∃ sx : State, Steps P sr sx ∧
              sx.status = .Exited (((sr.readReg64 .x0).setWidth 32).signExtend 64) ∧
              sx.fs = sr.fs ∧ sx.trace = sr.trace) :
    MuslHarnessFineNeedLocksGuardedPadPerInput exitStk libcAddr elf P mainPc inputsOf
      mmpl lim fineCostModel.init stk CodeOk Statics EntryGuard := by
  intro hE i hi
  obtain ⟨s0, sm, Fr, auxvPtr, errnoVal, hload, hsteps, hpc, hrun, hal, hfs, htr, hG, hx0,
    hVm, htpLo, htpHi, hCO, hCL, hsp, hmem, hexit⟩ := hStartup hE i hi
  obtain ⟨γ, hPool⟩ :=
    b2FineHookPool_of_needLocks hCL (hsh i) hLayout hload hVm htpLo htpHi hlibc hmem
  let A := fineHookRustCliAllocBudget γ mmpl sm.tpidrEl0 elf.brkStart
  have hEntry : sm.mem ⊨ b2MainEntryPreFinePad CodeOk A lim fineCostModel.init stk Statics i sm ∗ Fr := by
    simp only [b2MainEntryPreFinePad, b2MainFrameFinePad, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hCO, hsp⟩, ?_⟩
    let Argv := argvAtROPad (sm.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString)
    let Stk := stackAt sm.sp stk
    have heq :
        (A.pool lim fineCostModel.init sm ∗ (Argv ∗ Stk ∗ Statics ∗ Fr)) =
        (Argv ∗ Stk ∗ A.pool lim fineCostModel.init sm ∗ Statics ∗ Fr) := by sep_ac_rfl
    exact heq ▸ hPool
  exact ⟨s0, sm, Fr, γ, hload, hsteps, hpc, hrun, hal, hfs, htr, hG, hx0, hEntry, hexit⟩

/-! ## 3. Whole-Process Outcome, `CliSpecPqxdh*`, & `CliElfExtB2NeedLocksPadAssumptions` -/

theorem outcome_of_main_strict_b2_needLocks_guarded_pad_perInput_at
    {exitStk : Nat} {libcAddr : BitVec 64} {elf : ElfImage} {P : Program} {mainPc : BitVec 64}
    {inputsOf : Inputs → ProcessInputs}
    {mmpl : Obj.MultiPlacement} {CodeOk : Memory → Prop}
    {lim : BudgetLimits} {st : FineBudget} {stk : Nat} {Statics : SepProp}
    {EntryGuard : State → Prop}
    {Run : Inputs → RunAnswer → Prop}
    (hsvc : P.svc = Syscall.standard)
    (hovr : ExternPreservesNoAllocFailed P.overrides)
    (hext : ExternPreservesNoAllocFailed P.externs)
    (hE : ElfStaticOk elf)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hCode : ∀ m, CodeOk m → P.CodeLoaded m)
    (hH : MuslHarnessFineNeedLocksGuardedPadPerInput exitStk libcAddr elf P mainPc inputsOf
      mmpl lim st stk CodeOk Statics EntryGuard)
    (hmain : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok P mainPc
        { (b2MainSpecTightNeedLocksFineAtPad libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
            lim st stk Statics Run inputsOf) with
          pre := fun x s => ⌜EntryGuard s⌝ ∗
            (b2MainSpecTightNeedLocksFineAtPad libcAddr CodeOk
              (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
              lim st stk Statics Run inputsOf).pre x s })
    (hstk : exitStk ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs} {r : MainResult} (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hc : MainCaseB2 Run IsSendOverCap IsStdinOverCap i r) :
    ∃ res, outcomeOf elf P (inputsOf i) = some res ∧ MainResult.Observed i.files r res := by
  obtain ⟨s0, sm, Fr, γ, hload, hsteps0, hpc, hrun, hal, hfs, htr, hG, hx0, hmem, hexit⟩ :=
    hH hE i ⟨hi, hl⟩
  let A := fineHookRustCliAllocBudget γ mmpl sm.tpidrEl0 elf.brkStart
  obtain ⟨hfs0, htr0⟩ := loadState_fs_trace hload
  simp only [b2MainEntryPreFinePad, sepConj_assoc, satisfies_pure_sepConj] at hmem
  obtain ⟨⟨hCO, hsp⟩, hmem⟩ := hmem
  let baseSpec := b2MainSpecTightNeedLocksFineAtPad libcAddr CodeOk A lim st stk Statics Run inputsOf
  have hpre : sm.mem ⊨
      ({ baseSpec with pre := fun x s => ⌜EntryGuard s⌝ ∗ baseSpec.pre x s }).pre ⟨i, r⟩ sm ∗ Fr := by
    simp only [baseSpec, b2MainSpecTightNeedLocksFineAtPad, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hG, ⟨hCO, hc, hi, ⟨hx0, hfs.trans hfs0, htr.trans htr0⟩, hsp⟩, hmem⟩
  obtain ⟨sf, hsteps1, hout, _⟩ :=
    (hmain γ sm.tpidrEl0).no_fault_before_outcome ⟨i, r⟩ Fr sm hpc hrun hpre hal (hCode sm.mem hCO)
  have hsteps01 := hsteps0.trans hsteps1
  rcases hout with ⟨hret, _, hpost⟩ | ⟨hpan, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · simp only [b2MainSpecTightNeedLocksFineAtPad, sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨⟨code, w, out, rfl, hw0, hfiles, hout⟩, hpost⟩ := hpost
    have hpost' : sf.mem ⊨ (((libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt sm.sp stk ∗ anyHeap) ∗ Fr := by
      simpa only [sepConj_assoc] using hpost
    obtain ⟨sx, hsteps2, hst, hfsx, htrx⟩ :=
      hexit sf hsteps1 hret (exit_frame_needLocks_n hstk hstk' hpost')
    have hle := hc.code_le rfl
    refine ⟨_, outcomeOf_eq_exited hload (hsteps01.trans hsteps2) hst, ?_⟩
    dsimp only [MainResult.Observed]
    refine ⟨?_, ?_, ?_⟩
    · rw [hw0, signExtend_ofNat_small hle]
    · rw [htrx, hout]
    · rw [hfsx, fsView_congr hfiles, hfs, hfs0, hfs_eq i]
      exact fsView_writeAll_initFsState i w hc.commitOk
  · simp only [b2MainSpecTightNeedLocksFineAtPad, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost.1 with rfl | hA
    · exact ⟨_, outcomeOf_eq_aborted hload hsteps01 hpan, trivial⟩
    · have hs0 : allocFailedEvent ∉ s0.trace := by rw [htr0]; simp
      exact absurd (List.mem_of_mem_drop hA)
        (steps_preserves_no_allocFailed hsvc hext hovr hsteps01 hs0)
  · exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim

theorem outcome_of_main_strict_b2_needLocks_pad_perInput_at
    {exitStk : Nat} {libcAddr : BitVec 64} {elf : ElfImage} {P : Program} {mainPc : BitVec 64}
    {inputsOf : Inputs → ProcessInputs}
    {mmpl : Obj.MultiPlacement} {CodeOk : Memory → Prop}
    {lim : BudgetLimits} {st : FineBudget} {stk : Nat} {Statics : SepProp}
    {Run : Inputs → RunAnswer → Prop}
    (hsvc : P.svc = Syscall.standard)
    (hovr : ExternPreservesNoAllocFailed P.overrides)
    (hext : ExternPreservesNoAllocFailed P.externs)
    (hE : ElfStaticOk elf)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hCode : ∀ m, CodeOk m → P.CodeLoaded m)
    (hH : MuslHarnessFineNeedLocksPadPerInput exitStk libcAddr elf P mainPc inputsOf
      mmpl lim st stk CodeOk Statics)
    (hmain : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok P mainPc
        (b2MainSpecTightNeedLocksFineAtPad libcAddr CodeOk
          (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
          lim st stk Statics Run inputsOf))
    (hstk : exitStk ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs} {r : MainResult} (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hc : MainCaseB2 Run IsSendOverCap IsStdinOverCap i r) :
    ∃ res, outcomeOf elf P (inputsOf i) = some res ∧ MainResult.Observed i.files r res := by
  obtain ⟨s0, sm, Fr, γ, hload, hsteps0, hpc, hrun, hal, hfs, htr, hx0, hmem, hexit⟩ :=
    hH hE i ⟨hi, hl⟩
  let A := fineHookRustCliAllocBudget γ mmpl sm.tpidrEl0 elf.brkStart
  obtain ⟨hfs0, htr0⟩ := loadState_fs_trace hload
  simp only [b2MainEntryPreFinePad, sepConj_assoc, satisfies_pure_sepConj] at hmem
  obtain ⟨⟨hCO, hsp⟩, hmem⟩ := hmem
  have hpre : sm.mem ⊨
      (b2MainSpecTightNeedLocksFineAtPad libcAddr CodeOk A lim st stk Statics Run inputsOf).pre
        ⟨i, r⟩ sm ∗ Fr := by
    simp only [b2MainSpecTightNeedLocksFineAtPad, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hCO, hc, hi, ⟨hx0, hfs.trans hfs0, htr.trans htr0⟩, hsp⟩, hmem⟩
  obtain ⟨sf, hsteps1, hout, _⟩ :=
    (hmain γ sm.tpidrEl0).no_fault_before_outcome ⟨i, r⟩ Fr sm hpc hrun hpre hal (hCode sm.mem hCO)
  have hsteps01 := hsteps0.trans hsteps1
  rcases hout with ⟨hret, _, hpost⟩ | ⟨hpan, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · simp only [b2MainSpecTightNeedLocksFineAtPad, sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨⟨code, w, out, rfl, hw0, hfiles, hout⟩, hpost⟩ := hpost
    have hpost' : sf.mem ⊨ (((libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt sm.sp stk ∗ anyHeap) ∗ Fr := by
      simpa only [sepConj_assoc] using hpost
    obtain ⟨sx, hsteps2, hst, hfsx, htrx⟩ :=
      hexit sf hsteps1 hret (exit_frame_needLocks_n hstk hstk' hpost')
    have hle := hc.code_le rfl
    refine ⟨_, outcomeOf_eq_exited hload (hsteps01.trans hsteps2) hst, ?_⟩
    dsimp only [MainResult.Observed]
    refine ⟨?_, ?_, ?_⟩
    · rw [hw0, signExtend_ofNat_small hle]
    · rw [htrx, hout]
    · rw [hfsx, fsView_congr hfiles, hfs, hfs0, hfs_eq i]
      exact fsView_writeAll_initFsState i w hc.commitOk
  · simp only [b2MainSpecTightNeedLocksFineAtPad, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost.1 with rfl | hA
    · exact ⟨_, outcomeOf_eq_aborted hload hsteps01 hpan, trivial⟩
    · have hs0 : allocFailedEvent ∉ s0.trace := by rw [htr0]; simp
      exact absurd (List.mem_of_mem_drop hA)
        (steps_preserves_no_allocFailed hsvc hext hovr hsteps01 hs0)
  · exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim

theorem cliRunExtOnInputsSigAt_of_strict_b2_needLocks_pad_stdinOverCap
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {idx : Nat}
    {inputsOf : Inputs → ProcessInputs} {exitStk : Nat} {libcAddr : BitVec 64}
    {elf : ElfImage} {W : CliHooks}
    {CodeOk : Memory → Prop} {lim : BudgetLimits} {st : FineBudget} {stk : Nat}
    {Statics : SepProp} {Run : Inputs → RunAnswer → Prop}
    (hext : ExternPreservesNoAllocFailed (ext W))
    (hE : ElfStaticOk elf)
    (htok : CliElfTokenCellsPlacedAt mpl elf)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hCode : ∀ m, CodeOk m → (cliProgExtPlacedAt mpl ext idx W).CodeLoaded m)
    (hH : MuslHarnessFineNeedLocksPadPerInput exitStk libcAddr (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx) inputsOf
      mmpl lim st stk CodeOk Statics)
    (hmain : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx)
        (b2MainSpecTightNeedLocksFineAtPad libcAddr CodeOk
          (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
          lim st stk Statics Run inputsOf))
    (hstk : exitStk ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs}
    (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hstin : IsStdinOverCap i) :
    cliRunExtOnInputsSigAt mpl ext idx inputsOf elf W i =
      some (.exited 2 [] (filesOf i.files)) := by
  have hbrk : (patchElfTokensPlacedAt mpl elf).brkStart = elf.brkStart := rfl
  obtain ⟨res, hout, hresObs⟩ :=
    outcome_of_main_strict_b2_needLocks_pad_perInput_at rfl externPreservesNoAllocFailed_none hext
      (elfStaticOk_patchElfTokensPlacedAt hE) hfs_eq hCode hH
      (fun γ tp => by simpa only [hbrk] using hmain γ tp)
      hstk hstk' hi hl (MainCaseB2.stdinOverCap hstin)
  have hruns := cliRunsToExtOnInputsAt_of_outcomeOf_usage
    (loadState_patchElfTokensPlacedAt hE htok (inputsOf i)) hout hresObs
  exact cliRunExtOnInputsSigAt_eq_some hruns

theorem cliRunExtOnInputsSigAt_of_strict_b2_needLocks_pad_sendOverCap
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {idx : Nat}
    {inputsOf : Inputs → ProcessInputs} {exitStk : Nat} {libcAddr : BitVec 64}
    {elf : ElfImage} {W : CliHooks}
    {CodeOk : Memory → Prop} {lim : BudgetLimits} {st : FineBudget} {stk : Nat}
    {Statics : SepProp} {Run : Inputs → RunAnswer → Prop}
    (hext : ExternPreservesNoAllocFailed (ext W))
    (hE : ElfStaticOk elf)
    (htok : CliElfTokenCellsPlacedAt mpl elf)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hCode : ∀ m, CodeOk m → (cliProgExtPlacedAt mpl ext idx W).CodeLoaded m)
    (hH : MuslHarnessFineNeedLocksPadPerInput exitStk libcAddr (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx) inputsOf
      mmpl lim st stk CodeOk Statics)
    (hmain : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx)
        (b2MainSpecTightNeedLocksFineAtPad libcAddr CodeOk
          (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
          lim st stk Statics Run inputsOf))
    (hstk : exitStk ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs}
    (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hover : IsSendOverCap i) (hnstin : ¬ IsStdinOverCap i)
    (hcoins : CoinsReadable i) :
    cliRunExtOnInputsSigAt mpl ext idx inputsOf elf W i =
      some (.exited 1 [] (filesOf i.files)) := by
  have hbrk : (patchElfTokensPlacedAt mpl elf).brkStart = elf.brkStart := rfl
  obtain ⟨res, hout, hresObs⟩ :=
    outcome_of_main_strict_b2_needLocks_pad_perInput_at rfl externPreservesNoAllocFailed_none hext
      (elfStaticOk_patchElfTokensPlacedAt hE) hfs_eq hCode hH
      (fun γ tp => by simpa only [hbrk] using hmain γ tp)
      hstk hstk' hi hl (MainCaseB2.sendOverCap hover hnstin hcoins)
  have hruns := cliRunsToExtOnInputsAt_of_outcomeOf_observed (a := some none)
    (loadState_patchElfTokensPlacedAt hE htok (inputsOf i)) hout hresObs
  exact cliRunExtOnInputsSigAt_eq_some hruns

theorem cliRunExtOnInputsSigAt_of_strict_b2_needLocks_pad_call_obs
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {idx : Nat}
    {inputsOf : Inputs → ProcessInputs} {exitStk : Nat} {libcAddr : BitVec 64}
    {elf : ElfImage} {W : CliHooks}
    {CodeOk : Memory → Prop} {lim : BudgetLimits} {st : FineBudget} {stk : Nat}
    {Statics : SepProp} {Run : Inputs → RunAnswer → Prop}
    (hext : ExternPreservesNoAllocFailed (ext W))
    (hE : ElfStaticOk elf)
    (htok : CliElfTokenCellsPlacedAt mpl elf)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hCode : ∀ m, CodeOk m → (cliProgExtPlacedAt mpl ext idx W).CodeLoaded m)
    (hH : MuslHarnessFineNeedLocksPadPerInput exitStk libcAddr (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx) inputsOf
      mmpl lim st stk CodeOk Statics)
    (hmain : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx)
        (b2MainSpecTightNeedLocksFineAtPad libcAddr CodeOk
          (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
          lim st stk Statics Run inputsOf))
    (hstk : exitStk ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs} {a : RunAnswer} {o : Outcome}
    (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hrun : Run i a) (hnover : ¬ IsSendOverCap i) (hnstin : ¬ IsStdinOverCap i)
    (hobs : observe i.files a = o)
    (hcoins : CoinsReadable i) (hcommit : CommitOk i (MainResult.ofAnswer a)) :
    cliRunExtOnInputsSigAt mpl ext idx inputsOf elf W i = some o := by
  have hbrk : (patchElfTokensPlacedAt mpl elf).brkStart = elf.brkStart := rfl
  obtain ⟨res, hout, hresObs⟩ :=
    outcome_of_main_strict_b2_needLocks_pad_perInput_at rfl externPreservesNoAllocFailed_none hext
      (elfStaticOk_patchElfTokensPlacedAt hE) hfs_eq hCode hH
      (fun γ tp => by simpa only [hbrk] using hmain γ tp)
      hstk hstk' hi hl (MainCaseB2.call hrun hnover hnstin hcoins hcommit)
  have hruns := cliRunsToExtOnInputsAt_of_outcomeOf_observed
    (loadState_patchElfTokensPlacedAt hE htok (inputsOf i)) hout hresObs
  rw [hobs] at hruns
  exact cliRunExtOnInputsSigAt_eq_some hruns

theorem cliRunExtOnInputsSigAt_of_strict_b2_needLocks_pad_call_pred
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {idx : Nat}
    {inputsOf : Inputs → ProcessInputs} {exitStk : Nat} {libcAddr : BitVec 64}
    {elf : ElfImage} {W : CliHooks}
    {CodeOk : Memory → Prop} {lim : BudgetLimits} {st : FineBudget} {stk : Nat}
    {Statics : SepProp} {Run : Inputs → RunAnswer → Prop} {P : Outcome → Prop}
    (hext : ExternPreservesNoAllocFailed (ext W))
    (hE : ElfStaticOk elf)
    (htok : CliElfTokenCellsPlacedAt mpl elf)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hCode : ∀ m, CodeOk m → (cliProgExtPlacedAt mpl ext idx W).CodeLoaded m)
    (hH : MuslHarnessFineNeedLocksPadPerInput exitStk libcAddr (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx) inputsOf
      mmpl lim st stk CodeOk Statics)
    (hmain : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx)
        (b2MainSpecTightNeedLocksFineAtPad libcAddr CodeOk
          (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
          lim st stk Statics Run inputsOf))
    (hstk : exitStk ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs} {a : RunAnswer}
    (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hrun : Run i a) (hnover : ¬ IsSendOverCap i) (hnstin : ¬ IsStdinOverCap i)
    (hp : P (observe i.files a))
    (hcoins : CoinsReadable i) (hcommit : CommitOk i (MainResult.ofAnswer a)) :
    ∃ o, cliRunExtOnInputsSigAt mpl ext idx inputsOf elf W i = some o ∧ P o :=
  ⟨observe i.files a,
    cliRunExtOnInputsSigAt_of_strict_b2_needLocks_pad_call_obs hext hE htok hfs_eq hCode hH
      hmain hstk hstk' hi hl hrun hnover hnstin rfl hcoins hcommit, hp⟩

theorem cliSpecPqxdh_ext_strict_of_b2_needLocks_pad
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {mainIdx : Nat}
    {inputsOf : Inputs → ProcessInputs} {exitStk : Nat} {libcAddr : BitVec 64}
    {CodeOk : Memory → Prop} {stk : Nat} {lim : BudgetLimits}
    {elf : ElfImage} {W : CliHooks}
    (hext : ExternPreservesNoAllocFailed (ext W))
    (hE : ElfStaticOk elf)
    (htok : CliElfTokenCellsPlacedAt mpl elf)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hCode : ∀ m, CodeOk m → (cliProgExtPlacedAt mpl ext mainIdx W).CodeLoaded m)
    (hH : MuslHarnessFineNeedLocksPadPerInput exitStk libcAddr (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx) inputsOf
      mmpl lim fineCostModel.init stk CodeOk (cliStaticsPlacedAt mpl))
    (hstk : exitStk ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    (hDropNz : mpl.base 547 ≠ 0#64)
    (hmain : MainOkCliExtPqB2NeedLocksPadPlacedAt mpl mmpl ext mainIdx inputsOf CodeOk
      libcAddr elf.brkStart stk lim) :
    ∀ X : UnreachedPqxdhPrimitives,
      CliSpecPqxdh (cliRunExtOnInputsSigAt mpl ext mainIdx inputsOf elf W) X ⟨W.C, W.Q⟩ := by
  intro X p hp
  let WP : PEParams := ⟨W.C, W.Q⟩
  obtain ⟨Run, hmainW, hclauses⟩ := hmain hDropNz X W
  obtain ⟨hInit, hSend, hWhisper, hPrekey, hBad⟩ := hclauses p hp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b t hnone
    obtain ⟨a, hrun, hobs, hcommit⟩ := hInit b t hnone
    exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_pad_call_obs hext hE htok hfs_eq
      hCode hH hmainW hstk hstk'
      (cliInputsOk_pqInitInputs WP p b t) (inputsLoadable_pqInitInputs WP p b t hp)
      hrun (not_isSendOverCap_pqInitInputs WP p b t)
      (not_isStdinOverCap_pqInitInputs WP p b t) hobs
      (coinsReadable_pqInitInputs WP p b t) hcommit
  · intro m r hm
    by_cases hstin : m.length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_pad_stdinOverCap hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqSendInputs WP p m r) (inputsLoadable_pqSendInputs WP p m r hp)
        (isStdinOverCap_pqSendInputs WP p m r hstin)
    · simp only [hstin, ↓reduceIte]
      have hnstin : ¬ IsStdinOverCap (pqSendInputs WP p m r) :=
        not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)
      by_cases hover : m.length > maxPlaintextBytes
      · simp only [hover, ↓reduceIte]
        exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_pad_sendOverCap hext hE htok hfs_eq
          hCode hH hmainW hstk hstk'
          (cliInputsOk_pqSendInputs WP p m r) (inputsLoadable_pqSendInputs WP p m r hp)
          (isSendOverCap_pqSendInputs WP p m r (by unfold maxPlaintextBytes at hover; exact hover))
          hnstin (coinsReadable_pqSendInputs WP p m r)
      · simp only [hover, ↓reduceIte]
        obtain ⟨a, hrun, hobs, hcommit⟩ := hSend m r hm
        exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_pad_call_obs hext hE htok hfs_eq
          hCode hH hmainW hstk hstk'
          (cliInputsOk_pqSendInputs WP p m r) (inputsLoadable_pqSendInputs WP p m r hp)
          hrun
          (not_isSendOverCap_of_stdin_le
            (by simp only [pqSendInputs, pqInputs]; unfold maxPlaintextBytes at hover; omega))
          hnstin hobs (coinsReadable_pqSendInputs WP p m r) hcommit
  · intro c rc hc
    by_cases hstin : (wireWhisper :: c).length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_pad_stdinOverCap hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP p (wireWhisper :: c) rc)
        (inputsLoadable_pqRecvInputs WP p (wireWhisper :: c) rc hp)
        (isStdinOverCap_pqRecvInputs WP p (wireWhisper :: c) rc hstin)
    · simp only [hstin, ↓reduceIte]
      obtain ⟨a, hrun, hobs, hcommit⟩ := hWhisper c rc hc
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_pad_call_obs hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP p (wireWhisper :: c) rc)
        (inputsLoadable_pqRecvInputs WP p (wireWhisper :: c) rc hp)
        hrun (not_isSendOverCap_pqRecvInputs WP p (wireWhisper :: c) rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)) hobs
        (coinsReadable_pqRecvInputs WP p (wireWhisper :: c) rc) hcommit
  · intro m rc hm hmatch
    by_cases hstin : (wirePrekey :: m.bytes).length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_pad_stdinOverCap hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
        (inputsLoadable_pqRecvInputs WP p (wirePrekey :: m.bytes) rc hp)
        (isStdinOverCap_pqRecvInputs WP p (wirePrekey :: m.bytes) rc hstin)
    · simp only [hstin, ↓reduceIte]
      obtain ⟨a, hrun, hobs, hcommit⟩ := hPrekey m rc hm hmatch
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_pad_call_obs hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
        (inputsLoadable_pqRecvInputs WP p (wirePrekey :: m.bytes) rc hp)
        hrun (not_isSendOverCap_pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)) hobs
        (coinsReadable_pqRecvInputs WP p (wirePrekey :: m.bytes) rc) hcommit
  · intro c rc hc h2 h3
    by_cases hstin : c.length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_pad_stdinOverCap hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP p c rc) (inputsLoadable_pqRecvInputs WP p c rc hp)
        (isStdinOverCap_pqRecvInputs WP p c rc hstin)
    · simp only [hstin, ↓reduceIte]
      obtain ⟨a, hrun, hobs, hcommit⟩ := hBad c rc hc h2 h3
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_pad_call_obs hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP p c rc) (inputsLoadable_pqRecvInputs WP p c rc hp)
        hrun (not_isSendOverCap_pqRecvInputs WP p c rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)) hobs
        (coinsReadable_pqRecvInputs WP p c rc) hcommit

theorem cliSpecPqxdhNoMatch_ext_strict_of_b2_needLocks_pad
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {mainIdx : Nat}
    {inputsOf : Inputs → ProcessInputs} {exitStk : Nat} {libcAddr : BitVec 64}
    {CodeOk : Memory → Prop} {stk : Nat} {lim : BudgetLimits}
    {elf : ElfImage} {W : CliHooks}
    (hext : ExternPreservesNoAllocFailed (ext W))
    (hE : ElfStaticOk elf)
    (htok : CliElfTokenCellsPlacedAt mpl elf)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hCode : ∀ m, CodeOk m → (cliProgExtPlacedAt mpl ext mainIdx W).CodeLoaded m)
    (hH : MuslHarnessFineNeedLocksPadPerInput exitStk libcAddr (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx) inputsOf
      mmpl lim fineCostModel.init stk CodeOk (cliStaticsPlacedAt mpl))
    (hstk : exitStk ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    (hDropNz : mpl.base 547 ≠ 0#64)
    (hover : MainOkCliExtOverB2NeedLocksPadPlacedAt mpl mmpl ext mainIdx inputsOf CodeOk
      libcAddr elf.brkStart stk lim) :
    ∀ X : UnreachedPqxdhPrimitives,
      CliSpecPqxdhNoMatch (cliRunExtOnInputsSigAt mpl ext mainIdx inputsOf elf W) X ⟨W.C, W.Q⟩ := by
  intro X st hst x g hsess m rc hm hnomatch
  let WP : PEParams := ⟨W.C, W.Q⟩
  obtain ⟨Run, hmainW, hclause⟩ := hover hDropNz X W
  by_cases hstin : (wirePrekey :: m.bytes).length > stdinCapBytes
  · simp only [hstin, ↓reduceIte]
    exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_pad_stdinOverCap hext hE htok hfs_eq
      hCode hH hmainW hstk hstk'
      (cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
      (inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst)
      (isStdinOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hstin)
  · simp only [hstin, ↓reduceIte]
    obtain ⟨a, hrun, hobsEx, hcommit⟩ := hclause st hst x g hsess m rc hm hnomatch
    exact
      cliRunExtOnInputsSigAt_of_strict_b2_needLocks_pad_call_pred hext hE htok hfs_eq hCode hH
        hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
        (inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst)
        hrun (not_isSendOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin))
        hobsEx (coinsReadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc) hcommit

/-- SWAR-padded sibling of `CliStrictPlaced.CliElfExtB2NeedLocksAssumptions`, replacing
`MuslHarnessFineNeedLocksPerInput` in `.harness` with `MuslHarnessFineNeedLocksPadPerInput`. -/
structure CliElfExtB2NeedLocksPadAssumptions
    (mpl mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (inputsOf : Inputs → ProcessInputs)
    (exitStk : Nat) (libcAddr : BitVec 64) (stk : Nat) (CodeOk : Memory → Prop)
    (lim : BudgetLimits) (elf : ElfImage) : Prop where
  elfStaticOk : ElfStaticOk elf
  codeMatches : CliElfCodeMatchesPlaced mpl mmpl elf
  mallocngPlaceable : VerifiedLibraries.mallocngLib.Placeable mmpl
  mallocngInElf : VerifiedLibraries.mallocngLib.InElf elf mmpl
  mallocngDataDisjoint : VerifiedLibraries.mallocngLib.DataDisjoint mmpl
  tokenCells : CliElfTokenCellsPlacedAt mpl elf
  mallocngLayout : CliElfMallocngLayout elf lim
  base547NeZero : mpl.base 547 ≠ 0#64
  stkLo : exitStk ≤ stk
  stkHi : stk ≤ 2 ^ 64
  fsEq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i)
  codeLoaded : ∀ (W : CliHooks) (m : Memory),
    CodeOk m → (cliProgExtPlacedAt mpl ext mainIdx W).CodeLoaded m
  harness : ∀ W : CliHooks,
    MuslHarnessFineNeedLocksPadPerInput exitStk libcAddr (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx) inputsOf
      mmpl lim fineCostModel.init stk CodeOk (cliStaticsPlacedAt mpl)

theorem CliElfExtB2NeedLocksPadAssumptions.toUnpadded
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)}
    {mainIdx : Nat} {inputsOf : Inputs → ProcessInputs}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {lim : BudgetLimits} {elf : ElfImage}
    (H : CliElfExtB2NeedLocksPadAssumptions mpl mmpl ext mainIdx inputsOf
      exitStk libcAddr stk CodeOk lim elf) :
    CliElfExtB2NeedLocksAssumptions mpl mmpl ext mainIdx inputsOf
      exitStk libcAddr stk CodeOk lim elf :=
  { H with harness := fun W => (H.harness W).toUnpadded }

/-- **SWAR-Padded Route-B2 `NeedLocks` Top Strict Placed ELF Theorem:**
recovers the existing `CliPqxdhExtOnInputsElfCorrectStrictPlacedAt` conclusion token-for-token. -/
theorem cliPqxdhExtOnInputsElfCorrectStrictPlacedAt_of_b2NeedLocksPadAssumptions
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)}
    {mainIdx : Nat} {inputsOf : Inputs → ProcessInputs}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {lim : BudgetLimits} {elf : ElfImage}
    (hext : ∀ W : CliHooks, ExternPreservesNoAllocFailed (ext W))
    (H : CliElfExtB2NeedLocksPadAssumptions mpl mmpl ext mainIdx inputsOf
      exitStk libcAddr stk CodeOk lim elf)
    (hmain : MainOkCliExtPqB2NeedLocksPadPlacedAt mpl mmpl ext mainIdx inputsOf CodeOk
      libcAddr elf.brkStart stk lim)
    (hover : MainOkCliExtOverB2NeedLocksPadPlacedAt mpl mmpl ext mainIdx inputsOf CodeOk
      libcAddr elf.brkStart stk lim) :
    CliPqxdhExtOnInputsElfCorrectStrictPlacedAt mpl mmpl ext mainIdx inputsOf elf :=
  ⟨H.codeMatches, fun W X =>
    ⟨cliSpecPqxdh_ext_strict_of_b2_needLocks_pad (hext W) H.elfStaticOk H.tokenCells
      H.fsEq (H.codeLoaded W) (H.harness W) H.stkLo H.stkHi H.base547NeZero hmain X,
     cliSpecPqxdhNoMatch_ext_strict_of_b2_needLocks_pad (hext W) H.elfStaticOk H.tokenCells
      H.fsEq (H.codeLoaded W) (H.harness W) H.stkLo H.stkHi H.base547NeZero hover X⟩⟩

end LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlacedPadSat

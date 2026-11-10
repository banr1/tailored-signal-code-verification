/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomSpecF3 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MatchingPathBF3 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2G -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.BundleInitElfF3 -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
import Arm64.Trusted.Spec.Hoare
import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3NonCanonF3
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3ExternNoAllocFail
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.PlacedOomRecovery2
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process

/-!
# Guarded F3 Two-Placement Whole-Process Assembly of `CliPqBinaryV2OomF3Placed` (`D3BinaryOomProofF3G`)

- **Role**: `Role::Proof` (outside the TCB).
- **Overview**:
  Route-2 (`w2_c12_route2_stmts.md` §3.2 `R2-D1..D4`) entry-guarded siblings of the D3 / flat-bundle
  `init` `MainOk*` arm specifications and whole-process `D3BinaryOomProofF3` / `ElfSlicesPqOomPlaced`
  constructors. Each `MainOk*G` predicate wraps the `b2MainSpecTightNeedLocksFineAt` subroutine
  specification in `withEntryGuard (F3MemsetMemcpyEntryLrFalse mmpl)` and eliminates the guard
  internally at the process harness boundary via `CliStrictPlaced2G` (`R2-G4`), concluding the
  unchanged guard-free `cliRunPlacedSig = some …`, `OutcomeOrExcusedAbort …`, `≠ none`,
  `CliPqBinaryV2OomF3Placed`, `LibsignalCliPqBinaryV2OomF3PlacedAt`, and
  `CliPqBinaryV2OomF3BytesPlaced cliElfBytes`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomProofF3G

open Arm64 (FsEntry GhostName Memory normalizePath subroutine_ok)
open Arm64.Obj (MultiPlacement)
open Arm64.Process (ElfImage ProcessInputs)
open CryptoGames.LibsignalSession (GhostState)
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage)
open CryptoVerification.E2E
  (PEParams PreKeyBundleFields PreKeyMessageFields RecordExtras UnreachedPqxdhPrimitives
   initiateTapeLen wirePrekey)
open CryptoVerification.SignalSession
  (CliHooks CliReachesOOMPlaced Inputs Outcome OutcomeMatchesModelExceptPath OutcomeOrExcusedAbort
   PqParty PqSessionMatches PqxdhPartyInSpecDomain bundleDir cliExternsPlaced cliProcessInputs
   coinsFile dirsFold encodeDir fileCapBytes filesFold filesOf files_eq_entries fsView
   initFsState_entries observe partyAddress pqInitModel pqInputs pqRecvInputs pqRecvPrekeyModel
   pqxdhExpectedOutcome publicBundleOf sessionFile stdinCapBytes stdioPaths)
open CryptoVerification.SignalSession.Cli
  (CliInputsOk CoinsReadable CommitOk InputsLoadable IsSendOverCap IsStdinOverCap MainResult
    RunAnswer cliInputs)
open CryptoVerification.SignalSession.Cli.RunCompose (RunSem runAns runRel)
open CryptoVerification.SignalSession.Cli.RunProofs (SessMatchesPm pkToE?)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open CryptoVerification.SignalSession.Cli.Slots (filesOk₀ scopeIn)
open CryptoVerification.SignalSession.Placed (cliRunPlacedSig)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.D3
  (D3NoMatchSessionFile d3PqRecvMatchingModel d3PqSessionOf)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomSpecF3
  (BundleFilesFlatRaw CliPqBinaryV2OomF3Placed LibsignalCliPqBinaryV2OomF3PlacedAt
   pqInitInputsFRaw)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MatchingPathBF3
  (cliRunSemPathB runRel_pqRecv_matchingPathB)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3NonCanonF3
  (cliInputsOk_pqRecvInputs coinsReadable_pqRecvInputs inputsLoadable_pqRecvInputs
   isStdinOverCap_pqRecvInputs not_isSendOverCap_pqRecvInputs not_isStdinOverCap_of_stdin_le)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3
  (defaultExtrasF3 pqD3ScopedRun runRel_pqRecv_parseNone_of_runSem)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3
  (cliRunSemD3 runRel_pqRecv_untypedReject)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
  (b2MainSpecTightNeedLocksFineAt cliBudgetLimits cliRunPlacedSig_eq_on_input_of_progEq2)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2G
  (CliElfF3B2NeedLocksAssumptionsG F3MemsetMemcpyEntryLrFalse MainOkCliF3OverB2NeedLocksPlacedAtG
   MainOkCliF3PqB2NeedLocksPlacedAtG cliPqxdhElfCorrectPlaced_of_f3B2NeedLocksG
   cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_call_obs
   cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_call_pred
   cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_stdinOverCap)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3ExternNoAllocFail
  (externPreservesNoAllocFailed_cliExternsPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
  (cliProgExtPlacedAt cliProgExtPlacedSigAt_cliExternsPlaced_eq cliStaticsPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.PlacedOomRecovery2
  (outcomeOrExcusedAbort_of_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG (withEntryGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.Parity
  (BundleReadWithinCap InputsEquivRaw fileStep_entries filesFold_entries_eq_or
   filesFold_eq_foldl_fileStep parseBundleDir)
open LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.BundleInitElfF3
  (CliInitD3Inputs InitRunSemOk cliInputsOk_of_inputsEquivRaw cliInputsOk_pqInitInputsFRaw
   cliRunPlacedSig_eq_none_of_not_inputsLoadable initD3ScopedRun observe_accept_pqInitInputsFRaw_eq
   observe_overCap_pqInitInputsFRaw_eq observe_reject_pqInitInputsFRaw_eq)

/-! ## 1. Guarded D3 & Flat-Bundle `init` `MainOk*G` Specifications (`R2-D1`) -/

/-- Entry-guarded Route-B2 `NeedLocks` + `cliBudgetLimits` `main` specification for
empty-or-matching session pre-key `recv` on arbitrary valid wire payloads `body` (`R2-D1`). -/
@[expose] def MainOkValidMatchD3F3G
    (mpl mmpl : MultiPlacement) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → RunAnswer → Prop,
      (∀ (γ : GhostName) (tp : BitVec 64),
        subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
          (withEntryGuard (F3MemsetMemcpyEntryLrFalse mmpl)
            (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
              (fineHookRustCliAllocBudget γ mmpl tp brkStart)
              cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl)
              Run cliProcessInputs))) ∧
      ∀ (st : PqParty), PqxdhPartyInSpecDomain WP st →
        ∀ (body : List (BitVec 8)) (pm : PreKeySignalMessage) (m : PreKeyMessageFields)
          (rc : BitVec 256),
          body.length < 2 ^ 32 →
          pksmParse body = some pm →
          pkToE? pm = some m →
          m.inner.length + 2048 < 2 ^ 32 →
          (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
          let inp := pqRecvInputs WP st (wirePrekey :: body) rc
          ∃ a, Run inp a ∧
            observe inp.files a = pqxdhExpectedOutcome WP inp (pqRecvPrekeyModel X WP st m rc) ∧
            CommitOk inp (MainResult.ofAnswer a)

/-- Entry-guarded Route-B2 `NeedLocks` + `cliBudgetLimits` `main` specification for non-matching
session pre-key `recv` on both arbitrary parsed wire payloads `body` (`validOver`) and canonical
`m.bytes` (`canonicalNoMatch`) (`R2-D1`). -/
@[expose] def MainOkOverD3F3G
    (mpl mmpl : MultiPlacement) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → RunAnswer → Prop,
      (∀ (γ : GhostName) (tp : BitVec 64),
        subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
          (withEntryGuard (F3MemsetMemcpyEntryLrFalse mmpl)
            (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
              (fineHookRustCliAllocBudget γ mmpl tp brkStart)
              cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl)
              Run cliProcessInputs))) ∧
      (∀ (st : PqParty), PqxdhPartyInSpecDomain WP st →
        ∀ (x : RecordExtras) (g : GhostState (List (BitVec 8))), st.session = some (x, g) →
        ∀ (body : List (BitVec 8)) (pm : PreKeySignalMessage) (m : PreKeyMessageFields)
          (rc : BitVec 256),
          body.length < 2 ^ 32 →
          pksmParse body = some pm →
          pkToE? pm = some m →
          m.inner.length + 2048 < 2 ^ 32 →
          ¬ PqSessionMatches x g m →
          let inp := pqRecvInputs WP st (wirePrekey :: body) rc
          ∃ a, Run inp a ∧
            (OutcomeMatchesModelExceptPath WP inp (sessionFile (partyAddress st.party.other))
               (pqRecvPrekeyModel X WP { st with session := none } m rc)
               (observe inp.files a) ∧
             D3NoMatchSessionFile X WP st x g m rc (observe inp.files a)) ∧
            CommitOk inp (MainResult.ofAnswer a)) ∧
      (∀ (st : PqParty), PqxdhPartyInSpecDomain WP st →
        ∀ (x : RecordExtras) (g : GhostState (List (BitVec 8))), st.session = some (x, g) →
        ∀ (m : PreKeyMessageFields) (rc : BitVec 256),
          m.inner.length + 2048 < 2 ^ 32 →
          ¬ PqSessionMatches x g m →
          let inp := pqRecvInputs WP st (wirePrekey :: m.bytes) rc
          ∃ a, Run inp a ∧
            (OutcomeMatchesModelExceptPath WP inp (sessionFile (partyAddress st.party.other))
               (pqRecvPrekeyModel X WP { st with session := none } m rc)
               (observe inp.files a) ∧
             D3NoMatchSessionFile X WP st x g m rc (observe inp.files a)) ∧
            CommitOk inp (MainResult.ofAnswer a))

/-- Projects `MainOkOverD3F3G` onto `MainOkCliF3OverB2NeedLocksPlacedAtG` by dropping the
`D3NoMatchSessionFile` conjunct on canonical `m.bytes` inputs (`R2-D1`). -/
theorem mainOkCliF3OverG_of_mainOkOverD3F3G
    {mpl mmpl : MultiPlacement} {CodeOk : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (hoverD3 : MainOkOverD3F3G mpl mmpl CodeOk libcAddr brkStart stk) :
    MainOkCliF3OverB2NeedLocksPlacedAtG mpl mmpl CodeOk libcAddr brkStart stk := by
  intro hDropNz X W
  obtain ⟨Run, hmain, _, hcanon⟩ := hoverD3 hDropNz X W
  refine ⟨Run, hmain, fun st hst x g hsess m rc hinner hnomatch => ?_⟩
  obtain ⟨a, hrun, ⟨hobs, _⟩, hcommit⟩ := hcanon st hst x g hsess m rc hinner hnomatch
  exact ⟨a, hrun, hobs, hcommit⟩

/-- Entry-guarded Route-B2 `NeedLocks` + `cliBudgetLimits` `main` specification for `pksmParse`
rejection (`R2-D1`). -/
@[expose] def MainOkParseNoneD3F3G
    (mpl mmpl : MultiPlacement) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ W : CliHooks,
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → RunAnswer → Prop,
      (∀ (γ : GhostName) (tp : BitVec 64),
        subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
          (withEntryGuard (F3MemsetMemcpyEntryLrFalse mmpl)
            (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
              (fineHookRustCliAllocBudget γ mmpl tp brkStart)
              cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl)
              Run cliProcessInputs))) ∧
      ∀ (st : PqParty), PqxdhPartyInSpecDomain WP st →
        ∀ (body : List (BitVec 8)) (rc : BitVec 256),
          body.length < 2 ^ 32 → pksmParse body = none →
          let inp := pqRecvInputs WP st (wirePrekey :: body) rc
          ∃ a, Run inp a ∧ observe inp.files a = .exited 1 [] (filesOf inp.files) ∧
            CommitOk inp (MainResult.ofAnswer a)

private theorem mainOkParseNoneD3F3G_of_runSem
    {mpl mmpl : MultiPlacement} {CodeOk : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (SOf : CliHooks → RunSem)
    (hS_files : ∀ W, (SOf W).filesOk = filesOk₀ scopeIn (fun _ => True))
    (hS_pksm : ∀ W, (SOf W).pksmParse = pksmParse)
    (hmainS : mpl.base 547 ≠ 0#64 → ∀ W : CliHooks, ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
        (withEntryGuard (F3MemsetMemcpyEntryLrFalse mmpl)
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl)
            (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (SOf W))) cliProcessInputs))) :
    MainOkParseNoneD3F3G mpl mmpl CodeOk libcAddr brkStart stk := by
  intro hDropNz W
  refine ⟨pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (SOf W)), hmainS hDropNz W,
    fun st hst body rc hbody hnone => ?_⟩
  obtain ⟨_, hrun, hobs, hcommit⟩ :=
    runRel_pqRecv_parseNone_of_runSem (hS_files W) (hS_pksm W) ⟨W.C, W.Q⟩ st hst body rc hbody hnone
  exact ⟨some none, ⟨Or.inr ⟨st, wirePrekey :: body, rc, hst, rfl⟩, hrun⟩, hobs, hcommit⟩

/-- Entry-guarded Route-B2 `NeedLocks` + `cliBudgetLimits` `main` specification for `D3-B3`
untyped / bad-KEM PreKey rejection (`R2-D1`). -/
@[expose] def MainOkUntypedD3F3G
    (mpl mmpl : MultiPlacement) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ W : CliHooks,
    ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
        (withEntryGuard (F3MemsetMemcpyEntryLrFalse mmpl)
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl)
            (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD3 W))) cliProcessInputs))

/-- `MainOkUntypedD3F3G` discharges `MainOkParseNoneD3F3G` (`pksmParseNone`) with zero additional
`main`-level hypotheses (`R2-D1`). -/
theorem mainOkParseNoneD3F3G_of_untypedG
    {mpl mmpl : MultiPlacement} {CodeOk : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (huntyped : MainOkUntypedD3F3G mpl mmpl CodeOk libcAddr brkStart stk) :
    MainOkParseNoneD3F3G mpl mmpl CodeOk libcAddr brkStart stk :=
  mainOkParseNoneD3F3G_of_runSem cliRunSemD3 (fun _ => rfl) (fun _ => rfl) huntyped

/-- Entry-guarded Route-B2 `NeedLocks` + `cliBudgetLimits` `main` specification for
matching-session Path-B pre-key `recv` (`R2-D1`). -/
@[expose] def MainOkPathBD3F3G
    (mpl mmpl : MultiPlacement) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
        (withEntryGuard (F3MemsetMemcpyEntryLrFalse mmpl)
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl)
            (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemPathB X W))) cliProcessInputs))

/-- Entry-guarded Route-B2 `NeedLocks` + `cliBudgetLimits` `main` specification for flat-bundle
`init` (`InitRunSemOk`) (`R2-D1`). -/
@[expose] def MainInitRunSemOkF3G
    (mpl mmpl : MultiPlacement) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    ∃ S : RunSem,
      InitRunSemOk S X ⟨W.C, W.Q⟩ ∧
      ∀ (γ : GhostName) (tp : BitVec 64),
        subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
          (withEntryGuard (F3MemsetMemcpyEntryLrFalse mmpl)
            (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
              (fineHookRustCliAllocBudget γ mmpl tp brkStart)
              cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl)
              (initD3ScopedRun ⟨W.C, W.Q⟩ (runRel S)) cliProcessInputs))

/-- Canonical guarded `ElfSlicesPqOomPlaced` alias (`R2-D1`). -/
abbrev MainInitSemF3G := MainInitRunSemOkF3G

/-! ## 2. Guarded Whole-Process `recv` & Flat-Bundle `init` Lifts (`R2-D2`) -/

private theorem pqRecv_strict_obs_of_f3B2NeedLocksG
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage} {W : CliHooks} {Run : Inputs → RunAnswer → Prop}
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmainW : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
        (withEntryGuard (F3MemsetMemcpyEntryLrFalse mmpl)
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
            cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl) Run cliProcessInputs)))
    {st : PqParty} {c : List (BitVec 8)} {rc : BitVec 256} {o : Outcome}
    (hst : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st)
    (hclause : c.length ≤ stdinCapBytes →
      ∃ a, Run (pqRecvInputs ⟨W.C, W.Q⟩ st c rc) a ∧
        observe (pqRecvInputs ⟨W.C, W.Q⟩ st c rc).files a = o ∧
        CommitOk (pqRecvInputs ⟨W.C, W.Q⟩ st c rc) (MainResult.ofAnswer a)) :
    let inp := pqRecvInputs ⟨W.C, W.Q⟩ st c rc
    cliRunPlacedSig mpl mmpl elf W inp =
      some (if c.length > stdinCapBytes then .exited 2 [] (filesOf inp.files) else o) := by
  dsimp only
  let WP : PEParams := ⟨W.C, W.Q⟩
  have hprogEq := (cliProgExtPlacedSigAt_cliExternsPlaced_eq mpl mmpl W).symm
  rw [cliRunPlacedSig_eq_on_input_of_progEq2 hprogEq rfl]
  by_cases hstin : c.length > stdinCapBytes
  · simp only [hstin, ↓reduceIte]
    exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_stdinOverCap
      (externPreservesNoAllocFailed_cliExternsPlaced mmpl W)
      H.elfStaticOk H.tokenCells H.fsEq (H.codeLoaded W) (H.harnessG W) hmainW H.stkLo H.stkHi
      (cliInputsOk_pqRecvInputs WP st c rc) (inputsLoadable_pqRecvInputs WP st c rc hst)
      (isStdinOverCap_pqRecvInputs WP st c rc hstin)
  · simp only [hstin, ↓reduceIte]
    obtain ⟨a, hrun, hobs, hcommit⟩ := hclause (Nat.le_of_not_gt hstin)
    exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_call_obs
      (externPreservesNoAllocFailed_cliExternsPlaced mmpl W)
      H.elfStaticOk H.tokenCells H.fsEq (H.codeLoaded W) (H.harnessG W) hmainW H.stkLo H.stkHi
      (cliInputsOk_pqRecvInputs WP st c rc) (inputsLoadable_pqRecvInputs WP st c rc hst)
      hrun (not_isSendOverCap_pqRecvInputs WP st c rc)
      (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin))
      hobs (coinsReadable_pqRecvInputs WP st c rc) hcommit

private theorem d3_recvOverStdinCap_strict_of_f3G
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop} {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : MainOkCliF3PqB2NeedLocksPlacedAtG mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (W : CliHooks) (st : PqParty) (hst : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st)
    (body : List (BitVec 8)) (rc : BitVec 256)
    (hover : (wirePrekey :: body).length > stdinCapBytes) :
    let inp := pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc
    cliRunPlacedSig mpl mmpl elf W inp = some (.exited 2 [] (filesOf inp.files)) := by
  obtain ⟨Run, hmainW, _⟩ := hmain H.base547NeZero defaultExtrasF3 W
  have h := pqRecv_strict_obs_of_f3B2NeedLocksG (rc := rc) (o := .exited 2 []
      (filesOf (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc).files)) H hmainW hst
    (fun hle => False.elim (Nat.not_lt_of_ge hle hover))
  dsimp only at h ⊢; simpa only [hover, ↓reduceIte] using h

/-- Guarded twin of `D3ParseRejectF3.d3_recvOverStdinCap_f3` (`R2-D2`). -/
theorem d3_recvOverStdinCap_of_f3G
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop} {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : MainOkCliF3PqB2NeedLocksPlacedAtG mpl mmpl CodeOk libcAddr elf.brkStart stk) :
    ∀ (W : CliHooks) (st : PqParty), PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st →
      ∀ (body : List (BitVec 8)) (rc : BitVec 256),
        (wirePrekey :: body).length > stdinCapBytes →
        let inp := pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc
        OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
          (cliRunPlacedSig mpl mmpl elf W) inp (· = .exited 2 [] (filesOf inp.files)) :=
  fun W st hst body rc hover =>
    outcomeOrExcusedAbort_of_eq
      (d3_recvOverStdinCap_strict_of_f3G H hmain W st hst body rc hover)

/-- Guarded twin of `D3ParseRejectF3.d3_pksmParseNone_strict_of_f3` (`R2-D2`). -/
theorem d3_pksmParseNone_strict_of_f3G
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop} {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hparseNone : MainOkParseNoneD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (W : CliHooks) (st : PqParty) (hst : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st)
    (body : List (BitVec 8)) (rc : BitVec 256)
    (hbody : body.length < 2 ^ 32) (hnone : pksmParse body = none) :
    let inp := pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc
    cliRunPlacedSig mpl mmpl elf W inp =
      some (if (wirePrekey :: body).length > stdinCapBytes then .exited 2 [] (filesOf inp.files)
        else .exited 1 [] (filesOf inp.files)) := by
  obtain ⟨Run, hmainW, hcl⟩ := hparseNone H.base547NeZero W
  exact pqRecv_strict_obs_of_f3B2NeedLocksG H hmainW hst (fun _ => hcl st hst body rc hbody hnone)

/-- Guarded twin of `D3ParseRejectF3.d3_pksmParseNone_f3` (`R2-D2`). -/
theorem d3_pksmParseNone_of_f3G
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop} {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hparseNone : MainOkParseNoneD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk) :
    ∀ (W : CliHooks) (st : PqParty), PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st →
      ∀ (body : List (BitVec 8)) (rc : BitVec 256),
        body.length < 2 ^ 32 → pksmParse body = none →
        let inp := pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc
        OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
          (cliRunPlacedSig mpl mmpl elf W) inp
          (· = if (wirePrekey :: body).length > stdinCapBytes then .exited 2 [] (filesOf inp.files)
            else .exited 1 [] (filesOf inp.files)) :=
  fun W st hst body rc hbody hnone =>
    outcomeOrExcusedAbort_of_eq
      (d3_pksmParseNone_strict_of_f3G H hparseNone W st hst body rc hbody hnone)

/-- Guarded twin of `D3UntypedElfF3.d3_untypedReject_strict_of_f3` (`R2-D2`). -/
theorem d3_untypedReject_strict_of_f3G
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop} {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (huntyped : MainOkUntypedD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (W : CliHooks) (st : PqParty) (hst : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st)
    (body : List (BitVec 8)) (pm : PreKeySignalMessage) (rc : BitVec 256)
    (hbody : body.length < 2 ^ 32)
    (hparse : pksmParse body = some pm)
    (hpk : pkToE? pm = none)
    (hnomatch : ∀ x g, st.session = some (x, g) → ¬ SessMatchesPm (d3PqSessionOf x g) pm) :
    let inp := pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc
    cliRunPlacedSig mpl mmpl elf W inp =
      some (if (wirePrekey :: body).length > stdinCapBytes then .exited 2 [] (filesOf inp.files)
        else .exited 1 [] (filesOf inp.files)) :=
  pqRecv_strict_obs_of_f3B2NeedLocksG H (huntyped H.base547NeZero W) hst (fun _ => by
    obtain ⟨hrun, hobs, hcommit⟩ :=
      runRel_pqRecv_untypedReject W st body pm rc hst hbody hparse hpk hnomatch
    exact ⟨some none, ⟨Or.inr ⟨st, wirePrekey :: body, rc, hst, rfl⟩, hrun⟩, hobs, hcommit⟩)

/-- Guarded twin of `D3UntypedElfF3.d3_untypedReject_f3` (`R2-D2`). -/
theorem d3_untypedReject_of_f3G
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop} {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (huntyped : MainOkUntypedD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk) :
    ∀ (W : CliHooks) (st : PqParty), PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st →
      ∀ (body : List (BitVec 8)) (pm : PreKeySignalMessage) (rc : BitVec 256),
        body.length < 2 ^ 32 → pksmParse body = some pm → pkToE? pm = none →
        (∀ x g, st.session = some (x, g) → ¬ SessMatchesPm (d3PqSessionOf x g) pm) →
        let inp := pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc
        OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
          (cliRunPlacedSig mpl mmpl elf W) inp
          (· = if (wirePrekey :: body).length > stdinCapBytes then .exited 2 [] (filesOf inp.files)
            else .exited 1 [] (filesOf inp.files)) :=
  fun W st hst body pm rc hbody hparse hpk hnomatch =>
    outcomeOrExcusedAbort_of_eq
      (d3_untypedReject_strict_of_f3G H huntyped W st hst body pm rc hbody hparse hpk hnomatch)

/-- Guarded twin of `D3MatchingPathBF3.d3_matchingPathB_strict_of_f3` (`R2-D2`). -/
theorem d3_matchingPathB_strict_of_f3G
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop} {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hpathB : MainOkPathBD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (W : CliHooks) (st : PqParty) (x : RecordExtras) (g : GhostState (List (BitVec 8)))
    (body : List (BitVec 8)) (pm : PreKeySignalMessage) (rc : BitVec 256)
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hsess : st.session = some (x, g))
    (hlen : (wirePrekey :: body).length ≤ 2 ^ 32)
    (hparse : pksmParse body = some pm)
    (hmatch : SessMatchesPm (d3PqSessionOf x g) pm) :
    let WP : PEParams := ⟨W.C, W.Q⟩
    let inp := pqRecvInputs WP st (wirePrekey :: body) rc
    cliRunPlacedSig mpl mmpl elf W inp =
      some (if (wirePrekey :: body).length > stdinCapBytes then .exited 2 [] (filesOf inp.files)
        else pqxdhExpectedOutcome WP inp (d3PqRecvMatchingModel WP st x g pm rc)) :=
  pqRecv_strict_obs_of_f3B2NeedLocksG H (hpathB H.base547NeZero defaultExtrasF3 W) hwf (fun _ => by
    obtain ⟨hrun, hobs, hcommit⟩ :=
      runRel_pqRecv_matchingPathB defaultExtrasF3 W st x g body pm rc hwf hsess hlen hparse hmatch
    exact ⟨runAns (cliRunSemPathB defaultExtrasF3 W)
        (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc),
      ⟨Or.inr ⟨st, wirePrekey :: body, rc, hwf, rfl⟩, hrun⟩, hobs, hcommit⟩)

/-- Guarded twin of `D3MatchingPathBF3.d3_matchingPathB_f3` (`R2-D2`). -/
theorem d3_matchingPathB_of_f3G
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop} {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hpathB : MainOkPathBD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk) :
    ∀ (W : CliHooks) (st : PqParty) (x : RecordExtras)
      (g : GhostState (List (BitVec 8))) (body : List (BitVec 8))
      (pm : PreKeySignalMessage) (rc : BitVec 256),
      PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st → st.session = some (x, g) →
      (wirePrekey :: body).length ≤ 2 ^ 32 →
      pksmParse body = some pm → SessMatchesPm (d3PqSessionOf x g) pm →
      let WP : PEParams := ⟨W.C, W.Q⟩
      let inp := pqRecvInputs WP st (wirePrekey :: body) rc
      OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
        (cliRunPlacedSig mpl mmpl elf W) inp
        (· = if (wirePrekey :: body).length > stdinCapBytes then .exited 2 [] (filesOf inp.files)
          else pqxdhExpectedOutcome WP inp (d3PqRecvMatchingModel WP st x g pm rc)) :=
  fun W st x g body pm rc hwf hsess hlen hparse hmatch =>
    outcomeOrExcusedAbort_of_eq
      (d3_matchingPathB_strict_of_f3G H hpathB W st x g body pm rc hwf hsess hlen hparse hmatch)

/-- Guarded twin of `D3ValidMatchElfF3.d3_valid_match_strict_of_f3` (`R2-D2`). -/
theorem d3_valid_match_strict_of_f3G
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hvalidMatch : MainOkValidMatchD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (st : PqParty)
    (hst : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st)
    (body : List (BitVec 8)) (pm : PreKeySignalMessage) (m : PreKeyMessageFields)
    (rc : BitVec 256)
    (hbody : body.length < 2 ^ 32)
    (hpm : pksmParse body = some pm)
    (hm : pkToE? pm = some m)
    (hinner : m.inner.length + 2048 < 2 ^ 32)
    (hmatch : ∀ x g, st.session = some (x, g) → PqSessionMatches x g m) :
    let inp := pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc
    cliRunPlacedSig mpl mmpl elf W inp =
      some (if (wirePrekey :: body).length > stdinCapBytes then
        .exited 2 [] (filesOf inp.files)
      else
        pqxdhExpectedOutcome ⟨W.C, W.Q⟩ inp (pqRecvPrekeyModel X ⟨W.C, W.Q⟩ st m rc)) := by
  dsimp only
  let WP : PEParams := ⟨W.C, W.Q⟩
  let inp := pqRecvInputs WP st (wirePrekey :: body) rc
  obtain ⟨Run, hmainW, hcl⟩ := hvalidMatch H.base547NeZero X W
  have hprogEq := (cliProgExtPlacedSigAt_cliExternsPlaced_eq mpl mmpl W).symm
  have hsigEq : cliRunPlacedSig mpl mmpl elf W inp = _ :=
    cliRunPlacedSig_eq_on_input_of_progEq2 hprogEq rfl
  rw [hsigEq]
  by_cases hstin : (wirePrekey :: body).length > stdinCapBytes
  · simp only [hstin, ↓reduceIte]
    exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_stdinOverCap
      (externPreservesNoAllocFailed_cliExternsPlaced mmpl W)
      H.elfStaticOk H.tokenCells H.fsEq (H.codeLoaded W) (H.harnessG W) hmainW H.stkLo H.stkHi
      (cliInputsOk_pqRecvInputs WP st (wirePrekey :: body) rc)
      (inputsLoadable_pqRecvInputs WP st (wirePrekey :: body) rc hst)
      (isStdinOverCap_pqRecvInputs WP st (wirePrekey :: body) rc hstin)
  · simp only [hstin, ↓reduceIte]
    obtain ⟨a, hrun, hobs, hcommit⟩ := hcl st hst body pm m rc hbody hpm hm hinner hmatch
    exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_call_obs
      (externPreservesNoAllocFailed_cliExternsPlaced mmpl W)
      H.elfStaticOk H.tokenCells H.fsEq (H.codeLoaded W) (H.harnessG W) hmainW H.stkLo H.stkHi
      (cliInputsOk_pqRecvInputs WP st (wirePrekey :: body) rc)
      (inputsLoadable_pqRecvInputs WP st (wirePrekey :: body) rc hst)
      hrun (not_isSendOverCap_pqRecvInputs WP st (wirePrekey :: body) rc)
      (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin))
      hobs (coinsReadable_pqRecvInputs WP st (wirePrekey :: body) rc) hcommit

/-- Guarded twin of `D3ValidMatchElfF3.d3_valid_match_outcomeUpTo_of_f3` (`R2-D2`). -/
theorem d3_valid_match_outcomeUpTo_of_f3G
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hvalidMatch : MainOkValidMatchD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk) :
    ∀ (W : CliHooks) (X : UnreachedPqxdhPrimitives) (st : PqParty),
      PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st →
      ∀ (body : List (BitVec 8)) (pm : PreKeySignalMessage) (m : PreKeyMessageFields)
        (rc : BitVec 256),
        body.length < 2 ^ 32 → pksmParse body = some pm → pkToE? pm = some m →
        m.inner.length + 2048 < 2 ^ 32 →
        (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
        let inp := pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc
        OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
          (cliRunPlacedSig mpl mmpl elf W) inp
          (· = if (wirePrekey :: body).length > stdinCapBytes then
            .exited 2 [] (filesOf inp.files)
          else
            pqxdhExpectedOutcome ⟨W.C, W.Q⟩ inp (pqRecvPrekeyModel X ⟨W.C, W.Q⟩ st m rc)) :=
  fun W X st hst body pm m rc hbody hpm hm hinner hmatch =>
    outcomeOrExcusedAbort_of_eq
      (d3_valid_match_strict_of_f3G H hvalidMatch W X st hst body pm m rc hbody hpm hm hinner hmatch)

/-- Guarded twin of `D3ValidOverElfF3.d3_valid_over_strict_of_f3` (`R2-D2`). -/
theorem d3_valid_over_strict_of_f3G
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hoverD3 : MainOkOverD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (st : PqParty)
    (hst : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st)
    (x : RecordExtras) (g : GhostState (List (BitVec 8))) (hsess : st.session = some (x, g))
    (body : List (BitVec 8)) (pm : PreKeySignalMessage) (m : PreKeyMessageFields)
    (rc : BitVec 256)
    (hbody : body.length < 2 ^ 32)
    (hpm : pksmParse body = some pm)
    (hm : pkToE? pm = some m)
    (hinner : m.inner.length + 2048 < 2 ^ 32)
    (hnomatch : ¬ PqSessionMatches x g m) :
    let WP : PEParams := ⟨W.C, W.Q⟩
    let inp := pqRecvInputs WP st (wirePrekey :: body) rc
    ∃ o : Outcome,
      cliRunPlacedSig mpl mmpl elf W inp = some o ∧
      (if (wirePrekey :: body).length > stdinCapBytes then
        o = .exited 2 [] (filesOf inp.files)
      else
        OutcomeMatchesModelExceptPath WP inp (sessionFile (partyAddress st.party.other))
          (pqRecvPrekeyModel X WP { st with session := none } m rc) o ∧
        D3NoMatchSessionFile X WP st x g m rc o) := by
  dsimp only
  let WP : PEParams := ⟨W.C, W.Q⟩
  let inp := pqRecvInputs WP st (wirePrekey :: body) rc
  obtain ⟨Run, hmainW, hbodyCl, _⟩ := hoverD3 H.base547NeZero X W
  have hprogEq := (cliProgExtPlacedSigAt_cliExternsPlaced_eq mpl mmpl W).symm
  have hsigEq : cliRunPlacedSig mpl mmpl elf W inp = _ :=
    cliRunPlacedSig_eq_on_input_of_progEq2 hprogEq rfl
  by_cases hstin : (wirePrekey :: body).length > stdinCapBytes
  · refine ⟨.exited 2 [] (filesOf inp.files), ?_, by simp only [hstin, ↓reduceIte]; rfl⟩
    rw [hsigEq]
    exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_stdinOverCap
      (externPreservesNoAllocFailed_cliExternsPlaced mmpl W)
      H.elfStaticOk H.tokenCells H.fsEq (H.codeLoaded W) (H.harnessG W) hmainW H.stkLo H.stkHi
      (cliInputsOk_pqRecvInputs WP st (wirePrekey :: body) rc)
      (inputsLoadable_pqRecvInputs WP st (wirePrekey :: body) rc hst)
      (isStdinOverCap_pqRecvInputs WP st (wirePrekey :: body) rc hstin)
  · obtain ⟨a, hrun, hp, hcommit⟩ :=
      hbodyCl st hst x g hsess body pm m rc hbody hpm hm hinner hnomatch
    obtain ⟨o, ho, hpo⟩ :=
      cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_call_pred
        (P := fun o =>
          OutcomeMatchesModelExceptPath WP inp (sessionFile (partyAddress st.party.other))
            (pqRecvPrekeyModel X WP { st with session := none } m rc) o ∧
          D3NoMatchSessionFile X WP st x g m rc o)
        (externPreservesNoAllocFailed_cliExternsPlaced mmpl W)
        H.elfStaticOk H.tokenCells H.fsEq (H.codeLoaded W) (H.harnessG W) hmainW H.stkLo H.stkHi
        (cliInputsOk_pqRecvInputs WP st (wirePrekey :: body) rc)
        (inputsLoadable_pqRecvInputs WP st (wirePrekey :: body) rc hst)
        hrun (not_isSendOverCap_pqRecvInputs WP st (wirePrekey :: body) rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin))
        hp (coinsReadable_pqRecvInputs WP st (wirePrekey :: body) rc) hcommit
    refine ⟨o, hsigEq.trans ho, ?_⟩
    simp only [hstin, ↓reduceIte]
    exact hpo

/-- Guarded twin of `D3ValidOverElfF3.d3_valid_over_outcomeUpTo_of_f3` (`R2-D2`). -/
theorem d3_valid_over_outcomeUpTo_of_f3G
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hoverD3 : MainOkOverD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk) :
    ∀ (W : CliHooks) (X : UnreachedPqxdhPrimitives) (st : PqParty),
      PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st →
      ∀ (x : RecordExtras) (g : GhostState (List (BitVec 8))), st.session = some (x, g) →
      ∀ (body : List (BitVec 8)) (pm : PreKeySignalMessage) (m : PreKeyMessageFields)
        (rc : BitVec 256),
        body.length < 2 ^ 32 → pksmParse body = some pm → pkToE? pm = some m →
        m.inner.length + 2048 < 2 ^ 32 → ¬ PqSessionMatches x g m →
        let WP : PEParams := ⟨W.C, W.Q⟩
        let inp := pqRecvInputs WP st (wirePrekey :: body) rc
        OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
          (cliRunPlacedSig mpl mmpl elf W) inp
          (fun o => if (wirePrekey :: body).length > stdinCapBytes then
              o = .exited 2 [] (filesOf inp.files)
            else
              OutcomeMatchesModelExceptPath WP inp (sessionFile (partyAddress st.party.other))
                (pqRecvPrekeyModel X WP { st with session := none } m rc) o ∧
              D3NoMatchSessionFile X WP st x g m rc o) :=
  fun W X st hst x g hsess body pm m rc hbody hpm hm hinner hnomatch =>
    Or.inl (d3_valid_over_strict_of_f3G H hoverD3 W X st hst x g hsess body pm m rc
      hbody hpm hm hinner hnomatch)

private theorem d3_canonical_noMatch_strict_of_f3G
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hoverD3 : MainOkOverD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (st : PqParty)
    (hst : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st)
    (x : RecordExtras) (g : GhostState (List (BitVec 8))) (hsess : st.session = some (x, g))
    (m : PreKeyMessageFields) (rc : BitVec 256)
    (hinner : m.inner.length + 2048 < 2 ^ 32)
    (hnomatch : ¬ PqSessionMatches x g m) :
    let WP : PEParams := ⟨W.C, W.Q⟩
    let inp := pqRecvInputs WP st (wirePrekey :: m.bytes) rc
    ∃ o : Outcome,
      cliRunPlacedSig mpl mmpl elf W inp = some o ∧
      (if (wirePrekey :: m.bytes).length > stdinCapBytes then
        o = .exited 2 [] (filesOf inp.files)
      else
        OutcomeMatchesModelExceptPath WP inp (sessionFile (partyAddress st.party.other))
          (pqRecvPrekeyModel X WP { st with session := none } m rc) o ∧
        D3NoMatchSessionFile X WP st x g m rc o) := by
  dsimp only
  let WP : PEParams := ⟨W.C, W.Q⟩
  let inp := pqRecvInputs WP st (wirePrekey :: m.bytes) rc
  obtain ⟨Run, hmainW, _, hcanonCl⟩ := hoverD3 H.base547NeZero X W
  have hprogEq := (cliProgExtPlacedSigAt_cliExternsPlaced_eq mpl mmpl W).symm
  have hsigEq : cliRunPlacedSig mpl mmpl elf W inp = _ :=
    cliRunPlacedSig_eq_on_input_of_progEq2 hprogEq rfl
  by_cases hstin : (wirePrekey :: m.bytes).length > stdinCapBytes
  · refine ⟨.exited 2 [] (filesOf inp.files), ?_, by simp only [hstin, ↓reduceIte]; rfl⟩
    rw [hsigEq]
    exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_stdinOverCap
      (externPreservesNoAllocFailed_cliExternsPlaced mmpl W)
      H.elfStaticOk H.tokenCells H.fsEq (H.codeLoaded W) (H.harnessG W) hmainW H.stkLo H.stkHi
      (cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
      (inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst)
      (isStdinOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hstin)
  · obtain ⟨a, hrun, hp, hcommit⟩ := hcanonCl st hst x g hsess m rc hinner hnomatch
    obtain ⟨o, ho, hpo⟩ :=
      cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_call_pred
        (P := fun o =>
          OutcomeMatchesModelExceptPath WP inp (sessionFile (partyAddress st.party.other))
            (pqRecvPrekeyModel X WP { st with session := none } m rc) o ∧
          D3NoMatchSessionFile X WP st x g m rc o)
        (externPreservesNoAllocFailed_cliExternsPlaced mmpl W)
        H.elfStaticOk H.tokenCells H.fsEq (H.codeLoaded W) (H.harnessG W) hmainW H.stkLo H.stkHi
        (cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
        (inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst)
        hrun (not_isSendOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin))
        hp (coinsReadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc) hcommit
    refine ⟨o, hsigEq.trans ho, ?_⟩
    simp only [hstin, ↓reduceIte]
    exact hpo

/-- Guarded twin of `D3ValidOverElfF3.d3_canonical_noMatch_outcomeUpTo_of_f3` (`R2-D2`). -/
theorem d3_canonical_noMatch_outcomeUpTo_of_f3G
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hoverD3 : MainOkOverD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk) :
    ∀ (W : CliHooks) (X : UnreachedPqxdhPrimitives) (st : PqParty),
      PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st →
      ∀ (x : RecordExtras) (g : GhostState (List (BitVec 8))), st.session = some (x, g) →
      ∀ (m : PreKeyMessageFields) (rc : BitVec 256),
        m.inner.length + 2048 < 2 ^ 32 → ¬ PqSessionMatches x g m →
        let WP : PEParams := ⟨W.C, W.Q⟩
        let inp := pqRecvInputs WP st (wirePrekey :: m.bytes) rc
        OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
          (cliRunPlacedSig mpl mmpl elf W) inp
          (fun o => if (wirePrekey :: m.bytes).length > stdinCapBytes then
              o = .exited 2 [] (filesOf inp.files)
            else
              OutcomeMatchesModelExceptPath WP inp (sessionFile (partyAddress st.party.other))
                (pqRecvPrekeyModel X WP { st with session := none } m rc) o ∧
              D3NoMatchSessionFile X WP st x g m rc o) :=
  fun W X st hst x g hsess m rc hinner hnomatch =>
    Or.inl (d3_canonical_noMatch_strict_of_f3G H hoverD3 W X st hst x g hsess m rc hinner hnomatch)

private theorem ite_pos_f3 {α : Type} {c : Prop} [inst : Decidable c] (hc : c) {a b : α} :
    (if c then a else b) = a := match inst with | isTrue _ => rfl | isFalse h => absurd hc h

private theorem ite_neg_f3 {α : Type} {c : Prop} [inst : Decidable c] (hc : ¬ c) {a b : α} :
    (if c then a else b) = b := match inst with | isTrue h => absurd h hc | isFalse _ => rfl

private theorem filesOf_eq_match_filesFold_f3 (f : List (String × List (BitVec 8))) {p : String}
    (hne : normalizePath p ≠ [])
    (hns : normalizePath p ∉ stdioPaths.map normalizePath) :
    filesOf f p = match (filesFold f {}).entries (normalizePath p) with
      | some (.file bs) => some bs | _ => none := by
  unfold filesOf fsView
  rw [ite_neg_f3 hns, files_eq_entries,
    ite_neg_f3 (by rw [List.isEmpty_eq_false_iff.mpr hne]; decide),
    initFsState_entries ({ files := f } : ProcessInputs) (normalizePath p) hns]
  rfl

private theorem filesOf_pqInitInputsF_coins_f3 {P : PEParams} {st : PqParty}
    {files : List (String × List (BitVec 8))} {t : List.Vector (BitVec 8) initiateTapeLen}
    {i : Inputs} (heq : InputsEquivRaw i (pqInitInputsFRaw P st files t)) :
    filesOf i.files coinsFile = some t.toList := by
  rw [heq.2.2.2 coinsFile]
  have hne : normalizePath coinsFile ≠ [] := by decide
  have hns : normalizePath coinsFile ∉ stdioPaths.map normalizePath := by decide
  rw [filesOf_eq_match_filesFold_f3 _ hne hns,
    show (pqInitInputsFRaw P st files t).files =
      (encodeDir P st ++ files) ++ [(coinsFile, t.toList)] by
        simp [pqInitInputsFRaw, pqInputs, List.append_assoc],
    filesFold_eq_foldl_fileStep, List.foldl_append, List.foldl_cons, List.foldl_nil,
    fileStep_entries, ite_pos_f3 rfl]

private theorem coinsReadable_of_inputsEquiv_pqInitInputsF_f3 {P : PEParams} {st : PqParty}
    {files : List (String × List (BitVec 8))} {t : List.Vector (BitVec 8) initiateTapeLen}
    {i : Inputs} (heq : InputsEquivRaw i (pqInitInputsFRaw P st files t)) :
    CoinsReadable i := by
  have hc := filesOf_pqInitInputsF_coins_f3 heq
  have hne : normalizePath coinsFile ≠ [] := by decide
  have hns : normalizePath coinsFile ∉ stdioPaths.map normalizePath := by decide
  rw [filesOf_eq_match_filesFold_f3 _ hne hns] at hc
  have hfold : (filesFold i.files {}).entries (normalizePath coinsFile) =
      some (.file t.toList) := by
    rcases hf : (filesFold i.files {}).entries (normalizePath coinsFile) with _ | bs | _ <;>
      rw [hf] at hc <;>
      [cases hc;
       (dsimp only at hc
        exact congrArg (fun x => some (FsEntry.file x)) (Option.some.inj hc));
       cases hc]
  unfold CoinsReadable
  rw [show "coins" = coinsFile from rfl, files_eq_entries,
    ite_neg_f3 (by rw [List.isEmpty_eq_false_iff.mpr hne]; decide),
    initFsState_entries (cliInputs i) (normalizePath coinsFile) hns]
  change (filesFold i.files (dirsFold i.dirs {})).entries (normalizePath coinsFile) ≠
      some .dir ∧
    ∀ bs, (filesFold i.files (dirsFold i.dirs {})).entries (normalizePath coinsFile) =
      some (.file bs) → bs.length ≤ fileCapBytes
  rw [filesFold_entries_eq_or i.files _ hne, hfold, Option.some_or]
  refine ⟨fun h => FsEntry.noConfusion (Option.some.inj h), fun bs h => ?_⟩
  injection h with h
  injection h with h
  subst h
  simp [List.Vector.toList_length, initiateTapeLen, fileCapBytes]

private theorem not_isSendOverCap_of_inputsEquiv_pqInitInputsF_f3 {P : PEParams} {st : PqParty}
    {files : List (String × List (BitVec 8))} {t : List.Vector (BitVec 8) initiateTapeLen}
    {i : Inputs} (heq : InputsEquivRaw i (pqInitInputsFRaw P st files t)) :
    ¬ IsSendOverCap i := by
  rintro ⟨-, hgt⟩
  rw [heq.2.2.1] at hgt
  simp [pqInitInputsFRaw, pqInputs] at hgt

private theorem not_isStdinOverCap_of_inputsEquiv_pqInitInputsF_f3 {P : PEParams} {st : PqParty}
    {files : List (String × List (BitVec 8))} {t : List.Vector (BitVec 8) initiateTapeLen}
    {i : Inputs} (heq : InputsEquivRaw i (pqInitInputsFRaw P st files t)) :
    ¬ IsStdinOverCap i := by
  rintro ⟨-, hgt⟩
  rw [heq.2.2.1] at hgt
  simp [pqInitInputsFRaw, pqInputs, stdinCapBytes] at hgt

private def dummyUnreached : UnreachedPqxdhPrimitives where
  sigPkGen := fun _ => []
  sigSign := fun _ _ _ => []
  scalarMul := fun _ _ => []
  scalarAdd := fun _ _ => []
  kemKeyGen := fun _ => ([], [])
  pow8 := fun _ => []
  isValidDhTriple := fun _ _ _ => false

section OfF3G

variable {mpl mmpl : MultiPlacement}
  {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
  {elf : ElfImage}
  (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
  (hinitSem : MainInitRunSemOkF3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
include H hinitSem

private theorem cliRunPlacedSig_of_f3_semG (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    {i : Inputs} {o : Outcome}
    (hdom : CliInitD3Inputs ⟨W.C, W.Q⟩ i)
    (hi : CliInputsOk i) (hload : InputsLoadable i)
    (hnoc : ¬ IsSendOverCap i) (hnstin : ¬ IsStdinOverCap i)
    (hcoins : CoinsReadable i)
    (hstep : ∀ S : RunSem, InitRunSemOk S X ⟨W.C, W.Q⟩ →
      runRel S i (runAns S i) ∧
      CommitOk i (MainResult.ofAnswer (runAns S i)) ∧
      observe i.files (runAns S i) = o) :
    cliRunPlacedSig mpl mmpl elf W i = some o := by
  obtain ⟨S, hS, hmainW⟩ := hinitSem H.base547NeZero X W
  obtain ⟨hrel, hcommit, hobs⟩ := hstep S hS
  have hrunExt :=
    cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_call_obs
      (externPreservesNoAllocFailed_cliExternsPlaced mmpl W)
      H.elfStaticOk H.tokenCells H.fsEq (H.codeLoaded W) (H.harnessG W) hmainW
      H.stkLo H.stkHi hi hload ⟨hdom, hrel⟩ hnoc hnstin hobs hcoins hcommit
  have hprogEq := (cliProgExtPlacedSigAt_cliExternsPlaced_eq mpl mmpl W).symm
  exact (cliRunPlacedSig_eq_on_input_of_progEq2 hprogEq rfl).trans hrunExt

private theorem cliRunPlacedSig_pqInitFiles_exact_eq_some_of_f3G
    (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    {st : PqParty} {files : List (String × List (BitVec 8))} {b : PreKeyBundleFields}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    (hload : InputsLoadable i)
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hs : st.session = none)
    (hb : BundleFilesFlatRaw files)
    (hcap : BundleReadWithinCap (filesOf files) bundleDir)
    (hparse : parseBundleDir (filesOf files) bundleDir = some (publicBundleOf b)) :
    cliRunPlacedSig mpl mmpl elf W i =
      some (pqxdhExpectedOutcome ⟨W.C, W.Q⟩ (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t)
        (pqInitModel X ⟨W.C, W.Q⟩ st b t)) :=
  cliRunPlacedSig_of_f3_semG H hinitSem W X ⟨st, files, t, hwf, hs, hb, heq⟩
    (cliInputsOk_of_inputsEquivRaw heq (cliInputsOk_pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    hload (not_isSendOverCap_of_inputsEquiv_pqInitInputsF_f3 heq)
    (not_isStdinOverCap_of_inputsEquiv_pqInitInputsF_f3 heq)
    (coinsReadable_of_inputsEquiv_pqInitInputsF_f3 heq)
    (fun _ hS => observe_accept_pqInitInputsFRaw_eq X ⟨W.C, W.Q⟩ heq hwf hs hb hcap hparse hS)

/-- Guarded twin of `BundleInitElfF3Strict.cliRunPlacedSig_pqInitFiles_exact_ne_none_of_f3`
(`R2-D2`). -/
theorem cliRunPlacedSig_pqInitFiles_exact_ne_none_of_f3G
    (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    {st : PqParty} {files : List (String × List (BitVec 8))} {b : PreKeyBundleFields}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    (hload : InputsLoadable i)
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hs : st.session = none)
    (hb : BundleFilesFlatRaw files)
    (hcap : BundleReadWithinCap (filesOf files) bundleDir)
    (hparse : parseBundleDir (filesOf files) bundleDir = some (publicBundleOf b)) :
    cliRunPlacedSig mpl mmpl elf W i ≠ none := by
  rw [cliRunPlacedSig_pqInitFiles_exact_eq_some_of_f3G H hinitSem W X heq hload hwf hs hb hcap
    hparse]
  intro hnone; cases hnone

private theorem outcomeUpTo_pqInitFiles_exact_of_f3G (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    {st : PqParty} {files : List (String × List (BitVec 8))} {b : PreKeyBundleFields}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    (hload : InputsLoadable i)
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hs : st.session = none)
    (hb : BundleFilesFlatRaw files)
    (hcap : BundleReadWithinCap (filesOf files) bundleDir)
    (hparse : parseBundleDir (filesOf files) bundleDir = some (publicBundleOf b)) :
    OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
      (cliRunPlacedSig mpl mmpl elf W) i
      (· = pqxdhExpectedOutcome ⟨W.C, W.Q⟩ (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t)
        (pqInitModel X ⟨W.C, W.Q⟩ st b t)) :=
  outcomeOrExcusedAbort_of_eq
    (cliRunPlacedSig_pqInitFiles_exact_eq_some_of_f3G H hinitSem W X heq hload hwf hs hb hcap
      hparse)

/-- Guarded twin of `BundleInitElfF3.outcomeUpTo_pqInitFiles_exact_or_none_of_f3` (`R2-D2`). -/
theorem outcomeUpTo_pqInitFiles_exact_or_none_of_f3G (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    {st : PqParty} {files : List (String × List (BitVec 8))} {b : PreKeyBundleFields}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hs : st.session = none)
    (hb : BundleFilesFlatRaw files)
    (hcap : BundleReadWithinCap (filesOf files) bundleDir)
    (hparse : parseBundleDir (filesOf files) bundleDir = some (publicBundleOf b)) :
    cliRunPlacedSig mpl mmpl elf W i = none ∨
      OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
        (cliRunPlacedSig mpl mmpl elf W) i
        (· = pqxdhExpectedOutcome ⟨W.C, W.Q⟩ (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t)
          (pqInitModel X ⟨W.C, W.Q⟩ st b t)) := by
  by_cases hload : InputsLoadable i
  · exact .inr (outcomeUpTo_pqInitFiles_exact_of_f3G H hinitSem W X heq hload hwf hs hb hcap hparse)
  · exact .inl (cliRunPlacedSig_eq_none_of_not_inputsLoadable elf W hload)

private theorem cliRunPlacedSig_pqInitReject_eq_some_of_f3G (W : CliHooks)
    {st : PqParty} {files : List (String × List (BitVec 8))}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    (hload : InputsLoadable i)
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hs : st.session = none)
    (hb : BundleFilesFlatRaw files)
    (hparse : parseBundleDir (filesOf files) bundleDir = none) :
    cliRunPlacedSig mpl mmpl elf W i =
      some (.exited 1 [] (filesOf (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t).files)) :=
  cliRunPlacedSig_of_f3_semG H hinitSem W dummyUnreached ⟨st, files, t, hwf, hs, hb, heq⟩
    (cliInputsOk_of_inputsEquivRaw heq (cliInputsOk_pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    hload (not_isSendOverCap_of_inputsEquiv_pqInitInputsF_f3 heq)
    (not_isStdinOverCap_of_inputsEquiv_pqInitInputsF_f3 heq)
    (coinsReadable_of_inputsEquiv_pqInitInputsF_f3 heq)
    (fun _ hS => observe_reject_pqInitInputsFRaw_eq dummyUnreached ⟨W.C, W.Q⟩ heq hwf hs hb hparse hS)

/-- Guarded twin of `BundleInitElfF3Strict.cliRunPlacedSig_pqInitReject_ne_none_of_f3`
(`R2-D2`). -/
theorem cliRunPlacedSig_pqInitReject_ne_none_of_f3G (W : CliHooks)
    {st : PqParty} {files : List (String × List (BitVec 8))}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    (hload : InputsLoadable i)
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hs : st.session = none)
    (hb : BundleFilesFlatRaw files)
    (hparse : parseBundleDir (filesOf files) bundleDir = none) :
    cliRunPlacedSig mpl mmpl elf W i ≠ none := by
  rw [cliRunPlacedSig_pqInitReject_eq_some_of_f3G H hinitSem W heq hload hwf hs hb hparse]
  intro hnone; cases hnone

private theorem outcomeUpTo_pqInitReject_of_f3G (W : CliHooks)
    {st : PqParty} {files : List (String × List (BitVec 8))}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    (hload : InputsLoadable i)
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hs : st.session = none)
    (hb : BundleFilesFlatRaw files)
    (hparse : parseBundleDir (filesOf files) bundleDir = none) :
    OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
      (cliRunPlacedSig mpl mmpl elf W) i
      (· = .exited 1 [] (filesOf (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t).files)) :=
  outcomeOrExcusedAbort_of_eq
    (cliRunPlacedSig_pqInitReject_eq_some_of_f3G H hinitSem W heq hload hwf hs hb hparse)

/-- Guarded twin of `BundleInitElfF3.outcomeUpTo_pqInitReject_or_none_of_f3` (`R2-D2`). -/
theorem outcomeUpTo_pqInitReject_or_none_of_f3G (W : CliHooks)
    {st : PqParty} {files : List (String × List (BitVec 8))}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hs : st.session = none)
    (hb : BundleFilesFlatRaw files)
    (hparse : parseBundleDir (filesOf files) bundleDir = none) :
    cliRunPlacedSig mpl mmpl elf W i = none ∨
      OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
        (cliRunPlacedSig mpl mmpl elf W) i
        (· = .exited 1 [] (filesOf (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t).files)) := by
  by_cases hload : InputsLoadable i
  · exact .inr (outcomeUpTo_pqInitReject_of_f3G H hinitSem W heq hload hwf hs hb hparse)
  · exact .inl (cliRunPlacedSig_eq_none_of_not_inputsLoadable elf W hload)

private theorem cliRunPlacedSig_pqInitOverCap_eq_some_of_f3G (W : CliHooks)
    {st : PqParty} {files : List (String × List (BitVec 8))}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    (hload : InputsLoadable i)
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hs : st.session = none)
    (hb : BundleFilesFlatRaw files)
    (hover : ¬ BundleReadWithinCap (filesOf files) bundleDir) :
    cliRunPlacedSig mpl mmpl elf W i =
      some (.exited 1 [] (filesOf (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t).files)) :=
  cliRunPlacedSig_of_f3_semG H hinitSem W dummyUnreached ⟨st, files, t, hwf, hs, hb, heq⟩
    (cliInputsOk_of_inputsEquivRaw heq (cliInputsOk_pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    hload (not_isSendOverCap_of_inputsEquiv_pqInitInputsF_f3 heq)
    (not_isStdinOverCap_of_inputsEquiv_pqInitInputsF_f3 heq)
    (coinsReadable_of_inputsEquiv_pqInitInputsF_f3 heq)
    (fun _ hS => observe_overCap_pqInitInputsFRaw_eq dummyUnreached ⟨W.C, W.Q⟩ heq hwf hs hb hover hS)

/-- Guarded twin of `BundleInitElfF3Strict.cliRunPlacedSig_pqInitOverCap_ne_none_of_f3`
(`R2-D2`). -/
theorem cliRunPlacedSig_pqInitOverCap_ne_none_of_f3G (W : CliHooks)
    {st : PqParty} {files : List (String × List (BitVec 8))}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    (hload : InputsLoadable i)
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hs : st.session = none)
    (hb : BundleFilesFlatRaw files)
    (hover : ¬ BundleReadWithinCap (filesOf files) bundleDir) :
    cliRunPlacedSig mpl mmpl elf W i ≠ none := by
  rw [cliRunPlacedSig_pqInitOverCap_eq_some_of_f3G H hinitSem W heq hload hwf hs hb hover]
  intro hnone; cases hnone

private theorem outcomeUpTo_pqInitOverCap_of_f3G (W : CliHooks)
    {st : PqParty} {files : List (String × List (BitVec 8))}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    (hload : InputsLoadable i)
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hs : st.session = none)
    (hb : BundleFilesFlatRaw files)
    (hover : ¬ BundleReadWithinCap (filesOf files) bundleDir) :
    OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
      (cliRunPlacedSig mpl mmpl elf W) i
      (· = .exited 1 [] (filesOf (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t).files)) :=
  outcomeOrExcusedAbort_of_eq
    (cliRunPlacedSig_pqInitOverCap_eq_some_of_f3G H hinitSem W heq hload hwf hs hb hover)

/-- Guarded twin of `BundleInitElfF3.outcomeUpTo_pqInitOverCap_or_none_of_f3` (`R2-D2`). -/
theorem outcomeUpTo_pqInitOverCap_or_none_of_f3G (W : CliHooks)
    {st : PqParty} {files : List (String × List (BitVec 8))}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hs : st.session = none)
    (hb : BundleFilesFlatRaw files)
    (hover : ¬ BundleReadWithinCap (filesOf files) bundleDir) :
    cliRunPlacedSig mpl mmpl elf W i = none ∨
      OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
        (cliRunPlacedSig mpl mmpl elf W) i
        (· = .exited 1 [] (filesOf (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t).files)) := by
  by_cases hload : InputsLoadable i
  · exact .inr (outcomeUpTo_pqInitOverCap_of_f3G H hinitSem W heq hload hwf hs hb hover)
  · exact .inl (cliRunPlacedSig_eq_none_of_not_inputsLoadable elf W hload)

end OfF3G

/-! ## 3. Guarded Whole-Process `CliPqBinaryV2OomF3*` Assemblies (`R2-D3..D4`) -/

/-- Guarded twin of `D3BinaryOomProofF3.cliPqBinaryV2OomF3Placed_of_f3B2NeedLocks` assembling
the unchanged `CliPqBinaryV2OomF3Placed mpl mmpl elf` across all 16 `PqModelPostB2` clauses
(`R2-D3`). -/
theorem cliPqBinaryV2OomF3Placed_of_f3B2NeedLocksG
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : MainOkCliF3PqB2NeedLocksPlacedAtG mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hoverD3 : MainOkOverD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (huntyped : MainOkUntypedD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hpathB : MainOkPathBD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hvalidMatch : MainOkValidMatchD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hinitSem : MainInitRunSemOkF3G mpl mmpl CodeOk libcAddr elf.brkStart stk) :
    CliPqBinaryV2OomF3Placed mpl mmpl elf where
  base := cliPqxdhElfCorrectPlaced_of_f3B2NeedLocksG
    (externPreservesNoAllocFailed_cliExternsPlaced mmpl) H hmain
    (mainOkCliF3OverG_of_mainOkOverD3F3G hoverD3)
  recvOverStdinCap := d3_recvOverStdinCap_of_f3G H hmain
  canonicalNoMatch := d3_canonical_noMatch_outcomeUpTo_of_f3G H hoverD3
  pksmParseNone := d3_pksmParseNone_of_f3G H (mainOkParseNoneD3F3G_of_untypedG huntyped)
  untypedReject := d3_untypedReject_of_f3G H huntyped
  matchingPathB := d3_matchingPathB_of_f3G H hpathB
  validMatch := d3_valid_match_outcomeUpTo_of_f3G H hvalidMatch
  validOver := d3_valid_over_outcomeUpTo_of_f3G H hoverD3
  initFiles := fun W X _st _files _b _t _i heq hwf hs hb hcap hparse =>
    outcomeUpTo_pqInitFiles_exact_or_none_of_f3G H hinitSem W X heq hwf hs hb hcap hparse
  initReject := fun W _st _files _t _i heq hwf hs hb hparse =>
    outcomeUpTo_pqInitReject_or_none_of_f3G H hinitSem W heq hwf hs hb hparse
  initOverFileCap := fun W _st _files _t _i heq hwf hs hb hover =>
    outcomeUpTo_pqInitOverCap_or_none_of_f3G H hinitSem W heq hwf hs hb hover

/-- Guarded raw ELF-byte lifting constructor for `LibsignalCliPqBinaryV2OomF3PlacedAt mpl mmpl bytes`
(`R2-D3`). -/
theorem libsignalCliPqBinaryV2OomF3PlacedAt_of_f3B2NeedLocksG
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {bytes : List (BitVec 8)} {elf : ElfImage}
    (hparse : ElfImage.parse bytes = .ok elf)
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : MainOkCliF3PqB2NeedLocksPlacedAtG mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hoverD3 : MainOkOverD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (huntyped : MainOkUntypedD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hpathB : MainOkPathBD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hvalidMatch : MainOkValidMatchD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hinitSem : MainInitRunSemOkF3G mpl mmpl CodeOk libcAddr elf.brkStart stk) :
    LibsignalCliPqBinaryV2OomF3PlacedAt mpl mmpl bytes :=
  ⟨elf, hparse, cliPqBinaryV2OomF3Placed_of_f3B2NeedLocksG H hmain hoverD3 huntyped hpathB
    hvalidMatch hinitSem⟩

end LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomProofF3G

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3PollRejectAuxF3
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Domains
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Bounds
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Plumbing
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.EncOk
import ProofLib.ProgramReflection

/-!
# Two-Placement Whole-Process ELF Rejection for `pkToE? pm = none`

Defines `cliRunSemD3` and `MainOkUntypedD3F3`, projects `MainOkParseNoneD3F3` directly from
`MainOkUntypedD3F3`, and lifts `MainOkUntypedD3F3` to whole-process evaluation on
`cliRunPlacedSig mpl mmpl elf W` (`d3_untypedReject_strict_of_f3`, `d3_untypedReject_f3`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage)
open CryptoVerification.E2E (PEParams wirePrekey)
open CryptoVerification.SignalSession (
  CliHooks CliReachesOOMPlaced OutcomeOrExcusedAbort PqParty PqxdhPartyInSpecDomain
  cliExternsPlaced cliProcessInputs filesOf observe pqRecvInputs stdinCapBytes
)
open CryptoVerification.SignalSession.Cli (CommitOk MainResult)
open CryptoVerification.SignalSession.Cli.MainHops (domainArgv_pqRecv)
open CryptoVerification.SignalSession.Cli.RunCompose (
  RunSem finish runAns runFiles runRel
)
open CryptoVerification.SignalSession.Cli.RunProofs (SessMatchesPm decPkDef pkToE?)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open CryptoVerification.SignalSession.Cli.RunRefine (addrValE runAns_pqRecvPrekey_eq runBounds_pqRecv)
open CryptoVerification.SignalSession.Cli.Slots (runEncOk_pqRecv scopeIn)
open CryptoVerification.SignalSession.Placed (cliRunPlacedSig)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.D3 (d3PqSessionOf)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3 (
  MainOkParseNoneD3F3 cliRunSemF3 defaultExtrasF3 mainOkParseNoneD3F3_of_runSem pqD3ScopedRun
  pqRecv_strict_obs_of_f3B2NeedLocks runFilesOk_pqRecv_cli_f3 runHsOk_pqRecvPrekey_body_f3
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3PollRejectAuxF3 (
  DecPkOkD3Untyped decPkDef_eq_some_none_of_d3b3 decPkOkD3Untyped_pqRecv not_sessMatchesPm_pqRecv
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 (
  CliElfF3B2NeedLocksAssumptions b2MainSpecTightNeedLocksFineAt cliBudgetLimits
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (
  cliProgExtPlacedAt cliStaticsPlacedAt
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.PlacedOomRecovery2 (outcomeOrExcusedAbort_of_eq)

/-- `RunSem` bundle specialized to untyped / bad-KEM pre-key rejection (`pkToE? pm = none`). -/
noncomputable abbrev cliRunSemD3 (W : CliHooks) : RunSem :=
  cliRunSemF3 defaultExtrasF3 W
    (decPkDef defaultExtrasF3 ⟨W.C, W.Q⟩ scopeIn)
    (DecPkOkD3Untyped ⟨W.C, W.Q⟩ scopeIn)
    pksmParse

/-- On any `pkToE? pm = none` rejection input, `runAns (cliRunSemD3 W)` evaluates to
`some none`. -/
theorem runAns_d3_eq_some_none (W : CliHooks) (st : PqParty) (body : List (BitVec 8))
    (pm : PreKeySignalMessage) (rc : BitVec 256) (hst : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st)
    (hparse : pksmParse body = some pm)
    (huntyped : pkToE? pm = none)
    (hnomatch : ∀ x g, st.session = some (x, g) → ¬ SessMatchesPm (d3PqSessionOf x g) pm) :
    runAns (cliRunSemD3 W) (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc) = some none := by
  rw [runAns_pqRecvPrekey_eq]
  dsimp only [cliRunSemD3, cliRunSemF3]
  rw [hparse]
  dsimp only
  rw [decPkDef_eq_some_none_of_d3b3 defaultExtrasF3 ⟨W.C, W.Q⟩ scopeIn
    (runFiles (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc))
    (addrValE st.party.other) (addrValE st.party) pm (keyToBytes32 rc) huntyped
    (not_sessMatchesPm_pqRecv ⟨W.C, W.Q⟩ st (wirePrekey :: body) pm rc hst hnomatch)]
  rfl

theorem runRel_pqRecv_untypedReject (W : CliHooks) (st : PqParty) (body : List (BitVec 8))
    (pm : PreKeySignalMessage) (rc : BitVec 256) (hst : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st)
    (hbody : body.length < 2 ^ 32)
    (hparse : pksmParse body = some pm)
    (huntyped : pkToE? pm = none)
    (hnomatch : ∀ x g, st.session = some (x, g) → ¬ SessMatchesPm (d3PqSessionOf x g) pm) :
    let inp := pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc
    runRel (cliRunSemD3 W) inp (some none) ∧
      observe inp.files (some none) = .exited 1 [] (filesOf inp.files) ∧
      CommitOk inp (MainResult.ofAnswer (some none)) := by
  let WP : PEParams := ⟨W.C, W.Q⟩
  let S := cliRunSemD3 W
  have hans : runAns S (pqRecvInputs WP st (wirePrekey :: body) rc) = some none :=
    runAns_d3_eq_some_none W st body pm rc hst hparse huntyped hnomatch
  have hrun : runRel S (pqRecvInputs WP st (wirePrekey :: body) rc) (some none) := by
    rw [← hans]
    exact ⟨domainArgv_pqRecv WP st (wirePrekey :: body) rc,
      runBounds_pqRecv WP st (wirePrekey :: body) rc (Nat.succ_le_of_lt hbody),
      runFilesOk_pqRecv_cli_f3 (S := S) rfl WP st (wirePrekey :: body) rc hst,
      runEncOk_pqRecv S WP st (wirePrekey :: body) rc,
      runHsOk_pqRecvPrekey_body_f3 WP st body rc (fun pm' hpm' => by
        have hpm_eq : pm' = pm := Option.some.inj (hpm'.symm.trans hparse)
        rw [hpm_eq]
        exact decPkOkD3Untyped_pqRecv WP st body pm rc hst hparse huntyped hnomatch),
      rfl⟩
  exact ⟨hrun, rfl, fun _ h => by cases h⟩

/-- `NeedLocks` + `cliBudgetLimits` `main`-level specification for untyped / bad-KEM
pre-key rejection (`pkToE? pm = none`), scoped via `pqD3ScopedRun`. -/
def MainOkUntypedD3F3
    (mpl mmpl : MultiPlacement) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ W : CliHooks,
    ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
        (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
          (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl)
          (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD3 W))) cliProcessInputs)

/-- `MainOkUntypedD3F3` immediately discharges `MainOkParseNoneD3F3` (`pksmParseNone`) with zero
additional `main`-level hypotheses. -/
theorem mainOkParseNoneD3F3_of_untyped
    {mpl mmpl : MultiPlacement} {CodeOk : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (huntyped : MainOkUntypedD3F3 mpl mmpl CodeOk libcAddr brkStart stk) :
    MainOkParseNoneD3F3 mpl mmpl CodeOk libcAddr brkStart stk :=
  mainOkParseNoneD3F3_of_runSem cliRunSemD3 (fun _ => rfl) (fun _ => rfl) huntyped

/-- Strict whole-process evaluation of `cliRunPlacedSig mpl mmpl elf W` on untyped / bad-KEM
pre-key rejection inputs. -/
theorem d3_untypedReject_strict_of_f3
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop} {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr stk CodeOk elf)
    (huntyped : MainOkUntypedD3F3 mpl mmpl CodeOk libcAddr elf.brkStart stk)
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
  pqRecv_strict_obs_of_f3B2NeedLocks H (huntyped H.base547NeZero W) hst (fun _ => by
    obtain ⟨hrun, hobs, hcommit⟩ :=
      runRel_pqRecv_untypedReject W st body pm rc hst hbody hparse hpk hnomatch
    exact ⟨some none, ⟨Or.inr ⟨st, wirePrekey :: body, rc, hst, rfl⟩, hrun⟩, hobs, hcommit⟩)

/-- `OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)` lift of
`d3_untypedReject_strict_of_f3`, discharging `CliPqBinaryV2OomF3Placed.untypedReject`. -/
theorem d3_untypedReject_f3
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop} {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr stk CodeOk elf)
    (huntyped : MainOkUntypedD3F3 mpl mmpl CodeOk libcAddr elf.brkStart stk) :
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
      (d3_untypedReject_strict_of_f3 H huntyped W st hst body pm rc hbody hparse hpk hnomatch)

end LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3

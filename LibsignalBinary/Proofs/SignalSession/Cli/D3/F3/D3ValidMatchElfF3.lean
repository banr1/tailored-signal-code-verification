/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3NonCanonF3
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3ExternNoAllocFail
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.PlacedOomRecovery2

/-!
# Two-Placement Whole-Process ELF Lifts for Valid Pre-Key Match

Strict and `OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)` whole-process lifts
of `MainOkValidMatchD3F3` discharging `CliPqBinaryV2OomF3Placed.validMatch`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ValidMatchElfF3

open Arm64 (Memory)
open Arm64.Obj (MultiPlacement)
open Arm64.Process (ElfImage)
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage)
open CryptoVerification.E2E (
  PEParams PreKeyMessageFields UnreachedPqxdhPrimitives wirePrekey
)
open CryptoVerification.SignalSession (
  CliHooks CliReachesOOMPlaced OutcomeOrExcusedAbort PqParty PqSessionMatches
  PqxdhPartyInSpecDomain filesOf pqRecvInputs pqRecvPrekeyModel pqxdhExpectedOutcome stdinCapBytes
)
open CryptoVerification.SignalSession.Placed (cliRunPlacedSig)
open CryptoVerification.SignalSession.Cli.RunProofs (pkToE?)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3NonCanonF3 (
  MainOkValidMatchD3F3 cliInputsOk_pqRecvInputs coinsReadable_pqRecvInputs
  inputsLoadable_pqRecvInputs isStdinOverCap_pqRecvInputs not_isSendOverCap_pqRecvInputs
  not_isStdinOverCap_of_stdin_le
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3ExternNoAllocFail (
  externPreservesNoAllocFailed_cliExternsPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 (
  CliElfF3B2NeedLocksAssumptions cliRunExtOnInputsSigAt_of_strict_b2_needLocks_call_obs
  cliRunExtOnInputsSigAt_of_strict_b2_needLocks_stdinOverCap cliRunPlacedSig_eq_on_input_of_progEq2
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (
  cliProgExtPlacedSigAt_cliExternsPlaced_eq
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.PlacedOomRecovery2 (
  outcomeOrExcusedAbort_of_eq
)

/-- Strict whole-process evaluation of `cliRunPlacedSig mpl mmpl elf W` on empty-or-matching
session valid pre-key `recv` inputs. -/
theorem d3_valid_match_strict_of_f3
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hvalidMatch : MainOkValidMatchD3F3 mpl mmpl CodeOk libcAddr elf.brkStart stk)
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
    exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_stdinOverCap
      (externPreservesNoAllocFailed_cliExternsPlaced mmpl W)
      H.elfStaticOk H.tokenCells H.fsEq (H.codeLoaded W) (H.harness W) hmainW H.stkLo H.stkHi
      (cliInputsOk_pqRecvInputs WP st (wirePrekey :: body) rc)
      (inputsLoadable_pqRecvInputs WP st (wirePrekey :: body) rc hst)
      (isStdinOverCap_pqRecvInputs WP st (wirePrekey :: body) rc hstin)
  · simp only [hstin, ↓reduceIte]
    obtain ⟨a, hrun, hobs, hcommit⟩ := hcl st hst body pm m rc hbody hpm hm hinner hmatch
    exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_call_obs
      (externPreservesNoAllocFailed_cliExternsPlaced mmpl W)
      H.elfStaticOk H.tokenCells H.fsEq (H.codeLoaded W) (H.harness W) hmainW H.stkLo H.stkHi
      (cliInputsOk_pqRecvInputs WP st (wirePrekey :: body) rc)
      (inputsLoadable_pqRecvInputs WP st (wirePrekey :: body) rc hst)
      hrun (not_isSendOverCap_pqRecvInputs WP st (wirePrekey :: body) rc)
      (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin))
      hobs (coinsReadable_pqRecvInputs WP st (wirePrekey :: body) rc) hcommit

/-- `OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)` lift of
`d3_valid_match_strict_of_f3`, discharging `CliPqBinaryV2OomF3Placed.validMatch`. -/
theorem d3_valid_match_outcomeUpTo_of_f3
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hvalidMatch : MainOkValidMatchD3F3 mpl mmpl CodeOk libcAddr elf.brkStart stk) :
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
      (d3_valid_match_strict_of_f3 H hvalidMatch W X st hst body pm m rc hbody hpm hm hinner hmatch)

end LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ValidMatchElfF3

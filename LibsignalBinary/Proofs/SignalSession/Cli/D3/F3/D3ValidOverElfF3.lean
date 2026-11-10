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

/-!
# Two-Placement Whole-Process Overwrite and Canonical Non-Matching Session Lifts

Strict and `OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)` whole-process lifts
of `MainOkOverD3F3` discharging `CliPqBinaryV2OomF3Placed.validOver` and
`CliPqBinaryV2OomF3Placed.canonicalNoMatch`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ValidOverElfF3

open Arm64 (Memory)
open Arm64.Obj (MultiPlacement)
open Arm64.Process (ElfImage)
open CryptoGames.LibsignalSession (GhostState)
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage)
open CryptoVerification.E2E (
  PEParams PreKeyMessageFields RecordExtras UnreachedPqxdhPrimitives wirePrekey
)
open CryptoVerification.SignalSession (
  CliHooks CliReachesOOMPlaced Outcome OutcomeMatchesModelExceptPath OutcomeOrExcusedAbort
  PqParty PqSessionMatches PqxdhPartyInSpecDomain filesOf partyAddress pqRecvInputs
  pqRecvPrekeyModel sessionFile stdinCapBytes
)
open CryptoVerification.SignalSession.Placed (cliRunPlacedSig)
open CryptoVerification.SignalSession.Cli.RunProofs (pkToE?)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open LibsignalBinary.Proofs.SignalSession.Cli.D3 (D3NoMatchSessionFile)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3NonCanonF3 (
  MainOkOverD3F3 cliInputsOk_pqRecvInputs coinsReadable_pqRecvInputs
  inputsLoadable_pqRecvInputs isStdinOverCap_pqRecvInputs not_isSendOverCap_pqRecvInputs
  not_isStdinOverCap_of_stdin_le
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3ExternNoAllocFail (
  externPreservesNoAllocFailed_cliExternsPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 (
  CliElfF3B2NeedLocksAssumptions cliRunExtOnInputsSigAt_of_strict_b2_needLocks_call_pred
  cliRunExtOnInputsSigAt_of_strict_b2_needLocks_stdinOverCap cliRunPlacedSig_eq_on_input_of_progEq2
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (
  cliProgExtPlacedSigAt_cliExternsPlaced_eq
)

/-- Strict whole-process evaluation of `cliRunPlacedSig mpl mmpl elf W` on non-matching
session valid pre-key `recv` inputs (`validOver`, arbitrary `body`). -/
theorem d3_valid_over_strict_of_f3
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hoverD3 : MainOkOverD3F3 mpl mmpl CodeOk libcAddr elf.brkStart stk)
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
    exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_stdinOverCap
      (externPreservesNoAllocFailed_cliExternsPlaced mmpl W)
      H.elfStaticOk H.tokenCells H.fsEq (H.codeLoaded W) (H.harness W) hmainW H.stkLo H.stkHi
      (cliInputsOk_pqRecvInputs WP st (wirePrekey :: body) rc)
      (inputsLoadable_pqRecvInputs WP st (wirePrekey :: body) rc hst)
      (isStdinOverCap_pqRecvInputs WP st (wirePrekey :: body) rc hstin)
  · obtain ⟨a, hrun, hp, hcommit⟩ :=
      hbodyCl st hst x g hsess body pm m rc hbody hpm hm hinner hnomatch
    obtain ⟨o, ho, hpo⟩ :=
      cliRunExtOnInputsSigAt_of_strict_b2_needLocks_call_pred
        (P := fun o =>
          OutcomeMatchesModelExceptPath WP inp (sessionFile (partyAddress st.party.other))
            (pqRecvPrekeyModel X WP { st with session := none } m rc) o ∧
          D3NoMatchSessionFile X WP st x g m rc o)
        (externPreservesNoAllocFailed_cliExternsPlaced mmpl W)
        H.elfStaticOk H.tokenCells H.fsEq (H.codeLoaded W) (H.harness W) hmainW H.stkLo H.stkHi
        (cliInputsOk_pqRecvInputs WP st (wirePrekey :: body) rc)
        (inputsLoadable_pqRecvInputs WP st (wirePrekey :: body) rc hst)
        hrun (not_isSendOverCap_pqRecvInputs WP st (wirePrekey :: body) rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin))
        hp (coinsReadable_pqRecvInputs WP st (wirePrekey :: body) rc) hcommit
    refine ⟨o, hsigEq.trans ho, ?_⟩
    simp only [hstin, ↓reduceIte]
    exact hpo

/-- `OutcomeOrExcusedAbort` lift of `d3_valid_over_strict_of_f3`, discharging
`CliPqBinaryV2OomF3Placed.validOver`. -/
theorem d3_valid_over_outcomeUpTo_of_f3
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hoverD3 : MainOkOverD3F3 mpl mmpl CodeOk libcAddr elf.brkStart stk) :
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
    Or.inl (d3_valid_over_strict_of_f3 H hoverD3 W X st hst x g hsess body pm m rc
      hbody hpm hm hinner hnomatch)

/-- Strict whole-process evaluation of `cliRunPlacedSig mpl mmpl elf W` on canonical
`m.bytes` non-matching session pre-key `recv` inputs (`canonicalNoMatch`). -/
theorem d3_canonical_noMatch_strict_of_f3
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hoverD3 : MainOkOverD3F3 mpl mmpl CodeOk libcAddr elf.brkStart stk)
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
    exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_stdinOverCap
      (externPreservesNoAllocFailed_cliExternsPlaced mmpl W)
      H.elfStaticOk H.tokenCells H.fsEq (H.codeLoaded W) (H.harness W) hmainW H.stkLo H.stkHi
      (cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
      (inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst)
      (isStdinOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hstin)
  · obtain ⟨a, hrun, hp, hcommit⟩ := hcanonCl st hst x g hsess m rc hinner hnomatch
    obtain ⟨o, ho, hpo⟩ :=
      cliRunExtOnInputsSigAt_of_strict_b2_needLocks_call_pred
        (P := fun o =>
          OutcomeMatchesModelExceptPath WP inp (sessionFile (partyAddress st.party.other))
            (pqRecvPrekeyModel X WP { st with session := none } m rc) o ∧
          D3NoMatchSessionFile X WP st x g m rc o)
        (externPreservesNoAllocFailed_cliExternsPlaced mmpl W)
        H.elfStaticOk H.tokenCells H.fsEq (H.codeLoaded W) (H.harness W) hmainW H.stkLo H.stkHi
        (cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
        (inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst)
        hrun (not_isSendOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin))
        hp (coinsReadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc) hcommit
    refine ⟨o, hsigEq.trans ho, ?_⟩
    simp only [hstin, ↓reduceIte]
    exact hpo

/-- `OutcomeOrExcusedAbort` lift of `d3_canonical_noMatch_strict_of_f3`, discharging
`CliPqBinaryV2OomF3Placed.canonicalNoMatch`. -/
theorem d3_canonical_noMatch_outcomeUpTo_of_f3
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hoverD3 : MainOkOverD3F3 mpl mmpl CodeOk libcAddr elf.brkStart stk) :
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
    Or.inl (d3_canonical_noMatch_strict_of_f3 H hoverD3 W X st hst x g hsess m rc hinner hnomatch)

end LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ValidOverElfF3

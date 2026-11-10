/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.UA.Defs

/-!
# Run-After-Break Refinement Invariant and Slot Specifications

Defines the trace induction invariant `UAInvB`, the per-call postcondition `UASlotPostB`, and the
per-event/slot specification propositions (`UALeakSpecB`, `UAEnvSpecB`, `UASlot*SpecB`,
`UAInitWSpecB`, `UAXportSpecB`, `XlateInvSpecB`, `XlateExcWSpecB`, `XlateExcPSpecB`) for CLI traces
containing break and invert events.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.BI.RAB.Defs

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant ExecTrace)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (MachineEvent RunEvent EnvEvent CliEvent)
open _root_.DY.Libsignal.Composed
open _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed.Refinement.Cli
open _root_.DY.Libsignal.Composed.Refinement.Cli.ParD3
open _root_.DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open CryptoVerification.E2E (PEParams initiateTapeLen)
open CryptoVerification.SignalSession (Inputs bundleDir Address)
open Symbolic.Swarm.CREF (compSemOf SemReady)
open Symbolic.Swarm.CREF.Cli (interpOfParams)
open Symbolic.Swarm.Coinsplit.Lift (CliLiveAtCli)
open Symbolic.Proofs.Swarm.UA.Defs (AliceRecordPendingInSession flatEvents callsOf SchedFits)

/-! ## Trace Invariant and Call Postcondition -/

/-- Trace invariant after CLI events `evs`: either `CollisionAfterExplainedPrefix` holds on `evs`,
or `CliLiveAtCli` holds on `flatEvents evs`, every clean explanation of `evs` satisfies
`AliceRecordPendingInSession`, and some clean explanation of `evs` exists. -/
def UAInvB (interp' : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (who : List Participant)
    (ok : Nat → Bool) (t_clean : CliTurn) (accepted : List HwBytes) (evs : List CliEvent) : Prop :=
  CollisionAfterExplainedPrefix interp' r S evs ∨
    (CliLiveAtCli interp' r S who ok t_clean accepted (flatEvents evs) ∧
      (∀ g ss vis, Explains interp' r S g ss vis evs → ¬ ReadCollisionCli interp' r S g ss evs →
        AliceRecordPendingInSession interp' r S g (runTrace r ss) (t_clean.leakRecords r) (activeBundleIds evs)) ∧
      ∃ g ss vis, Explains interp' r S g ss vis evs ∧ ¬ ReadCollisionCli interp' r S g ss evs)

/-- Per-call postcondition advancing `PqTurnSim1A` and preserving `UAInvB` across `c`. -/
def UASlotPostB (interp : ExternInterpretation) (P : PEParams) (r : ProtocolSetup)
    (t t_clean : CliTurn) (c : CliCall) (code : Nat) (out : HwBytes) (files : DirectorySnapshot)
    (accepted : List HwBytes) (evs_pre : List CliEvent) : Prop :=
  let interp' := interpOfParams interp P
  let S := compSemOf interp' r
  let evs := evs_pre ++ [.run (runEventOf c (some (code, out)))]
  ∃ (t_clean' : CliTurn) (accepted' : List HwBytes),
    PqTurnSim1A interp' P r (CliTurn.after t r c code out files) t_clean' accepted' ∧
    ∀ (who : List Participant) (ok : Nat → Bool),
      SchedFits (callsOf evs) who ok →
      UAInvB interp' r S who ok t_clean accepted evs_pre →
      UAInvB interp' r S who ok t_clean' accepted' evs

/-! ## Induction Step Specifications -/

/-- Environment leak events (`LeaksFrom`) preserve `UAInvB`. -/
def UALeakSpecB : Prop :=
  ∀ (interp : ExternInterpretation) (P : PEParams) (r : ProtocolSetup),
    ExternContractsHoldCli interp → ModelAgree interp P → ProtocolSetupWF r →
    ∀ {t t_clean : CliTurn} {accepted : List HwBytes} {evs leaks : List CliEvent}
      {who : List Participant} {ok : Nat → Bool},
      PqTurnSim1A (interpOfParams interp P) P r t t_clean accepted →
      LeaksFrom r t leaks →
      SchedFits (callsOf evs) who ok →
      UAInvB (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r) who ok
        t_clean accepted evs →
      UAInvB (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r) who ok
        t_clean accepted (evs ++ leaks)

/-- A guarded break or invert environment event preserves `UAInvB`. -/
def UAEnvSpecB : Prop :=
  ∀ (interp : ExternInterpretation) (P : PEParams) (r : ProtocolSetup),
    ExternContractsHoldCli interp → ModelAgree interp P → ProtocolSetupWF r →
    ∀ {t t_clean : CliTurn} {accepted : List HwBytes} {evs : List CliEvent} {e : EnvEvent}
      {who : List Participant} {ok : Nat → Bool},
      PqTurnSim1A (interpOfParams interp P) P r t t_clean accepted →
      e.IsBreakInvert →
      InvertsGuarded interp r (evs ++ [.env e]) →
      SchedFits (callsOf evs) who ok →
      UAInvB (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r) who ok
        t_clean accepted evs →
      UAInvB (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r) who ok
        t_clean accepted (evs ++ [.env e])

/-- Specification for Alice's `init` call slot. -/
def UASlotInitSpecB : Prop :=
  ∀ (interp : ExternInterpretation) (P : PEParams) (r : ProtocolSetup),
    ExternContractsHoldCli interp → ModelAgree interp P → ProtocolSetupWF r →
    ∀ {t t_clean : CliTurn} {c : CliCall} {i : Inputs}
      {code : Nat} {out : HwBytes} {files : DirectorySnapshot}
      {accepted : List HwBytes} {evs_pre : List CliEvent},
      PqTurnSim1A (interpOfParams interp P) P r t t_clean accepted →
      c.party = r.alice →
      c.cmd = .init (peerOf r r.alice) bundleDir →
      c.stdin = [] →
      c.coins.length = initiateTapeLen →
      t.records r r.alice = none →
      BundleFilesFlat c.bundle →
      HonestBundleFiles interp r c.bundle →
      InputsFor c (t.dirs c.party) i →
      PqModelRel interp P i (some (.exited code out files)) →
      UASlotPostB interp P r t t_clean c code out files accepted evs_pre

/-- Specification for the `send` call slot. -/
def UASlotSendSpecB : Prop :=
  ∀ (interp : ExternInterpretation) (P : PEParams) (r : ProtocolSetup),
    ExternContractsHoldCli interp → ModelAgree interp P → ProtocolSetupWF r →
    ∀ {t t_clean : CliTurn} {c : CliCall} {i : Inputs}
      {code : Nat} {out : HwBytes} {files : DirectorySnapshot}
      {accepted : List HwBytes} {evs_pre : List CliEvent},
      PqTurnSim1A (interpOfParams interp P) P r t t_clean accepted →
      (c.party = r.alice ∨ c.party = r.bob) →
      c.cmd = .send (peerOf r c.party) →
      c.bundle = [] →
      c.coins.length = 64 →
      c.stdin.length < 2 ^ 32 →
      FilesBounded (t.dirs c.party) →
      BobCallAllowed r t c →
      t.sent.length < 2 ^ 32 - 1 →
      t.records r c.party ≠ none →
      InputsFor c (t.dirs c.party) i →
      PqModelRel interp P i (some (.exited code out files)) →
      UASlotPostB interp P r t t_clean c code out files accepted evs_pre

/-- Specification for the whisper `recv` call slot. -/
def UASlotRecvWSpecB : Prop :=
  ∀ (interp : ExternInterpretation) (P : PEParams) (r : ProtocolSetup),
    ExternContractsHoldCli interp → ModelAgree interp P → ProtocolSetupWF r →
    ∀ {t t_clean : CliTurn} {c : CliCall} {i : Inputs} {body : HwBytes}
      {code : Nat} {out : HwBytes} {files : DirectorySnapshot}
      {accepted : List HwBytes} {evs_pre : List CliEvent},
      PqTurnSim1A (interpOfParams interp P) P r t t_clean accepted →
      (c.party = r.alice ∨ c.party = r.bob) →
      c.cmd = .recv (peerOf r c.party) →
      c.bundle = [] →
      c.coins.length = 32 →
      c.stdin = wireWhisperTag :: body →
      body.length < 2 ^ 32 →
      FilesBounded (t.dirs c.party) →
      BobCallAllowed r t c →
      t.records r c.party ≠ none →
      PqFromHonest t.sent body →
      InputsFor c (t.dirs c.party) i →
      PqModelRel interp P i (some (.exited code out files)) →
      UASlotPostB interp P r t t_clean c code out files accepted evs_pre

/-- Specification for Bob's non-promote pre-key `recv` call slot. -/
def UASlotRpkNOSpecB : Prop :=
  ∀ (interp : ExternInterpretation) (P : PEParams) (r : ProtocolSetup),
    ExternContractsHoldCli interp → ModelAgree interp P → ProtocolSetupWF r →
    ∀ {t t_clean : CliTurn} {c : CliCall} {i : Inputs}
      {code : Nat} {out : HwBytes} {files : DirectorySnapshot}
      {accepted : List HwBytes} {evs_pre : List CliEvent},
      PqTurnSim1A (interpOfParams interp P) P r t t_clean accepted →
      c.party = r.bob →
      c.cmd = .recv (peerOf r r.bob) →
      c.bundle = [] →
      c.coins.length = 32 →
      StdinBounded c →
      FilesBounded (t.dirs c.party) →
      BobCallAllowed r t c →
      (c.stdin.head? ≠ some wireWhisperTag ∨ t.records r r.bob = none) →
      (∀ q, parsePreKeyWire c.stdin = some q → PqFromHonest t.sent q.message) →
      (∀ rec_ q, t.records r r.bob = some rec_ → parsePreKeyWire c.stdin = some q →
        ¬ EligibleForSessionPromotion rec_ c.stdin) →
      InputsFor c (t.dirs c.party) i →
      PqModelRel interp P i (some (.exited code out files)) →
      UASlotPostB interp P r t t_clean c code out files accepted evs_pre

/-- Specification for Bob's matching-session promotion `recv` call slot. -/
def UASlotRpkPromSpecB : Prop :=
  ∀ (interp : ExternInterpretation) (P : PEParams) (r : ProtocolSetup),
    ExternContractsHoldCli interp → ModelAgree interp P → ProtocolSetupWF r →
    ∀ {t t_clean : CliTurn} {c : CliCall} {i : Inputs} {rec_ : HwBytes} {q : PreKeyFields}
      {code : Nat} {out : HwBytes} {files : DirectorySnapshot}
      {accepted : List HwBytes} {evs_pre : List CliEvent},
      PqTurnSim1A (interpOfParams interp P) P r t t_clean accepted →
      c.party = r.bob →
      c.cmd = .recv (peerOf r r.bob) →
      c.bundle = [] →
      c.coins.length = 32 →
      StdinBounded c →
      FilesBounded (t.dirs c.party) →
      BobCallAllowed r t c →
      t.records r r.bob = some rec_ →
      parsePreKeyWire c.stdin = some q →
      EligibleForSessionPromotion rec_ c.stdin →
      (∀ q₀, parsePreKeyWire c.stdin = some q₀ → PqFromHonest t.sent q₀.message) →
      InputsFor c (t.dirs c.party) i →
      PqModelRel interp P i (some (.exited code out files)) →
      UASlotPostB interp P r t t_clean c code out files accepted evs_pre

/-- The empty event list has a clean explanation. -/
def UAInitWSpecB : Prop :=
  ∀ {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics},
    ProtocolSetupWF r → SemReady interp' r S →
    ∃ g ss vis, Explains interp' r S g ss vis [] ∧ ¬ ReadCollisionCli interp' r S g ss []

/-- `Explains` and `CollisionAfterExplainedPrefix` are invariant under `interpOfParams`. -/
def UAXportSpecB : Prop :=
  ∀ (interp : ExternInterpretation) (P : PEParams) (r : ProtocolSetup) (S : OpaqueSymbolSemantics),
    (∀ g ss vis evs, Explains (interpOfParams interp P) r S g ss vis evs ↔
      Explains interp r S g ss vis evs) ∧
    (∀ evs, CollisionAfterExplainedPrefix (interpOfParams interp P) r S evs ↔ CollisionAfterExplainedPrefix interp r S evs)

/-! ## Step-to-Move Translation Specifications -/

/-- Every clean step-level explanation of `evs` translates to a clean move-level explanation of
`flatEvents evs` with matching `runTrace`, `honestSalts`, `prefixTerms`, and `plaintextTerms`. -/
def XlateInvSpecB : Prop :=
  ∀ {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant}
    {ok : Nat → Bool} {evs : List CliEvent} {g : Ghost} {ss : List Step} {vis : List VisEntry},
    ProtocolSetupWF r → SemReady interp' r S →
    SchedFits (callsOf evs) who ok →
    Explains interp' r S g ss vis evs → ¬ ReadCollisionCli interp' r S g ss evs →
    ∃ τ ms, ExplainsCli interp' r S who ok (flatEvents evs) τ g ms ∧
      ¬ ReadCollision interp' r S g ms τ ∧
      runTraceMoves r ms = runTrace r ss ∧ honestSalts r ms = honestSaltsOf r ss ∧
      prefixTerms r (runTrace r ss) (runVis r ms) = prefixTerms r (runTrace r ss) vis ∧
      plaintextTerms (runVis r ms) = plaintextTerms vis

/-- Absence of `CollisionAfterExplainedPrefix` on an accepted whisper or promoted-session `recv`
run refutes `SignalMsgAcceptedOnlyViaCollisionMoves` at the call's cut. -/
def XlateExcWSpecB : Prop :=
  ∀ {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant}
    {ok : Nat → Bool} {evs : List CliEvent} {ev : RunEvent} {g₀ : Ghost} {ss₀ : List Step}
    {vis₀ : List VisEntry} {peer : Address} {out b : HwBytes}
    {t_clean : CliTurn} {accepted : List HwBytes},
    ProtocolSetupWF r → SemReady interp' r S →
    SchedFits (callsOf (evs ++ [.run ev])) who ok →
    CliLiveAtCli interp' r S who ok t_clean accepted (flatEvents evs) →
    Explains interp' r S g₀ ss₀ vis₀ evs → ¬ ReadCollisionCli interp' r S g₀ ss₀ evs →
    ev.cmd = .recv peer → ev.exit = some (0, out) → ev.coins.length = 32 →
    (∃ t, t ∈ recvRepresentationsOn interp' S g₀ (runTrace r ss₀) b) →
    ((∃ body, ev.input = wireWhisperTag :: body ∧ b = body) ∨
      ∃ p, parsePreKeyWire ev.input = some p ∧ b = p.message ∧
        p.version = 4 ∧
        p.identityKey.take 33 = ecKey (pubBytes interp' (secretBytes r 0)) ∧
        KnownBaseKeyOn interp' S g₀ (runTrace r ss₀) p) →
    ¬ CollisionAfterExplainedPrefix interp' r S (evs ++ [.run ev]) →
    ∀ τ₁ g ms, ExplainsCli interp' r S who ok (flatEvents evs) τ₁ g ms →
      ¬ ReadCollision interp' r S g ms τ₁ →
      ¬ SignalMsgAcceptedOnlyViaCollisionMoves interp' r S who ok g ms (flatEvents evs) (.recv ev.input)
          [.rng ev.coins, .accept out] b

/-- Absence of `CollisionAfterExplainedPrefix` on an accepted non-promote pre-key `recv` run
refutes `PreKeyStartCollidesOrRejectsMoves` at the call's cut. -/
def XlateExcPSpecB : Prop :=
  ∀ {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant}
    {ok : Nat → Bool} {evs : List CliEvent} {ev : RunEvent} {g₀ : Ghost} {ss₀ : List Step}
    {vis₀ : List VisEntry} {peer : Address} {out : HwBytes} {p : PreKeyFields}
    {t_clean : CliTurn} {accepted : List HwBytes},
    ProtocolSetupWF r → SemReady interp' r S →
    SchedFits (callsOf (evs ++ [.run ev])) who ok →
    CliLiveAtCli interp' r S who ok t_clean accepted (flatEvents evs) →
    Explains interp' r S g₀ ss₀ vis₀ evs → ¬ ReadCollisionCli interp' r S g₀ ss₀ evs →
    ev.cmd = .recv peer → ev.exit = some (0, out) →
    parsePreKeyWire ev.input = some p →
    ¬ KnownBaseKeyOn interp' S g₀ (runTrace r ss₀) p →
    (∃ x, x ∈ preKeyRepresentationsOn interp' r S g₀ (runTrace r ss₀) ev.input) →
    ¬ CollisionAfterExplainedPrefix interp' r S (evs ++ [.run ev]) →
    ∀ τ₁ g ms, ExplainsCli interp' r S who ok (flatEvents evs) τ₁ g ms →
      ¬ ReadCollision interp' r S g ms τ₁ →
      ¬ PreKeyStartCollidesOrRejectsMoves interp' r S who ok g ms (flatEvents evs) ev.input p

end Symbolic.Proofs.Swarm.UA.BI.RAB.Defs

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.Coinsplit.Lift.Defs
public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredClassical

/-!
# Classical CLI Refinement Invariant and Slot Contracts

Defines event flattening (`flatEvents`, `callsOf`, `SchedFits`), the combined CLI refinement
invariant (`UAInv`), per-slot contracts (`UALeakSpec`, `UASlot*Spec`, `UAInitWSpec`, `UAXportSpec`),
and translation contracts (`XlateInvSpec`, `XlateExcWSpec`, `XlateExcPSpec`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.Defs

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
open CryptoGames.LibsignalSessionApi (Session PendingPreKey PendingKyberPreKey)
open Symbolic.Swarm.CREF (compSemOf SemReady)
open Symbolic.Swarm.CREF.TR.Pure (slots_RecordCanonical_Q slots_NonEmptyV1Q)
open Symbolic.Swarm.CREF.Cli (interpOfParams)
open Symbolic.Swarm.Coinsplit.Lift (CliLiveAtCli)

/-! ## Event Flattening and Schedules -/

/-- Whether a CLI run event exited with code `0`. -/
def runOk (ev : RunEvent) : Bool :=
  match ev.exit with
  | some (0, _) => true
  | _ => false

/-- Entry `MachineEvent`s of a run: its input followed by `.rng ev.coins`. -/
def flatEntry (ev : RunEvent) : List MachineEvent :=
  (match ev.cmd with
   | .send _ => [.pt ev.input]
   | _ => [.recv ev.input]) ++ [.rng ev.coins]

/-- Exit `MachineEvent`s of a run: `.send out` or `.accept out` on exit `0`, empty otherwise. -/
def flatExit (ev : RunEvent) : List MachineEvent :=
  match ev.exit, ev.cmd with
  | some (0, out), .send _ => [.send out]
  | some (0, out), .recv _ => [.accept out]
  | _, _ => []

/-- Whether `ev` is a `send` run that did not exit with code `0`; such runs flatten to `[]` and
make no call in `callsOf`. -/
def failedSend (ev : RunEvent) : Bool :=
  match ev.cmd with
  | .send _ => !runOk ev
  | _ => false

/-- Flattened `MachineEvent`s of a single CLI event. -/
def flatEvent : CliEvent → List MachineEvent
  | .run ev => if failedSend ev then [] else flatEntry ev ++ flatExit ev
  | .env (.leak _ k) => [.leak k]
  | .env _ => []

/-- Flattened `MachineEvent`s of a list of CLI events. -/
def flatEvents (evs : List CliEvent) : List MachineEvent := evs.flatMap flatEvent

/-- Caller and exit-`0` status for each non-failed-`send` run event in `evs`. -/
def callsOf : List CliEvent → List (Participant × Bool)
  | [] => []
  | .run ev :: evs => if failedSend ev then callsOf evs else (ev.party, runOk ev) :: callsOf evs
  | .env _ :: evs => callsOf evs

/-- The schedule `(who, ok)` extends the caller sequence of `calls` and agrees with every call's
exit-`0` status. -/
def SchedFits (calls : List (Participant × Bool)) (who : List Participant) (ok : Nat → Bool) :
    Prop :=
  calls.map Prod.fst <+: who ∧ ∀ k p b, calls[k]? = some (p, b) → ok k = b

/-! ## Combined Invariant -/

/-- Every current `alice` snapshot on `tr` has `pendingPreKey` items `(ek, ct)` with serialized
base key `bk` and Kyber ciphertext `kct`. -/
def AlicePendingKeysOn (interp' : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (alice : Participant)
    (tr : ExecTrace) (bk kct : HwBytes) : Prop :=
  ∀ (stateIdx : Nat) (st : _root_.DY.Libsignal.TripleRatchet.TRState),
    ((_root_.DY.PersistentLocalState.getLocalState alice stateIdx :
        _root_.DY.Traceful _root_.DY.Libsignal.TripleRatchet.TRState).run tr).1 = some st →
    _root_.DY.Libsignal.TripleRatchet.isCurrentSnapshot tr stateIdx = true →
    ∃ ek ct, pendingPreKey tr stateIdx = some (ek, ct) ∧
      bk = ecKey (gamma interp' S g ek) ∧ kct = kyberKey (gamma interp' S g ct)

/-- Every current `alice` snapshot on `tr` has `pendingPreKey tr stateIdx = none`. -/
def AliceNotPendingOn (alice : Participant) (tr : ExecTrace) : Prop :=
  ∀ (stateIdx : Nat) (st : _root_.DY.Libsignal.TripleRatchet.TRState),
    ((_root_.DY.PersistentLocalState.getLocalState alice stateIdx :
        _root_.DY.Traceful _root_.DY.Libsignal.TripleRatchet.TRState).run tr).1 = some st →
    _root_.DY.Libsignal.TripleRatchet.isCurrentSnapshot tr stateIdx = true →
    pendingPreKey tr stateIdx = none

/-- Alice's leaked session record in `records` agrees with `initIds` and the `pendingPreKey` state
of every current Alice snapshot on `tr`. -/
def AliceRecordPendingInSession (interp' : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (tr : ExecTrace) (records : Participant → Option HwBytes)
    (initIds : Option BundlePreKeyIds := none) : Prop :=
  ∀ (rec : HwBytes) (sess : Session (List (BitVec 8))),
    records r.alice = some rec →
    slots_RecordCanonical_Q slots_NonEmptyV1Q rec sess →
    (∀ (items : PendingPreKey) (kpk : PendingKyberPreKey),
      sess.pendingPreKey = some items →
      sess.pendingKyberPreKey = some kpk →
      initIds = some (items.preKeyId, items.signedPreKeyId, kpk.preKeyId) ∧
        AlicePendingKeysOn interp' S g r.alice tr items.baseKey.serialize kpk.ciphertext) ∧
    (sess.pendingPreKey = none → AliceNotPendingOn r.alice tr)

/-- Combined CLI invariant after `evs`: either `CollisionAfterExplainedPrefixClassical` holds, or
`CliLiveAtCli` holds on `flatEvents evs`, every clean `ExplainsClassical` witness satisfies
`AliceRecordPendingInSession`, and at least one clean `ExplainsClassical` witness exists. -/
def UAInv (interp' : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (who : List Participant)
    (ok : Nat → Bool) (t_clean : CliTurn) (accepted : List HwBytes) (evs : List CliEvent) : Prop :=
  CollisionAfterExplainedPrefixClassical interp' r S evs ∨
    (CliLiveAtCli interp' r S who ok t_clean accepted (flatEvents evs) ∧
      (∀ g ss vis, ExplainsClassical interp' r S g ss vis evs → ¬ ReadCollisionCliClassical interp' r S g ss evs →
        AliceRecordPendingInSession interp' r S g (runTrace r ss) (t_clean.leakRecords r) (activeBundleIds evs)) ∧
      ∃ g ss vis, ExplainsClassical interp' r S g ss vis evs ∧ ¬ ReadCollisionCliClassical interp' r S g ss evs)

/-- Per-call postcondition preserving `PqTurnSim1A` and advancing `UAInv` across a single CLI call. -/
def UASlotPost (interp : ExternInterpretation) (P : PEParams) (r : ProtocolSetup)
    (t t_clean : CliTurn) (c : CliCall) (code : Nat) (out : HwBytes) (files : DirectorySnapshot)
    (accepted : List HwBytes) (evs_pre : List CliEvent) : Prop :=
  let interp' := interpOfParams interp P
  let S := compSemOf interp' r
  let evs := evs_pre ++ [.run (runEventOf c (some (code, out)))]
  ∃ (t_clean' : CliTurn) (accepted' : List HwBytes),
    PqTurnSim1A interp' P r (CliTurn.after t r c code out files) t_clean' accepted' ∧
    ∀ (who : List Participant) (ok : Nat → Bool),
      SchedFits (callsOf evs) who ok →
      UAInv interp' r S who ok t_clean accepted evs_pre →
      UAInv interp' r S who ok t_clean' accepted' evs

/-! ## Slot Contracts -/

/-- Environment leak events (`LeaksFrom`) preserve `UAInv`. -/
def UALeakSpec : Prop :=
  ∀ (interp : ExternInterpretation) (P : PEParams) (r : ProtocolSetup),
    ExternContractsHoldCli interp → ModelAgree interp P → ProtocolSetupWF r →
    ∀ {t t_clean : CliTurn} {accepted : List HwBytes} {evs leaks : List CliEvent}
      {who : List Participant} {ok : Nat → Bool},
      PqTurnSim1A (interpOfParams interp P) P r t t_clean accepted →
      LeaksFrom r t leaks →
      SchedFits (callsOf evs) who ok →
      UAInv (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r) who ok
        t_clean accepted evs →
      UAInv (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r) who ok
        t_clean accepted (evs ++ leaks)

/-- Contract for Alice's `init` CLI slot. -/
def UASlotInitSpec : Prop :=
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
      UASlotPost interp P r t t_clean c code out files accepted evs_pre

/-- Contract for the `send` CLI slot. -/
def UASlotSendSpec : Prop :=
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
      UASlotPost interp P r t t_clean c code out files accepted evs_pre

/-- Contract for the whisper `recv` CLI slot. -/
def UASlotRecvWSpec : Prop :=
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
      UASlotPost interp P r t t_clean c code out files accepted evs_pre

/-- Contract for Bob's non-promote `recv` CLI slot. -/
def UASlotRpkNOSpec : Prop :=
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
      UASlotPost interp P r t t_clean c code out files accepted evs_pre

/-- Contract for Bob's session-promotion `recv` CLI slot. -/
def UASlotRpkPromSpec : Prop :=
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
      UASlotPost interp P r t t_clean c code out files accepted evs_pre

/-- Clean explanation existence for the empty CLI event list. -/
def UAInitWSpec : Prop :=
  ∀ {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics},
    ProtocolSetupWF r → SemReady interp' r S →
    ∃ g ss vis, ExplainsClassical interp' r S g ss vis [] ∧ ¬ ReadCollisionCliClassical interp' r S g ss []

/-- Invariance of `ExplainsClassical` and `CollisionAfterExplainedPrefixClassical` under
`interpOfParams`. -/
def UAXportSpec : Prop :=
  ∀ (interp : ExternInterpretation) (P : PEParams) (r : ProtocolSetup) (S : OpaqueSymbolSemantics),
    (∀ g ss vis evs, ExplainsClassical (interpOfParams interp P) r S g ss vis evs ↔
      ExplainsClassical interp r S g ss vis evs) ∧
    (∀ evs, CollisionAfterExplainedPrefixClassical (interpOfParams interp P) r S evs ↔ CollisionAfterExplainedPrefixClassical interp r S evs)

/-! ## Translation Contracts -/

/-- Flattened-event per-call postcondition for `CliLiveAtCli` under side condition `NC`. -/
def CliSlotPostW (NC : List Participant → (Nat → Bool) → Prop)
    (interp : ExternInterpretation) (P : PEParams) (r : ProtocolSetup)
    (t t_clean : CliTurn) (c : CliCall) (code : Nat) (out : HwBytes) (files : DirectorySnapshot)
    (accepted : List HwBytes) (σ_pre : List MachineEvent) : Prop :=
  let interp' := interpOfParams interp P
  let S := compSemOf interp' r
  let blk_cli := cliEntryEvents c ++ cliExitEvents c code out
  ∃ (t_clean' : CliTurn) (accepted' : List HwBytes),
    PqTurnSim1A interp' P r (CliTurn.after t r c code out files) t_clean' accepted' ∧
    ∀ (who : List Participant) (ok : Nat → Bool),
      who[(callStarts σ_pre).length]? = some c.party →
      CliLiveAtCli interp' r S who ok t_clean accepted σ_pre →
      NC who ok →
      ok (callStarts σ_pre).length = decide (code = 0) →
      CliLiveAtCli interp' r S who ok t_clean' accepted' (σ_pre ++ blk_cli)

/-- Every clean `ExplainsClassical` witness on `evs` translates to a clean `ExplainsCli` move run on
`flatEvents evs` with matching trace, candidate salts, `prefixTerms`, and `plaintextTerms`. -/
def XlateInvSpec : Prop :=
  ∀ {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant}
    {ok : Nat → Bool} {evs : List CliEvent} {g : Ghost} {ss : List Step} {vis : List VisEntry},
    ProtocolSetupWF r → SemReady interp' r S →
    SchedFits (callsOf evs) who ok →
    ExplainsClassical interp' r S g ss vis evs → ¬ ReadCollisionCliClassical interp' r S g ss evs →
    ∃ τ ms, ExplainsCli interp' r S who ok (flatEvents evs) τ g ms ∧
      ¬ ReadCollision interp' r S g ms τ ∧
      runTraceMoves r ms = runTrace r ss ∧ honestSalts r ms = honestSaltsOf r ss ∧
      prefixTerms r (runTrace r ss) (runVis r ms) = prefixTerms r (runTrace r ss) vis ∧
      plaintextTerms (runVis r ms) = plaintextTerms vis

/-- Absence of `CollisionAfterExplainedPrefixClassical` at an accepted whisper or known-base-key
pre-key `recv` run refutes `SignalMsgAcceptedOnlyViaCollisionMoves` on every clean move explanation
of `flatEvents evs`. -/
def XlateExcWSpec : Prop :=
  ∀ {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant}
    {ok : Nat → Bool} {evs : List CliEvent} {ev : RunEvent} {g₀ : Ghost} {ss₀ : List Step}
    {vis₀ : List VisEntry} {peer : Address} {out b : HwBytes}
    {t_clean : CliTurn} {accepted : List HwBytes},
    ProtocolSetupWF r → SemReady interp' r S →
    SchedFits (callsOf (evs ++ [.run ev])) who ok →
    CliLiveAtCli interp' r S who ok t_clean accepted (flatEvents evs) →
    ExplainsClassical interp' r S g₀ ss₀ vis₀ evs → ¬ ReadCollisionCliClassical interp' r S g₀ ss₀ evs →
    ev.cmd = .recv peer → ev.exit = some (0, out) → ev.coins.length = 32 →
    (∃ t, t ∈ recvRepresentationsOn interp' S g₀ (runTrace r ss₀) b) →
    ((∃ body, ev.input = wireWhisperTag :: body ∧ b = body) ∨
      ∃ p, parsePreKeyWire ev.input = some p ∧ b = p.message ∧
        p.version = 4 ∧
        p.identityKey.take 33 = ecKey (pubBytes interp' (secretBytes r 0)) ∧
        KnownBaseKeyOn interp' S g₀ (runTrace r ss₀) p) →
    ¬ CollisionAfterExplainedPrefixClassical interp' r S (evs ++ [.run ev]) →
    ∀ τ₁ g ms, ExplainsCli interp' r S who ok (flatEvents evs) τ₁ g ms →
      ¬ ReadCollision interp' r S g ms τ₁ →
      ¬ SignalMsgAcceptedOnlyViaCollisionMoves interp' r S who ok g ms (flatEvents evs) (.recv ev.input)
          [.rng ev.coins, .accept out] b

/-- Absence of `CollisionAfterExplainedPrefixClassical` at an accepted pre-key `recv` run on an
unknown base key refutes `PreKeyStartCollidesOrRejectsMoves` on every clean move explanation of
`flatEvents evs`. -/
def XlateExcPSpec : Prop :=
  ∀ {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant}
    {ok : Nat → Bool} {evs : List CliEvent} {ev : RunEvent} {g₀ : Ghost} {ss₀ : List Step}
    {vis₀ : List VisEntry} {peer : Address} {out : HwBytes} {p : PreKeyFields}
    {t_clean : CliTurn} {accepted : List HwBytes},
    ProtocolSetupWF r → SemReady interp' r S →
    SchedFits (callsOf (evs ++ [.run ev])) who ok →
    CliLiveAtCli interp' r S who ok t_clean accepted (flatEvents evs) →
    ExplainsClassical interp' r S g₀ ss₀ vis₀ evs → ¬ ReadCollisionCliClassical interp' r S g₀ ss₀ evs →
    ev.cmd = .recv peer → ev.exit = some (0, out) →
    parsePreKeyWire ev.input = some p →
    ¬ KnownBaseKeyOn interp' S g₀ (runTrace r ss₀) p →
    (∃ x, x ∈ preKeyRepresentationsOn interp' r S g₀ (runTrace r ss₀) ev.input) →
    ¬ CollisionAfterExplainedPrefixClassical interp' r S (evs ++ [.run ev]) →
    ∀ τ₁ g ms, ExplainsCli interp' r S who ok (flatEvents evs) τ₁ g ms →
      ¬ ReadCollision interp' r S g ms τ₁ →
      ¬ PreKeyStartCollidesOrRejectsMoves interp' r S who ok g ms (flatEvents evs) ev.input p

end Symbolic.Proofs.Swarm.UA.Defs

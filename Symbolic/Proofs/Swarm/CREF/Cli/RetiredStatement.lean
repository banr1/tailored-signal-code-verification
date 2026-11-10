/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.Statement
public import Symbolic.Proofs.SpecLemmas.LeakableSecretProofDefs
public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredTraceExplanation

/-!
# Move-Based CLI Refinement Statement

Defines CLI trace generation (`CliTracesMoves`), coin-file splitting (`CoinSplit`), CLI-level
explanation predicates (`ExplainsCli`), collision excuses, and the move-based refinement
statement `CompRefinesCliMoves`.
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Refinement.Cli

open DY DY.Comparse
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open CryptoVerification.SignalSession (Inputs Outcome CliRun Cmd PublicBundle filesOf stdioPaths partyDirs
  bundleDir coinsFile oneTimePreKeyFile)

/-! ## Events and Traces -/

/-- Entry events emitted by a CLI call `c`: its input (`recv` of the parsed bundle blob or stdin,
or `pt` of stdin) followed by `.rng c.coins`. -/
def cliEntryEvents (c : CliCall) : List MachineEvent :=
  (match c.cmd with
   | .init _ _ => [.recv (((parseBundleFiles (filesOf c.bundle)).map bundleBlob).getD [])]
   | .send _ => [.pt c.stdin]
   | .recv _ => [.recv c.stdin]) ++
  [.rng c.coins]

/-- Exit events emitted by a CLI call `c` with exit code `code` and stdout `out`. -/
def cliExitEvents (c : CliCall) (code : Nat) (out : HwBytes) : List MachineEvent :=
  match code, c.cmd with
  | 0, .send _ => [.send out]
  | 0, .recv _ => [.accept out]
  | _, _ => []

/-- Relates a CLI-granularity trace (with one `.rng` event per call's `coins` file) to a
hardware-granularity trace splitting a prefix of each `coins` file into non-empty `.rng` draws. -/
inductive CoinSplit : List MachineEvent → List MachineEvent → Prop
  | nil : CoinSplit [] []
  | keep {e : MachineEvent} {τ τhw : List MachineEvent} :
      (∀ b, e ≠ .rng b) → CoinSplit τ τhw → CoinSplit (e :: τ) (e :: τhw)
  | split {coins : HwBytes} {pieces : List HwBytes} {τ τhw : List MachineEvent} :
      (∀ p ∈ pieces, p ≠ []) → pieces.flatten <+: coins → CoinSplit τ τhw →
      CoinSplit (.rng coins :: τ) (pieces.map MachineEvent.rng ++ τhw)

/-- Execution traces of run relation `Rel` from turn `t`, paired with the `(party, exitedZero)`
call log. -/
inductive CliTracesMoves (Rel : Inputs → Option Outcome → Prop) (interp : ExternInterpretation)
    (r : ProtocolSetup) : CliTurn → List MachineEvent → List (Participant × Bool) → Prop
  | done (t : CliTurn) : CliTracesMoves Rel interp r t [] []
  | clear {t : CliTurn} {τ : List MachineEvent} {calls : List (Participant × Bool)}
      (p : Participant) :
      CliTracesMoves Rel interp r (t.clearSession r p) τ calls → CliTracesMoves Rel interp r t τ calls
  | step {t : CliTurn} {leaks : List MachineEvent} {c : CliCall} {i : Inputs} {code : Nat}
      {out : HwBytes} {files : DirectorySnapshot} {τ : List MachineEvent} {calls : List (Participant × Bool)} :
      (∀ e ∈ leaks, ∃ k, KeyInDirs r t k ∧ e = .leak k) →
      ValidCall interp r t c → InputsFor c (t.dirs c.party) i →
      Rel i (some (.exited code out files)) →
      CliTracesMoves Rel interp r (t.after r c code out files) τ calls →
      CliTracesMoves Rel interp r t (leaks ++ cliEntryEvents c ++ cliExitEvents c code out ++ τ)
        ((c.party, decide (code = 0)) :: calls)
  | stop {t : CliTurn} {leaks : List MachineEvent} {c : CliCall} {i : Inputs}
      {o : Option Outcome} :
      (∀ e ∈ leaks, ∃ k, KeyInDirs r t k ∧ e = .leak k) →
      ValidCall interp r t c → InputsFor c (t.dirs c.party) i →
      Rel i o → (o = some .aborted ∨ o = none) →
      CliTracesMoves Rel interp r t (leaks ++ cliEntryEvents c) [(c.party, false)]

/-- Agreement of `calls` with caller schedule `who` and non-final call outcome schedule `ok`. -/
def CallsMatchSchedules (calls : List (Participant × Bool)) (who : List Participant) (ok : Nat → Bool) :
    Prop :=
  calls.map Prod.fst <+: who ∧ ∀ k p b, k + 1 < calls.length → calls[k]? = some (p, b) → ok k = b

/-! ## Explanations at CLI Granularity -/

/-- `OutcomeFaithful` strengthened at CLI granularity: every call in `ms` with `ok k = true`
completes in the model via `send`, `accept`, or `AliceDone`. -/
def OutcomeFaithfulCli (r : ProtocolSetup) (ok : Nat → Bool) (ms : List Move) : Prop :=
  OutcomeFaithful r ok ms ∧
    ∀ (i : Nat) (m : Move), ms[i]? = some m →
      let tr := runTraceMoves r (ms.take i)
      let vs := m.vis tr
      vs.any (fun v => v.kind == .recv || v.kind == .pt) →
      ok (callCount (runVis r (ms.take i))) = true →
      vs.any (fun v => v.kind == .send || v.kind == .accept) ∨
        (eventIdx isAliceDone tr (m.next tr)).isSome

/-- Every `.single`-layout `.rng` entry of a `.recv`-headed move in `ms` concretizes to 32 bytes. -/
def RngLengthsFaithfulCli (interp : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ms : List Move) : Prop :=
  ∀ (i : Nat) (m : Move), ms[i]? = some m →
    let tr := runTraceMoves r (ms.take i)
    let vs := m.vis tr
    vs.any (fun v => v.kind == .recv) →
    ∀ (v : VisEntry) (t : DY.Bytes),
      v ∈ vs → v.kind = .rng → v.layout = .single → v.terms = [t] →
      (gamma interp S g t).length = 32

/-- CLI-granularity prefix explanation of `σ₁` via coin split `τ₁` and model run `(g, ms)`. -/
def ExplainsCli (interp : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (who : List Participant)
    (ok : Nat → Bool) (σ₁ τ₁ : List MachineEvent) (g : Ghost) (ms : List Move) : Prop :=
  CoinSplit σ₁ τ₁ ∧ MatchedPrefix interp r S who g ms τ₁ ∧ OutcomeFaithfulCli r ok ms ∧
    RngLengthsFaithfulCli interp r S g ms

def ModelAcceptsTermAfterAttackerSendsMoves (interp : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (who : List Participant)
    (ok : Nat → Bool) (g : Ghost) (ms : List Move) (τ₁ : List MachineEvent) (e : MachineEvent)
    (σ₂ : List MachineEvent) (t : DY.Bytes) : Prop :=
  ∃ τ₂, CoinSplit σ₂ τ₂ ∧ ModelAcceptsTermAfterCoinSplit interp r S who ok g ms τ₁ e τ₂ t

/-- Under prefix explanation `(τ₁', g', ms')`, either every representation of `b` hits a receive or
reselection collision, or some representation is accepted and every accepted representation hits
`RecvCollision`. -/
def RepresentationsCollideOrAcceptedCollideMoves (interp : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (who : List Participant) (ok : Nat → Bool)
    (τ₁' : List MachineEvent) (g' : Ghost) (ms' : List Move)
    (e : MachineEvent) (σ₂ : List MachineEvent) (b : HwBytes) : Prop :=
  let reps := recvRepresentations interp r S g' ms' b
  let accepts := ModelAcceptsTermAfterAttackerSendsMoves interp r S who ok g' ms' τ₁' e σ₂
  (∀ t ∈ reps, RecvCollision interp r S g' ms' t ∨ ReselectCollision interp r S g' ms' t) ∨
    ((∃ t ∈ reps, accepts t) ∧ ∀ t ∈ reps, accepts t → RecvCollision interp r S g' ms' t)

/-- Received `SignalMessage` body `b` has a term representation and triggers
`RepresentationsCollideOrAcceptedCollideMoves` under every read-collision-free explanation of `σ₁`. -/
def SignalMsgAcceptedOnlyViaCollisionMoves (interp : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (who : List Participant) (ok : Nat → Bool)
    (g : Ghost) (ms : List Move) (σ₁ : List MachineEvent)
    (e : MachineEvent) (σ₂ : List MachineEvent) (b : HwBytes) : Prop :=
  (∃ t, t ∈ recvRepresentations interp r S g ms b) ∧
    ∀ τ₁' g' ms', ExplainsCli interp r S who ok σ₁ τ₁' g' ms' →
      ¬ ReadCollision interp r S g' ms' τ₁' →
      RepresentationsCollideOrAcceptedCollideMoves interp r S who ok τ₁' g' ms' e σ₂ b

/-- Collision or `KyberMismatch` excuse for a new pre-key message `p` after CLI prefix `σ₁`. -/
def PreKeyStartCollidesOrRejectsMoves (interp : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (ok : Nat → Bool) (g : Ghost) (ms : List Move)
    (σ₁ : List MachineEvent) (b : HwBytes) (p : PreKeyFields) : Prop :=
  (∃ x, x ∈ preKeyRepresentations interp r S g ms b) ∧
    (KyberMismatch interp r p ∨
      ∀ τ₁' g' ms', ExplainsCli interp r S who ok σ₁ τ₁' g' ms' →
        ¬ ReadCollision interp r S g' ms' τ₁' →
        ∀ x ∈ preKeyRepresentations interp r S g' ms' b, BobSessionStartCollidesOrImplicitRejects interp r S g' ms' p x)

/-- Ghosts sharing `g.σ` that explain some coin split `τ₁'` of `σ₁` under `ms`. -/
def PrefixExplainingGhostsMoves (interp : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (g : Ghost) (ms : List Move) (σ₁ : List MachineEvent) : Set Ghost :=
  {g' | g'.σ = g.σ ∧ ∃ τ₁', CoinSplit σ₁ τ₁' ∧ MatchedPrefix interp r S who g' ms τ₁'}

/-- Next hardware event `e` after prefix `σ₁` triggers a cryptographic collision relative to `(g, ms)`. -/
def NextEventCollidesMoves (interp : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (who : List Participant) (ok : Nat → Bool)
    (g : Ghost) (ms : List Move) (σ₁ : List MachineEvent) (e : MachineEvent)
    (σ₂ : List MachineEvent) : Prop :=
  let accepted := ∃ pt, (σ₂.filter fun e => eventKind e != .rng).head? = some (.accept pt)
  match e with
  | .recv (tag :: body) =>
    accepted ∧
    ((tag = wireWhisperTag ∧
        SignalMsgAcceptedOnlyViaCollisionMoves interp r S who ok g ms σ₁ (.recv (tag :: body)) σ₂ body) ∨
     (∃ p, parsePreKeyWire (tag :: body) = some p ∧
        ((KnownBaseKey interp r S g ms p ∧
            SignalMsgAcceptedOnlyViaCollisionMoves interp r S who ok g ms σ₁ (.recv (tag :: body)) σ₂
              p.message) ∨
         (¬ KnownBaseKey interp r S g ms p ∧
            PreKeyStartCollidesOrRejectsMoves interp r S who ok g ms σ₁ (tag :: body) p))))
  | .pt b =>
    let v := ptEntryOfNextEncrypt r ms
    let tr := runTraceMoves r ms
    EventMatchesEntry interp r S g (.pt b) v ∧
      ∀ g' ∈ PrefixExplainingGhostsMoves interp r S who g ms σ₁,
        MemoCollisionOn interp r S g' (fun u => u.AttackerKnows tr) tr (runVis r ms)
          v.terms v.terms
  | _ => False

/-- Existence of an explained CLI prefix `σ₁` of `σ` whose next event triggers `NextEventCollidesMoves`. -/
def CollisionAfterExplainedPrefixMoves (interp : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (who : List Participant) (ok : Nat → Bool)
    (σ : List MachineEvent) : Prop :=
  ∃ (σ₁ : List MachineEvent) (e : MachineEvent) (σ₂ τ₁ : List MachineEvent) (g : Ghost)
    (ms : List Move),
    σ = σ₁ ++ (e :: σ₂) ∧
    ExplainsCli interp r S who ok σ₁ τ₁ g ms ∧
    NextEventCollidesMoves interp r S who ok g ms σ₁ e σ₂

/-! ## Refinement Statement -/

/-- Move-based whole-protocol CLI refinement from initial directories `dirs`, parameterized by run
relation `R`. -/
def CompRefinesCliRMoves {ω : Type} (Agree : ExternInterpretation → ω → Prop)
    (R : ExternInterpretation → ω → Inputs → Option Outcome → Prop)
    (dirs : ExternInterpretation → ProtocolSetup → Participant → DirectorySnapshot) : Prop :=
  ∀ interp : ExternInterpretation, ExternContractsHoldCli interp →
  ∀ W : ω, Agree interp W →
  ∀ r : ProtocolSetup, ProtocolSetupWF r →
  ∃ S : OpaqueSymbolSemantics, ∀ (τ : List MachineEvent) (calls : List (Participant × Bool)),
    CliTracesMoves (R interp W) interp r (CliTurn.init (dirs interp r)) τ calls →
    ∀ (who : List Participant) (ok : Nat → Bool), CallsMatchSchedules calls who ok →
      (∃ τhw g ms, CoinSplit τ τhw ∧ MatchedPrefix interp r S who g ms τhw) ∨
        CollisionAfterExplainedPrefixMoves interp r S who ok τ

/-- `CompRefinesCliRMoves` instantiated at `initDirs`. -/
def CompRefinesCliMoves {ω : Type} (Agree : ExternInterpretation → ω → Prop)
    (R : ExternInterpretation → ω → Inputs → Option Outcome → Prop) : Prop :=
  CompRefinesCliRMoves Agree R initDirs

end DY.Libsignal.Composed.Refinement.Cli

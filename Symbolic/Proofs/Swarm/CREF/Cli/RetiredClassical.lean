/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Refinement.Composed.Cli.Model

/-!
# Classical-Attacker Refinement Definitions

Classical-attacker counterparts (`*Classical`) of the trace-explanation and CLI refinement
predicates without break, invert, or corrupt-registration environment events, bridged to the
unified-attacker statement on `BreakFree` traces in `ClassicalBridge`.
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Refinement

open DY DY.Comparse
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (RunEvent EnvEvent CliEvent)

/-- Classical environment-event matching: matches `leak p k` against an environment leak step of
`p` and rejects all other `EnvEvent` constructors. -/
def EnvMatchesClassical (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (tr : ExecTrace) (s : Step) (ev : EnvEvent) (vis : List VisEntry) : Prop :=
  match ev with
  | .leak p k =>
    s.cls = .env ∧ s.IsLeak ∧ (∀ q, s.party? = some q → q = p) ∧
      vis = stepView s tr false ∧
      ∃ v, vis = [v] ∧ BytesMatchEntry interpretation r S g .leak k v
  | .breakDH | .breakKEM | .invertDH .. | .invertKEM .. | .registerCorrupt .. => False

/-- Event-to-step matching relation parameterized by `EnvMatchesClassical` and active bundle
pre-key IDs `initIds`. -/
inductive MatchesEventsClassicalAt (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) : Option BundlePreKeyIds → ExecTrace → List Step → List CliEvent → List VisEntry → Prop
  | nil {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {ss : List Step} :
      (∀ x ∈ ss, x.cls = .invisible) →
      MatchesEventsClassicalAt interpretation r S g initIds tr ss [] []
  | run1 {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {pre : List Step} {s : Step} {ss : List Step} {ev : RunEvent}
      {evs : List CliEvent} {v vs : List VisEntry} :
      (∀ x ∈ pre, x.cls = .invisible) →
      RunMatches interpretation r S g (runSteps pre tr) s ev v initIds →
      MatchesEventsClassicalAt interpretation r S g (nextBundleIds initIds ev) (s.next (runSteps pre tr)) ss evs vs →
      MatchesEventsClassicalAt interpretation r S g initIds tr (pre ++ s :: ss) (.run ev :: evs) (v ++ vs)
  | run0 {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {pre ss : List Step} {ev : RunEvent} {evs : List CliEvent}
      {vs : List VisEntry} :
      (∀ x ∈ pre, x.cls = .invisible) →
      RunRejected ev →
      MatchesEventsClassicalAt interpretation r S g initIds (runSteps pre tr) ss evs vs →
      MatchesEventsClassicalAt interpretation r S g initIds tr (pre ++ ss) (.run ev :: evs) vs
  | env {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {pre : List Step} {s : Step} {ss : List Step} {ev : EnvEvent}
      {evs : List CliEvent} {v vs : List VisEntry} :
      (∀ x ∈ pre, x.cls = .invisible) →
      EnvMatchesClassical interpretation r S g (runSteps pre tr) s ev v →
      MatchesEventsClassicalAt interpretation r S g initIds (s.next (runSteps pre tr)) ss evs vs →
      MatchesEventsClassicalAt interpretation r S g initIds tr (pre ++ s :: ss) (.env ev :: evs) (v ++ vs)

abbrev MatchesEventsClassical (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) : ExecTrace → List Step → List CliEvent → List VisEntry → Prop :=
  MatchesEventsClassicalAt interpretation r S g none

/-- Classical trace explanation over `MatchesEventsClassical`. -/
def ExplainsClassical (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ss : List Step) (vis : List VisEntry) (evs : List CliEvent) : Prop :=
  GhostAndSemMatchSetup interpretation r S g ∧ GhostWF g vis ∧ ModelRunWF r ss ∧
    MatchesEventsClassical interpretation r S g (setupTrace r) ss evs vis

end DY.Libsignal.Composed.Refinement

namespace DY.Libsignal.Composed.Refinement.Cli

open DY DY.Comparse
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (RunEvent EnvEvent CliEvent)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open CryptoVerification.SignalSession (Inputs Outcome)

/-- Classical CLI execution traces without `breakInvert` steps. -/
inductive CliTracesClassical (Rel : Inputs → Option Outcome → Prop) (interp : ExternInterpretation)
    (r : ProtocolSetup) : CliTurn → List CliEvent → Prop
  | done (t : CliTurn) : CliTracesClassical Rel interp r t []
  | clear {t : CliTurn} {evs : List CliEvent} (p : Participant) :
      CliTracesClassical Rel interp r (t.clearSession r p) evs →
      CliTracesClassical Rel interp r t evs
  | step {t : CliTurn} {leaks : List CliEvent} {c : CliCall} {i : Inputs} {code : Nat}
      {out : HwBytes} {files : DirectorySnapshot} {evs : List CliEvent} :
      LeaksFrom r t leaks →
      ValidCall interp r t c → InputsFor c (t.dirs c.party) i →
      Rel i (some (.exited code out files)) →
      CliTracesClassical Rel interp r (t.after r c code out files) evs →
      CliTracesClassical Rel interp r t (leaks ++ .run (runEventOf c (some (code, out))) :: evs)
  | stop {t : CliTurn} {leaks : List CliEvent} {c : CliCall} {i : Inputs}
      {o : Option Outcome} :
      LeaksFrom r t leaks →
      ValidCall interp r t c → InputsFor c (t.dirs c.party) i →
      Rel i o → o = some .aborted →
      CliTracesClassical Rel interp r t (leaks ++ [.run (runEventOf c none)])

/-- Earlier accepted read collision along a `MatchesEventsClassical` prefix. -/
def ReadCollisionCliClassical (interp : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ss : List Step) (evs : List CliEvent) : Prop :=
  ∃ (evs₁ : List CliEvent) (ev : RunEvent) (evs₂ : List CliEvent) (ss₁ ss₂ : List Step) (m : Step)
    (vis₁ : List VisEntry) (msgIdx : Nat) (out b : HwBytes) (t : DY.Bytes),
    evs = evs₁ ++ .run ev :: evs₂ ∧ ss = ss₁ ++ m :: ss₂ ∧
    (∃ peer, ev.cmd = .recv peer) ∧ ev.exit = some (0, out) ∧ RecvBody ev.input b ∧
    MatchesEventsClassical interp r S g (setupTrace r) ss₁ evs₁ vis₁ ∧
    m.decryptMsgIdx? = some msgIdx ∧
    (runTrace r ss₁).getMessageSentAt msgIdx = some t ∧
    RecvCollisionOn interp r S g (runTrace r ss₁) vis₁ (honestSaltsOf r ss₁) t

def ModelAcceptsTermAfterAttackerSendsClassical (interp : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ss : List Step) (evs₁ : List CliEvent) (ev : RunEvent) (t : DY.Bytes) : Prop :=
  ∃ (ext : List DY.Bytes) (m : Step) (msgIdx : Nat) (g₁ : Ghost) (vis₁ : List VisEntry),
    (∀ x ∈ ext, x.AttackerKnows (runTrace r ss)) ∧
    m.decryptMsgIdx? = some msgIdx ∧
    g₁.addr = g.addr ∧ (∀ i, i < (runTrace r ss).length → g₁.σ i = g.σ i) ∧
    (runTrace r (ss ++ ext.map .network)).getMessageSentAt msgIdx = some t ∧
    ExplainsClassical interp r S g₁ (ss ++ ext.map .network ++ [m]) vis₁ (evs₁ ++ [.run ev])

def RepresentationsCollideOrAcceptedCollideClassical (interp : ExternInterpretation)
    (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (evs₁ : List CliEvent) (g' : Ghost)
    (ss' : List Step) (vis' : List VisEntry) (ev : RunEvent) (b : HwBytes) : Prop :=
  let tr := runTrace r ss'
  let salts := honestSaltsOf r ss'
  let reps := recvRepresentationsOn interp S g' tr b
  let accepts := ModelAcceptsTermAfterAttackerSendsClassical interp r S g' ss' evs₁ ev
  (∀ t ∈ reps, RecvCollisionOn interp r S g' tr vis' salts t ∨
      ReselectCollisionOn interp r S g' tr vis' salts t) ∨
    ((∃ t ∈ reps, accepts t) ∧
      ∀ t ∈ reps, accepts t → RecvCollisionOn interp r S g' tr vis' salts t)

def SignalMsgAcceptedOnlyViaCollisionClassical (interp : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (g : Ghost) (ss : List Step) (evs₁ : List CliEvent) (ev : RunEvent)
    (b : HwBytes) : Prop :=
  (∃ t, t ∈ recvRepresentationsOn interp S g (runTrace r ss) b) ∧
    ∀ g' ss' vis', ExplainsClassical interp r S g' ss' vis' evs₁ →
      ¬ ReadCollisionCliClassical interp r S g' ss' evs₁ →
      RepresentationsCollideOrAcceptedCollideClassical interp r S evs₁ g' ss' vis' ev b

def PreKeyStartCollidesOrRejectsClassical (interp : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ss : List Step) (evs₁ : List CliEvent) (b : HwBytes) (p : PreKeyFields) : Prop :=
  (∃ x, x ∈ preKeyRepresentationsOn interp r S g (runTrace r ss) b) ∧
    (KyberMismatch interp r p ∨
      ∀ g' ss' vis', ExplainsClassical interp r S g' ss' vis' evs₁ →
        ¬ ReadCollisionCliClassical interp r S g' ss' evs₁ →
        ∀ x ∈ preKeyRepresentationsOn interp r S g' (runTrace r ss') b,
          BobSessionStartCollidesOrImplicitRejectsOn interp r S g' (runTrace r ss') vis' (honestSaltsOf r ss') p x)

def PrefixExplainingGhostsClassical (interp : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ss : List Step) (evs₁ : List CliEvent) : Set Ghost :=
  {g' | g'.σ = g.σ ∧ ∃ vis', ExplainsClassical interp r S g' ss vis' evs₁}

/-- Collision excuse for the next `RunEvent` after a classical explained prefix `evs₁`. -/
def NextEventCollidesClassical (interp : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (g : Ghost) (ss : List Step) (vis : List VisEntry)
    (evs₁ : List CliEvent) (ev : RunEvent) : Prop :=
  let tr := runTrace r ss
  match ev.cmd with
  | .recv _ =>
    (∃ out, ev.exit = some (0, out)) ∧
    match ev.input with
    | tag :: body =>
      (tag = wireWhisperTag ∧ SignalMsgAcceptedOnlyViaCollisionClassical interp r S g ss evs₁ ev body) ∨
      (∃ p, parsePreKeyWire (tag :: body) = some p ∧
        ((KnownBaseKeyOn interp S g tr p ∧ p.version = 4 ∧
            p.identityKey.take 33 = ecKey (pubBytes interp (secretBytes r 0)) ∧
            SignalMsgAcceptedOnlyViaCollisionClassical interp r S g ss evs₁ ev p.message) ∨
         (¬ KnownBaseKeyOn interp S g tr p ∧
            PreKeyStartCollidesOrRejectsClassical interp r S g ss evs₁ (tag :: body) p)))
    | [] => False
  | .send _ =>
    let v := ptEntryAt tr
    BytesMatchEntry interp r S g .pt ev.input v ∧
      ∀ g' ∈ PrefixExplainingGhostsClassical interp r S g ss evs₁,
        MemoCollisionOn interp r S g' (fun u => u.AttackerKnows tr) tr vis v.terms v.terms
  | .init _ _ => False

/-- Existence of a classical explained prefix `evs₁` whose next `RunEvent` triggers
`NextEventCollidesClassical`. -/
def CollisionAfterExplainedPrefixClassical (interp : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (evs : List CliEvent) : Prop :=
  ∃ (evs₁ : List CliEvent) (ev : RunEvent) (evs₂ : List CliEvent) (g : Ghost) (ss : List Step)
    (vis : List VisEntry),
    evs = evs₁ ++ .run ev :: evs₂ ∧
    ExplainsClassical interp r S g ss vis evs₁ ∧
    NextEventCollidesClassical interp r S g ss vis evs₁ ev

end DY.Libsignal.Composed.Refinement.Cli

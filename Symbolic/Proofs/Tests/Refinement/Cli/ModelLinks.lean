/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Refinement.Composed.Cli.OldShape
public import Symbolic.Specifications.Refinement.ElfBinding
public import Symbolic.Proofs.SpecLemmas.ExternInterpretationProofDefs
import Symbolic.Proofs.Tests.Refinement.Cli.ExternWitness

/-!
# Links and Non-Vacuity Checks for `Composed/Cli/Model.lean`

Relates `CompRefinesCliModelMoves` to `LockedReading` under model determinism (`DraftDet`),
proves that `PqModelRel` admits every spec-conforming run with file-system extensionality
(`FilesExt`) as well as every aborted outcome (`rel_of_specs`, `rel_nonempty`), and checks
joint satisfiability of `ExternInterpretationTotalOnUsedSymbols`, `ExternContractsHoldCli`,
and `ModelAgree`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.Refinement.Cli.ModelLinks.Draft

open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoVerification.E2E (PreKeyBundleFields PreKeyMessageFields UnreachedPqxdhPrimitives PEParams initiateTapeLen wireWhisper
  wirePrekey)
open CryptoVerification.SignalSession (PqParty pqInitInputs pqSendInputs pqRecvInputs
  pqxdhExpectedOutcome pqInitModel pqSendModel pqRecvWhisperModel pqRecvPrekeyModel PqSessionMatches PqxdhPartyInSpecDomain
  Inputs Outcome filesOf)

/-- Process input equivalence up to `filesOf` from the CLI migration design draft. -/
def InputsEquiv (i i' : Inputs) : Prop :=
  i.argv = i'.argv ∧ i.dirs = i'.dirs ∧ i.stdin = i'.stdin ∧
    ∀ p, filesOf i.files p = filesOf i'.files p

/-- Four-clause call relation from the CLI migration design draft. -/
def PqCall (X : UnreachedPqxdhPrimitives) (W : PEParams) (st : PqParty) (i₀ : Inputs) (o₀ : Outcome) : Prop :=
  (∃ (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen), st.session = none ∧
    i₀ = pqInitInputs W st b t ∧ o₀ = pqxdhExpectedOutcome W i₀ (pqInitModel X W st b t)) ∨
  (∃ (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64), m.length < 2 ^ 32 ∧
    i₀ = pqSendInputs W st m r ∧ o₀ = pqxdhExpectedOutcome W i₀ (pqSendModel W st m r.toList)) ∨
  (∃ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 ∧
    i₀ = pqRecvInputs W st (wireWhisper :: c) rc ∧ o₀ = pqxdhExpectedOutcome W i₀ (pqRecvWhisperModel W st c rc)) ∨
  (∃ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 ∧
    (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) ∧
    i₀ = pqRecvInputs W st (wirePrekey :: m.bytes) rc ∧
    o₀ = pqxdhExpectedOutcome W i₀ (pqRecvPrekeyModel X W st m rc))

/-- Five-argument run relation from the CLI migration design draft. -/
def PqModelRel (Xof : ExternInterpretation → UnreachedPqxdhPrimitives) (Wof : ExternInterpretation → PEParams)
    (interp : ExternInterpretation) (i : Inputs) (o : Outcome) : Prop :=
  ∃ st i₀, PqxdhPartyInSpecDomain (Wof interp) st ∧ InputsEquiv i i₀ ∧ PqCall (Xof interp) (Wof interp) st i₀ o

end Symbolic.Proofs.Tests.Refinement.Cli.ModelLinks.Draft

namespace Symbolic.Proofs.Tests.Refinement.Cli.ModelLinks

open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open CryptoVerification.E2E (UnreachedPqxdhPrimitives PEParams)
open CryptoVerification.SignalSession (Inputs Outcome CliRun CliHooks CliSpecPqxdh CliSpecPqxdhNoMatch PqxdhPartyInSpecDomain
  OutcomeMatchesModelExceptPath)

theorem draft_at (Xof : ExternInterpretation → UnreachedPqxdhPrimitives) (Wof : ExternInterpretation → PEParams)
    (interp : ExternInterpretation) (i : Inputs) (o : Outcome) :
    Draft.PqModelRel Xof Wof interp i o ↔
      Draft.PqModelRel (fun _ => Xof interp) (fun _ => Wof interp) interp i o :=
  Iff.rfl

theorem inputsEquiv_draft (i i' : Inputs) :
    InputsEquiv i i' ↔ Draft.InputsEquiv i i' := Iff.rfl

/-- On an input that the draft relation names at `(X, P)` with outcome `o`, every outcome
that meets `PqModelPost` at `P` equals `o`. -/
theorem post_eq_of_draft {interp : ExternInterpretation} {P : PEParams} {X : UnreachedPqxdhPrimitives}
    {i : Inputs} {o o' : Outcome}
    (hd : Draft.PqModelRel (fun _ => X) (fun _ => P) interp i o)
    (hp : PqModelPost interp P i o') : o' = o := by
  obtain ⟨st, i₀, hwf, heq, hc⟩ := hd
  have heq' : InputsEquiv i i₀ := heq
  rcases hc with ⟨b, t, hs0, rfl, rfl⟩ | ⟨m, r, hm, rfl, rfl⟩ | ⟨c, rc, hc, rfl, rfl⟩ |
      ⟨m, rc, hm, hmatch, rfl, rfl⟩
  · exact hp.init X st b t hwf hs0 heq'
  · exact hp.send st m r hwf hm heq'
  · exact hp.recvWhisper st c rc hwf hc heq'
  · exact hp.recvPrekey X st m rc hwf hm hmatch heq'

/-- On an input the draft names, `PqModelRel` lets the run exit only with the draft's outcome. -/
theorem rel_exited_eq_draft {interp : ExternInterpretation} {P : PEParams} {X : UnreachedPqxdhPrimitives}
    {i : Inputs} {o : Outcome} {code : Nat} {out : DY.Libsignal.HwBytes} {files : DirectorySnapshot}
    (hd : Draft.PqModelRel (fun _ => X) (fun _ => P) interp i o)
    (hr : PqModelRel interp P i (some (.exited code out files))) :
    Outcome.exited code out files = o := by
  rcases hr with h | ⟨o', ho, hp⟩
  · cases h
  · cases ho
    exact post_eq_of_draft hd hp

theorem cliTraces_mono {Rel Rel' : Inputs → Option Outcome → Prop}
    (h : ∀ i o, Rel i o → Rel' i o) {interp : ExternInterpretation} {r : ProtocolSetup} {t : CliTurn}
    {τ : List DY.Libsignal.HwEvents.MachineEvent} {calls : List (DY.Participant × Bool)}
    (htr : CliTracesMoves Rel interp r t τ calls) : CliTracesMoves Rel' interp r t τ calls := by
  induction htr with
  | done t => exact .done t
  | clear p _ ih => exact .clear p ih
  | step hleak hnext hin hRel _ ih => exact .step hleak hnext hin (h _ _ hRel) ih
  | stop hleak hnext hin hRel habort => exact .stop hleak hnext hin (h _ _ hRel) habort

/-- Model determinism obligation: on an input that the draft relation names with outcome `o`, `o`
meets every clause naming the same call. -/
def DraftDet (Xof : ExternInterpretation → UnreachedPqxdhPrimitives) (Wof : ExternInterpretation → PEParams) :
    Prop :=
  ∀ interp i o, Draft.PqModelRel Xof Wof interp i o → PqModelPost interp (Wof interp) i o

/-- Nearest well-typed reading of the design draft's target line (`ω := Unit`; `Agree` ties
`Wof interp` to `interp` by `ModelAgree`; `R` lifts the draft relation to `Option Outcome`). -/
def LockedReading (Xof : ExternInterpretation → UnreachedPqxdhPrimitives) (Wof : ExternInterpretation → PEParams) :
    Prop :=
  CompRefinesCliRMoves (ω := Unit) (fun interp _ => ModelAgree interp (Wof interp))
    (fun interp _ i o => ∃ o', o = some o' ∧ Draft.PqModelRel Xof Wof interp i o')
    initDirs

/-- `CompRefinesCliModelMoves` implies `LockedReading Xof Wof` for every `Xof`, `Wof`, under `DraftDet`. -/
theorem locked_of_root (Xof : ExternInterpretation → UnreachedPqxdhPrimitives)
    (Wof : ExternInterpretation → PEParams) (hdet : DraftDet Xof Wof)
    (hroot : CompRefinesCliModelMoves) : LockedReading Xof Wof := by
  intro interp hx _ hA r hr
  obtain ⟨S, hS⟩ := hroot interp hx (Wof interp) hA r hr
  refine ⟨S, fun τ calls htr => hS τ calls (cliTraces_mono ?_ htr)⟩
  rintro i o ⟨o', rfl, hd⟩
  exact Or.inr ⟨o', rfl, hdet interp i o' hd⟩

def X₀ : UnreachedPqxdhPrimitives :=
  ⟨fun _ => [], fun _ _ _ => [], fun _ _ => [], fun _ _ => [], fun _ => ([], []), fun _ => [],
    fun _ _ _ => false⟩

/-- File-system extensionality of a run up to `InputsEquiv` (allowing `none`). -/
def FilesExt (run : CliRun) : Prop :=
  ∀ i i' : Inputs, InputsEquiv i i' → run i = none ∨ run i = run i'

/-- On within-cap inputs (`i.stdin.length ≤ stdinCapBytes` and `send` plaintext
`≤ maxPlaintextBytes`), `PqModelRel` contains every run that reads files through `filesOf` only and
meets `CliSpecPqxdh`, `CliSpecPqxdhNoMatch`, and `NoMatchSessionFile` at `P` for every `X`. -/
theorem rel_of_specs {run : CliRun} {interp : ExternInterpretation} {P : PEParams}
    (hext : FilesExt run) (hspec : ∀ X, CliSpecPqxdh run X P ∧ CliSpecPqxdhNoMatch run X P)
    (hnoMatchSess : ∀ X st x g m rc, PqxdhPartyInSpecDomain P st → st.session = some (x, g) →
      m.inner.length + 2048 < 2 ^ 32 →
      (CryptoVerification.E2E.wirePrekey :: m.bytes).length ≤
        CryptoVerification.SignalSession.stdinCapBytes →
      ¬ CryptoVerification.SignalSession.PqSessionMatches x g m →
      ∀ o, run (CryptoVerification.SignalSession.pqRecvInputs P st
        (CryptoVerification.E2E.wirePrekey :: m.bytes) rc) = some o →
        NoMatchSessionFile X P st x g m rc o)
    (hpkReject : ∀ st body rc, PqxdhPartyInSpecDomain P st → body.length < 2 ^ 32 →
      (CryptoVerification.E2E.wirePrekey :: body).length ≤
        CryptoVerification.SignalSession.stdinCapBytes →
      parsePreKey body = none →
      ∀ o, run (CryptoVerification.SignalSession.pqRecvInputs P st
        (CryptoVerification.E2E.wirePrekey :: body) rc) = some o →
        o = .exited 1 [] (CryptoVerification.SignalSession.filesOf
          (CryptoVerification.SignalSession.pqRecvInputs P st
            (CryptoVerification.E2E.wirePrekey :: body) rc).files))
    (hpkUntyped : ∀ st body q rc, PqxdhPartyInSpecDomain P st → body.length < 2 ^ 32 →
      (CryptoVerification.E2E.wirePrekey :: body).length ≤
        CryptoVerification.SignalSession.stdinCapBytes →
      parsePreKey body = some q → preKeyOfBody? body = none →
      (∀ x g, st.session = some (x, g) → ¬ PqFieldsMatch x g q) →
      ∀ o, run (CryptoVerification.SignalSession.pqRecvInputs P st
        (CryptoVerification.E2E.wirePrekey :: body) rc) = some o →
        o = .exited 1 [] (CryptoVerification.SignalSession.filesOf
          (CryptoVerification.SignalSession.pqRecvInputs P st
            (CryptoVerification.E2E.wirePrekey :: body) rc).files))
    (hpkMatching : ∀ st x g body q rc, PqxdhPartyInSpecDomain P st → st.session = some (x, g) →
      body.length < 2 ^ 32 →
      (CryptoVerification.E2E.wirePrekey :: body).length ≤
        CryptoVerification.SignalSession.stdinCapBytes →
      parsePreKey body = some q → PqFieldsMatch x g q →
      ∀ o, run (CryptoVerification.SignalSession.pqRecvInputs P st
        (CryptoVerification.E2E.wirePrekey :: body) rc) = some o →
        o = CryptoVerification.SignalSession.pqxdhExpectedOutcome P
          (CryptoVerification.SignalSession.pqRecvInputs P st
            (CryptoVerification.E2E.wirePrekey :: body) rc)
          (pqRecvMatchingFieldsModel P st x g q rc))
    (hpkParsed : ∀ X st body m rc, PqxdhPartyInSpecDomain P st → body.length < 2 ^ 32 →
      (CryptoVerification.E2E.wirePrekey :: body).length ≤
        CryptoVerification.SignalSession.stdinCapBytes →
      preKeyOfBody? body = some m → m.inner.length + 2048 < 2 ^ 32 →
      (∀ x g, st.session = some (x, g) → CryptoVerification.SignalSession.PqSessionMatches x g m) →
      ∀ o, run (CryptoVerification.SignalSession.pqRecvInputs P st
        (CryptoVerification.E2E.wirePrekey :: body) rc) = some o →
        o = CryptoVerification.SignalSession.pqxdhExpectedOutcome P
          (CryptoVerification.SignalSession.pqRecvInputs P st
            (CryptoVerification.E2E.wirePrekey :: body) rc)
          (CryptoVerification.SignalSession.pqRecvPrekeyModel X P st m rc))
    (hpkParsedNm : ∀ X st x g body m rc, PqxdhPartyInSpecDomain P st → st.session = some (x, g) →
      body.length < 2 ^ 32 →
      (CryptoVerification.E2E.wirePrekey :: body).length ≤
        CryptoVerification.SignalSession.stdinCapBytes →
      preKeyOfBody? body = some m → m.inner.length + 2048 < 2 ^ 32 →
      ¬ CryptoVerification.SignalSession.PqSessionMatches x g m →
      ∀ o, run (CryptoVerification.SignalSession.pqRecvInputs P st
        (CryptoVerification.E2E.wirePrekey :: body) rc) = some o →
        OutcomeMatchesModelExceptPath P (CryptoVerification.SignalSession.pqRecvInputs P st
            (CryptoVerification.E2E.wirePrekey :: body) rc)
          (CryptoVerification.SignalSession.sessionFile (CryptoVerification.SignalSession.partyAddress st.party.other))
          (CryptoVerification.SignalSession.pqRecvPrekeyModel X P { st with session := none } m rc) o ∧
        NoMatchSessionFile X P st x g m rc o)
    (hinitFiles : ∀ X st files b t, PqxdhPartyInSpecDomain P st → st.session = none → BundleFilesFlat files →
      parseBundleFiles (CryptoVerification.SignalSession.filesOf files) =
        some (CryptoVerification.SignalSession.publicBundleOf b) →
      ∀ o, run (pqInitInputsF P st files t) = some o →
        ScrubAgree o (CryptoVerification.SignalSession.pqxdhExpectedOutcome P (pqInitInputsF P st files t)
          (CryptoVerification.SignalSession.pqInitModel X P st b t)))
    (hinitReject : ∀ st files t, PqxdhPartyInSpecDomain P st → st.session = none → BundleFilesFlat files →
      parseBundleFiles (CryptoVerification.SignalSession.filesOf files) = none →
      ∀ o, run (pqInitInputsF P st files t) = some o →
        o = .exited 1 []
          (CryptoVerification.SignalSession.filesOf (pqInitInputsF P st files t).files))
    (i : Inputs)
    (hstdin : i.stdin.length ≤ CryptoVerification.SignalSession.stdinCapBytes)
    (hsendCap : ∀ st m coins,
      InputsEquiv i (CryptoVerification.SignalSession.pqSendInputs P st m coins) →
      m.length ≤ CryptoVerification.SignalSession.maxPlaintextBytes) :
    run i = none ∨ PqModelRel interp P i (run i) := by
  cases hri : run i with
  | none => exact Or.inl rfl
  | some o =>
    refine Or.inr (Or.inr ⟨o, rfl, ?_⟩)
    have key : ∀ i₀, InputsEquiv i i₀ → run i = run i₀ := fun i₀ he =>
      (hext i i₀ he).resolve_left (by rw [hri]; simp)
    have stdin_le {s : List (BitVec 8)} (hs : i.stdin = s) :
        s.length ≤ CryptoVerification.SignalSession.stdinCapBytes := hs ▸ hstdin
    have ite_not {α : Type} {p : Prop} [Decidable p] {a b : α} (hp : ¬ p) :
        (if p then a else b) = b := by
      split
      · next h => exact absurd h hp
      · rfl
    have not_gt_stdin (s : List (BitVec 8)) (hs : i.stdin = s) :
        ¬ s.length > CryptoVerification.SignalSession.stdinCapBytes :=
      Nat.not_lt.mpr (stdin_le hs)
    constructor
    · intro X st b t hwf hs0 he
      have h := ((hspec X).1 st hwf).1 b t hs0
      rw [← key _ he, hri] at h
      exact Option.some.inj h
    · intro st m coins hwf hm he
      have h := ((hspec X₀).1 st hwf).2.1 m coins hm
      have h2 : ¬ m.length > CryptoVerification.SignalSession.maxPlaintextBytes :=
        Nat.not_lt.mpr (hsendCap st m coins he)
      rw [ite_not (not_gt_stdin m he.2.2.1), ite_not h2, ← key _ he, hri] at h
      exact Option.some.inj h
    · intro st body rc hwf hb he
      have h := ((hspec X₀).1 st hwf).2.2.1 body rc hb
      rw [ite_not (not_gt_stdin (CryptoVerification.E2E.wireWhisper :: body) he.2.2.1),
          ← key _ he, hri] at h
      exact Option.some.inj h
    · intro X st m rc hwf hm hmatch he
      have h := ((hspec X).1 st hwf).2.2.2.1 m rc hm hmatch
      rw [ite_not (not_gt_stdin (CryptoVerification.E2E.wirePrekey :: m.bytes) he.2.2.1),
          ← key _ he, hri] at h
      exact Option.some.inj h
    · intro X st x g m rc hwf hs hm hnm he
      have hspecNm := (hspec X).2 st hwf x g hs m rc hm hnm
      rw [ite_not (not_gt_stdin (CryptoVerification.E2E.wirePrekey :: m.bytes) he.2.2.1)] at hspecNm
      obtain ⟨o₁, h₁, hobs⟩ := hspecNm
      rw [← key _ he, hri] at h₁
      cases h₁
      exact hobs
    · intro st c rc hwf hc h1 h2 he
      have h := ((hspec X₀).1 st hwf).2.2.2.2 c rc hc h1 h2
      rw [ite_not (not_gt_stdin c he.2.2.1), ← key _ he, hri] at h
      exact Option.some.inj h
    · intro X st x g m rc hwf hs hm hnm he
      exact hnoMatchSess X st x g m rc hwf hs hm (stdin_le he.2.2.1) hnm o
        ((key _ he).symm.trans hri)
    · intro st body rc hwf hlen hp he
      exact hpkReject st body rc hwf hlen (stdin_le he.2.2.1) hp o
        ((key _ he).symm.trans hri)
    · intro st body q rc hwf hlen hp hpk hnm he
      exact hpkUntyped st body q rc hwf hlen (stdin_le he.2.2.1) hp hpk hnm o
        ((key _ he).symm.trans hri)
    · intro st x g body q rc hwf hs hlen hp hfm he
      exact hpkMatching st x g body q rc hwf hs hlen (stdin_le he.2.2.1) hp hfm o
        ((key _ he).symm.trans hri)
    · intro X st body m rc hwf hlen hpk hin hsm he
      exact hpkParsed X st body m rc hwf hlen (stdin_le he.2.2.1) hpk hin hsm o
        ((key _ he).symm.trans hri)
    · intro X st x g body m rc hwf hs hlen hpk hin hnm he
      exact hpkParsedNm X st x g body m rc hwf hs hlen (stdin_le he.2.2.1) hpk hin hnm o
        ((key _ he).symm.trans hri)
    · intro X st files b t hwf hs hflat hparse he
      exact hinitFiles X st files b t hwf hs hflat hparse o ((key _ he).symm.trans hri)
    · intro st files t hwf hs hflat hparse he
      exact hinitReject st files t hwf hs hflat hparse o ((key _ he).symm.trans hri)

theorem rel_nonempty (interp : ExternInterpretation) (P : PEParams) (i : Inputs) :
    PqModelRel interp P i (some .aborted) := Or.inl rfl

theorem hooksAgree_iff_modelAgree (interp : ExternInterpretation) (W : CliHooks) :
    HooksMatchInterpretation interp W ↔ ModelAgree interp ⟨W.C, W.Q⟩ := Iff.rfl

/-- Joint satisfiability of `ExternInterpretationTotalOnUsedSymbols`, `ExternContractsHoldCli`,
and `ModelAgree`. -/
theorem modelAgree_satisfiable :
    ∃ (interp : ExternInterpretation) (P : PEParams),
      ExternInterpretationTotalOnUsedSymbols interp ∧ ExternContractsHoldCli interp ∧ ModelAgree interp P := by
  obtain ⟨interp, W, ht, hx, hA⟩ :=
    Symbolic.Proofs.Tests.Refinement.Cli.comp_externsSatisfiable_cli_test
  exact ⟨interp, ⟨W.C, W.Q⟩, ht, hx, (hooksAgree_iff_modelAgree interp W).1 hA⟩

#print axioms DY.Libsignal.Composed.Refinement.Cli.ModelAgree
#print axioms DY.Libsignal.Composed.Refinement.Cli.InputsEquiv
#print axioms DY.Libsignal.Composed.Refinement.Cli.PqModelPost
#print axioms DY.Libsignal.Composed.Refinement.Cli.PqModelRel
#print axioms DY.Libsignal.Composed.Refinement.Cli.CompRefinesCliModelMoves
#print axioms draft_at
#print axioms inputsEquiv_draft
#print axioms post_eq_of_draft
#print axioms rel_exited_eq_draft
#print axioms cliTraces_mono
#print axioms locked_of_root
#print axioms rel_of_specs
#print axioms rel_nonempty
#print axioms hooksAgree_iff_modelAgree
#print axioms modelAgree_satisfiable

end Symbolic.Proofs.Tests.Refinement.Cli.ModelLinks

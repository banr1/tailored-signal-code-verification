/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Refinement.Composed.Cli.Model

/-!
# Run-Relation and Turn Transfer for `CompRefinesCliR`

Defines relational (`TraceSim`) and unary (`TraceInv`) turn-simulation structures over
`CliTraces` and proves witness-transfer combinators (`compRefinesCliR_of_sim`,
`compRefinesCliR_of_inv`) together with one-time pre-key and session path disjointness
(`samePath_oneTimePreKeyFile_sessionPathOf`, `opkUsed_eq_of_bob_agree`).
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Refinement.Cli

open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (CliEvent)
open DY.Libsignal.Composed.Refinement
open CryptoVerification.SignalSession (Inputs Outcome filesOf fsView stdioPaths oneTimePreKeyFile)

/-! ## Process input extensionality -/

theorem InputsEquiv.refl (i : Inputs) : InputsEquiv i i := ⟨rfl, rfl, rfl, fun _ => rfl⟩
theorem InputsEquiv.symm {i i' : Inputs} (h : InputsEquiv i i') : InputsEquiv i' i :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, fun p => (h.2.2.2 p).symm⟩
theorem InputsEquiv.trans {i₁ i₂ i₃ : Inputs} (h₁ : InputsEquiv i₁ i₂) (h₂ : InputsEquiv i₂ i₃) :
    InputsEquiv i₁ i₃ :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.1.trans h₂.2.2.1,
    fun p => (h₁.2.2.2 p).trans (h₂.2.2.2 p)⟩

theorem filesOf_eq_none_of_mem_stdioPaths (files : List (String × HwBytes)) {p : String}
    (hp : p ∈ stdioPaths) : filesOf files p = none := by
  unfold filesOf fsView; split <;> [rfl; exact absurd (List.mem_map.mpr ⟨p, hp, rfl⟩) ‹_›]

/-! ## Relational turn simulation and trace transfer -/

/-- Relational turn simulation `Sim : CliTurn → CliTurn → Prop` from `Rel` to `Rel'`. -/
structure TraceSim (Rel Rel' : Inputs → Option Outcome → Prop) (interp : ExternInterpretation)
    (r : ProtocolSetup) (Sim : CliTurn → CliTurn → Prop) : Prop where
  leaks : ∀ t t' p k, Sim t t' → KeyInDir r t p k → KeyInDir r t' p k
  clear : ∀ t t' p, Sim t t' → Sim (t.clearSession r p) (t'.clearSession r p)
  step : ∀ t t' c i code out files, Sim t t' → ValidCall interp r t c →
    InputsFor c (t.dirs c.party) i → Rel i (some (.exited code out files)) →
    ∃ i' files', ValidCall interp r t' c ∧ InputsFor c (t'.dirs c.party) i' ∧
      Rel' i' (some (.exited code out files')) ∧
      Sim (t.after r c code out files) (t'.after r c code out files')
  stop : ∀ t t' c i o, Sim t t' → ValidCall interp r t c →
    InputsFor c (t.dirs c.party) i → Rel i o → o = some .aborted →
    ∃ i' o', ValidCall interp r t' c ∧ InputsFor c (t'.dirs c.party) i' ∧
      Rel' i' o' ∧ o' = some .aborted

/-- Transfers `CliTraces` along `TraceSim` with identical event trace `evs`. -/
theorem traces_transfer_sim {Rel Rel' : Inputs → Option Outcome → Prop}
    {interp : ExternInterpretation} {r : ProtocolSetup} {Sim : CliTurn → CliTurn → Prop}
    (hSim : TraceSim Rel Rel' interp r Sim) {t t' : CliTurn} {evs : List CliEvent}
    (hst : Sim t t') (htr : CliTraces Rel interp r t evs) :
    CliTraces Rel' interp r t' evs := by
  induction htr generalizing t' with
  | done _ => exact .done t'
  | clear p _ ih => exact .clear p (ih (hSim.clear _ _ p hst))
  | breakInvert hbi _ ih => exact .breakInvert hbi (ih hst)
  | step hleak hnext hin hRel _ ih =>
    obtain ⟨i', files', hnext', hin', hRel', hst'⟩ := hSim.step _ _ _ _ _ _ _ hst hnext hin hRel
    exact .step (fun e he => let ⟨p, k, hk, heq⟩ := hleak e he; ⟨p, k, hSim.leaks _ _ p k hst hk, heq⟩)
      hnext' hin' hRel' (ih hst')
  | stop hleak hnext hin hRel habort =>
    obtain ⟨i', o', hnext', hin', hRel', habort'⟩ := hSim.stop _ _ _ _ _ hst hnext hin hRel habort
    exact .stop (fun e he => let ⟨p, k, hk, heq⟩ := hleak e he; ⟨p, k, hSim.leaks _ _ p k hst hk, heq⟩)
      hnext' hin' hRel' habort'

section WitnessTransfer
variable {ω₁ ω₂ : Type} {Agree₁ : ExternInterpretation → ω₁ → Prop}
  {Agree₂ : ExternInterpretation → ω₂ → Prop}
  {R₁ : ExternInterpretation → ω₁ → Inputs → Option Outcome → Prop}
  {R₂ : ExternInterpretation → ω₂ → Inputs → Option Outcome → Prop}

/-- Transfers `CompRefinesCliR` across witness types `ω₁` and `ω₂` via `TraceSim`. -/
theorem compRefinesCliR_of_sim {dirs₁ dirs₂ : ExternInterpretation → ProtocolSetup → Participant → DirectorySnapshot}
    (hsim : ∀ interp W₁, ExternContractsHoldCli interp → Agree₁ interp W₁ → ∃ W₂,
      Agree₂ interp W₂ ∧ ∀ r, ProtocolSetupWF r → ∃ Sim,
        Sim (CliTurn.init (dirs₁ interp r)) (CliTurn.init (dirs₂ interp r)) ∧
        TraceSim (R₁ interp W₁) (R₂ interp W₂) interp r Sim)
    (hmodel : CompRefinesCliR Agree₂ R₂ dirs₂) : CompRefinesCliR Agree₁ R₁ dirs₁ :=
  fun interp hx W₁ hW₁ r hr =>
    let ⟨W₂, hW₂, hrSim⟩ := hsim interp W₁ hx hW₁
    let ⟨_, hinit, hSim⟩ := hrSim r hr
    let ⟨S, hS⟩ := hmodel interp hx W₂ hW₂ r hr
    ⟨S, fun evs hevs => hS evs (traces_transfer_sim hSim hinit hevs)⟩

/-! ## Unary turn invariant -/

/-- Unary turn invariant `I` for transferring `CliTraces` from `Rel` to `Rel'`. -/
structure TraceInv (Rel Rel' : Inputs → Option Outcome → Prop) (interp : ExternInterpretation)
    (r : ProtocolSetup) (I : CliTurn → Prop) : Prop where
  clear : ∀ t p, I t → I (t.clearSession r p)
  step : ∀ t c i code out files, I t → ValidCall interp r t c →
    InputsFor c (t.dirs c.party) i → Rel i (some (.exited code out files)) →
    Rel' i (some (.exited code out files)) ∧ I (t.after r c code out files)
  stop : ∀ t c i o, I t → ValidCall interp r t c → InputsFor c (t.dirs c.party) i →
    Rel i o → o = some .aborted →
    ∃ o', Rel' i o' ∧ o' = some .aborted

theorem TraceInv.toTraceSim {Rel Rel' : Inputs → Option Outcome → Prop}
    {interp : ExternInterpretation} {r : ProtocolSetup} {I : CliTurn → Prop}
    (hI : TraceInv Rel Rel' interp r I) :
    TraceSim Rel Rel' interp r (fun t t' => t = t' ∧ I t) :=
  ⟨fun _ _ _ _ ⟨heq, _⟩ hk => heq ▸ hk, fun _ _ p ⟨rfl, ht⟩ => ⟨rfl, hI.clear _ p ht⟩,
   fun _ _ c i code out files ⟨rfl, ht⟩ hn hi hr =>
     let ⟨hr', ht'⟩ := hI.step _ c i code out files ht hn hi hr; ⟨i, files, hn, hi, hr', rfl, ht'⟩,
   fun _ _ c i o ⟨rfl, ht⟩ hn hi hr ho =>
     let ⟨o', hr', ho'⟩ := hI.stop _ c i o ht hn hi hr ho; ⟨i, o', hn, hi, hr', ho'⟩⟩

theorem compRefinesCliR_of_inv {dirs : ExternInterpretation → ProtocolSetup → Participant → DirectorySnapshot}
    (hinv : ∀ interp W₁, ExternContractsHoldCli interp → Agree₁ interp W₁ → ∃ W₂,
      Agree₂ interp W₂ ∧ ∀ r, ProtocolSetupWF r →
        ∃ I, I (CliTurn.init (dirs interp r)) ∧ TraceInv (R₁ interp W₁) (R₂ interp W₂) interp r I)
    (hmodel : CompRefinesCliR Agree₂ R₂ dirs) : CompRefinesCliR Agree₁ R₁ dirs :=
  compRefinesCliR_of_sim (fun interp W₁ hx hW₁ => let ⟨W₂, hW₂, hr⟩ := hinv interp W₁ hx hW₁
    ⟨W₂, hW₂, fun r hwf => let ⟨_, h0, hI⟩ := hr r hwf; ⟨_, ⟨rfl, h0⟩, hI.toTraceSim⟩⟩) hmodel
end WitnessTransfer

/-! ## One-time pre-key and session path disjointness -/

set_option linter.auxLemma false in
private theorem splitSlash_go_cons_ne_transfer {c : Char} (cur rest : List Char) (hc : c ≠ '/') :
    Arm64.splitSlash.go cur (c :: rest) = Arm64.splitSlash.go (c :: cur) rest := by
  delta Arm64.splitSlash.go Arm64.splitSlash.go._f Arm64.splitSlash.go.match_1
  dsimp only [List.brecOn, List.brecOn.go, List.casesOn]
  split_ifs with h
  · exact absurd h hc
  · rfl

private theorem splitSlash_go_append_slash :
    ∀ (pref cur cs : List Char), '/' ∉ pref → Arm64.splitSlash.go cur (pref ++ '/' :: cs) =
      String.ofList (cur.reverse ++ pref) :: Arm64.splitSlash.go [] cs
  | [], cur, cs, _ => by rw [List.nil_append, List.append_nil]; rfl
  | c :: pref, cur, cs, h => by
    have hc : c ≠ '/' := fun heq => h (heq ▸ List.mem_cons_self ..)
    have h' : '/' ∉ pref := fun hm => h (List.mem_cons_of_mem _ hm)
    rw [List.cons_append, splitSlash_go_cons_ne_transfer cur _ hc,
        splitSlash_go_append_slash pref (c :: cur) cs h']
    simp [List.reverse_cons, List.append_assoc]

private theorem normalizePath_head_slash (dir rest : String)
    (hno : '/' ∉ dir.toList) (hne : (!dir.isEmpty && dir != ".") = true) :
    (Arm64.normalizePath ((dir ++ "/") ++ rest)).head? = some dir := by
  have hsplit : Arm64.splitSlash ((dir ++ "/") ++ rest) = dir :: Arm64.splitSlash.go [] rest.toList := by
    unfold Arm64.splitSlash
    simpa [String.toList_append] using splitSlash_go_append_slash dir.toList [] rest.toList hno
  simp [Arm64.normalizePath, hsplit, hne]

theorem samePath_oneTimePreKeyFile_sessionPathOf (r : ProtocolSetup) (id : BitVec 32) (p : Participant) :
    SamePath (oneTimePreKeyFile id) (sessionPathOf r p) = false := by
  unfold SamePath; apply beq_eq_false_iff_ne.mpr; intro heq
  have h1 := normalizePath_head_slash "one-time-pre-keys" (toString id.toNat) (by decide) (by decide)
  have h2 := normalizePath_head_slash "sessions" (peerOf r p).text (by decide) (by decide)
  change (Arm64.normalizePath (oneTimePreKeyFile id)).head? = _ at h1
  change (Arm64.normalizePath (sessionPathOf r p)).head? = _ at h2
  rw [heq, h2] at h1; exact absurd (Option.some.inj h1) (by decide)

theorem opkUsed_eq_of_bob_agree {r : ProtocolSetup} {t t' : CliTurn}
    (hbob : ∀ q, SamePath q (sessionPathOf r r.bob) = false → t.dirs r.bob q = t'.dirs r.bob q) :
    t.opkUsed r = t'.opkUsed r := by
  simp only [CliTurn.opkUsed,
    hbob (oneTimePreKeyFile r.opkId) (samePath_oneTimePreKeyFile_sessionPathOf r r.opkId r.bob)]

#print axioms traces_transfer_sim
#print axioms compRefinesCliR_of_sim
#print axioms compRefinesCliR_of_inv
#print axioms samePath_oneTimePreKeyFile_sessionPathOf
#print axioms opkUsed_eq_of_bob_agree
end DY.Libsignal.Composed.Refinement.Cli

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.RefinementPreservation
public import Symbolic.Proofs.Refinement.Composed.Cli.Model
import Symbolic.Proofs.Swarm.UA.BreakInvert
import Symbolic.Proofs.Swarm.UA.HwKnows
import Symbolic.Proofs.TopLevelHelpers.Composed.FS
import Symbolic.Proofs.TopLevelHelpers.Composed.Handshake
import Symbolic.Proofs.TopLevelHelpers.Composed.PCS

/-!
# CLI Model Refinement and Security Preservation over CLI Events

Establishes top-level CLI refinement preservation (`comp_refinement_preservation_cli`,
`signalSessionSecureFor_of_refines`) and exports the whole-protocol CLI model refinement theorem
(`comp_refines_cli_model`). Reachability and Dolev-Yao attacker knowledge on explained model traces
lift the ten symbolic security queries (`AllModelSecurityQueriesHold`) to hardware CLI event traces.
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Refinement.Cli

open DY DY.Comparse
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (CliEvent)
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Security (SignalSessionSecureFor)
open CryptoVerification.SignalSession (Inputs Outcome)

theorem runSteps_reachable : ∀ (ss : List Step) (tr : ExecTrace),
    tr.Reachable reachability → StepsWF ss tr → (runSteps ss tr).Reachable reachability
  | [], _, h, _ => h
  | s :: ss, tr, h, ⟨hpre, _, hwf⟩ =>
    runSteps_reachable ss (s.next tr) (Trace.Reachable.Step s.toInput hpre h) hwf

theorem runTrace_reachable_of_explains {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {vis : List VisEntry} {evs : List CliEvent}
    (h : Explains interp r S g ss vis evs) : (runTrace r ss).Reachable reachability :=
  runSteps_reachable ss (setupTrace r) h.2.2.1.2.1 h.2.2.1.2.2.1

/-- Hardware attacker knowledge under an explanation implies Dolev-Yao attacker knowledge on the
explained model trace. -/
theorem hwAttackerKnows_implies_attackerKnows_of_explains {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {vis : List VisEntry}
    {evs : List CliEvent} (h : Explains interp r S g ss vis evs) {t : DY.Bytes}
    (ht : HwAttackerKnows r vis t) : t.AttackerKnows (runTrace r ss) :=
  Symbolic.Proofs.Swarm.UA.HwKnows.hwAttackerKnows_implies_attackerKnows_of_explains' h ht

private theorem trKeyKnown_mono {K₁ K₂ : DY.Bytes → Prop}
    (hk : ∀ t, K₁ t → K₂ t) {mk pqSalt : DY.Bytes}
    (h : TripleRatchet.Cheval.TRKeyKnown K₁ mk pqSalt) :
    TripleRatchet.Cheval.TRKeyKnown K₂ mk pqSalt :=
  h.imp (hk _) (hk _)

/-- Lifts `Security.AllModelSecurityQueriesHold` from reachable model traces to hardware CLI event
traces via `Explains`. -/
theorem asmSecure_of_model_theorems
    (hM : Security.AllModelSecurityQueriesHold)
    (interp : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (evs : List CliEvent) :
    AllSecurityQueriesHoldOnHwTrace interp r S evs := by
  rcases hM with ⟨hFS, hPCS, hRS, hIS, hAu, hPA, hHFS, hKCI, hSI, hHNDL⟩
  intro g ss vis hE
  have hreach : (runTrace r ss).Reachable reachability := runTrace_reachable_of_explains hE
  have hk : ∀ b, HwAttackerKnows r vis b → b.AttackerKnows (runTrace r ss) :=
    fun _ => hwAttackerKnows_implies_attackerKnows_of_explains hE
  exact ⟨
    fun mk pqSalt hmk hkn => hFS _ hreach mk pqSalt hmk (trKeyKnown_mono hk hkn),
    fun mk pqSalt rk_prev ownSk peerSk hmk hkn hown hpeer hder =>
      hPCS _ hreach mk pqSalt rk_prev ownSk peerSk hmk
        (trKeyKnown_mono hk hkn) hown hpeer hder,
    fun a b ikA ikB spk pqpk opk ek ct keys i hd k hblk hkn =>
      hRS _ hreach a b ikA ikB spk pqpk opk ek ct keys i hd k hblk (hk _ hkn),
    fun b a ikB ikA spk pqpk opk ek ct keys i hd k hblk hkn =>
      hIS _ hreach b a ikB ikA spk pqpk opk ek ct keys i hd k hblk (hk _ hkn),
    hAu _ hreach, hPA _ hreach,
    fun a b ikA ikB spk pqpk opk keys i hd hp k hblk hnexp hkn =>
      hHFS _ hreach a b ikA ikB spk pqpk opk keys i hd hp k hblk hnexp (hk _ hkn),
    hKCI _ hreach,
    fun a b ikA ikB spk pqpk opk keys i hd hp k hblk hnexp hkn =>
      hSI _ hreach a b ikA ikB spk pqpk opk keys i hd hp k hblk hnexp (hk _ hkn),
    fun a b ikA ikB spk pqpk opk keys i hd hp k hblk hnexp hkn =>
      hHNDL _ hreach a b ikA ikB spk pqpk opk keys i hd hp k hblk hnexp (hk _ hkn)⟩

/-- Transfers all ten symbolic security properties along `CompRefinesCli` to hardware CLI runs
starting from provisioned directories (`initDirs`). -/
theorem comp_refinement_preservation_cli {ω : Type}
    (Agree : ExternInterpretation → ω → Prop)
    (R : ExternInterpretation → ω → Inputs → Option Outcome → Prop) :
    CompRefinementPreservationCli Agree R := by
  intro hM hR interp hext W hW r hwf
  obtain ⟨S, hS⟩ := hR interp hext W hW r hwf
  have hSec : ∀ evs', AllSecurityQueriesHoldOnHwTrace interp r S evs' :=
    asmSecure_of_model_theorems hM interp r S
  exact ⟨S, fun evs htr hg _hcf => (hS evs htr hg).imp
    (fun hE => ⟨hE, hSec evs⟩)
    (fun ⟨evs₁, ev, evs₂, g, ss, vis, heq, hE, hN⟩ =>
      ⟨evs₁, ev, evs₂, heq, ⟨g, ss, vis, hE, hN⟩, hSec evs₁⟩)⟩

/-- Instantiates `comp_refinement_preservation_cli` with the ten proved symbolic security theorems. -/
theorem signalSessionSecureFor_of_refines {ω : Type}
    {Agree : ExternInterpretation → ω → Prop}
    {R : ExternInterpretation → ω → Inputs → Option Outcome → Prop}
    (hR : CompRefinesCli Agree R) : SignalSessionSecureFor Agree R :=
  comp_refinement_preservation_cli Agree R
    ⟨Symbolic.Proofs.TopLevelHelpers.Composed.FS.forward_secrecy,
     Symbolic.Proofs.TopLevelHelpers.Composed.PCS.post_compromise_security,
     Symbolic.Proofs.TopLevelHelpers.Composed.Handshake.alice_initiator_secrecy,
     Symbolic.Proofs.TopLevelHelpers.Composed.Handshake.bob_responder_secrecy,
     Symbolic.Proofs.TopLevelHelpers.Composed.Handshake.authentication,
     Symbolic.Proofs.TopLevelHelpers.Composed.Handshake.peer_authentication,
     Symbolic.Proofs.TopLevelHelpers.Composed.Handshake.handshake_forward_secrecy,
     Symbolic.Proofs.TopLevelHelpers.Composed.Handshake.kci_resistance,
     Symbolic.Proofs.TopLevelHelpers.Composed.Handshake.session_independence,
     Symbolic.Proofs.TopLevelHelpers.Composed.Handshake.hndl_resistance⟩ hR

/-- Whole-protocol CLI model refinement over CLI events: every guarded CLI trace from provisioned
directories is explained by a model run (`Explains`) or satisfies `CollisionAfterExplainedPrefix`. -/
theorem comp_refines_cli_model : CompRefinesCliModel :=
  Symbolic.Proofs.Swarm.UA.BreakInvert.comp_refines_cli_model_ua_b

end DY.Libsignal.Composed.Refinement.Cli

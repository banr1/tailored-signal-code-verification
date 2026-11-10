/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.UA.BI.RAB.Defs
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.Steps
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.UA.BI.InvertDH
import Symbolic.Proofs.Swarm.UA.BI.InvertKEM
import Symbolic.Proofs.Swarm.UA.BI.RAB.Base
import Symbolic.Proofs.Swarm.UA.BI.Step
import Symbolic.Proofs.Swarm.UA.Base
import Symbolic.Proofs.Swarm.UA.BI.G.PendingPreKey

/-!
# Break and Invert Environment Steps

Proves `uab_env : UAEnvSpecB`, showing that a guarded break or invert environment event preserves
the trace invariant `UAInvB`. A break or invert event flattens to the empty retired event list,
preserves `AliceRecordPendingInSession`, and extends any clean explanation by decrypt-free steps.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.BI.RAB.Env

open scoped _root_.DY.Libsignal.Composed _root_.DY.Libsignal.Composed.Refinement
cref_hide_foreign_instances

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant ExecTrace)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (MachineEvent RunEvent EnvEvent CliEvent)
open _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed.Refinement.Cli
open _root_.DY.Libsignal.Composed.Refinement.Cli.ParD3 (PqTurnSim1A)
open CryptoVerification.E2E (PEParams)
open Symbolic.Swarm.CREF (compSemOf)
open Symbolic.Swarm.CREF.Cli (interpOfParams pubBytes_interpOfParams
  externContractsHoldCli_interpOfParams)
open Symbolic.Swarm.Coinsplit.Lift (CliLiveAtCli)
open Symbolic.Proofs.Swarm.UA.Defs (AliceRecordPendingInSession flatEvent flatEvents)
open Symbolic.Proofs.Swarm.UA.Base (flatEvents_append)
open Symbolic.Proofs.Swarm.UA.BI.G.PendingPreKey (aliceRecordPendingInSession_of_explains_append)
open Symbolic.Proofs.Swarm.UA.BI.Step (preCond_breakDH preCond_breakKEM explains_snoc_env_silent)
open Symbolic.Proofs.Swarm.UA.BI.InvertDH (explains_snoc_invertDH_step)
open Symbolic.Proofs.Swarm.UA.BI.InvertKEM (explains_snoc_invertKEM_step)
open Symbolic.Proofs.Swarm.UA.BI.RAB.Defs (UAInvB UAEnvSpecB)
open Symbolic.Proofs.Swarm.UA.BI.RAB.Base (collisionAtCli_append readCollisionCli_append)

theorem flatEvent_env_of_isBreakInvert {e : EnvEvent} (hbi : e.IsBreakInvert) :
    flatEvent (.env e) = [] := by
  cases e with
  | leak _ _ => exact (hbi : False).elim
  | registerCorrupt _ _ => exact (hbi : False).elim
  | _ => rfl

theorem invertsGuarded_interpOfParams {interp : ExternInterpretation} {P : PEParams}
    {r : ProtocolSetup} {evs : List CliEvent} (h : InvertsGuarded interp r evs) :
    InvertsGuarded (interpOfParams interp P) r evs := by
  intro pre post e heq
  have h' := h pre post e heq
  cases e with
  | invertDH pk sk =>
    obtain ⟨h1, h2, h3⟩ := h'
    exact ⟨h1, h2, by rw [pubBytes_interpOfParams]; exact h3⟩
  | invertKEM pk sk => exact h'
  | _ => trivial

theorem aliceRecordPendingInSession_env {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {t_clean : CliTurn} {evs : List CliEvent} {e : EnvEvent} (hr : ProtocolSetupWF r)
    (hap : ∀ g ss vis, Explains interp' r S g ss vis evs → ¬ ReadCollisionCli interp' r S g ss evs →
      AliceRecordPendingInSession interp' r S g (runTrace r ss) (t_clean.leakRecords r) (activeBundleIds evs)) :
    ∀ g ss vis, Explains interp' r S g ss vis (evs ++ [.env e]) →
      ¬ ReadCollisionCli interp' r S g ss (evs ++ [.env e]) →
      AliceRecordPendingInSession interp' r S g (runTrace r ss) (t_clean.leakRecords r) (activeBundleIds (evs ++ [.env e])) := by
  intro g ss vis hex hnrc
  exact aliceRecordPendingInSession_of_explains_append hr hex hnrc
    (fun _ hmem => by simp at hmem) rfl (fun ss₁ vis₁ => hap g ss₁ vis₁)

/-- Extends an explanation across a guarded break or invert event using decrypt-free steps. -/
theorem explains_snoc_breakInvert_step {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {vis : List VisEntry} {evs : List CliEvent} {e : EnvEvent}
    (hext : ExternContractsHoldCli interp) (hr : ProtocolSetupWF r) (hbi : e.IsBreakInvert)
    (h : Explains interp r S g ss vis evs) (hg : InvertsGuarded interp r (evs ++ [.env e])) :
    ∃ (ext : List Step) (v : List VisEntry), (∀ x ∈ ext, x.decryptMsgIdx? = none) ∧
      Explains interp r S g (ss ++ ext) (vis ++ v) (evs ++ [.env e]) := by
  cases e with
  | leak _ _ => exact (hbi : False).elim
  | registerCorrupt _ _ => exact (hbi : False).elim
  | breakDH =>
    refine ⟨[.breakDH], [], fun x hx => by rw [List.mem_singleton.mp hx]; rfl, ?_⟩
    rw [List.append_nil]
    exact explains_snoc_env_silent h (preCond_breakDH _) trivial rfl ⟨rfl, rfl⟩
  | breakKEM =>
    refine ⟨[.breakKEM], [], fun x hx => by rw [List.mem_singleton.mp hx]; rfl, ?_⟩
    rw [List.append_nil]
    exact explains_snoc_env_silent h (preCond_breakKEM _) trivial rfl ⟨rfl, rfl⟩
  | invertDH pk sk => exact explains_snoc_invertDH_step hext hr h hg
  | invertKEM pk sk => exact explains_snoc_invertKEM_step hext hr h hg

theorem not_readCollisionCli_append_env {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss ext : List Step} {evs : List CliEvent} {e : EnvEvent}
    (hnrc : ¬ ReadCollisionCli interp r S g ss evs)
    (hext : ∀ x ∈ ext, x.decryptMsgIdx? = none) :
    ¬ ReadCollisionCli interp r S g (ss ++ ext) (evs ++ [.env e]) := by
  rintro ⟨evs₁, ev, evs₂, ss₁, ss₂, m, vis₁, msgIdx, out, b, t_msg,
    hevs, hss, hcmd, hexit, hbody, hm₁, hm_dec, hmsg, hcol⟩
  have hm_ext : m ∉ ext := fun hm => by rw [hext m hm] at hm_dec; cases hm_dec
  obtain ⟨evs₂', hevs'⟩ : ∃ evs₂', evs = evs₁ ++ .run ev :: evs₂' := by
    rcases List.append_eq_append_iff.mp hevs with ⟨a', h1, h2⟩ | ⟨c', h1, h2⟩
    ·
      rcases a' with _ | ⟨a, as⟩
      · simp only [List.nil_append] at h2
        injection h2 with h2a
        cases h2a
      · simp only [List.cons_append] at h2
        injection h2 with _ h2b
        have := congrArg List.length h2b
        simp at this
    · rcases c' with _ | ⟨c, cs⟩
      · simp only [List.nil_append, List.append_nil] at h1 h2
        injection h2 with h2a
        cases h2a
      · simp only [List.cons_append] at h2
        injection h2 with hc hcs
        subst hc
        exact ⟨cs, by rw [h1]⟩
  obtain ⟨ss₂', hss'⟩ : ∃ ss₂', ss = ss₁ ++ m :: ss₂' := by
    rcases List.append_eq_append_iff.mp hss with ⟨a', h1, h2⟩ | ⟨c', h1, h2⟩
    · exact absurd (by rw [h2]; simp) hm_ext
    · rcases c' with _ | ⟨c, cs⟩
      · simp only [List.nil_append] at h2
        exact absurd (by rw [← h2]; simp) hm_ext
      · simp only [List.cons_append] at h2
        injection h2 with hc hcs
        subst hc
        exact ⟨cs, by rw [h1]⟩
  exact hnrc ⟨evs₁, ev, evs₂', ss₁, ss₂', m, vis₁, msgIdx, out, b, t_msg,
    hevs', hss', hcmd, hexit, hbody, hm₁, hm_dec, hmsg, hcol⟩

/-- A guarded break or invert environment event preserves `UAInvB`. -/
theorem uab_env : UAEnvSpecB := by
  intro interp P r hext _hagree hr t t_clean accepted evs e who ok _hsim hbi hg _hfits hinv
  rcases hinv with hcol | ⟨hlive, hap, g₀, ss₀, vis₀, hex₀, hnrc₀⟩
  · exact Or.inl (collisionAtCli_append _ hcol)
  · refine Or.inr ⟨?_, aliceRecordPendingInSession_env hr hap, ?_⟩
    · rw [flatEvents_append]
      simpa only [flatEvents, List.flatMap_cons, List.flatMap_nil, flatEvent_env_of_isBreakInvert hbi,
        List.append_nil] using hlive
    · obtain ⟨ext, v, hdec, hex⟩ :=
        explains_snoc_breakInvert_step (externContractsHoldCli_interpOfParams P hext) hr hbi hex₀
          (invertsGuarded_interpOfParams hg)
      exact ⟨g₀, ss₀ ++ ext, vis₀ ++ v, hex, not_readCollisionCli_append_env hnrc₀ hdec⟩

end Symbolic.Proofs.Swarm.UA.BI.RAB.Env

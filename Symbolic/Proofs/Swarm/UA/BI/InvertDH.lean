/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.EquationalTheory.DiffieHellman
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.ProtocolEvent
public import Symbolic.Specifications.Refinement.Statement
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.Steps
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RatchetDHRkSwapStepTRPureA
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.RecvRep
import Symbolic.Proofs.Swarm.UA.PendingPreKey
import Symbolic.Proofs.Swarm.UA.SlotInitTransfer
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# Diffie-Hellman Inversion Step

Proves `explains_snoc_invertDH` and `explains_snoc_invertDH_step`: a guarded `invertDH pk sk`
environment event extends any `Explains` witness of `evs` by appending `Step.network (dhPk (litOf sk))`
and `Step.invertDH`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.BI.InvertDH

open scoped _root_.DY.Libsignal.Composed _root_.DY.Libsignal.Composed.Refinement
cref_hide_foreign_instances

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant ExecTrace Trace Traceful ExecTraceTypes)
open _root_.DY.DiffieHellman (dhPk)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (RunEvent EnvEvent CliEvent)
open _root_.DY.Libsignal.Composed (reachability)
open _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed.Refinement.Cli
open Symbolic.Proofs.Swarm.UA.SlotInitTransfer (stepsWF_append_iff stepsStateFaithful_append_noLoad)
open Symbolic.Proofs.Swarm.UA.PendingPreKey (stepsWF_le)

private theorem stepIn_preCond_of (c : _root_.DY.ReachabilityConfig)
    [inst : _root_.DY.ReachabilityConfig.HasStep c reachability]
    (x : c.Input) (tr : ExecTrace) (h : c.PreCond x tr) :
    reachability.PreCond (stepIn c x) tr :=
  (inst.pf_pre x tr).mp h

private theorem stepIn_next_eq (c : _root_.DY.ReachabilityConfig)
    [inst : _root_.DY.ReachabilityConfig.HasStep c reachability]
    (x : c.Input) (tr : ExecTrace) :
    ((reachability.step (stepIn c x)).2.run tr).2.val = ((c.step x).2.run tr).2.val :=
  congrArg (fun s => (s.2.run tr).2.val) (inst.pf_step x).symm

private theorem stepIn_ok_eq (c : _root_.DY.ReachabilityConfig)
    [inst : _root_.DY.ReachabilityConfig.HasStep c reachability]
    (x : c.Input) (tr : ExecTrace) :
    ((reachability.step (stepIn c x)).2.run tr).1.isSome = ((c.step x).2.run tr).1.isSome :=
  congrArg (fun s => (s.2.run tr).1.isSome) (inst.pf_step x).symm

private theorem next_breakDH (tr : ExecTrace) :
    Step.breakDH.next tr =
      tr.append (⟨_root_.DY.Libsignal.PQXDH.PQXDHEvent.BrokenDH⟩ :
        _root_.DY.ProtocolEvent.ExecEntryT _root_.DY.Libsignal.PQXDH.PQXDHEvent) := by
  refine (stepIn_next_eq _root_.DY.Libsignal.PQXDH.breakDH.reachability () tr).trans ?_
  dsimp only [_root_.DY.Libsignal.PQXDH.breakDH.reachability, _root_.DY.Libsignal.PQXDH.breakDH]
  rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Traceful.run_bind,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  dsimp only
  rw [Traceful.run_pure]

private theorem next_network (msg : _root_.DY.Bytes) (tr : ExecTrace) :
    (Step.network msg).next tr = tr.append (⟨msg⟩ : _root_.DY.Network.ExecEntryT) := by
  refine (stepIn_next_eq _root_.DY.Network.reachability msg tr).trans ?_
  dsimp only [_root_.DY.Network.reachability]
  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]

private theorem ok_invertDH_eq (pkIdx : Nat) (tr : ExecTrace) :
    (Step.invertDH pkIdx).ok tr =
      ((_root_.DY.Libsignal.PQXDH.invertDH pkIdx).run tr).1.isSome :=
  stepIn_ok_eq _root_.DY.Libsignal.PQXDH.invertDH.reachability pkIdx tr

private theorem next_invertDH_eq (pkIdx : Nat) (tr : ExecTrace) :
    (Step.invertDH pkIdx).next tr =
      ((_root_.DY.Libsignal.PQXDH.invertDH pkIdx).run tr).2.val :=
  stepIn_next_eq _root_.DY.Libsignal.PQXDH.invertDH.reachability pkIdx tr

private theorem at?_some_of_le {E : Type} [ExecTraceTypes.Has E]
    {tr₁ tr₂ : ExecTrace} {i : Nat} {e : E}
    (hle : tr₁ ≤ tr₂) (hat : (tr₁.at? i : Option E) = some e) :
    i < tr₂.length ∧ (tr₂.at? i : Option E) = some e := by
  have hat₂ : (tr₂.at? i : Option E) = some e := by
    have h' := Trace.at?_le (EntryT := E) tr₁ tr₂ i hle
    rwa [hat] at h'
  have hi₂ : i < tr₂.length := by
    by_contra hge
    simp [Trace.at?, hge] at hat₂
  exact ⟨hi₂, hat₂⟩

private theorem someEventB_mono {tr₁ tr₂ : ExecTrace}
    {p : _root_.DY.Libsignal.PQXDH.PQXDHEvent → Bool}
    (hle : tr₁ ≤ tr₂) (h : (_root_.DY.Libsignal.TripleRatchet.anyEventOnTrace _root_.DY.Libsignal.PQXDH.PQXDHEvent) tr₁ p = true) :
    (_root_.DY.Libsignal.TripleRatchet.anyEventOnTrace _root_.DY.Libsignal.PQXDH.PQXDHEvent) tr₂ p = true := by
  simp only [_root_.DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?] at h ⊢
  rw [List.any_eq_true] at h ⊢
  obtain ⟨i, hi_mem, hi_p⟩ := h
  rw [List.mem_range] at hi_mem
  cases hat : (tr₁.at? i : Option (_root_.DY.ProtocolEvent.ExecEntryT _root_.DY.Libsignal.PQXDH.PQXDHEvent)) with
  | none => simp [hat] at hi_p
  | some e =>
    simp only [hat] at hi_p
    obtain ⟨hi₂, hat₂⟩ := at?_some_of_le hle hat
    exact ⟨i, List.mem_range.mpr hi₂, by simp [hat₂, hi_p]⟩

private theorem someEventB_append_self (tr : ExecTrace)
    (ev : _root_.DY.Libsignal.PQXDH.PQXDHEvent)
    {p : _root_.DY.Libsignal.PQXDH.PQXDHEvent → Bool} (hp : p ev = true) :
    (_root_.DY.Libsignal.TripleRatchet.anyEventOnTrace _root_.DY.Libsignal.PQXDH.PQXDHEvent)
      (tr.append (⟨ev⟩ : _root_.DY.ProtocolEvent.ExecEntryT _root_.DY.Libsignal.PQXDH.PQXDHEvent)) p = true := by
  rw [_root_.DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]
  rw [List.any_eq_true]
  refine ⟨tr.length, ?_, ?_⟩
  · rw [List.mem_range]
    simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  · rw [Trace.at?_append]
    exact hp

private theorem matchesEvents_brokenDHB {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    (hme : MatchesEventsAt interp r S g initIds tr ss evs vis) (hmem : .env .breakDH ∈ evs) :
    _root_.DY.Libsignal.PQXDH.brokenDHB (runSteps ss tr) = true := by
  induction hme with
  | nil _ => cases hmem
  | @run1 _ tr pre s ss' ev evs' v vs _ _ _ ih =>
    rcases List.mem_cons.mp hmem with h | h
    · cases h
    · simpa only [runSteps_append, runSteps] using ih h
  | @run0 _ tr pre ss' ev evs' vs _ _ _ ih =>
    rcases List.mem_cons.mp hmem with h | h
    · cases h
    · simpa only [runSteps_append] using ih h
  | @env _ tr pre s ss' ev evs' v vs _ hem _ ih =>
    rcases List.mem_cons.mp hmem with h | h
    · injection h with hev
      subst hev
      obtain ⟨rfl, _⟩ := hem
      have hbr : _root_.DY.Libsignal.PQXDH.brokenDHB (Step.breakDH.next (runSteps pre tr)) = true := by
        rw [next_breakDH]
        exact someEventB_append_self (runSteps pre tr) .BrokenDH rfl
      have hmono := someEventB_mono (stepsWF_le ss' (Step.breakDH.next (runSteps pre tr))) hbr
      simpa only [runSteps_append, runSteps, _root_.DY.Libsignal.PQXDH.brokenDHB] using hmono
    · simpa only [runSteps_append, runSteps] using ih h

private theorem invertDH_run_at_dhPk {tr : ExecTrace} {pkIdx : Nat} {skTerm : _root_.DY.Bytes}
    (hbr : _root_.DY.Libsignal.PQXDH.brokenDHB tr = true)
    (hat : (tr.at? pkIdx : Option _root_.DY.Network.ExecEntryT) = some ⟨dhPk skTerm⟩) :
    ((_root_.DY.Libsignal.PQXDH.invertDH pkIdx).run tr).1 = some tr.length ∧
      ((_root_.DY.Libsignal.PQXDH.invertDH pkIdx).run tr).2.val =
        tr.append (⟨skTerm⟩ : _root_.DY.Network.ExecEntryT) := by
  have h1 : _root_.DY.X25519.normalizeX25519Key (dhPk skTerm) = dhPk skTerm := by
    unfold _root_.DY.X25519.normalizeX25519Key
    dsimp only [dhPk, _root_.DY.DiffieHellman.CanDH.dhPk]
    rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _root_.DY.X25519.Variant.SubF]
  have hsk : _root_.DY.Libsignal.PQXDH.extractDhSecretKey
      (_root_.DY.X25519.normalizeX25519Key (dhPk skTerm)) = some skTerm := by
    rw [h1]
    simp only [_root_.DY.Libsignal.PQXDH.extractDhSecretKey, dhPk, _root_.DY.BytesView.view_pack]
  have hg_run :
      ((_root_.DY.Libsignal.TripleRatchet.guardTrace _root_.DY.Libsignal.PQXDH.brokenDHB).run tr).1 = some () ∧
      ((_root_.DY.Libsignal.TripleRatchet.guardTrace _root_.DY.Libsignal.PQXDH.brokenDHB).run tr).2.val = tr := by
    unfold _root_.DY.Libsignal.TripleRatchet.guardTrace
    simp only [Traceful.run_mk, hbr, ↓reduceIte]
    exact ⟨trivial, trivial⟩
  have hrcv_run :
      ((_root_.DY.Network.receiveMessage pkIdx).run tr).1 = some (dhPk skTerm) ∧
      ((_root_.DY.Network.receiveMessage pkIdx).run tr).2.val = tr := by
    rw [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1, Traceful.run_bind,
      Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
    dsimp only
    rw [hat]
    dsimp only
    rw [Traceful.run_pure]
    exact ⟨rfl, rfl⟩
  obtain ⟨hg1, hg2⟩ := hg_run
  obtain ⟨hrcv1, hrcv2⟩ := hrcv_run
  unfold _root_.DY.Libsignal.PQXDH.invertDH
  rw [Traceful.run_bind]
  rcases hg : (_root_.DY.Libsignal.TripleRatchet.guardTrace _root_.DY.Libsignal.PQXDH.brokenDHB).run tr with ⟨og, tg, _⟩
  rw [hg] at hg1 hg2
  dsimp only at hg1 hg2
  cases hg1
  cases hg2
  dsimp only
  rw [Traceful.run_bind]
  rcases hr : (_root_.DY.Network.receiveMessage pkIdx).run tr with ⟨or_, tr_, _⟩
  rw [hr] at hrcv1 hrcv2
  dsimp only at hrcv1 hrcv2
  cases hrcv1
  cases hrcv2
  dsimp only
  rw [hsk]
  dsimp only
  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  exact ⟨rfl, rfl⟩

private theorem ghostWF_snoc_leak {g : Ghost} {vis : List VisEntry} {ve : VisEntry}
    (hg : GhostWF g vis) (hve : ve.kind = .leak) :
    GhostWF g (vis ++ [ve]) := by
  refine ⟨fun w hw hwk => ?_, hg.2.1, fun w hw hwk => ?_⟩
  · rcases List.mem_append.mp hw with hw_vis | hw_v
    · exact hg.1 w hw_vis hwk
    · rw [List.mem_singleton.mp hw_v, hve] at hwk
      cases hwk
  · rcases List.mem_append.mp hw with hw_vis | hw_v
    · exact hg.2.2 w hw_vis hwk
    · rw [List.mem_singleton.mp hw_v, hve] at hwk
      cases hwk

private theorem matchesEvents_snoc_env_pre {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {ss pre : List Step} {s : Step}
    {evs : List CliEvent} {ev : EnvEvent} {vis v : List VisEntry}
    (hme : MatchesEventsAt interp r S g initIds tr ss evs vis)
    (hpre : ∀ x ∈ pre, x.cls = .invisible)
    (hem : EnvMatches interp r S g (runSteps pre (runSteps ss tr)) s ev v) :
    MatchesEventsAt interp r S g initIds tr (ss ++ (pre ++ [s])) (evs ++ [.env ev]) (vis ++ v) := by
  induction hme with
  | @nil initIds tr ss₀ hinv =>
    have hpre' : ∀ x ∈ ss₀ ++ pre, x.cls = .invisible := by
      intro x hx
      rcases List.mem_append.mp hx with h₀ | hp
      · exact hinv x h₀
      · exact hpre x hp
    have hem' : EnvMatches interp r S g (runSteps (ss₀ ++ pre) tr) s ev v := by
      rwa [runSteps_append]
    have h0 : MatchesEventsAt interp r S g initIds tr ((ss₀ ++ pre) ++ s :: []) [.env ev] (v ++ []) :=
      .env hpre' hem' (.nil (by simp))
    simpa [List.append_assoc] using h0
  | @run1 _ tr pre₀ s₀ ss' ev₀ evs' v₀ vs' hpre₀ hrm₀ _ ih =>
    have hem' : EnvMatches interp r S g
        (runSteps pre (runSteps ss' (s₀.next (runSteps pre₀ tr)))) s ev v := by
      simpa only [runSteps_append, runSteps] using hem
    have ih' := ih hem'
    simpa only [List.append_assoc, List.cons_append] using MatchesEventsAt.run1 hpre₀ hrm₀ ih'
  | @run0 _ tr pre₀ ss' ev₀ evs' vs' hpre₀ hrej₀ _ ih =>
    have hem' : EnvMatches interp r S g
        (runSteps pre (runSteps ss' (runSteps pre₀ tr))) s ev v := by
      simpa only [runSteps_append] using hem
    have ih' := ih hem'
    simpa only [List.append_assoc, List.cons_append] using MatchesEventsAt.run0 hpre₀ hrej₀ ih'
  | @env _ tr pre₀ s₀ ss' ev₀ evs' v₀ vs' hpre₀ hem₀ _ ih =>
    have hem' : EnvMatches interp r S g
        (runSteps pre (runSteps ss' (s₀.next (runSteps pre₀ tr)))) s ev v := by
      simpa only [runSteps_append, runSteps] using hem
    have ih' := ih hem'
    simpa only [List.append_assoc, List.cons_append] using MatchesEventsAt.env hpre₀ hem₀ ih'

/-- Explicit-extension form of `explains_snoc_invertDH` preserving the ghost `g` and appending
decrypt-free steps `ext`. -/
theorem explains_snoc_invertDH_step {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {vis : List VisEntry} {evs : List CliEvent} {pk sk : HwBytes}
    (hext : ExternContractsHoldCli interp) (hr : ProtocolSetupWF r)
    (h : Explains interp r S g ss vis evs)
    (hg : InvertsGuarded interp r (evs ++ [.env (.invertDH pk sk)])) :
    ∃ ext v, (∀ x ∈ ext, x.decryptMsgIdx? = none) ∧
      Explains interp r S g (ss ++ ext) (vis ++ v) (evs ++ [.env (.invertDH pk sk)]) := by
  have _ := hext
  have _ := hr
  obtain ⟨hbr_mem, _, hpk⟩ :
      .env .breakDH ∈ evs ∧ HonestDHSecret r evs sk ∧ pk = pubBytes interp sk :=
    hg evs [] (.invertDH pk sk) rfl
  let tr := runTrace r ss
  let pkTerm : _root_.DY.Bytes := dhPk (litOf sk)
  let s_net : Step := .network pkTerm
  let tr₁ : ExecTrace := s_net.next tr
  let s_inv : Step := .invertDH tr.length
  let v_inv : VisEntry := ⟨.leak, [litOf sk], .leakRecord, none⟩
  have htr₁_eq : tr₁ = tr.append (⟨pkTerm⟩ : _root_.DY.Network.ExecEntryT) :=
    next_network pkTerm tr
  have hknows_pk : pkTerm.AttackerKnows tr :=
    _root_.DY.DiffieHellman.attacker_knows_dhPk (litOf sk) tr
      (Symbolic.Swarm.CREF.CliPure.TR.G1.knows_litOf sk tr)
  have hnet_pre : s_net.PreCond tr :=
    stepIn_preCond_of _root_.DY.Network.reachability pkTerm tr hknows_pk
  have hinv_pre : s_inv.PreCond tr₁ :=
    stepIn_preCond_of _root_.DY.Libsignal.PQXDH.invertDH.reachability tr.length tr₁ trivial
  have hbr_tr : _root_.DY.Libsignal.PQXDH.brokenDHB tr = true :=
    matchesEvents_brokenDHB h.2.2.2 hbr_mem
  have hbr_tr₁ : _root_.DY.Libsignal.PQXDH.brokenDHB tr₁ = true := by
    have hle : tr ≤ tr₁ := stepsWF_le [s_net] tr
    exact someEventB_mono hle hbr_tr
  have hat_pk : (tr₁.at? tr.length : Option _root_.DY.Network.ExecEntryT) = some ⟨pkTerm⟩ := by
    rw [htr₁_eq, Trace.at?_append]
  obtain ⟨hrun_fst, hrun_snd⟩ := invertDH_run_at_dhPk hbr_tr₁ hat_pk
  have hok_inv : s_inv.ok tr₁ = true := by
    rw [ok_invertDH_eq, hrun_fst]
    rfl
  have hnext_inv : s_inv.next tr₁ = tr₁.append (⟨litOf sk⟩ : _root_.DY.Network.ExecEntryT) := by
    rw [next_invertDH_eq, hrun_snd]
  have hmsg_pk : (tr₁.getMessageSentAt tr.length).map (gamma interp S g) = some pk := by
    have hget : tr₁.getMessageSentAt tr.length = some pkTerm := by
      simp [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, hat_pk]
    rw [hget, Option.map_some]
    apply congrArg some
    dsimp only [pkTerm]
    rw [Symbolic.Swarm.CREF.TR.gamma_dhPk, Symbolic.Swarm.CREF.TR.RecvRep.gamma_litOf, hpk]
    rfl
  have hlast : lastSent tr₁ (s_inv.next tr₁) = some (litOf sk) := by
    rw [hnext_inv]
    unfold lastSent
    have hlen : (tr₁.append (⟨litOf sk⟩ : _root_.DY.Network.ExecEntryT)).length = tr₁.length + 1 := by
      simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
    have hlt : tr₁.length < (tr₁.append (⟨litOf sk⟩ : _root_.DY.Network.ExecEntryT)).length := by
      omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true hlt), hlen, Nat.add_sub_cancel]
    have hat_sk : ((tr₁.append (⟨litOf sk⟩ : _root_.DY.Network.ExecEntryT)).at? tr₁.length :
        Option _root_.DY.Network.ExecEntryT) = some ⟨litOf sk⟩ := Trace.at?_append ..
    simp [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, hat_sk]
  have hinv_entry : [v_inv] = invertEntry s_inv tr₁ .leakRecord := by
    unfold invertEntry
    rw [hlast]
    rfl
  have hbme : BytesMatchEntry interp r S g .leak sk v_inv :=
    ⟨rfl, litOf sk, rfl, Or.inl (Symbolic.Swarm.CREF.TR.RecvRep.gamma_litOf interp S g sk).symm⟩
  have hem : EnvMatches interp r S g (runSteps [s_net] (runSteps ss (setupTrace r))) s_inv
      (.invertDH pk sk) [v_inv] := by
    change EnvMatches interp r S g tr₁ s_inv (.invertDH pk sk) [v_inv]
    exact ⟨tr.length, rfl, hok_inv, hmsg_pk, hinv_entry, v_inv, rfl, hbme⟩
  have hextra_wf : StepsWF ([s_net] ++ [s_inv]) tr :=
    (stepsWF_append_iff [s_net] [s_inv] tr).mpr
      ⟨⟨hnet_pre, trivial, trivial⟩, hinv_pre, trivial, trivial⟩
  have hextra_noload : ∀ x ∈ [s_net] ++ [s_inv], x.stateLoad? = none := by
    intro x hx
    simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> rfl
  have hextra_nodec : ∀ x ∈ [s_net] ++ [s_inv], x.decryptMsgIdx? = none := by
    intro x hx
    simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> rfl
  have hmr_wf : ModelRunWF r (ss ++ ([s_net] ++ [s_inv])) :=
    ⟨h.2.2.1.1, h.2.2.1.2.1,
      (stepsWF_append_iff ss ([s_net] ++ [s_inv]) (setupTrace r)).mpr ⟨h.2.2.1.2.2.1, hextra_wf⟩,
      stepsStateFaithful_append_noLoad h.2.2.1.2.2.2 hextra_noload⟩
  have hme' : MatchesEvents interp r S g (setupTrace r) (ss ++ ([s_net] ++ [s_inv]))
      (evs ++ [.env (.invertDH pk sk)]) (vis ++ [v_inv]) :=
    matchesEvents_snoc_env_pre h.2.2.2 (by intro x hx; rw [List.mem_singleton.mp hx]; rfl) hem
  exact ⟨[s_net] ++ [s_inv], [v_inv], hextra_nodec,
    h.1, ghostWF_snoc_leak h.2.1 rfl, hmr_wf, hme'⟩

/-- A guarded `invertDH pk sk` environment event extends any explanation of `evs`. -/
theorem explains_snoc_invertDH {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry} {evs : List CliEvent} {pk sk : HwBytes}
    (hext : ExternContractsHoldCli interp) (hr : ProtocolSetupWF r)
    (h : Explains interp r S g ss vis evs)
    (hg : InvertsGuarded interp r (evs ++ [.env (.invertDH pk sk)])) :
    ∃ g' ss' vis', Explains interp r S g' ss' vis' (evs ++ [.env (.invertDH pk sk)]) := by
  obtain ⟨ext, v, -, h'⟩ := explains_snoc_invertDH_step hext hr h hg
  exact ⟨g, ss ++ ext, vis ++ v, h'⟩

end Symbolic.Proofs.Swarm.UA.BI.InvertDH

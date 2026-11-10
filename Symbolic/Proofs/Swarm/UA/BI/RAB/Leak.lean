/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.UA.BI.RAB.Defs
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.Steps
import Symbolic.Proofs.Swarm.CREF.Cli.World.RelCliPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.PQLeak
import Symbolic.Proofs.Swarm.CREF.TRView
import Symbolic.Proofs.Swarm.Coinsplit.Lift.L01InitClearLeak
import Symbolic.Proofs.Swarm.Coinsplit.Lift.L02GoodExit0Cut
import Symbolic.Proofs.Swarm.UA.BI.RAB.Base
import Symbolic.Proofs.Swarm.UA.BI.G.PendingPreKey
import Symbolic.Proofs.Swarm.UA.Base
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# Key-Leak Environment Steps

Proves `leak_ua_of_xlate : XlateInvSpecB -> UALeakSpecB`, showing that guarded key-leak events
(`LeaksFrom`) preserve `UAInvB`. Setup-key leaks extend explanations directly via `compromise*`
steps, while session-state leaks use `XlateInvSpecB` and `cliLiveAt_of_cut` to locate the matching
live model state.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.BI.RAB.Leak

open scoped _root_.DY.Libsignal.Composed _root_.DY.Libsignal.Composed.Refinement
cref_hide_foreign_instances

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant ExecTrace Trace Traceful ExecTraceTypes TraceEntryHas)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.Rust (SessionRec ChainRec)
open _root_.DY.Libsignal.HwEvents (MachineEvent RunEvent EnvEvent CliEvent)
open _root_.DY.Libsignal.PQXDH (PQXDHEvent)
open _root_.DY.Libsignal.TripleRatchet (TREvent TRState isCurrentSnapshot)
open _root_.DY.Libsignal.Composed (ComposedEvent reachability)
open _root_.DY.Libsignal.Composed.Refinement
  (ProtocolSetup ProtocolSetupWF OpaqueSymbolSemantics Ghost GhostWF Step Move VisEntry BytesMatchEntry EnvMatches
   BundlePreKeyIds activeBundleIds MatchesEventsAt MatchesEvents Explains StepsWF StepsStateFaithful ModelRunWF stepView exposures setupSecret setupPublic
   secretBytes recordBytes KeyInRecord gamma
   setupTrace runSteps runTrace runTraceMoves pendingPreKey isAliceDone keyInDirs_iff_exists_keyInDir stepIn)
open _root_.DY.Libsignal.Composed.Refinement.Cli
  (CliTurn KeyInDir KeyInDirsV1 LeaksFrom ReadCollisionCli)
open _root_.DY.Libsignal.Composed.Refinement.Cli.ParD3
  (PqTurnSim1A pqTurnSim1A_opkUsed_eq keyInDirs_iff_keyInDirsV1_clean)
open CryptoVerification.E2E (PEParams)
open Symbolic.Swarm.CREF
  (SemReady compSemOf_ready length_append' at?_append_lt at?_append_length at?_ge_length
   getEventAt_append_lt)
open Symbolic.Swarm.CREF.TR
  (PureTRSlots IsAnyExposureEv AppendsOnlyExposure run_bind_snd getLocalState_fst getLocalState_snd
   exposeSkipped_trace exposeKey_next_eq exposeSpqr_next_eq exposeSkipped_next_eq
   getLocalState_fst_of_appendsOnlyExposure isCurrentSnapshot_of_appendsOnlyExposure proj_inj_eq
   setupTrace_state_entries setupPublic_8_eq compromise_vis gamma_setupSecret keyInRecord_of_recordBytes_eq
   eraseSkipped eraseUnmodelled sessionOf serializedKey
   visOf_exposeKey_rk visOf_exposeKey_dhs visOf_exposeKey_cks visOf_exposeKey_ckr
   visOf_exposeSkipped visOf_exposeSpqr)
open Symbolic.Swarm.CREF.CliPure
  (pureStripPrev pureStripBytes_recordBytes keyInRecord_pureStripPrev trRecordStateInv_pureStripPrev)
open Symbolic.Swarm.Coinsplit.Lift (CliLiveAtCli explainsCli_toClean)
open Symbolic.Swarm.Coinsplit.Lift.L01 (init_clear_leak)
open Symbolic.Swarm.Coinsplit.Lift.L02 (outcomeFaithfulCli_of_goodExit0Cut)
open Symbolic.Proofs.Swarm.UA.Defs
  (SchedFits callsOf AlicePendingKeysOn AliceRecordPendingInSession flatEvent flatEvents)
open Symbolic.Proofs.Swarm.UA.BI.RAB.Defs (UALeakSpecB XlateInvSpecB)
open Symbolic.Proofs.Swarm.UA.Base
  (callsOf_append flatEvents_append runSteps_append runTrace_append
   ghostWF_of_append modelRunWF_of_append)
open Symbolic.Proofs.Swarm.UA.BI.RAB.Base (collisionAtCli_append readCollisionCli_append)
open Symbolic.Proofs.Swarm.UA.BI.G.PendingPreKey (aliceRecordPendingInSession_of_explains_append)

/-! ## Retired `CliLiveAtCli` preservation -/

private theorem flatEvents_leaks_keyInDirsV1 {interp' : ExternInterpretation} {P : PEParams}
    {r : ProtocolSetup} {t t_clean : CliTurn} {accepted : List HwBytes} {leaks : List CliEvent}
    (hr : ProtocolSetupWF r) (hsim : PqTurnSim1A interp' P r t t_clean accepted)
    (hleaks : LeaksFrom r t leaks) :
    ∀ m ∈ flatEvents leaks, ∃ k, KeyInDirsV1 r t_clean k ∧ m = .leak k := by
  intro m hm
  simp only [flatEvents, List.mem_flatMap] at hm
  obtain ⟨e, he, hm_e⟩ := hm
  obtain ⟨p, k, hk, rfl⟩ := hleaks e he
  simp only [flatEvent, List.mem_singleton] at hm_e
  refine ⟨k, ?_, hm_e⟩
  exact (keyInDirs_iff_keyInDirsV1_clean hsim).mp
    ((keyInDirs_iff_exists_keyInDir r hr.1 t k).mpr ⟨p, hk⟩)

theorem leak_old {interp' : ExternInterpretation} {P : PEParams} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {t t_clean : CliTurn} {accepted : List HwBytes} {evs leaks : List CliEvent}
    (hr : ProtocolSetupWF r) (hsim : PqTurnSim1A interp' P r t t_clean accepted)
    (hleaks : LeaksFrom r t leaks)
    (hlive : CliLiveAtCli interp' r S who ok t_clean accepted (flatEvents evs)) :
    CliLiveAtCli interp' r S who ok t_clean accepted (flatEvents (evs ++ leaks)) := by
  rw [flatEvents_append]
  exact (init_clear_leak outcomeFaithfulCli_of_goodExit0Cut).2.2 hr
    (flatEvents_leaks_keyInDirsV1 hr hsim hleaks) hlive

/-! ## `AliceRecordPendingInSession` preservation -/

private theorem run_discard_snd {α : Type} (x : Traceful α) (tr : ExecTrace) :
    ((do let _ ← x; pure ()).run tr).2.val = (x.run tr).2.val := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | _, _⟩ <;> (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)

private theorem stepIn_next (c : _root_.DY.ReachabilityConfig)
    [inst : _root_.DY.ReachabilityConfig.HasStep c reachability]
    (x : c.Input) (tr : ExecTrace) :
    ((reachability.step (stepIn c x)).2.run tr).2.val = ((c.step x).2.run tr).2.val :=
  congrArg (fun s => (s.2.run tr).2.val) (inst.pf_step x).symm

private theorem aliceRecordPendingInSession_leaks {interp' : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {t t_clean : CliTurn} {evs leaks : List CliEvent}
    (hr : ProtocolSetupWF r) (hleaks : LeaksFrom r t leaks)
    (hap : ∀ g ss vis, Explains interp' r S g ss vis evs → ¬ ReadCollisionCli interp' r S g ss evs →
      AliceRecordPendingInSession interp' r S g (runTrace r ss) (t_clean.leakRecords r) (activeBundleIds evs)) :
    ∀ g ss vis, Explains interp' r S g ss vis (evs ++ leaks) →
      ¬ ReadCollisionCli interp' r S g ss (evs ++ leaks) →
      AliceRecordPendingInSession interp' r S g (runTrace r ss) (t_clean.leakRecords r) (activeBundleIds (evs ++ leaks)) := by
  intro g ss vis hex hnrc
  refine aliceRecordPendingInSession_of_explains_append hr hex hnrc (fun ev hev => ?_) rfl
    (fun ss₁ vis₁ => hap g ss₁ vis₁)
  obtain ⟨_, _, _, h⟩ := hleaks _ hev; cases h

/-! ## Witness extension across `LeaksFrom` -/

private theorem runSteps_le : ∀ (ss : List Step) (tr : ExecTrace), tr ≤ runSteps ss tr
  | [], tr => Trace.le_refl tr
  | s :: ss, tr =>
    Trace.le_trans tr (s.next tr) (runSteps ss (s.next tr))
      ((reachability.step s.toInput).2.run tr).2.property (runSteps_le ss (s.next tr))

private theorem at?_some_of_le {E : Type} [ExecTraceTypes.Has E] {t T : ExecTrace} (hle : t ≤ T)
    {j : Nat} {x : E} (h : (t.at? j : Option E) = some x) : (T.at? j : Option E) = some x := by
  have h' := Trace.at?_le (EntryT := E) t T j hle
  rwa [h] at h'

private theorem stepIn_preCond_of (c : _root_.DY.ReachabilityConfig)
    [inst : _root_.DY.ReachabilityConfig.HasStep c reachability]
    (x : c.Input) (tr : ExecTrace) (h : c.PreCond x tr) :
    reachability.PreCond (stepIn c x) tr :=
  (inst.pf_pre x tr).mp h

private theorem stepView_compromiseIK (p : Participant) (idx : Nat) (tr : ExecTrace) :
    stepView (.compromiseIK p idx) tr false = (Move.compromiseIK p idx).vis tr := by
  have hnext : (Step.compromiseIK p idx).next tr = (Move.compromiseIK p idx).next tr :=
    (stepIn_next _root_.DY.Libsignal.PQXDH.compromiseIK.reachability (p, idx) tr).trans
      (run_discard_snd (_root_.DY.Libsignal.PQXDH.compromiseIK p idx) tr).symm
  unfold stepView Move.vis
  dsimp only [List.filter_nil, List.nil_append]
  rw [hnext]
  split <;> rfl

private theorem stepView_compromiseSPK (b : Participant) (idx : Nat) (tr : ExecTrace) :
    stepView (.compromiseSPK b idx) tr false = (Move.compromiseSPK b idx).vis tr := by
  have hnext : (Step.compromiseSPK b idx).next tr = (Move.compromiseSPK b idx).next tr :=
    (stepIn_next _root_.DY.Libsignal.PQXDH.compromiseSPK.reachability (b, idx) tr).trans
      (run_discard_snd (_root_.DY.Libsignal.PQXDH.compromiseSPK b idx) tr).symm
  unfold stepView Move.vis
  dsimp only [List.filter_nil, List.nil_append]
  rw [hnext]
  split <;> rfl

private theorem stepView_compromisePQSPK (b : Participant) (idx : Nat) (tr : ExecTrace) :
    stepView (.compromisePQSPK b idx) tr false = (Move.compromisePQSPK b idx).vis tr := by
  have hnext : (Step.compromisePQSPK b idx).next tr = (Move.compromisePQSPK b idx).next tr :=
    (stepIn_next _root_.DY.Libsignal.PQXDH.compromisePQSPK.reachability (b, idx) tr).trans
      (run_discard_snd (_root_.DY.Libsignal.PQXDH.compromisePQSPK b idx) tr).symm
  unfold stepView Move.vis
  dsimp only [List.filter_nil, List.nil_append]
  rw [hnext]
  split <;> rfl

private theorem stepView_compromiseOPK (b : Participant) (idx : Nat) (tr : ExecTrace) :
    stepView (.compromiseOPK b idx) tr false = (Move.compromiseOPK b idx).vis tr := by
  have hnext : (Step.compromiseOPK b idx).next tr = (Move.compromiseOPK b idx).next tr :=
    (stepIn_next _root_.DY.Libsignal.PQXDH.compromiseOPK.reachability (b, idx) tr).trans
      (run_discard_snd (_root_.DY.Libsignal.PQXDH.compromiseOPK b idx) tr).symm
  unfold stepView Move.vis
  dsimp only [List.filter_nil, List.nil_append]
  rw [hnext]
  split <;> rfl

private theorem stepView_exposeKey (me : Participant) (stH : Nat)
    (kc : _root_.DY.Libsignal.TripleRatchet.KeyComponent) (tr : ExecTrace) :
    stepView (.exposeKey me stH kc) tr false = (Move.exposeKey me stH kc).vis tr := by
  have hnext : (Step.exposeKey me stH kc).next tr = (Move.exposeKey me stH kc).next tr :=
    (stepIn_next _root_.DY.Libsignal.TripleRatchet.exposeKey.reachability (me, stH, kc) tr).trans
      (exposeKey_next_eq me stH kc tr).symm
  unfold stepView Move.vis
  dsimp only [List.filter_nil, List.nil_append]
  rw [hnext]
  split <;> rfl

private theorem stepView_exposeSpqr (me : Participant) (stH : Nat) (tr : ExecTrace) :
    stepView (.exposeSpqr me stH) tr false = (Move.exposeSpqr me stH).vis tr := by
  have hnext : (Step.exposeSpqr me stH).next tr = (Move.exposeSpqr me stH).next tr :=
    (stepIn_next _root_.DY.Libsignal.TripleRatchet.exposeSpqr.reachability (me, stH) tr).trans
      (exposeSpqr_next_eq me stH tr).symm
  unfold stepView Move.vis
  dsimp only [List.filter_nil, List.nil_append]
  rw [hnext]
  split <;> rfl

private theorem stepView_exposeSkipped (evH : Nat) (tr : ExecTrace) :
    stepView (.exposeSkipped evH) tr false = (Move.exposeSkipped evH).vis tr := by
  have hnext : (Step.exposeSkipped evH).next tr = (Move.exposeSkipped evH).next tr :=
    (stepIn_next _root_.DY.Libsignal.TripleRatchet.exposeSkipped.reachability evH tr).trans
      (exposeSkipped_next_eq evH tr).symm
  unfold stepView Move.vis
  dsimp only [List.filter_nil, List.nil_append]
  rw [hnext]
  split <;> rfl

private theorem stepsWF_snoc {ss : List Step} {s : Step} {tr : ExecTrace}
    (hwf : StepsWF ss tr) (hpre : s.PreCond (runSteps ss tr))
    (hlok : s.LocalOk (runSteps ss tr)) :
    StepsWF (ss ++ [s]) tr := by
  induction ss generalizing tr with
  | nil => exact ⟨hpre, hlok, trivial⟩
  | cons x xs ih => exact ⟨hwf.1, hwf.2.1, ih hwf.2.2 hpre hlok⟩

private theorem stepsStateFaithful_snoc_nonLoad {r : ProtocolSetup} {ss : List Step} {s : Step}
    (hsf : StepsStateFaithful r ss) (hn : s.stateLoad? = none) :
    StepsStateFaithful r (ss ++ [s]) := by
  intro i j si sj p k b hij hi hj hload hok hload'
  by_cases hjlt : j < ss.length
  · have hilt : i < ss.length := Nat.lt_trans hij hjlt
    rw [List.getElem?_append_left hilt] at hi
    rw [List.getElem?_append_left hjlt] at hj
    rw [List.take_append_of_le_length (Nat.le_of_lt hilt)] at hok
    exact hsf i j si sj p k b hij hi hj hload hok hload'
  · by_cases hjeq : j = ss.length
    · subst hjeq
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero] at hj
      injection hj with hseq
      subst hseq
      rw [hn] at hload'
      cases hload'
    · have hjge : (ss ++ [s]).length ≤ j := by simp only [List.length_append, List.length_singleton]; omega
      rw [List.getElem?_eq_none hjge] at hj
      cases hj

private theorem ghostWF_snoc_leak {g : Ghost} {vis : List VisEntry} {v : VisEntry}
    (hg : GhostWF g vis) (hv : v.kind = .leak) : GhostWF g (vis ++ [v]) := by
  refine ⟨fun w hw hwk => ?_, hg.2.1, fun w hw hwk => ?_⟩
  · rcases List.mem_append.mp hw with hw_vis | hw_v
    · exact hg.1 w hw_vis hwk
    · rw [List.mem_singleton.mp hw_v, hv] at hwk; cases hwk
  · rcases List.mem_append.mp hw with hw_vis | hw_v
    · exact hg.2.2 w hw_vis hwk
    · rw [List.mem_singleton.mp hw_v, hv] at hwk; cases hwk

private theorem matchesEvents_snoc_env {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {s : Step} {ev : EnvEvent} {v : VisEntry} :
    ∀ {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {ss : List Step} {evs : List CliEvent} {vis : List VisEntry},
      MatchesEventsAt interp r S g initIds tr ss evs vis →
      EnvMatches interp r S g (runSteps ss tr) s ev [v] →
      MatchesEventsAt interp r S g initIds tr (ss ++ [s]) (evs ++ [.env ev]) (vis ++ [v])
  | _, _, _, _, _, .nil hinv, hem =>
    MatchesEventsAt.env (v := [v]) (vs := []) hinv hem (.nil fun _ hx => nomatch hx)
  | _, _, _, _, _, .run1 hpre hrm hrest, hem => by
    have ih := matchesEvents_snoc_env hrest (by simpa only [runSteps_append, runSteps] using hem)
    simpa only [List.append_assoc, List.cons_append] using MatchesEventsAt.run1 hpre hrm ih
  | _, _, _, _, _, .run0 hpre hrej hrest, hem => by
    have ih := matchesEvents_snoc_env hrest (by simpa only [runSteps_append] using hem)
    simpa only [List.append_assoc, List.cons_append] using MatchesEventsAt.run0 hpre hrej ih
  | _, _, _, _, _, .env hpre hem₀ hrest, hem => by
    have ih := matchesEvents_snoc_env hrest (by simpa only [runSteps_append, runSteps] using hem)
    simpa only [List.append_assoc, List.cons_append] using MatchesEventsAt.env hpre hem₀ ih

private theorem append_singleton_eq_append_cons {α : Type} {xs ys zs : List α} {a b : α}
    (heq : xs ++ [a] = ys ++ b :: zs) (hne : a ≠ b) :
    ∃ zs', zs = zs' ++ [a] ∧ xs = ys ++ b :: zs' := by
  induction zs using List.reverseRecOn with
  | nil =>
    have hab : [a] = [b] := List.append_inj_right' heq rfl
    injection hab with h'
    exact False.elim (hne h')
  | append_singleton zs' z _ =>
    have heq' : xs ++ [a] = (ys ++ b :: zs') ++ [z] := by simpa [List.append_assoc] using heq
    have haz : [a] = [z] := List.append_inj_right' heq' rfl
    injection haz with hza
    subst hza
    exact ⟨zs', rfl, List.append_inj_left' heq' rfl⟩

private theorem not_readCollisionCli_snoc_leak {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {s : Step} {evs : List CliEvent}
    {p : Participant} {k : HwBytes}
    (hnrc : ¬ ReadCollisionCli interp r S g ss evs) (hdec : s.decryptMsgIdx? = none) :
    ¬ ReadCollisionCli interp r S g (ss ++ [s]) (evs ++ [.env (.leak p k)]) := by
  rintro ⟨evs₁, ev, evs₂, ss₁, ss₂, m, vis₁, msgIdx, out, b, t_msg,
    hevs, hss, hcmd, hexit, hbody, hm₁, hm_dec, hmsg, hcol⟩
  obtain ⟨evs₂', _, rfl⟩ := append_singleton_eq_append_cons hevs nofun
  have hsm : s ≠ m := by
    intro h; subst h; rw [hdec] at hm_dec; cases hm_dec
  obtain ⟨ss₂', _, rfl⟩ := append_singleton_eq_append_cons hss hsm
  exact hnrc ⟨evs₁, ev, evs₂', ss₁, ss₂', m, vis₁, msgIdx, out, b, t_msg,
    rfl, rfl, hcmd, hexit, hbody, hm₁, hm_dec, hmsg, hcol⟩

private theorem finish_leak_step {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g₀ : Ghost} {ss₀ : List Step} {vis₀ : List VisEntry} {evs : List CliEvent}
    {p : Participant} {k : HwBytes} (s : Step) (v : VisEntry)
    (hex₀ : Explains interp' r S g₀ ss₀ vis₀ evs)
    (hnrc₀ : ¬ ReadCollisionCli interp' r S g₀ ss₀ evs)
    (hcls : s.cls = .env) (hleak : s.IsLeak) (hparty : ∀ q, s.party? = some q → q = p)
    (hpre : s.PreCond (runTrace r ss₀)) (hlok : s.LocalOk (runTrace r ss₀))
    (hnload : s.stateLoad? = none) (hndec : s.decryptMsgIdx? = none)
    (hview : stepView s (runTrace r ss₀) false = [v]) (hvk : v.kind = .leak)
    (hbme : BytesMatchEntry interp' r S g₀ .leak k v) :
    Explains interp' r S g₀ (ss₀ ++ [s]) (vis₀ ++ [v]) (evs ++ [.env (.leak p k)]) ∧
      ¬ ReadCollisionCli interp' r S g₀ (ss₀ ++ [s]) (evs ++ [.env (.leak p k)]) := by
  have hem : EnvMatches interp' r S g₀ (runTrace r ss₀) s (.leak p k) [v] :=
    ⟨hcls, hleak, hparty, hview.symm, v, rfl, hbme⟩
  refine ⟨⟨hex₀.1, ghostWF_snoc_leak hex₀.2.1 hvk,
    ⟨hex₀.2.2.1.1, hex₀.2.2.1.2.1, stepsWF_snoc hex₀.2.2.1.2.2.1 hpre hlok,
      stepsStateFaithful_snoc_nonLoad hex₀.2.2.1.2.2.2 hnload⟩,
    matchesEvents_snoc_env hex₀.2.2.2 hem⟩,
    not_readCollisionCli_snoc_leak hnrc₀ hndec⟩

private def zAnyPure : PureTRSlots :=
  { canon := fun _ _ => True, recvSim := fun _ _ => True, tok := fun _ => True }

private theorem find?_eq_some_of_mem_nodup {α β : Type} (f : α → β) {l : List α}
    (hnd : (l.map f).Nodup) {x : α} (hx : x ∈ l) (p : α → Bool)
    (hpx : p x = true) (hpf : ∀ y, p y = true → f y = f x) :
    l.find? p = some x := by
  induction l with
  | nil => cases hx
  | cons a xs ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp hx with rfl | hx'
    · simp [List.find?, hpx]
    · have hpa : p a = false := by
        cases hp : p a
        · rfl
        · exact False.elim (hnd.1 ⟨x, hx', (hpf a hp).symm⟩)
      simp [List.find?, hpa, ih hnd.2 hx']

private theorem single_leak_explains_snoc {interp' : ExternInterpretation} {P : PEParams}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {t t_clean : CliTurn} {accepted : List HwBytes} {evs : List CliEvent}
    {g₀ : Ghost} {ss₀ : List Step} {vis₀ : List VisEntry} {p : Participant} {k : HwBytes}
    (hr : ProtocolSetupWF r) (hS : SemReady interp' r S)
    (hsim : PqTurnSim1A interp' P r t t_clean accepted)
    (hfit : SchedFits (callsOf evs) who ok)
    (hlive : CliLiveAtCli interp' r S who ok t_clean accepted (flatEvents evs))
    (hXlate : XlateInvSpecB)
    (hk : KeyInDir r t p k)
    (hex₀ : Explains interp' r S g₀ ss₀ vis₀ evs)
    (hnrc₀ : ¬ ReadCollisionCli interp' r S g₀ ss₀ evs) :
    ∃ s v, Explains interp' r S g₀ (ss₀ ++ [s]) (vis₀ ++ [v]) (evs ++ [.env (.leak p k)]) ∧
      ¬ ReadCollisionCli interp' r S g₀ (ss₀ ++ [s]) (evs ++ [.env (.leak p k)]) := by
  have hle : setupTrace r ≤ runTrace r ss₀ := runSteps_le ss₀ (setupTrace r)
  obtain ⟨h4, h9, h13, h19, h24⟩ := setupTrace_state_entries r hr.1
  obtain ⟨hg0, hg1, hg2, _, hg6⟩ := gamma_setupSecret interp' r S g₀ hex₀.1 hr.1
  rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl | rfl | ⟨hopk, hused, rfl⟩⟩ | ⟨rec_env, hp, hk_rec⟩
  · refine ⟨.compromiseIK r.alice 4,
      ⟨.leak, [setupSecret r 0], .leakPq false, some (runTrace r ss₀).length⟩, ?_⟩
    exact finish_leak_step _ _ hex₀ hnrc₀ rfl trivial
      (fun _ h => (Option.some.inj h).symm)
      (stepIn_preCond_of _root_.DY.Libsignal.PQXDH.compromiseIK.reachability (r.alice, 4) _ trivial)
      trivial rfl rfl
      ((stepView_compromiseIK r.alice 4 _).trans
        (compromise_vis (m := .compromiseIK r.alice 4) rfl (at?_some_of_le hle h4) rfl))
      rfl ⟨rfl, congrArg (· :: []) hg0⟩
  · refine ⟨.compromisePQSPK r.bob 19,
      ⟨.leak, [setupSecret r 4], .leakPq true, some (runTrace r ss₀).length⟩, ?_⟩
    exact finish_leak_step _ _ hex₀ hnrc₀ rfl trivial
      (fun _ h => (Option.some.inj h).symm)
      (stepIn_preCond_of _root_.DY.Libsignal.PQXDH.compromisePQSPK.reachability (r.bob, 19) _ trivial)
      trivial rfl rfl
      ((stepView_compromisePQSPK r.bob 19 _).trans
        (compromise_vis (m := .compromisePQSPK r.bob 19) rfl (at?_some_of_le hle h19) rfl))
      rfl ⟨rfl, rfl⟩
  · refine ⟨.compromiseIK r.bob 9,
      ⟨.leak, [setupSecret r 1], .leakPq false, some (runTrace r ss₀).length⟩, ?_⟩
    exact finish_leak_step _ _ hex₀ hnrc₀ rfl trivial
      (fun _ h => (Option.some.inj h).symm)
      (stepIn_preCond_of _root_.DY.Libsignal.PQXDH.compromiseIK.reachability (r.bob, 9) _ trivial)
      trivial rfl rfl
      ((stepView_compromiseIK r.bob 9 _).trans
        (compromise_vis (m := .compromiseIK r.bob 9) rfl (at?_some_of_le hle h9) rfl))
      rfl ⟨rfl, congrArg (· :: []) hg1⟩
  · refine ⟨.compromiseSPK r.bob 13,
      ⟨.leak, [setupSecret r 2], .leakPq false, some (runTrace r ss₀).length⟩, ?_⟩
    exact finish_leak_step _ _ hex₀ hnrc₀ rfl trivial
      (fun _ h => (Option.some.inj h).symm)
      (stepIn_preCond_of _root_.DY.Libsignal.PQXDH.compromiseSPK.reachability (r.bob, 13) _ trivial)
      trivial rfl rfl
      ((stepView_compromiseSPK r.bob 13 _).trans
        (compromise_vis (m := .compromiseSPK r.bob 13) rfl (at?_some_of_le hle h13) rfl))
      rfl ⟨rfl, congrArg (· :: []) hg2⟩
  · obtain ⟨τ₀, ms₀, hex_cli, hnrc_cli, htr_eq, _, _, _⟩ := hXlate hr hS hfit hex₀ hnrc₀
    obtain ⟨_, _, hopk₀⟩ := hlive.cliLiveAt_of_cut ⟨g₀, ms₀, hex_cli, hnrc_cli⟩
    have hc₀ := explainsCli_toClean hex_cli hnrc_cli
    have hopk_guard : _root_.DY.Libsignal.PQXDH.opkUsedB (runTrace r ss₀) r.bob
        (_root_.DY.DiffieHellman.CanDH.dhPk (setupSecret r 6)) = false := by
      rw [← htr_eq, ← setupPublic_8_eq r hr.1 hopk]
      exact hopk₀.apply hopk ((pqTurnSim1A_opkUsed_eq hsim).symm.trans hused) hc₀
    refine ⟨.compromiseOPK r.bob 24,
      ⟨.leak, [setupSecret r 6], .leakPq false, some (runTrace r ss₀).length⟩, ?_⟩
    exact finish_leak_step _ _ hex₀ hnrc₀ rfl trivial
      (fun _ h => (Option.some.inj h).symm)
      (stepIn_preCond_of _root_.DY.Libsignal.PQXDH.compromiseOPK.reachability (r.bob, 24) _ trivial)
      trivial rfl rfl
      ((stepView_compromiseOPK r.bob 24 _).trans
        (compromise_vis (m := .compromiseOPK r.bob 24) rfl (at?_some_of_le hle (h24 hopk)) rfl
          (fun _ => hopk_guard)))
      rfl ⟨rfl, congrArg (· :: []) (hg6 hopk)⟩
  · obtain ⟨τ₀, ms₀, hex_cli, hnrc_cli, htr_eq, _, _, _⟩ := hXlate hr hS hfit hex₀ hnrc₀
    obtain ⟨_, hrel₀, _⟩ := hlive.cliLiveAt_of_cut ⟨g₀, ms₀, hex_cli, hnrc_cli⟩
    have hc₀ := explainsCli_toClean hex_cli hnrc_cli
    have hrecInv := trRecordStateInv_pureStripPrev (Z := zAnyPure) (fun _ _ => trivial) (hrel₀.recs hc₀)
    have hpb : pureStripPrev (t_clean.leakRecords r) p =
        some (recordBytes { rec_env with previous := [] }) := by
      rw [← hsim.strip_eq]
      simp only [pureStripPrev, hp, Option.map_some, pureStripBytes_recordBytes]
    have hk_strip : KeyInRecord { rec_env with previous := [] } k :=
      (keyInRecord_pureStripPrev rec_env k).mpr hk_rec
    obtain ⟨_, rec, st, stateIdx, heq_bytes, hget, hcurr, hsr, hkeys, _, _, hnd⟩ :=
      hrecInv p (recordBytes { rec_env with previous := [] }) hpb
    rw [htr_eq] at hget hcurr hkeys
    have hkey : KeyInRecord rec k := keyInRecord_of_recordBytes_eq heq_bytes hk_strip
    have hrk_eq : rec.current.rootKey = gamma interp' S g₀ st.rk := by
      simpa [eraseSkipped, eraseUnmodelled, sessionOf] using congrArg SessionRec.rootKey hsr.2
    have hsc_eq : rec.current.senderChain =
        (sessionOf interp' (gamma interp' S g₀) st).senderChain := by
      simpa [eraseSkipped, eraseUnmodelled] using congrArg SessionRec.senderChain hsr.2
    have hrc_eq : rec.current.receiverChains.map (fun c => { c with messageKeys := [] }) =
        (sessionOf interp' (gamma interp' S g₀) st).receiverChains := by
      simpa [eraseSkipped, eraseUnmodelled] using congrArg SessionRec.receiverChains hsr.2
    have hpq_eq : rec.current.pqRatchetState = gamma interp' S g₀ st.spqr := by
      simpa [eraseSkipped, eraseUnmodelled, sessionOf] using
        congrArg SessionRec.pqRatchetState hsr.2
    rcases hkey with rfl | ⟨sc, hsc, rfl | ⟨ck, hck, rfl⟩⟩ |
        ⟨rc, hrc, ⟨hne, _⟩ | ⟨ck, hck, rfl⟩ | ⟨mk, hmk, rfl⟩⟩ | rfl
    · refine ⟨.exposeKey p stateIdx .rk,
        ⟨.leak, [st.rk], .leakRecord, some (runTrace r ss₀).length⟩, ?_⟩
      exact finish_leak_step _ _ hex₀ hnrc₀ rfl trivial
        (fun _ h => (Option.some.inj h).symm)
        (stepIn_preCond_of _root_.DY.Libsignal.TripleRatchet.exposeKey.reachability
          (p, stateIdx, .rk) _ trivial)
        hcurr rfl rfl
        ((stepView_exposeKey p stateIdx .rk _).trans (visOf_exposeKey_rk hget))
        rfl ⟨rfl, st.rk, rfl, .inl hrk_eq⟩
    · rw [hsc_eq] at hsc; dsimp only [sessionOf] at hsc; injection hsc with hsc'; subst hsc'
      refine ⟨.exposeKey p stateIdx .dhs,
        ⟨.leak, [st.dhs], .leakRecord, some (runTrace r ss₀).length⟩, ?_⟩
      exact finish_leak_step _ _ hex₀ hnrc₀ rfl trivial
        (fun _ h => (Option.some.inj h).symm)
        (stepIn_preCond_of _root_.DY.Libsignal.TripleRatchet.exposeKey.reachability
          (p, stateIdx, .dhs) _ trivial)
        hcurr rfl rfl
        ((stepView_exposeKey p stateIdx .dhs _).trans (visOf_exposeKey_dhs hget))
        rfl ⟨rfl, st.dhs, rfl, .inr rfl⟩
    · rw [hsc_eq] at hsc; dsimp only [sessionOf] at hsc; injection hsc with hsc'; subst hsc'
      dsimp only at hck; injection hck with hck'; subst hck'
      refine ⟨.exposeKey p stateIdx .cks,
        ⟨.leak, [st.cks], .leakRecord, some (runTrace r ss₀).length⟩, ?_⟩
      exact finish_leak_step _ _ hex₀ hnrc₀ rfl trivial
        (fun _ h => (Option.some.inj h).symm)
        (stepIn_preCond_of _root_.DY.Libsignal.TripleRatchet.exposeKey.reachability
          (p, stateIdx, .cks) _ trivial)
        hcurr rfl rfl
        ((stepView_exposeKey p stateIdx .cks _).trans (visOf_exposeKey_cks hget))
        rfl ⟨rfl, st.cks, rfl, .inl rfl⟩
    · have hmem_map : { rc with messageKeys := [] } ∈
          rec.current.receiverChains.map (fun c => { c with messageKeys := [] }) :=
        List.mem_map.mpr ⟨rc, hrc, rfl⟩
      rw [hrc_eq] at hmem_map; dsimp only [sessionOf] at hmem_map
      obtain ⟨_, _, hc₀_eq⟩ := List.mem_map.mp hmem_map
      exact absurd (congrArg ChainRec.senderRatchetKeyPrivate hc₀_eq).symm hne
    · have hmem_map : { rc with messageKeys := [] } ∈
          rec.current.receiverChains.map (fun c => { c with messageKeys := [] }) :=
        List.mem_map.mpr ⟨rc, hrc, rfl⟩
      rw [hrc_eq] at hmem_map; dsimp only [sessionOf] at hmem_map
      obtain ⟨c₀, hc₀_mem, hc₀_eq⟩ := List.mem_map.mp hmem_map
      have hck_eq : rc.chainKey =
          some (c₀.index.toBitVec, gamma interp' S g₀ c₀.chainKey) :=
        (congrArg ChainRec.chainKey hc₀_eq).symm
      rw [hck_eq] at hck; injection hck with hck'; subst hck'
      have hmap_srk : st.recv.map (fun c => serializedKey (gamma interp' S g₀ c.ratchetKey)) =
          rec.current.receiverChains.map ChainRec.senderRatchetKey := by
        have h1 := congrArg (List.map ChainRec.senderRatchetKey) hrc_eq.symm
        rw [List.map_map] at h1; dsimp only [sessionOf] at h1; rw [List.map_map] at h1
        exact h1
      have hnd_recv :
          (st.recv.map (fun c => serializedKey (gamma interp' S g₀ c.ratchetKey))).Nodup := by
        rw [hmap_srk]; exact hnd.1
      have hfind : _root_.DY.Libsignal.TripleRatchet.findRecvChain st.recv c₀.ratchetKey = some c₀ :=
        find?_eq_some_of_mem_nodup
          (fun c => serializedKey (gamma interp' S g₀ c.ratchetKey))
          hnd_recv hc₀_mem (·.ratchetKey == c₀.ratchetKey) (beq_self_eq_true _)
          (fun _ hy => by rw [beq_iff_eq.mp hy])
      refine ⟨.exposeKey p stateIdx (.ckr c₀.ratchetKey),
        ⟨.leak, [c₀.chainKey], .leakRecord, some (runTrace r ss₀).length⟩, ?_⟩
      exact finish_leak_step _ _ hex₀ hnrc₀ rfl trivial
        (fun _ h => (Option.some.inj h).symm)
        (stepIn_preCond_of _root_.DY.Libsignal.TripleRatchet.exposeKey.reachability
          (p, stateIdx, .ckr c₀.ratchetKey) _ trivial)
        hcurr rfl rfl
        ((stepView_exposeKey p stateIdx (.ckr c₀.ratchetKey) _).trans (visOf_exposeKey_ckr hget hfind))
        rfl ⟨rfl, c₀.chainKey, rfl, .inl rfl⟩
    · obtain ⟨pk, rIdx, srcIdx, skIdx, seed, hlog, _, hru, hgam, _, hfind_pk⟩ := hkeys rc hrc mk hmk
      rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hlog
      have hat_st : ((runTrace r ss₀).at? stateIdx :
          Option (_root_.DY.PersistentGlobalState.State.ExecEntryT
            (_root_.DY.PersistentLocalState.LocalState TRState))) = some ⟨⟨p, st⟩⟩ := by
        have hg := hget
        rw [getLocalState_fst] at hg
        rcases h : ((runTrace r ss₀).at? stateIdx :
            Option (_root_.DY.PersistentGlobalState.State.ExecEntryT
              (_root_.DY.PersistentLocalState.LocalState TRState))) with _ | ⟨⟨q, st'⟩⟩
        · simp [h] at hg
        · simp only [h] at hg
          by_cases hqp : q = p
          · subst hqp; simp only [↓reduceIte, Option.some.injEq] at hg; subst hg; rfl
          · simp [hqp] at hg
      have hlt_st : stateIdx < (runTrace r ss₀).length := by
        by_contra hge
        have hnone := at?_ge_length (E2 := _root_.DY.PersistentGlobalState.State.ExecEntryT
          (_root_.DY.PersistentLocalState.LocalState TRState)) (runTrace r ss₀) (Nat.le_of_not_lt hge)
        rw [hat_st] at hnone; cases hnone
      have hlok_sk : (Step.exposeSkipped skIdx).LocalOk (runTrace r ss₀) := by
        show _root_.DY.Libsignal.TripleRatchet.isSkippedChainCurrent (runTrace r ss₀) skIdx = true
        unfold _root_.DY.Libsignal.TripleRatchet.isSkippedChainCurrent
        rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hlog]
        dsimp only
        refine List.any_eq_true.mpr ⟨stateIdx, List.mem_range.mpr hlt_st, ?_⟩
        rw [hcurr, hat_st]
        have hsme : (st.sessionInfo p).me = p := rfl
        simp [hsme, hfind_pk]
      refine ⟨.exposeSkipped skIdx,
        ⟨.leak, [seed], .leakRecord, some (runTrace r ss₀).length⟩, ?_⟩
      exact finish_leak_step _ _ hex₀ hnrc₀ rfl trivial
        (fun _ h => by cases h)
        (stepIn_preCond_of _root_.DY.Libsignal.TripleRatchet.exposeSkipped.reachability skIdx _ trivial)
        hlok_sk rfl rfl
        ((stepView_exposeSkipped skIdx _).trans (visOf_exposeSkipped hlog hru))
        rfl ⟨rfl, seed, rfl, .inl hgam.symm⟩
    · refine ⟨.exposeSpqr p stateIdx,
        ⟨.leak, [st.spqr], .leakRecord, some (runTrace r ss₀).length⟩, ?_⟩
      exact finish_leak_step _ _ hex₀ hnrc₀ rfl trivial
        (fun _ h => (Option.some.inj h).symm)
        (stepIn_preCond_of _root_.DY.Libsignal.TripleRatchet.exposeSpqr.reachability
          (p, stateIdx) _ trivial)
        hcurr rfl rfl
        ((stepView_exposeSpqr p stateIdx _).trans (visOf_exposeSpqr hget))
        rfl ⟨rfl, st.spqr, rfl, .inl hpq_eq⟩

private theorem leaks_explains {interp' : ExternInterpretation} {P : PEParams}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {t t_clean : CliTurn} {accepted : List HwBytes} {g₀ : Ghost}
    (hr : ProtocolSetupWF r) (hS : SemReady interp' r S)
    (hsim : PqTurnSim1A interp' P r t t_clean accepted)
    (hXlate : XlateInvSpecB) :
    ∀ {leaks evs : List CliEvent} {ss₀ : List Step} {vis₀ : List VisEntry},
      LeaksFrom r t leaks →
      SchedFits (callsOf evs) who ok →
      CliLiveAtCli interp' r S who ok t_clean accepted (flatEvents evs) →
      Explains interp' r S g₀ ss₀ vis₀ evs →
      ¬ ReadCollisionCli interp' r S g₀ ss₀ evs →
      ∃ ss vis, Explains interp' r S g₀ ss vis (evs ++ leaks) ∧
        ¬ ReadCollisionCli interp' r S g₀ ss (evs ++ leaks)
  | [], evs, ss₀, vis₀, _, _, _, hex₀, hnrc₀ => by
    rw [List.append_nil]; exact ⟨ss₀, vis₀, hex₀, hnrc₀⟩
  | e :: ls, evs, ss₀, vis₀, hleaks, hfit, hlive, hex₀, hnrc₀ => by
    obtain ⟨p, k, hk, rfl⟩ := hleaks e (List.mem_cons_self ..)
    obtain ⟨s, v, hex₁, hnrc₁⟩ :=
      single_leak_explains_snoc hr hS hsim hfit hlive hXlate hk hex₀ hnrc₀
    have hfit₁ : SchedFits (callsOf (evs ++ [.env (.leak p k)])) who ok := by
      simpa only [callsOf_append, callsOf, List.append_nil] using hfit
    have hleaks_one : LeaksFrom r t [.env (.leak p k)] := by
      intro x hx; rw [List.mem_singleton.mp hx]; exact ⟨p, k, hk, rfl⟩
    have hlive₁ := leak_old hr hsim hleaks_one hlive
    obtain ⟨ss, vis, hex₂, hnrc₂⟩ :=
      leaks_explains hr hS hsim hXlate (fun x hx => hleaks x (List.mem_cons_of_mem _ hx))
        hfit₁ hlive₁ hex₁ hnrc₁
    refine ⟨ss, vis, ?_, ?_⟩
    · simpa only [List.append_assoc, List.singleton_append] using hex₂
    · simpa only [List.append_assoc, List.singleton_append] using hnrc₂

/-- Assuming `XlateInvSpecB`, guarded key-leak events (`LeaksFrom`) preserve `UAInvB`. -/
theorem leak_ua_of_xlate (hXlate : XlateInvSpecB) : UALeakSpecB := by
  intro interp P r _ _ hr t t_clean accepted evs leaks who ok hsim hleaks hfit hinv
  rcases hinv with hcol | ⟨hlive, hap, ⟨g₀, ss₀, vis₀, hex₀, hnrc₀⟩⟩
  · exact Or.inl (collisionAtCli_append leaks hcol)
  · refine Or.inr ⟨leak_old hr hsim hleaks hlive, aliceRecordPendingInSession_leaks hr hleaks hap, ?_⟩
    obtain ⟨ss, vis, hex, hnrc⟩ :=
      leaks_explains hr (compSemOf_ready _ r hr) hsim hXlate hleaks hfit hlive hex₀ hnrc₀
    exact ⟨g₀, ss, vis, hex, hnrc⟩

end Symbolic.Proofs.Swarm.UA.BI.RAB.Leak

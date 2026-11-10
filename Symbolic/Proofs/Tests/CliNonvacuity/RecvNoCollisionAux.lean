/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Specifications.Refinement.TraceExplanation
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.UA.XlateSteps
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Pre-Key `¬ KnownBaseKeyOn` Helper Before Any `recv` Run

Proves that under every CLI prefix explanation `Explains interp r S g ss vis evs₁` of a prefix
`evs₁` containing no `.recv` run events (`evs₁.all noRecvEvent = true`), no `PQXDHEvent.BobDone`
event occurs in `runTrace r ss`, so `bobDoneBaseKeys (runTrace r ss) = []` and
`¬ KnownBaseKeyOn interp S g (runTrace r ss) p` holds across all `(g, ss, vis)`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollisionAux

cref_hide_foreign_instances
open DY
open DY.Libsignal.Composed (ComposedEvent)
open scoped DY.Libsignal.Composed
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (CliEvent)
open DY.Libsignal.PQXDH (PQXDHEvent)
open DY.Libsignal.TripleRatchet (TREvent TRState)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry PreKeyFields BundlePreKeyIds
   ProtocolSetupWF KnownBaseKeyOn EnvMatches RunMatches MatchesEventsAt MatchesEvents Explains
   setupTrace runSteps runTrace bobDoneBaseKeys)
open Symbolic.Proofs.Swarm.UA.XlateSteps
  (stepIn_next invisible_eq_network)
open Symbolic.Swarm.CREF.XplSteps
  (XQuiet xquiet_of_fix xquiet_aliceHandshake xquiet_genRand xquiet_sendMessage
   xfix_getKey xfix_receiveMessage xfix_getLocalState xfix_getEntry xfix_guard
   xfix_traceLength xfix_guardOnTrace xfix_guardTrace xfix_pure xfix_failure
   xat?_le_eq xlt_of_at?_some)

def noRecvEvent : CliEvent → Bool
  | .run ev => match ev.cmd with | .recv _ => false | _ => true
  | .env _ => true

theorem not_knownBaseKeyOn_of_bobDoneBaseKeys_nil {interp : ExternInterpretation}
    {S : OpaqueSymbolSemantics} {g : Ghost} {tr : ExecTrace} {p : PreKeyFields}
    (hnil : bobDoneBaseKeys tr = []) :
    ¬ KnownBaseKeyOn interp S g tr p := by
  rintro ⟨ek, hek, _⟩
  rw [hnil] at hek
  cases hek

private abbrev PQEventEntry := DY.ProtocolEvent.ExecEntryT PQXDHEvent

private def isBobDoneEv : PQXDHEvent → Bool
  | .BobDone .. => true
  | _ => false

private def NoBobDone (tr : ExecTrace) : Prop :=
  ∀ (i : Nat) (e : PQEventEntry), tr.at? i = some e → isBobDoneEv e.ev = false

private def NoBobDonePres {α : Type} (act : DY.Traceful α) : Prop :=
  ∀ tr : ExecTrace, NoBobDone tr → NoBobDone (act.run tr).2.val

private theorem at?_append_pq_cases {E : Type} [DY.ExecTraceTypes.Has E]
    {tr : ExecTrace} {x : E} {i : Nat} {res : PQEventEntry}
    (h : ((tr.append x).at? i : Option PQEventEntry) = some res) :
    (tr.at? i : Option PQEventEntry) = some res ∨
      (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj x : ExecTrace.Entry) : Option PQEventEntry) =
        some res := by
  by_cases hlt : i < tr.length
  · left
    rw [← Symbolic.Swarm.CREF.TR.at?_append_of_lt tr x hlt]
    exact h
  · by_cases heq : i = tr.length
    · right
      rw [← Symbolic.Swarm.CREF.TR.at?_append_eq_of_proj tr x heq _ rfl]
      exact h
    · exfalso
      have hi_lt : i < (tr.append x).length := xlt_of_at?_some h
      have hlen : (tr.append x).length = tr.length + 1 := by
        rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
      omega

private theorem noBobDone_nil : NoBobDone DY.Trace.nil := by
  intro _ _ h
  simp only [DY.Trace.at?, Symbolic.DYBridge.DY.Trace.nil_length_not_lt,
    ↓reduceDIte, reduceCtorEq] at h

private theorem noBobDone_append_nonPQ {E : Type} [DY.ExecTraceTypes.Has E]
    {tr : ExecTrace} {x : E} (htr : NoBobDone tr)
    (hproj : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj x : ExecTrace.Entry) :
      Option PQEventEntry) = none) :
    NoBobDone (tr.append x) := by
  intro i e h
  rcases at?_append_pq_cases h with h1 | h2
  · exact htr i e h1
  · rw [hproj] at h2; cases h2

private theorem noBobDone_append_pq {tr : ExecTrace} {ev : PQXDHEvent}
    (htr : NoBobDone tr) (hbad : isBobDoneEv ev = false) :
    NoBobDone (tr.append (Symbolic.Swarm.CREF.TR.EvE ev)) := by
  intro i e h
  rcases at?_append_pq_cases h with h1 | h2
  · exact htr i e h1
  · rw [Symbolic.Swarm.CREF.TR.proj_inj_eq] at h2
    cases h2
    exact hbad

private theorem noBobDone_setupTrace (r : ProtocolSetup) (hNe : r.alice ≠ r.bob) :
    NoBobDone (setupTrace r) := by
  have h1 : NoBobDone (Symbolic.Swarm.CREF.TR.setupTr1 r.alice) := by
    unfold Symbolic.Swarm.CREF.TR.setupTr1
    exact noBobDone_append_nonPQ
      (noBobDone_append_nonPQ
        (noBobDone_append_nonPQ
          (noBobDone_append_pq
            (noBobDone_append_nonPQ noBobDone_nil rfl) rfl) rfl) rfl) rfl
  have h2 : NoBobDone (Symbolic.Swarm.CREF.TR.setupTr2 r.alice r.bob) := by
    unfold Symbolic.Swarm.CREF.TR.setupTr2
    exact noBobDone_append_nonPQ
      (noBobDone_append_nonPQ
        (noBobDone_append_nonPQ
          (noBobDone_append_pq
            (noBobDone_append_nonPQ h1 rfl) rfl) rfl) rfl) rfl
  have h3 : NoBobDone (Symbolic.Swarm.CREF.TR.setupTr3 r.alice r.bob) := by
    unfold Symbolic.Swarm.CREF.TR.setupTr3
    exact noBobDone_append_nonPQ
      (noBobDone_append_nonPQ
        (noBobDone_append_nonPQ
          (noBobDone_append_pq
            (noBobDone_append_nonPQ
              (noBobDone_append_nonPQ h2 rfl) rfl) rfl) rfl) rfl) rfl
  have h4 : NoBobDone (Symbolic.Swarm.CREF.TR.setupTr4 r.alice r.bob) := by
    unfold Symbolic.Swarm.CREF.TR.setupTr4
    exact noBobDone_append_nonPQ
      (noBobDone_append_nonPQ
        (noBobDone_append_nonPQ
          (noBobDone_append_pq
            (noBobDone_append_nonPQ
              (noBobDone_append_nonPQ h3 rfl) rfl) rfl) rfl) rfl) rfl
  have h5 : NoBobDone (Symbolic.Swarm.CREF.TR.setupTr5 r.alice r.bob) := by
    unfold Symbolic.Swarm.CREF.TR.setupTr5
    exact noBobDone_append_nonPQ
      (noBobDone_append_nonPQ
        (noBobDone_append_pq
          (noBobDone_append_nonPQ h4 rfl) rfl) rfl) rfl
  rw [Symbolic.Swarm.CREF.TR.setupTrace_eq r hNe]
  cases r.withOpk
  · exact h4
  · exact h5

private theorem noBobDonePres_bind {α β : Type} {f : DY.Traceful α} {g : α → DY.Traceful β}
    (hf : NoBobDonePres f) (hg : ∀ a, NoBobDonePres (g a)) :
    NoBobDonePres (f >>= g) := by
  intro tr htr
  have hf' := hf tr htr
  rw [DY.Traceful.run_bind]
  rcases h : f.run tr with ⟨o, t, _⟩
  rw [h] at hf'
  cases o with
  | none => exact hf'
  | some a => exact hg a t hf'

private theorem noBobDonePres_of_quiet {α : Type} {f : DY.Traceful α}
    (hq : XQuiet f) : NoBobDonePres f := by
  intro tr htr i e he
  have hle : tr ≤ (f.run tr).2.val := (f.run tr).2.property
  by_cases hlt : i < tr.length
  · rw [xat?_le_eq hle hlt] at he
    exact htr i e he
  · have hge : tr.length ≤ i := Nat.le_of_not_lt hlt
    have hnone := (hq tr i hge).2.1
    rw [hnone] at he
    cases he

private theorem noBobDonePres_monadLiftOpt {α : Type} (x : DY.Err α) :
    NoBobDonePres (liftM x : DY.Traceful α) := by
  intro _ h
  cases (x : Option α) <;>
    (simp only [liftM, monadLift, MonadLift.monadLift, DY.Traceful.run_mk]; exact h)

private theorem noBobDonePres_requireTracePredicate (p : ExecTrace → Bool) :
    NoBobDonePres (DY.Libsignal.PQXDH.guardTrace p) := by
  intro _ h
  unfold DY.Libsignal.PQXDH.guardTrace
  simp only [DY.Traceful.run_mk]
  exact h

private theorem noBobDonePres_logEvent_pq (ev : PQXDHEvent)
    (hbad : isBobDoneEv ev = false) :
    NoBobDonePres (DY.ProtocolEvent.logEvent ev : DY.Traceful Unit) := by
  intro _ htr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_bind, DY.Traceful.run_mk, DY.Traceful.run_pure]
  exact noBobDone_append_pq htr hbad

private theorem noBobDonePres_logEvent_tr (ev : TREvent) :
    NoBobDonePres (DY.ProtocolEvent.logEvent ev : DY.Traceful Unit) := by
  intro _ htr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_bind, DY.Traceful.run_mk, DY.Traceful.run_pure]
  exact noBobDone_append_nonPQ htr rfl

private theorem noBobDonePres_logEvent_c (ev : ComposedEvent) :
    NoBobDonePres (DY.ProtocolEvent.logEvent ev : DY.Traceful Unit) := by
  intro _ htr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_bind, DY.Traceful.run_mk, DY.Traceful.run_pure]
  exact noBobDone_append_nonPQ htr rfl

private theorem noBobDonePres_storeLocalState (p : Participant) (st : TRState) :
    NoBobDonePres (DY.PersistentLocalState.storeLocalState p st) := by
  intro _ htr
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
  exact noBobDone_append_nonPQ htr rfl

private theorem noBobDonePres_logMessageKeyAndStore (me : Participant)
    (s : DY.Libsignal.TripleRatchet.SessionInfo) (dir : DY.Libsignal.TripleRatchet.KeyDir)
    (seed pqSalt : DY.Bytes) (n : UInt32) (r p : Nat) (st : TRState) :
    NoBobDonePres
      (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n r p st) := by
  unfold DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  exact noBobDonePres_bind (noBobDonePres_logEvent_tr _) fun _ =>
    noBobDonePres_storeLocalState _ _

local macro "xnbd_step" : tactic =>
  `(tactic| first
    | with_reducible refine noBobDonePres_bind ?_ fun _ => ?_
    | with_reducible refine noBobDonePres_logEvent_pq _ ?_
    | with_reducible exact noBobDonePres_logEvent_tr _
    | with_reducible exact noBobDonePres_logEvent_c _
    | with_reducible exact noBobDonePres_storeLocalState _ _
    | with_reducible exact noBobDonePres_logMessageKeyAndStore _ _ _ _ _ _ _ _ _
    | with_reducible exact noBobDonePres_of_quiet (xquiet_aliceHandshake _ _ _ _ _)
    | with_reducible exact noBobDonePres_of_quiet (xquiet_genRand _)
    | with_reducible exact noBobDonePres_of_quiet (xquiet_sendMessage _)
    | with_reducible exact noBobDonePres_of_quiet (xquiet_of_fix (xfix_getKey _ _ _))
    | with_reducible exact noBobDonePres_of_quiet (xquiet_of_fix (xfix_receiveMessage _))
    | with_reducible exact noBobDonePres_of_quiet (xquiet_of_fix (xfix_getLocalState _ _))
    | with_reducible exact noBobDonePres_of_quiet (xquiet_of_fix (xfix_getEntry _))
    | with_reducible exact noBobDonePres_of_quiet (xquiet_of_fix (xfix_guard _))
    | with_reducible exact noBobDonePres_of_quiet (xquiet_of_fix xfix_traceLength)
    | with_reducible exact noBobDonePres_of_quiet (xquiet_of_fix (xfix_guardOnTrace _))
    | with_reducible exact noBobDonePres_of_quiet (xquiet_of_fix (xfix_guardTrace _))
    | with_reducible exact noBobDonePres_of_quiet (xquiet_of_fix (xfix_pure _))
    | with_reducible exact noBobDonePres_of_quiet (xquiet_of_fix xfix_failure)
    | with_reducible exact noBobDonePres_monadLiftOpt _
    | with_reducible exact noBobDonePres_requireTracePredicate _
    | split)

private theorem noBobDone_network (msg : DY.Bytes) {tr : ExecTrace} (htr : NoBobDone tr) :
    NoBobDone ((Step.network msg).next tr) := by
  have heq : (Step.network msg).next tr = tr.append (⟨msg⟩ : DY.Network.ExecEntryT) := by
    refine (stepIn_next DY.Network.reachability msg tr).trans ?_
    dsimp only [DY.Network.reachability]
    simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
  rw [heq]
  exact noBobDone_append_nonPQ htr rfl

private theorem noBobDone_invisible :
    ∀ (pre : List Step) {tr : ExecTrace},
      (∀ x ∈ pre, x.cls = .invisible) → NoBobDone tr → NoBobDone (runSteps pre tr)
  | [], _, _, htr => htr
  | x :: xs, tr, hinv, htr => by
    obtain ⟨msg, rfl⟩ := invisible_eq_network (hinv x List.mem_cons_self)
    exact noBobDone_invisible xs (fun y hy => hinv y (List.mem_cons_of_mem _ hy))
      (noBobDone_network msg htr)

private theorem noBobDone_nonRecvParty {s : Step} {tr : ExecTrace}
    (htr : NoBobDone tr)
    {cmd : CryptoVerification.SignalSession.Cmd}
    (hcmd : (match cmd with | .recv _ => false | _ => true) = true)
    (hfits : s.FitsCmd cmd) :
    NoBobDone (s.next tr) := by
  cases cmd with
  | recv _ => cases hcmd
  | init _ _ =>
    cases s <;> try exact False.elim hfits
    rename_i a b i r h
    rw [show (Step.aliceStart a b i r h).next tr =
        ((DY.Libsignal.Composed.aliceStart a b i r h).run tr).2.val from
      stepIn_next DY.Libsignal.Composed.aliceStart.reachability (a, b, i, r, h) tr]
    refine (?_ : NoBobDonePres (DY.Libsignal.Composed.aliceStart a b i r h)) tr htr
    simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
    refine noBobDonePres_bind (noBobDonePres_of_quiet (xquiet_aliceHandshake _ _ _ _ _)) fun o => ?_
    refine noBobDonePres_bind (noBobDonePres_of_quiet (xquiet_genRand _)) fun dhsA => ?_
    dsimp only
    refine noBobDonePres_bind (noBobDonePres_of_quiet (xquiet_sendMessage _)) fun _ => ?_
    refine noBobDonePres_bind (noBobDonePres_of_quiet (xquiet_sendMessage _)) fun _ => ?_
    refine noBobDonePres_bind (noBobDonePres_of_quiet (xquiet_of_fix xfix_traceLength)) fun _ => ?_
    refine noBobDonePres_bind (noBobDonePres_logEvent_pq _ rfl) fun _ => ?_
    refine noBobDonePres_bind (noBobDonePres_logEvent_tr _) fun _ => ?_
    refine noBobDonePres_bind (noBobDonePres_logEvent_c _) fun _ => ?_
    exact noBobDonePres_storeLocalState _ _
  | send _ =>
    cases s <;> try exact False.elim hfits
    · rename_i me si cl pq
      rw [show (Step.messageEncrypt me si cl pq).next tr =
          ((DY.Libsignal.TripleRatchet.messageEncrypt me si cl pq).run tr).2.val from
        stepIn_next DY.Libsignal.TripleRatchet.messageEncrypt.reachability (me, si, cl, pq) tr]
      exact (by unfold DY.Libsignal.TripleRatchet.messageEncrypt; repeat' xnbd_step :
        NoBobDonePres (DY.Libsignal.TripleRatchet.messageEncrypt me si cl pq)) tr htr
    · rename_i me si
      rw [show (Step.messageEncryptAbort me si).next tr =
          ((DY.Libsignal.TripleRatchet.messageEncryptAbort me si).run tr).2.val from
        stepIn_next DY.Libsignal.TripleRatchet.messageEncryptAbort.reachability (me, si) tr]
      exact (by unfold DY.Libsignal.TripleRatchet.messageEncryptAbort; repeat' xnbd_step :
        NoBobDonePres (DY.Libsignal.TripleRatchet.messageEncryptAbort me si)) tr htr

private theorem noBobDone_envMatches {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {tr : ExecTrace} {s : Step}
    {ev : DY.Libsignal.HwEvents.EnvEvent} {vis : List VisEntry}
    (htr : NoBobDone tr) (hem : EnvMatches interp r S g tr s ev vis) :
    NoBobDone (s.next tr) := by
  cases ev with
  | registerCorrupt _ _ => exact False.elim hem
  | breakDH =>
    rcases hem with ⟨rfl, _⟩
    rw [show Step.breakDH.next tr = (DY.Libsignal.PQXDH.breakDH.run tr).2.val from
      stepIn_next DY.Libsignal.PQXDH.breakDH.reachability () tr]
    exact (by unfold DY.Libsignal.PQXDH.breakDH; repeat' xnbd_step; all_goals rfl :
      NoBobDonePres DY.Libsignal.PQXDH.breakDH) tr htr
  | breakKEM =>
    rcases hem with ⟨rfl, _⟩
    rw [show Step.breakKEM.next tr = (DY.Libsignal.PQXDH.breakKEM.run tr).2.val from
      stepIn_next DY.Libsignal.PQXDH.breakKEM.reachability () tr]
    exact (by unfold DY.Libsignal.PQXDH.breakKEM; repeat' xnbd_step; all_goals rfl :
      NoBobDonePres DY.Libsignal.PQXDH.breakKEM) tr htr
  | invertDH _ _ =>
    rcases hem with ⟨h, rfl, _⟩
    rw [show (Step.invertDH h).next tr = ((DY.Libsignal.PQXDH.invertDH h).run tr).2.val from
      stepIn_next DY.Libsignal.PQXDH.invertDH.reachability h tr]
    exact (by unfold DY.Libsignal.PQXDH.invertDH; repeat' xnbd_step :
      NoBobDonePres (DY.Libsignal.PQXDH.invertDH h)) tr htr
  | invertKEM _ _ =>
    rcases hem with ⟨h, rfl, _⟩
    rw [show (Step.invertKEM h).next tr = ((DY.Libsignal.PQXDH.invertKEM h).run tr).2.val from
      stepIn_next DY.Libsignal.PQXDH.invertKEM.reachability h tr]
    exact (by unfold DY.Libsignal.PQXDH.invertKEM; repeat' xnbd_step :
      NoBobDonePres (DY.Libsignal.PQXDH.invertKEM h)) tr htr
  | leak _ _ =>
    have hleak : s.IsLeak := hem.2.1
    cases s <;> try exact False.elim hleak
    · rename_i me si k
      rw [show (Step.exposeKey me si k).next tr =
          ((DY.Libsignal.TripleRatchet.exposeKey me si k).run tr).2.val from
        stepIn_next DY.Libsignal.TripleRatchet.exposeKey.reachability (me, si, k) tr]
      exact (by unfold DY.Libsignal.TripleRatchet.exposeKey; repeat' xnbd_step :
        NoBobDonePres (DY.Libsignal.TripleRatchet.exposeKey me si k)) tr htr
    · rename_i me si
      rw [show (Step.exposeSpqr me si).next tr =
          ((DY.Libsignal.TripleRatchet.exposeSpqr me si).run tr).2.val from
        stepIn_next DY.Libsignal.TripleRatchet.exposeSpqr.reachability (me, si) tr]
      exact (by unfold DY.Libsignal.TripleRatchet.exposeSpqr; repeat' xnbd_step :
        NoBobDonePres (DY.Libsignal.TripleRatchet.exposeSpqr me si)) tr htr
    · rename_i sk
      rw [show (Step.exposeSkipped sk).next tr =
          ((DY.Libsignal.TripleRatchet.exposeSkipped sk).run tr).2.val from
        stepIn_next DY.Libsignal.TripleRatchet.exposeSkipped.reachability sk tr]
      exact (by unfold DY.Libsignal.TripleRatchet.exposeSkipped; repeat' xnbd_step :
        NoBobDonePres (DY.Libsignal.TripleRatchet.exposeSkipped sk)) tr htr
    · rename_i p si
      rw [show (Step.compromiseIK p si).next tr =
          ((DY.Libsignal.PQXDH.compromiseIK p si).run tr).2.val from
        stepIn_next DY.Libsignal.PQXDH.compromiseIK.reachability (p, si) tr]
      refine (?_ : NoBobDonePres (DY.Libsignal.PQXDH.compromiseIK p si)) tr htr
      unfold DY.Libsignal.PQXDH.compromiseIK
      exact noBobDonePres_bind (noBobDonePres_of_quiet (xquiet_of_fix (xfix_getKey _ _ _))) fun _ =>
        noBobDonePres_bind (noBobDonePres_logEvent_pq _ rfl) fun _ =>
          noBobDonePres_of_quiet (xquiet_sendMessage _)
    · rename_i b si
      rw [show (Step.compromiseSPK b si).next tr =
          ((DY.Libsignal.PQXDH.compromiseSPK b si).run tr).2.val from
        stepIn_next DY.Libsignal.PQXDH.compromiseSPK.reachability (b, si) tr]
      refine (?_ : NoBobDonePres (DY.Libsignal.PQXDH.compromiseSPK b si)) tr htr
      unfold DY.Libsignal.PQXDH.compromiseSPK
      exact noBobDonePres_bind (noBobDonePres_of_quiet (xquiet_of_fix (xfix_getKey _ _ _))) fun _ =>
        noBobDonePres_bind (noBobDonePres_logEvent_pq _ rfl) fun _ =>
          noBobDonePres_of_quiet (xquiet_sendMessage _)
    · rename_i b si
      rw [show (Step.compromisePQSPK b si).next tr =
          ((DY.Libsignal.PQXDH.compromisePQSPK b si).run tr).2.val from
        stepIn_next DY.Libsignal.PQXDH.compromisePQSPK.reachability (b, si) tr]
      refine (?_ : NoBobDonePres (DY.Libsignal.PQXDH.compromisePQSPK b si)) tr htr
      unfold DY.Libsignal.PQXDH.compromisePQSPK
      exact noBobDonePres_bind (noBobDonePres_of_quiet (xquiet_of_fix (xfix_getKey _ _ _))) fun _ =>
        noBobDonePres_bind (noBobDonePres_logEvent_pq _ rfl) fun _ =>
          noBobDonePres_of_quiet (xquiet_sendMessage _)
    · rename_i b si
      rw [show (Step.compromiseOPK b si).next tr =
          ((DY.Libsignal.PQXDH.compromiseOPK b si).run tr).2.val from
        stepIn_next DY.Libsignal.PQXDH.compromiseOPK.reachability (b, si) tr]
      refine (?_ : NoBobDonePres (DY.Libsignal.PQXDH.compromiseOPK b si)) tr htr
      unfold DY.Libsignal.PQXDH.compromiseOPK
      exact noBobDonePres_bind (noBobDonePres_of_quiet (xquiet_of_fix (xfix_getKey _ _ _))) fun _ =>
        noBobDonePres_bind (noBobDonePres_of_quiet (xquiet_of_fix (xfix_guardOnTrace _))) fun _ =>
          noBobDonePres_bind (noBobDonePres_logEvent_pq _ rfl) fun _ =>
            noBobDonePres_of_quiet (xquiet_sendMessage _)

private theorem runSteps_append :
    ∀ (xs ys : List Step) (tr : ExecTrace),
      runSteps (xs ++ ys) tr = runSteps ys (runSteps xs tr)
  | [], _, _ => rfl
  | x :: xs, ys, tr => runSteps_append xs ys (x.next tr)

private theorem noBobDone_matchesEvents {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {initIds : Option BundlePreKeyIds}
    {tr : ExecTrace} {ss : List Step}
    {evs : List CliEvent} {vis : List VisEntry}
    (hMe : MatchesEventsAt interp r S g initIds tr ss evs vis)
    (hNoRecv : evs.all noRecvEvent = true)
    (htr : NoBobDone tr) :
    NoBobDone (runSteps ss tr) := by
  induction hMe with
  | nil hinv => exact noBobDone_invisible _ hinv htr
  | run0 hinv _ _ ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hNoRecv
    rw [runSteps_append]
    exact ih hNoRecv.2 (noBobDone_invisible _ hinv htr)
  | run1 hinv hrm _ ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hNoRecv
    rw [runSteps_append]
    exact ih hNoRecv.2
      (noBobDone_nonRecvParty (noBobDone_invisible _ hinv htr) hNoRecv.1 hrm.2.2.1)
  | env hinv hem _ ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hNoRecv
    rw [runSteps_append]
    exact ih hNoRecv.2 (noBobDone_envMatches (noBobDone_invisible _ hinv htr) hem)

private theorem bobDoneBaseKeys_eq_nil_of_noBobDone {tr : ExecTrace} (htr : NoBobDone tr) :
    bobDoneBaseKeys tr = [] := by
  unfold bobDoneBaseKeys
  rw [List.filterMap_eq_nil_iff]
  intro i _
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
  cases h : (tr.at? i : Option PQEventEntry) with
  | none => rfl
  | some e =>
    have hbad := htr i e h
    rcases e with ⟨ev⟩
    cases ev <;> simp [isBobDoneEv] at hbad ⊢

/-- Under every prefix explanation `Explains interp r S g ss vis evs₁` of a CLI prefix `evs₁`
containing no `.recv` run events (`evs₁.all noRecvEvent = true`),
`bobDoneBaseKeys (runTrace r ss) = []`. -/
theorem bobDoneBaseKeys_eq_nil_of_no_recv {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry} {evs₁ : List CliEvent}
    (hwf : ProtocolSetupWF r)
    (hExp : Explains interp r S g ss vis evs₁)
    (hNoRecv : evs₁.all noRecvEvent = true := by decide) :
    bobDoneBaseKeys (runTrace r ss) = [] :=
  bobDoneBaseKeys_eq_nil_of_noBobDone
    (noBobDone_matchesEvents hExp.2.2.2 hNoRecv (noBobDone_setupTrace r hwf.1))

/-- Discharges `¬ KnownBaseKeyOn interp S g (runTrace r ss) p` for every `(g, ss, vis)` explaining
a prefix `evs₁` that contains no `.recv` run event. -/
theorem not_knownBaseKeyOn_of_no_recv {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry} {evs₁ : List CliEvent} {p : PreKeyFields}
    (hwf : ProtocolSetupWF r)
    (hExp : Explains interp r S g ss vis evs₁)
    (hNoRecv : evs₁.all noRecvEvent = true := by decide) :
    ¬ KnownBaseKeyOn interp S g (runTrace r ss) p :=
  not_knownBaseKeyOn_of_bobDoneBaseKeys_nil (bobDoneBaseKeys_eq_nil_of_no_recv hwf hExp hNoRecv)

end Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollisionAux

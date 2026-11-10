/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyTR
public import Symbolic.Proofs.Swarm.CREF.Initiate.InitOk35Pure
import all DY.Trace.Basic
import all DY.Trace.Monad
import all DY.Trace.Manipulation
import all DY.Actions.Network
import all DY.Actions.PersistentLocalState
import all DY.Actions.PersistentGlobalState
import all DY.Actions.ProtocolEvent
import all DY.Actions.Random
public import Symbolic.Proofs.Swarm.UA.Defs
public import Symbolic.Proofs.Swarm.UA.PendingPreKey
import Symbolic.Proofs.Swarm.COMPOSED.CompTermAlgebra
import Symbolic.Proofs.Swarm.UA.BI.RAB.Base
import Symbolic.Proofs.Swarm.UA.Base

/-!
# Pending PreKey Session Invariants under Break and Invert Events

Proves `HandshakeSessionValid` on reachable traces, `pendingPreKey` monotonicity, and preservation
of `AlicePendingKeysOn` and `AliceRecordPendingInSession` across non-handshake steps including
environment compromise and inversion events.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.BI.G.PendingPreKey

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant ExecTrace Trace Traceful ExecTraceTypes)
open _root_.DY.Concat (concat)
open _root_.DY.DiffieHellman (dhPk)
open _root_.DY.PQKem (kemPk)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (RunEvent EnvEvent CliEvent)
open _root_.DY.Libsignal.PQXDH (PQXDHEvent PQXDHState BundleHandles BobKeyHandles
  PreKeyMsgHandles AliceHandshakeOut)
open _root_.DY.Libsignal.TripleRatchet (TRState TREvent SessionInfo isCurrentSnapshot)
open _root_.DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open _root_.DY.Libsignal.Composed (ComposedEvent reachability )
open _root_.DY.Libsignal.Composed.Refinement (ProtocolSetup ProtocolSetupWF OpaqueSymbolSemantics Ghost Step VisEntry
  BundlePreKeyIds stepBundleIds activeBundleIds
  randTerm pendingPreKey runSteps runTrace StepsWF ModelRunWF MatchesEventsAt MatchesEvents RunMatches EnvMatches
  preKeyRepresentationsOn parsePreKeyWire ecKey kyberKey gamma)
open _root_.DY.Libsignal.Composed.Refinement.Cli (ReadCollisionCli)
open CryptoGames.LibsignalSessionApi (Session PendingPreKey PendingKyberPreKey)
open Symbolic.Swarm.CREF (NewBobSinfo BkNew BkTraceful RoleSnapshots RoleStE
  bks_getEventAt_of_le bks_lt_length_of_at? bks_lt_length_of_getEventAt
  bks_getLocalState_of_stored bks_stored_of_getLocalState
  isCurrentSnapshot_of_le_of_lt isCurrentSnapshot_false_of_later
  newBobSinfo_refl newBobSinfo_trans newBobSinfo_of_bkNew
  bkNew_refl bkNew_append_non_st bkNew_append_st_ne
  bkNew_messageEncrypt bkNew_messageEncryptAbort bkNew_messageDecrypt bkNew_messageDecryptSkipped
  iniAliceStartState iniAliceStartTr)
open Symbolic.Swarm.CREF.TR.Pure (slots_RecordCanonical_Q slots_NonEmptyV1Q)
open Symbolic.Swarm.COMPOSED.CompTrace (TRStEntry PQXDHEntry NetE RndE CEvE CEntry Preserves
  at?_le_some composed_reachable_induction bind_aliceHandshake_at bind_bobHandshake_at
  aliceOut NetMsgAt mkRand_inj)
open Symbolic.Swarm.COMPOSED.CompTermAlgebra (concat_inj dhPk_inj)
open Symbolic.Proofs.Swarm.UA.Defs (AlicePendingKeysOn AliceNotPendingOn AliceRecordPendingInSession)

attribute [local instance 2000]
  _root_.DY.Libsignal.Composed.instBytesFunctor_symbolic _root_.DY.Libsignal.Composed.instBytesLength_symbolic
  _root_.DY.Libsignal.Composed.instAttackerKnowledge_symbolic _root_.DY.Libsignal.Composed.instExecTraceTypes_symbolic
  _root_.DY.Libsignal.Composed.instBaseAttackerKnowledge_symbolic _root_.DY.Libsignal.Composed.instHasExecBytes
  _root_.DY.Libsignal.Composed.instHasExecEntryT _root_.DY.Libsignal.Composed.instHasExecEntryTBaseAttackerKnowledge
  _root_.DY.Libsignal.Composed.instHasExecTrace _root_.DY.Libsignal.Composed.instHasSubF
  _root_.DY.Libsignal.Composed.instHasSubFAttackerKnowledge _root_.DY.Libsignal.Composed.instHasSubFLength
  _root_.DY.Libsignal.Composed.HasExecBytes.toPQXDHExecBytes _root_.DY.Libsignal.Composed.toTripleRatchet
  _root_.DY.Libsignal.Composed.toPQXDHSpqr

/-! ## Re-exported Pure Trace Lemmas -/

export Symbolic.Proofs.Swarm.UA.PendingPreKey
  (HandshakeSessionValid handshakeSessionValid_nil handshakeSessionValid_reachable stepsWF_reachable stepsWF_le)
export Symbolic.Proofs.Swarm.UA.PendingPreKey
  (modelRunWF_reachable ppkOf NoNewHsFrom NoNewRecvMKFrom pendingPreKey_eq_ppkOf)
export Symbolic.Proofs.Swarm.UA.PendingPreKey
  (ppkOf_eq_none_of_initiator_false pendingPreKey_eq_none_of_initiator_false
   sessionHasDecrypted_of_le sessionHasDecrypted_mono_true sessionHasDecrypted_eq_false_of_current_and_noRecv)
export Symbolic.Proofs.Swarm.UA.PendingPreKey
  (ppkOf_mono ppkOf_eq_of_noHs pendingPreKey_mono pendingPreKey_eq_of_sinfo bkNew_step)

/-! ## Pending Key Transport -/

export Symbolic.Proofs.Swarm.UA.PendingPreKey
  (alicePendingKeysOn_ext aliceNotPendingOn_ext StepNoStartFor StepNoAliceInitOrRecv stepNoStartFor_of_invisible)
export Symbolic.Proofs.Swarm.UA.PendingPreKey
  (stepNoStartFor_of_leak stepNoAliceInitOrRecv_of_invisible stepNoAliceInitOrRecv_of_leak noNewHs_step noNewRecvMK_step)
export Symbolic.Proofs.Swarm.UA.PendingPreKey
  (noNewHs_runSteps noNewRecvMK_runSteps newBobSinfo_step_ua newBobSinfo_runSteps_ua aliceRecordPendingInSession_of_no_record)
export Symbolic.Proofs.Swarm.UA.PendingPreKey
  (aliceRecordPendingInSession_of_not_pending trSt_iniAliceStartTr pendingPreKey_iniAliceStartTr
   alicePendingKeysOn_start alicePendingKeysOn_iniAliceStartTr)
export Symbolic.Proofs.Swarm.UA.PendingPreKey
  (aliceStart_ok_eq_iniAliceStartTr)

theorem stepNoStartFor_of_envMatches {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {tr : ExecTrace} {s : Step} {ev : EnvEvent} {vis : List VisEntry}
    {alice : Participant} (hem : EnvMatches interp' r S g tr s ev vis) :
    StepNoStartFor alice s := by
  cases ev with
  | leak _ _ => exact stepNoStartFor_of_leak hem.2.1
  | breakDH =>
    rcases hem with ⟨rfl, -⟩
    exact And.intro (fun _ _ _ _ h => nomatch h) (fun _ _ _ _ _ _ h => nomatch h)
  | breakKEM =>
    rcases hem with ⟨rfl, -⟩
    exact And.intro (fun _ _ _ _ h => nomatch h) (fun _ _ _ _ _ _ h => nomatch h)
  | invertDH _ _ =>
    rcases hem with ⟨_, rfl, -⟩
    exact And.intro (fun _ _ _ _ h => nomatch h) (fun _ _ _ _ _ _ h => nomatch h)
  | invertKEM _ _ =>
    rcases hem with ⟨_, rfl, -⟩
    exact And.intro (fun _ _ _ _ h => nomatch h) (fun _ _ _ _ _ _ h => nomatch h)
  | registerCorrupt _ _ => exact hem.elim

theorem stepNoAliceInitOrRecv_of_envMatches {interp' : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {tr : ExecTrace} {s : Step} {ev : EnvEvent}
    {vis : List VisEntry} {alice : Participant} (hem : EnvMatches interp' r S g tr s ev vis) :
    StepNoAliceInitOrRecv alice s := by
  refine And.intro (stepNoStartFor_of_envMatches hem) ?_
  cases ev with
  | leak _ _ => exact (stepNoAliceInitOrRecv_of_leak hem.2.1).2
  | breakDH =>
    rcases hem with ⟨rfl, -⟩
    exact And.intro (fun _ _ _ _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
  | breakKEM =>
    rcases hem with ⟨rfl, -⟩
    exact And.intro (fun _ _ _ _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
  | invertDH _ _ =>
    rcases hem with ⟨_, rfl, -⟩
    exact And.intro (fun _ _ _ _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
  | invertKEM _ _ =>
    rcases hem with ⟨_, rfl, -⟩
    exact And.intro (fun _ _ _ _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
  | registerCorrupt _ _ => exact hem.elim

/-- A `MatchesEventsAt` suffix whose run events are never `init` and whose Alice `recv` runs have a
whisper-tagged input contains no `aliceStart r.alice ..` or `bobStart r.alice ..`. -/
theorem matchesEvents_noStart_alice {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} (hwf : ProtocolSetupWF r) :
    ∀ {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {ss : List Step} {evs : List CliEvent} {vis : List VisEntry},
      MatchesEventsAt interp' r S g initIds tr ss evs vis →
      (∀ ev, .run ev ∈ evs →
        (∀ p d, ev.cmd ≠ .init p d) ∧
        (ev.party = r.alice → ∀ p, ev.cmd = .recv p → ev.input.head? = some wireWhisperTag)) →
      ∀ s ∈ ss, StepNoStartFor r.alice s
  | _, _, _, _, _, .nil hinv, _, s, hs => stepNoStartFor_of_invisible (hinv s hs)
  | _, _, _, _, _, .run0 hpre _ hrest, hevs, s, hs => by
    rcases List.mem_append.mp hs with hsp | hsr
    · exact stepNoStartFor_of_invisible (hpre s hsp)
    · exact matchesEvents_noStart_alice hwf hrest
        (fun ev hev => hevs ev (List.mem_cons_of_mem _ hev)) s hsr
  | _, _, _, _, _, @MatchesEventsAt.env _ _ _ _ _ _ pre s₀ ss' _ _ _ _ hpre hem hrest, hevs, s, hs => by
    rcases List.mem_append.mp hs with hsp | hsr
    · exact stepNoStartFor_of_invisible (hpre s hsp)
    · rcases List.mem_cons.mp hsr with rfl | hst
      · exact stepNoStartFor_of_envMatches hem
      · exact matchesEvents_noStart_alice hwf hrest
          (fun ev hev => hevs ev (List.mem_cons_of_mem _ hev)) s hst
  | _, _, _, _, _, @MatchesEventsAt.run1 _ _ _ _ _ _ pre s₀ ss' ev _ _ _ hpre hrm hrest, hevs, s, hs => by
    rcases List.mem_append.mp hs with hsp | hsr
    · exact stepNoStartFor_of_invisible (hpre s hsp)
    · rcases List.mem_cons.mp hsr with rfl | hst
      · obtain ⟨hno_init, hwhisper⟩ := hevs ev List.mem_cons_self
        obtain ⟨_, hparty, hfits, _, hok, _, hvis, inp, drs, outs, hvis_eq, hbme, _, _, _, _⟩ := hrm
        refine ⟨fun b idIdx regB bh heq => ?_, fun a kh regA mh pqIdx spqrIdx heq => ?_⟩
        · subst heq
          cases hcmd : ev.cmd with
          | init p d => exact hno_init p d hcmd
          | send _ | recv _ => rw [hcmd] at hfits; cases hfits
        · subst heq
          simp only [Step.party?, Option.some.injEq] at hparty
          cases hcmd : ev.cmd with
          | init p d => exact hno_init p d hcmd
          | send _ => rw [hcmd] at hfits; cases hfits
          | recv p =>
            have hhead := hwhisper hparty.symm p hcmd
            rw [hvis] at hvis_eq
            unfold _root_.DY.Libsignal.Composed.Refinement.stepView at hvis_eq
            rw [hok] at hvis_eq
            simp only [↓reduceIte, _root_.DY.Libsignal.Composed.Refinement.bobVis,
              List.cons_append, List.cons.injEq] at hvis_eq
            rw [← hvis_eq.1] at hbme
            have hp_some : ∃ q, parsePreKeyWire ev.input = some q := by
              have hprm := hbme.2
              dsimp only [_root_.DY.Libsignal.Composed.Refinement.PreKeyRecvOpkMatches] at hprm
              split at hprm
              · obtain ⟨⟨q, hq, _⟩, _⟩ := hprm; exact ⟨q, hq⟩
              · obtain ⟨⟨q, hq, _⟩, _⟩ := hprm; exact ⟨q, hq⟩
              · exact hprm.elim
            obtain ⟨q, hq⟩ := hp_some
            unfold parsePreKeyWire at hq
            rcases hinp : ev.input with _ | ⟨hd, tl⟩
            · simp [hinp] at hhead
            · simp only [hinp, List.head?_cons, Option.some.injEq] at hhead
              subst hhead; rw [hinp] at hq
              have hne : wireWhisperTag ≠ _root_.DY.Libsignal.PQXDH.Refinement.wirePrekeyTag := by decide
              simp [hne] at hq
      · exact matchesEvents_noStart_alice hwf hrest
          (fun ev' hev' => hevs ev' (List.mem_cons_of_mem _ hev')) s hst

theorem matchesEvents_noAliceInitOrRecv {interp' : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} :
    ∀ {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {ss : List Step} {evs : List CliEvent} {vis : List VisEntry},
      MatchesEventsAt interp' r S g initIds tr ss evs vis →
      (∀ ev, .run ev ∈ evs →
        (∀ p d, ev.cmd ≠ .init p d) ∧
        (ev.party = r.alice → ∀ p out, ev.cmd = .recv p → ev.exit ≠ some (0, out))) →
      ∀ s ∈ ss, StepNoAliceInitOrRecv r.alice s
  | _, _, _, _, _, .nil hinv, _, s, hs => stepNoAliceInitOrRecv_of_invisible (hinv s hs)
  | _, _, _, _, _, .run0 hpre _ hrest, hevs, s, hs => by
    rcases List.mem_append.mp hs with hsp | hsr
    · exact stepNoAliceInitOrRecv_of_invisible (hpre s hsp)
    · exact matchesEvents_noAliceInitOrRecv hrest
        (fun ev hev => hevs ev (List.mem_cons_of_mem _ hev)) s hsr
  | _, _, _, _, _, @MatchesEventsAt.env _ _ _ _ _ _ pre s₀ ss' _ _ _ _ hpre hem hrest, hevs, s, hs => by
    rcases List.mem_append.mp hs with hsp | hsr
    · exact stepNoAliceInitOrRecv_of_invisible (hpre s hsp)
    · rcases List.mem_cons.mp hsr with rfl | hst
      · exact stepNoAliceInitOrRecv_of_envMatches hem
      · exact matchesEvents_noAliceInitOrRecv hrest
          (fun ev hev => hevs ev (List.mem_cons_of_mem _ hev)) s hst
  | _, _, _, _, _, @MatchesEventsAt.run1 _ _ _ _ _ _ pre s₀ ss' ev _ _ _ hpre hrm hrest, hevs, s, hs => by
    rcases List.mem_append.mp hs with hsp | hsr
    · exact stepNoAliceInitOrRecv_of_invisible (hpre s hsp)
    · rcases List.mem_cons.mp hsr with rfl | hst
      · obtain ⟨hno_init, hno_recv⟩ := hevs ev List.mem_cons_self
        obtain ⟨_, hparty, hfits, _, _, ⟨out, hexit⟩, _⟩ := hrm
        refine ⟨⟨fun b idIdx regB bh heq => ?_, fun a kh regA mh pqIdx spqrIdx heq => ?_⟩,
          fun stateIdx msgIdx pqIdx spqrIdx heq => ?_,
          fun stateIdx msgIdx k pqIdx spqrIdx heq => ?_⟩
        · subst heq
          cases hcmd : ev.cmd with
          | init p d => exact hno_init p d hcmd
          | send _ | recv _ => rw [hcmd] at hfits; cases hfits
        · subst heq
          simp only [Step.party?, Option.some.injEq] at hparty
          cases hcmd : ev.cmd with
          | init p d => exact hno_init p d hcmd
          | send _ => rw [hcmd] at hfits; cases hfits
          | recv p => exact hno_recv hparty.symm p out hcmd hexit
        · subst heq
          simp only [Step.party?, Option.some.injEq] at hparty
          cases hcmd : ev.cmd with
          | init p d => exact hno_init p d hcmd
          | send _ => rw [hcmd] at hfits; cases hfits
          | recv p => exact hno_recv hparty.symm p out hcmd hexit
        · subst heq
          simp only [Step.party?, Option.some.injEq] at hparty
          cases hcmd : ev.cmd with
          | init p d => exact hno_init p d hcmd
          | send _ => rw [hcmd] at hfits; cases hfits
          | recv p => exact hno_recv hparty.symm p out hcmd hexit
      · exact matchesEvents_noAliceInitOrRecv hrest
          (fun ev' hev' => hevs ev' (List.mem_cons_of_mem _ hev')) s hst

theorem matchesEventsAt_split {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} (more : List CliEvent) :
    ∀ (evs : List CliEvent) {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {ss : List Step} {vis : List VisEntry},
      MatchesEventsAt interp r S g initIds tr ss (evs ++ more) vis →
      ∃ ss₁ ss₂ vis₁ vis₂, ss = ss₁ ++ ss₂ ∧ vis = vis₁ ++ vis₂ ∧
        MatchesEventsAt interp r S g initIds tr ss₁ evs vis₁ ∧
        MatchesEventsAt interp r S g (evs.foldl stepBundleIds initIds) (runSteps ss₁ tr) ss₂ more vis₂
  | [], _, _, _, _, h => ⟨[], _, [], _, rfl, rfl, .nil (by simp), h⟩
  | e :: evs, initIds, tr, ss, vis, h => by
    rw [List.cons_append] at h
    generalize hE : e :: (evs ++ more) = E at h
    cases h with
    | nil _ => cases hE
    | @run1 _ _ pre s ss' ev _ v vs hpre hrm hrest =>
      injection hE with he hevs; subst he hevs
      obtain ⟨a, b, c, d, rfl, rfl, hm₁, hm₂⟩ := matchesEventsAt_split more evs hrest
      refine ⟨pre ++ s :: a, b, v ++ c, d, by simp, by simp, .run1 hpre hrm hm₁, ?_⟩
      simpa [Symbolic.Proofs.Swarm.UA.Base.runSteps_append, runSteps,
        Symbolic.Proofs.Swarm.UA.Base.stepBundleIds_run_of_runMatches hrm] using hm₂
    | @run0 _ _ pre ss' ev _ vs hpre hrej hrest =>
      injection hE with he hevs; subst he hevs
      obtain ⟨a, b, c, d, rfl, rfl, hm₁, hm₂⟩ := matchesEventsAt_split more evs hrest
      refine ⟨pre ++ a, b, c, d, by simp, rfl, .run0 hpre hrej hm₁, ?_⟩
      simpa [Symbolic.Proofs.Swarm.UA.Base.runSteps_append,
        Symbolic.Proofs.Swarm.UA.Base.stepBundleIds_run_of_runRejected hrej] using hm₂
    | @env _ _ pre s ss' ev _ v vs hpre hem hrest =>
      injection hE with he hevs; subst he hevs
      obtain ⟨a, b, c, d, rfl, rfl, hm₁, hm₂⟩ := matchesEventsAt_split more evs hrest
      refine ⟨pre ++ s :: a, b, v ++ c, d, by simp, by simp, .env hpre hem hm₁, ?_⟩
      simpa [Symbolic.Proofs.Swarm.UA.Base.runSteps_append, runSteps, stepBundleIds] using hm₂

theorem matchesEvents_split {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} (more : List CliEvent) (evs : List CliEvent)
    {tr : ExecTrace} {ss : List Step} {vis : List VisEntry}
    (h : MatchesEvents interp r S g tr ss (evs ++ more) vis) :
    ∃ ss₁ ss₂ vis₁ vis₂, ss = ss₁ ++ ss₂ ∧ vis = vis₁ ++ vis₂ ∧
      MatchesEvents interp r S g tr ss₁ evs vis₁ ∧
      MatchesEventsAt interp r S g (activeBundleIds evs) (runSteps ss₁ tr) ss₂ more vis₂ :=
  matchesEventsAt_split more evs h

theorem alicePendingKeysOn_of_matchesEvents {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {initIds : Option BundlePreKeyIds} {ss₁ ss₂ : List Step} {evs₂ : List CliEvent} {vis₂ : List VisEntry}
    {bk kct : HwBytes}
    (_hwf : ProtocolSetupWF r)
    (hrun : ModelRunWF r (ss₁ ++ ss₂))
    (hm : MatchesEventsAt interp' r S g initIds (runTrace r ss₁) ss₂ evs₂ vis₂)
    (hevs : ∀ ev, .run ev ∈ evs₂ →
      (∀ p d, ev.cmd ≠ .init p d) ∧
      (ev.party = r.alice → ∀ p out, ev.cmd = .recv p → ev.exit ≠ some (0, out)))
    (hap : AlicePendingKeysOn interp' S g r.alice (runTrace r ss₁) bk kct) :
    AlicePendingKeysOn interp' S g r.alice (runTrace r (ss₁ ++ ss₂)) bk kct := by
  have hReach₁ : (runTrace r ss₁).Reachable reachability :=
    modelRunWF_reachable (Symbolic.Proofs.Swarm.UA.Base.modelRunWF_of_append hrun)
  have hwf₂ : StepsWF ss₂ (runTrace r ss₁) := by
    let rec go (a b : List Step) (tr : ExecTrace) (h : StepsWF (a ++ b) tr) : StepsWF b (runSteps a tr) :=
      match a with
      | [] => h
      | x :: xs => go xs b (x.next tr) h.2.2
    exact go ss₁ ss₂ (_root_.DY.Libsignal.Composed.Refinement.setupTrace r) hrun.2.2.1
  have hno := matchesEvents_noAliceInitOrRecv hm hevs
  rw [Symbolic.Proofs.Swarm.UA.Base.runTrace_append]
  exact alicePendingKeysOn_ext (handshakeSessionValid_reachable hReach₁)
    (stepsWF_le ss₂ (runTrace r ss₁))
    (newBobSinfo_runSteps_ua ss₂ hReach₁ hwf₂ (fun s hs => (hno s hs).1))
    (noNewRecvMK_runSteps ss₂ ⟨Nat.le_refl _, fun _ h1 h2 => absurd h1 (Nat.not_le_of_gt h2)⟩ hno)
    hap

theorem aliceNotPendingOn_of_matchesEvents {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {initIds : Option BundlePreKeyIds} {ss₁ ss₂ : List Step} {evs₂ : List CliEvent} {vis₂ : List VisEntry}
    (hwf : ProtocolSetupWF r)
    (hrun : ModelRunWF r (ss₁ ++ ss₂))
    (hm : MatchesEventsAt interp' r S g initIds (runTrace r ss₁) ss₂ evs₂ vis₂)
    (hevs : ∀ ev, .run ev ∈ evs₂ →
      (∀ p d, ev.cmd ≠ .init p d) ∧
      (ev.party = r.alice → ∀ p, ev.cmd = .recv p → ev.input.head? = some wireWhisperTag))
    (hnp : AliceNotPendingOn r.alice (runTrace r ss₁)) :
    AliceNotPendingOn r.alice (runTrace r (ss₁ ++ ss₂)) := by
  have hReach₁ : (runTrace r ss₁).Reachable reachability :=
    modelRunWF_reachable (Symbolic.Proofs.Swarm.UA.Base.modelRunWF_of_append hrun)
  have hwf₂ : StepsWF ss₂ (runTrace r ss₁) := by
    let rec go (a b : List Step) (tr : ExecTrace) (h : StepsWF (a ++ b) tr) : StepsWF b (runSteps a tr) :=
      match a with
      | [] => h
      | x :: xs => go xs b (x.next tr) h.2.2
    exact go ss₁ ss₂ (_root_.DY.Libsignal.Composed.Refinement.setupTrace r) hrun.2.2.1
  have hno := matchesEvents_noStart_alice hwf hm hevs
  rw [Symbolic.Proofs.Swarm.UA.Base.runTrace_append]
  exact aliceNotPendingOn_ext (handshakeSessionValid_reachable hReach₁)
    (stepsWF_le ss₂ (runTrace r ss₁))
    (newBobSinfo_runSteps_ua ss₂ hReach₁ hwf₂ hno)
    (noNewHs_runSteps ss₂ ⟨Nat.le_refl _, fun _ h1 h2 => absurd h1 (Nat.not_le_of_gt h2)⟩ hno)
    hnp

theorem alicePendingKeysOn_of_explains_append {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {vis : List VisEntry} {evs₁ evs₂ : List CliEvent} {bk kct : HwBytes}
    (hwf : ProtocolSetupWF r)
    (hex : _root_.DY.Libsignal.Composed.Refinement.Explains interp' r S g ss vis (evs₁ ++ evs₂))
    (hnrc : ¬ ReadCollisionCli interp' r S g ss (evs₁ ++ evs₂))
    (hevs : ∀ ev, .run ev ∈ evs₂ →
      (∀ p d, ev.cmd ≠ .init p d) ∧
      (ev.party = r.alice → ∀ p out, ev.cmd = .recv p → ev.exit ≠ some (0, out)))
    (hpre : ∀ ss₁ vis₁,
      _root_.DY.Libsignal.Composed.Refinement.Explains interp' r S g ss₁ vis₁ evs₁ →
      ¬ ReadCollisionCli interp' r S g ss₁ evs₁ →
      AlicePendingKeysOn interp' S g r.alice (runTrace r ss₁) bk kct) :
    AlicePendingKeysOn interp' S g r.alice (runTrace r ss) bk kct := by
  obtain ⟨hc, hg, hrun, hm⟩ := hex
  obtain ⟨ss₁, ss₂, vis₁, vis₂, rfl, rfl, hm₁, hm₂⟩ := matchesEvents_split evs₂ evs₁ hm
  exact alicePendingKeysOn_of_matchesEvents hwf hrun hm₂ hevs
    (hpre ss₁ vis₁ ⟨hc, Symbolic.Proofs.Swarm.UA.Base.ghostWF_of_append hg,
      Symbolic.Proofs.Swarm.UA.Base.modelRunWF_of_append hrun, hm₁⟩
      (fun hrc => hnrc (Symbolic.Proofs.Swarm.UA.BI.RAB.Base.readCollisionCli_append ss₂ evs₂ hrc)))

theorem aliceNotPendingOn_of_explains_append {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {vis : List VisEntry} {evs₁ evs₂ : List CliEvent}
    (hwf : ProtocolSetupWF r)
    (hex : _root_.DY.Libsignal.Composed.Refinement.Explains interp' r S g ss vis (evs₁ ++ evs₂))
    (hnrc : ¬ ReadCollisionCli interp' r S g ss (evs₁ ++ evs₂))
    (hevs : ∀ ev, .run ev ∈ evs₂ →
      (∀ p d, ev.cmd ≠ .init p d) ∧
      (ev.party = r.alice → ∀ p, ev.cmd = .recv p → ev.input.head? = some wireWhisperTag))
    (hpre : ∀ ss₁ vis₁,
      _root_.DY.Libsignal.Composed.Refinement.Explains interp' r S g ss₁ vis₁ evs₁ →
      ¬ ReadCollisionCli interp' r S g ss₁ evs₁ →
      AliceNotPendingOn r.alice (runTrace r ss₁)) :
    AliceNotPendingOn r.alice (runTrace r ss) := by
  obtain ⟨hc, hg, hrun, hm⟩ := hex
  obtain ⟨ss₁, ss₂, vis₁, vis₂, rfl, rfl, hm₁, hm₂⟩ := matchesEvents_split evs₂ evs₁ hm
  exact aliceNotPendingOn_of_matchesEvents hwf hrun hm₂ hevs
    (hpre ss₁ vis₁ ⟨hc, Symbolic.Proofs.Swarm.UA.Base.ghostWF_of_append hg,
      Symbolic.Proofs.Swarm.UA.Base.modelRunWF_of_append hrun, hm₁⟩
      (fun hrc => hnrc (Symbolic.Proofs.Swarm.UA.BI.RAB.Base.readCollisionCli_append ss₂ evs₂ hrc)))

theorem aliceRecordPendingInSession_of_explains_append {interp' : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {vis : List VisEntry}
    {evs₁ evs₂ : List CliEvent} {records₁ records₂ : Participant → Option HwBytes}
    (hwf : ProtocolSetupWF r)
    (hex : _root_.DY.Libsignal.Composed.Refinement.Explains interp' r S g ss vis (evs₁ ++ evs₂))
    (hnrc : ¬ ReadCollisionCli interp' r S g ss (evs₁ ++ evs₂))
    (hevs : ∀ ev, .run ev ∈ evs₂ →
      (∀ p d, ev.cmd ≠ .init p d) ∧
      (ev.party = r.alice → ∀ p out, ev.cmd = .recv p → ev.exit ≠ some (0, out)))
    (hrec_eq : records₂ r.alice = records₁ r.alice)
    (hpre : ∀ ss₁ vis₁,
      _root_.DY.Libsignal.Composed.Refinement.Explains interp' r S g ss₁ vis₁ evs₁ →
      ¬ ReadCollisionCli interp' r S g ss₁ evs₁ →
      AliceRecordPendingInSession interp' r S g (runTrace r ss₁) records₁ (activeBundleIds evs₁)) :
    AliceRecordPendingInSession interp' r S g (runTrace r ss) records₂ (activeBundleIds (evs₁ ++ evs₂)) := by
  obtain ⟨hc, hg, hrun, hm⟩ := hex
  obtain ⟨ss₁, ss₂, vis₁, vis₂, rfl, rfl, hm₁, hm₂⟩ := matchesEvents_split evs₂ evs₁ hm
  have hex₁ : _root_.DY.Libsignal.Composed.Refinement.Explains interp' r S g ss₁ vis₁ evs₁ :=
    ⟨hc, Symbolic.Proofs.Swarm.UA.Base.ghostWF_of_append hg,
      Symbolic.Proofs.Swarm.UA.Base.modelRunWF_of_append hrun, hm₁⟩
  have hnrc₁ : ¬ ReadCollisionCli interp' r S g ss₁ evs₁ :=
    fun hrc => hnrc (Symbolic.Proofs.Swarm.UA.BI.RAB.Base.readCollisionCli_append ss₂ evs₂ hrc)
  have hap₁ := hpre ss₁ vis₁ hex₁ hnrc₁
  have habi : activeBundleIds (evs₁ ++ evs₂) = activeBundleIds evs₁ :=
    Symbolic.Proofs.Swarm.UA.Base.activeBundleIds_append_of_no_init fun ev hev => (hevs ev hev).1
  rw [habi]
  have hReach₁ : (runTrace r ss₁).Reachable reachability := modelRunWF_reachable hex₁.2.2.1
  have hwf₂ : StepsWF ss₂ (runTrace r ss₁) := by
    let rec go (a b : List Step) (tr : ExecTrace) (h : StepsWF (a ++ b) tr) : StepsWF b (runSteps a tr) :=
      match a with
      | [] => h
      | x :: xs => go xs b (x.next tr) h.2.2
    exact go ss₁ ss₂ (_root_.DY.Libsignal.Composed.Refinement.setupTrace r) hrun.2.2.1
  have hno := matchesEvents_noAliceInitOrRecv hm₂ hevs
  intro rec sess hrec₂ hcan
  rw [hrec_eq] at hrec₂
  obtain ⟨hsome₁, hnone₁⟩ := hap₁ rec sess hrec₂ hcan
  refine ⟨fun items kpk hp hk => ?_, fun hp_none => ?_⟩
  · obtain ⟨hids, hap_k⟩ := hsome₁ items kpk hp hk
    exact ⟨hids, alicePendingKeysOn_of_matchesEvents hwf hrun hm₂ hevs hap_k⟩
  · rw [Symbolic.Proofs.Swarm.UA.Base.runTrace_append]
    exact aliceNotPendingOn_ext (handshakeSessionValid_reachable hReach₁)
      (stepsWF_le ss₂ (runTrace r ss₁))
      (newBobSinfo_runSteps_ua ss₂ hReach₁ hwf₂ (fun s hs => (hno s hs).1))
      (noNewHs_runSteps ss₂ ⟨Nat.le_refl _, fun _ h1 h2 => absurd h1 (Nat.not_le_of_gt h2)⟩
        (fun s hs => (hno s hs).1))
      (hnone₁ hp_none)

end Symbolic.Proofs.Swarm.UA.BI.G.PendingPreKey

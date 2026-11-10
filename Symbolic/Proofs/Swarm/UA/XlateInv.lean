/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.UA.Defs
import Symbolic.Proofs.Swarm.CREF.Cli.World.LeakPure
import Symbolic.Proofs.Swarm.CREF.Cli.World.XplTransferPure
import Symbolic.Proofs.Swarm.UA.Base
import Symbolic.Proofs.Swarm.UA.XlateSteps

/-!
# Prefix Explanation Translation

Proves `xlate_inv : XlateInvSpec`: every clean `ExplainsClassical` prefix explanation of `evs`
translates to a clean `ExplainsCli` explanation of `flatEvents evs` with identical `Ghost`,
`runTrace`, `honestSalts`, `prefixTerms`, and `plaintextTerms`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.XlateInv

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant ExecTrace)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (MachineEvent RunEvent EnvEvent CliEvent)
open _root_.DY.Libsignal.Composed
open _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed.Refinement.Cli
open Symbolic.Swarm.CREF (SemReady)
open _root_.DY.Libsignal.TripleRatchet (parseTrSignalMsg)
open Symbolic.Proofs.Swarm.UA.Defs (XlateInvSpec runOk flatEntry flatExit failedSend
  flatEvent flatEvents callsOf SchedFits)
open Symbolic.Proofs.Swarm.UA.XlateSteps (
  VisSendPtEq visSendPtEq_refl visSendPtEq_append visSendPtEq_reject_nil
  ptAtoms_eq_of_visSendPtEq principalTerms_eq_of_visSendPtEq prefixTerms_eq_of_visSendPtEq
  memoCollisionOn_iff_of_terms recvRepresentations_eq preKeyRepresentations_eq
   recvBody_iff recvCollision_iff reselectCollision_iff bobStartCollision_iff
  stepIn_next stepIn_ok stepIn_pre step_reachable runSteps_reachable
  invisible_eq_network network_preCond attackerSend_next_eq_network
  eventMatchesEntry_pt_iff eventMatchesEntry_recv_iff eventMatchesEntry_rng_iff
  eventMatchesEntry_of_bytesMatchEntry eventMatchesEntry_accept_iff eventMatchesEntry_leak_iff
  pendingPreKey_handles_of_reachable encSend_some_eq_encSendEntry gamma_randTerm_eq
  exposures_kind encDraws_kind encSendEntry_kind encSend_kind
  run_bind_pure_isSome run_bind_pure_snd messageEncrypt_fail_not_ok aliceStart_ok_trOfOut
  bobStart_newRandoms_32 messageDecrypt_newRandoms_32 messageDecryptSkipped_newRandoms_32
  list_split_of_getElem? NoReadColAt not_readCollision_of_noReadColAt
  readColMove_vis_pos noReadColAt_snoc matchesEvents_append_invisible
  callStarts_eq_of_coinSplit honestKeysFrom_append honestKeysOf_append
  PrekeyCallsPos prekeyCallsPos_snoc pathFaithful_append_of_prekeyCallsPos
  OutcomeFaithfulCli2 outcomeFaithfulCli2_snoc rngLengthsFaithfulCli_snoc
  StateLoadSub stateLoadSub_append_steps stateLoadSub_snoc_none stateLoadSub_snoc_step
  AccInv accInv_nil accInv_step_network accInv_step_invisible_list)

private theorem accInv_step_run0 {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g : Ghost}
    {evs_acc evs_rem : List CliEvent} {ev : RunEvent}
    {ss_acc : List Step} {vis_acc : List VisEntry} {τ : List MachineEvent} {ms : List Move}
    (hsched : SchedFits (callsOf (evs_acc ++ .run ev :: evs_rem)) who ok)
    (hrej : RunRejected ev)
    (h : AccInv interp r S who ok g evs_acc ss_acc vis_acc τ ms) :
    ∃ τ' ms', AccInv interp r S who ok g (evs_acc ++ [.run ev]) ss_acc vis_acc τ' ms' := by
  have hrok : runOk ev = false := by
    unfold runOk; split
    · next out heq => exact False.elim (hrej out heq)
    · rfl
  by_cases hfs : failedSend ev = true
  · refine ⟨τ, ms, { h with
      cs := by
        rw [Symbolic.Proofs.Swarm.UA.Base.flatEvents_append,
          Symbolic.Proofs.Swarm.UA.Base.flatEvents_run_failedSend hfs, List.append_nil]
        exact h.cs
      mev := Symbolic.Proofs.Swarm.UA.Base.matchesEvents_snoc_rejected hrej h.mev }⟩
  · have hfs_f : failedSend ev = false := Bool.eq_false_iff.mpr hfs
    have hcmd_not_send : ∀ peer, ev.cmd ≠ .send peer := by
      intro peer hc; simp [failedSend, hc, hrok] at hfs_f
    have hfe : flatEvents [.run ev] = [.recv ev.input, .rng ev.coins] := by
      simp only [flatEvents, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        flatEvent, hfs_f, flatEntry, flatExit]
      cases hc : ev.cmd with
      | send peer => exact False.elim (hcmd_not_send peer hc)
      | init _ _ | recv _ =>
        cases hex : ev.exit with
        | none => rfl
        | some pr =>
          rcases pr with ⟨code, out⟩
          by_cases h0 : code = 0
          · subst h0; exact False.elim (hrej out hex)
          · simp [h0]
    have hcs_blk : CoinSplit [.recv ev.input, .rng ev.coins] [.recv ev.input] :=
      .keep (by intro _ hc; cases hc) (.split (pieces := []) (by simp) (List.nil_prefix) .nil)
    have hcalls_at : (callsOf (evs_acc ++ .run ev :: evs_rem))[(callsOf evs_acc).length]? =
        some (ev.party, false) := by
      rw [Symbolic.Proofs.Swarm.UA.Base.callsOf_append]
      simp [callsOf, hfs_f, hrok]
    have hok_len : ok (callStarts τ).length = false := by
      rw [callStarts_eq_of_coinSplit h.cs,
        Symbolic.Proofs.Swarm.UA.Base.callStarts_flatEvents_length]
      exact hsched.2 _ _ _ hcalls_at
    have hpath' := pathFaithful_append_of_prekeyCallsPos h.clean.1.1 h.ppos [.recv ev.input]
    have hcl' : Clean interp r S who ok g (ms ++ [.reject []]) (τ ++ [.recv ev.input]) := by
      simpa using clean_snoc_reject ev.input [] h.clean hpath' hok_len
    have hvis_rej : (Move.reject []).vis (runTraceMoves r ms) =
        [⟨.recv, [], .unconstrained, none⟩] := by
      simp [Move.vis, exposures, newIndices]
    refine ⟨τ ++ [.recv ev.input], ms ++ [.reject []], {
      cs := by
        rw [Symbolic.Proofs.Swarm.UA.Base.flatEvents_append, hfe]
        exact Symbolic.Swarm.CREF.CliPure.coinSplit_append h.cs hcs_blk
      clean := hcl'
      nr := noReadColAt_snoc (m := .reject []) h.clean.1.1 h.nr (fun _ _ _ hc => hc)
      ppos := prekeyCallsPos_snoc (m := .reject []) h.ppos (fun hp => nomatch hp)
      out2 := outcomeFaithfulCli2_snoc h.out2 (fun _ hok_true => by
        rw [matchedPrefix_callCount_eq h.clean.1.1, hok_len] at hok_true
        cases hok_true)
      rng32 := rngLengthsFaithfulCli_snoc h.rng32 (fun _ v _ hv hk => by
        rw [hvis_rej] at hv
        rcases List.mem_singleton.mp hv with rfl
        cases hk)
      tr_eq := by rw [runTrace_snoc, reject_next, h.tr_eq]
      keys_eq := by
        rw [honestKeysFrom_append]
        simp [honestKeysFrom, h.keys_eq]
      vpt := by
        rw [runVis_snoc, hvis_rej, ← List.append_nil vis_acc]
        exact visSendPtEq_append h.vpt visSendPtEq_reject_nil
      mev := Symbolic.Proofs.Swarm.UA.Base.matchesEvents_snoc_rejected hrej h.mev
      sload := stateLoadSub_snoc_none h.sload rfl
    }⟩

private theorem matchesEventsAt_snoc_env {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {initIds : Option BundlePreKeyIds} {s : Step} {ev : EnvEvent} {v : List VisEntry}
    {tr : ExecTrace} {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    (h : MatchesEventsClassicalAt interp r S g initIds tr ss evs vis)
    (hem : EnvMatchesClassical interp r S g (runSteps ss tr) s ev v) :
    MatchesEventsClassicalAt interp r S g initIds tr (ss ++ [s]) (evs ++ [.env ev]) (vis ++ v) := by
  induction h with
  | nil hinv =>
    simpa using MatchesEventsClassicalAt.env hinv hem (.nil (by simp))
  | run1 hp hrm _ ih =>
    rw [Symbolic.Proofs.Swarm.UA.Base.runSteps_append, runSteps] at hem
    simpa [List.append_assoc] using MatchesEventsClassicalAt.run1 hp hrm (ih hem)
  | run0 hp hrej _ ih =>
    rw [Symbolic.Proofs.Swarm.UA.Base.runSteps_append] at hem
    simpa [List.append_assoc] using MatchesEventsClassicalAt.run0 hp hrej (ih hem)
  | env hp hem' _ ih =>
    rw [Symbolic.Proofs.Swarm.UA.Base.runSteps_append, runSteps] at hem
    simpa [List.append_assoc] using MatchesEventsClassicalAt.env hp hem' (ih hem)

private theorem matchesEvents_snoc_env {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {s : Step} {ev : EnvEvent} {v : List VisEntry}
    {tr : ExecTrace} {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    (h : MatchesEventsClassical interp r S g tr ss evs vis)
    (hem : EnvMatchesClassical interp r S g (runSteps ss tr) s ev v) :
    MatchesEventsClassical interp r S g tr (ss ++ [s]) (evs ++ [.env ev]) (vis ++ v) :=
  matchesEventsAt_snoc_env h hem

private theorem matchesEventsAt_snoc_run1 {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {initIds : Option BundlePreKeyIds} {s : Step} {ev : RunEvent} {v : List VisEntry}
    {tr : ExecTrace} {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    (h : MatchesEventsClassicalAt interp r S g initIds tr ss evs vis)
    (hrm : RunMatches interp r S g (runSteps ss tr) s ev v (evs.foldl stepBundleIds initIds)) :
    MatchesEventsClassicalAt interp r S g initIds tr (ss ++ [s]) (evs ++ [.run ev]) (vis ++ v) := by
  induction h with
  | nil hinv =>
    simpa using MatchesEventsClassicalAt.run1 hinv hrm (.nil (by simp))
  | run1 hp hrm' _ ih =>
    rw [Symbolic.Proofs.Swarm.UA.Base.runSteps_append, runSteps, List.foldl_cons,
      Symbolic.Proofs.Swarm.UA.Base.stepBundleIds_run_of_runMatches hrm'] at hrm
    simpa [List.append_assoc] using MatchesEventsClassicalAt.run1 hp hrm' (ih hrm)
  | run0 hp hrej _ ih =>
    rw [Symbolic.Proofs.Swarm.UA.Base.runSteps_append, List.foldl_cons,
      Symbolic.Proofs.Swarm.UA.Base.stepBundleIds_run_of_runRejected hrej] at hrm
    simpa [List.append_assoc] using MatchesEventsClassicalAt.run0 hp hrej (ih hrm)
  | env hp hem _ ih =>
    rw [Symbolic.Proofs.Swarm.UA.Base.runSteps_append, runSteps, List.foldl_cons] at hrm
    simpa [List.append_assoc, stepBundleIds] using MatchesEventsClassicalAt.env hp hem (ih hrm)

theorem matchesEvents_snoc_run1 {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {s : Step} {ev : RunEvent} {v : List VisEntry}
    {tr : ExecTrace} {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    (h : MatchesEventsClassical interp r S g tr ss evs vis)
    (hrm : RunMatches interp r S g (runSteps ss tr) s ev v (activeBundleIds evs)) :
    MatchesEventsClassical interp r S g tr (ss ++ [s]) (evs ++ [.run ev]) (vis ++ v) :=
  matchesEventsAt_snoc_run1 h hrm

private def stepLeakMove : Step → Move
  | .compromiseIK q idx => .compromiseIK q idx
  | .compromiseSPK q idx => .compromiseSPK q idx
  | .compromisePQSPK q idx => .compromisePQSPK q idx
  | .compromiseOPK q idx => .compromiseOPK q idx
  | .exposeKey me idx kc => .exposeKey me idx kc
  | .exposeSpqr me idx => .exposeSpqr me idx
  | .exposeSkipped skIdx => .exposeSkipped skIdx
  | _ => .reject []

private theorem stepLeakMove_props {r : ProtocolSetup} {s : Step} {tr : ExecTrace}
    (hlk : s.IsLeak) (hloc : s.LocalOk tr) :
    let m := stepLeakMove s
    Symbolic.Swarm.CREF.LeakKind m ∧
    m.next tr = s.next tr ∧
    m.vis tr = stepView s tr false ∧
    MoveOK r m tr ∧
    m.party? = none ∧ m.prekeyPath? = none ∧ m.stateLoad? = none ∧
    (∀ pre e interp S g, ¬ MoveReadsCollidingMsg interp r S g pre e m) := by
  cases s <;> try exact False.elim hlk
  all_goals
    refine ⟨trivial, ?_, ?_, ⟨rfl, trivial, trivial, ?_, trivial⟩, rfl, rfl, rfl,
      fun _ _ _ _ _ hc => hc⟩
    · dsimp only [stepLeakMove, Move.next, Move.act, Step.next, Step.toInput]
      erw [stepIn_next]; exact run_bind_pure_snd _ tr
    · simp only [stepLeakMove, Move.vis, stepView, List.nil_append, List.filter_nil, ite_self]
      congr 1
      dsimp only [Move.next, Move.act, Step.next, Step.toInput]
      erw [stepIn_next]; exact run_bind_pure_snd _ tr
    · first | exact hloc | trivial

private theorem accInv_step_env {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g : Ghost}
    {evs_acc : List CliEvent} {ev : EnvEvent} {s : Step} {v : List VisEntry}
    {ss_acc : List Step} {vis_acc : List VisEntry} {τ : List MachineEvent} {ms : List Move}
    (hs_pre : s.PreCond (runTrace r ss_acc))
    (hs_loc : s.LocalOk (runTrace r ss_acc))
    (hem : EnvMatchesClassical interp r S g (runTrace r ss_acc) s ev v)
    (h : AccInv interp r S who ok g evs_acc ss_acc vis_acc τ ms) :
    ∃ τ' ms', AccInv interp r S who ok g (evs_acc ++ [.env ev]) (ss_acc ++ [s]) (vis_acc ++ v)
      τ' ms' := by
  cases ev <;> try exact False.elim hem
  rename_i p k
  have hem0 := hem
  obtain ⟨_, hlk, _, hv_eq, ve, rfl, hbme⟩ := hem
  have htr_m := h.tr_eq
  obtain ⟨hlk_m, hnxt, hvis_eq, hm_ok, hm_party, hm_ppath, hm_sload, hm_nrc⟩ :=
    stepLeakMove_props (r := r) (tr := runTraceMoves r ms) hlk (by rwa [htr_m])
  let m := stepLeakMove s
  have hreach' : (runTraceMoves r (ms ++ [m])).Reachable reachability := by
    rw [runTrace_snoc, hnxt, htr_m]
    exact step_reachable (by rw [← htr_m]; exact h.clean.1.1.2.1.2.2.1.1) hs_pre
  have hrun' : ModelRun r (ms ++ [m]) :=
    modelRun_snoc h.clean.1.1.2.1 hm_ok hreach' (fun _ _ _ _ _ _ _ _ hml => by
      rw [hm_sload] at hml; cases hml)
  have hve_k : ve.kind = .leak := hbme.1.symm
  have hm_vis : m.vis (runTraceMoves r ms) = [ve] := by
    rw [hvis_eq, htr_m, ← hv_eq]
  have hF_blk : List.Forall₂ (EventMatchesEntry interp r S g) [.leak k]
      (runMoves [m] (runTraceMoves r ms)).2 := by
    simp only [runMoves, List.append_nil, hm_vis]
    exact .cons (eventMatchesEntry_of_bytesMatchEntry (e := .leak k) hbme) .nil
  have hmp' : MatchedPrefix interp r S who g (ms ++ [m]) (τ ++ [.leak k]) :=
    matchedPrefix_append h.clean.1.1 hrun'
      (roleFaithful_snoc_none h.clean.1.1.2.2.1 hm_party)
      (pathFaithful_snoc_none (pathFaithful_append_of_prekeyCallsPos h.clean.1.1 h.ppos _) hm_ppath)
      (fun evz hevz hk => by
        simp only [runMoves, List.append_nil, hm_vis, List.zip_cons_cons, List.zip_nil_right,
          List.mem_singleton] at hevz
        rw [hevz, hve_k] at hk; cases hk)
      hF_blk
  have hcl' : Clean interp r S who ok g (ms ++ [m]) (τ ++ [.leak k]) :=
    Symbolic.Swarm.CREF.CliPure.clean_snoc_leakKind h.clean hlk_m hmp'
  have hfe : flatEvents [.env (.leak p k)] = [.leak k] := rfl
  refine ⟨τ ++ [.leak k], ms ++ [m], {
    cs := by
      rw [Symbolic.Proofs.Swarm.UA.Base.flatEvents_append, hfe]
      exact Symbolic.Swarm.CREF.CliPure.coinSplit_append h.cs
        (.keep (fun _ hc => by cases hc) .nil)
    clean := hcl'
    nr := noReadColAt_snoc (m := m) h.clean.1.1 h.nr (fun _ _ _ hc => hm_nrc _ _ _ _ _ hc)
    ppos := prekeyCallsPos_snoc (m := m) h.ppos (fun hp => by rw [hm_ppath] at hp; cases hp)
    out2 := outcomeFaithfulCli2_snoc h.out2 (by simp [hm_vis, hve_k])
    rng32 := rngLengthsFaithfulCli_snoc h.rng32 (by simp [hm_vis, hve_k])
    tr_eq := by
      rw [runTrace_snoc, Symbolic.Proofs.Swarm.UA.Base.runTrace_append, runSteps, runSteps,
        hnxt, htr_m]
    keys_eq := by
      rw [honestKeysFrom_append, honestKeysOf_append]
      cases s <;> try exact False.elim hlk
      all_goals simp [m, stepLeakMove, honestKeysFrom, honestKeysOf, Step.publishedSpqrKey?, h.keys_eq]
    vpt := by
      rw [runVis_snoc, hm_vis]
      exact visSendPtEq_append h.vpt (visSendPtEq_refl [ve])
    mev := matchesEvents_snoc_env h.mev (by simpa [runTrace] using hem0)
    sload := stateLoadSub_append_steps (stateLoadSub_snoc_none h.sload hm_sload) [s]
  }⟩

theorem stepsWF_split_append :
    ∀ (pre ss : List Step) (tr : ExecTrace),
      StepsWF (pre ++ ss) tr ↔ StepsWF pre tr ∧ StepsWF ss (runSteps pre tr)
  | [], ss, tr => by simp [StepsWF, runSteps]
  | s :: pre, ss, tr => by
    simp only [List.cons_append, StepsWF, runSteps, stepsWF_split_append pre ss (s.next tr),
      and_assoc]

theorem readColMove_iff_decryptMsgIdx? {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {pre : List Move} {e : MachineEvent} {m : Move} :
    MoveReadsCollidingMsg interp r S g pre e m ↔
      ∃ msgIdx b t, m.decryptMsgIdx? = some msgIdx ∧ RecvMsgBody e b ∧
        (runTraceMoves r pre).getMessageSentAt msgIdx = some t ∧
        RecvCollision interp r S g pre t := by
  cases m <;> simp [MoveReadsCollidingMsg, Move.decryptMsgIdx?]

theorem forall₂_rng_of_bytesMatchEntry {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {initIds : Option BundlePreKeyIds} :
    ∀ {pieces : List HwBytes} {drs : List VisEntry},
      List.Forall₂ (fun p ve => BytesMatchEntry interp r S g .rng p ve initIds) pieces drs →
      List.Forall₂ (EventMatchesEntry interp r S g) (pieces.map .rng) drs ∧
        (∀ vd ∈ drs, vd.kind = .rng)
  | _, _, .nil => ⟨.nil, fun _ h => nomatch h⟩
  | _, _, .cons hb hrest => by
    obtain ⟨hf, hk⟩ := forall₂_rng_of_bytesMatchEntry hrest
    exact ⟨.cons (eventMatchesEntry_of_bytesMatchEntry (e := .rng _) hb) hf,
      fun vd hvd => (List.mem_cons.mp hvd).elim (fun h1 => h1 ▸ hb.1.symm) (hk vd)⟩

private structure PartyMoveBundle (interp : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (tr : ExecTrace) (s : Step) (ev : RunEvent) (v : List VisEntry)
    (m : Move) : Prop where
  vis_eq : m.vis tr = v
  next_eq : m.next tr = s.next tr
  mok : MoveOK r m tr
  party_eq : m.party? = some ev.party
  sload_eq : m.stateLoad? = s.stateLoad?
  act_ok : (m.act.run tr).1.isSome = s.ok tr
  hkeys_eq : honestKeysFrom tr [m] = honestKeysOf tr [s]
  out2_ok : (m.vis tr).any (fun ve => ve.kind == .send || ve.kind == .accept) ∨
    (eventIdx isAliceDone tr (m.next tr)).isSome
  rng32_ok : (m.vis tr).any (fun ve => ve.kind == .recv) →
    ∀ (ve : VisEntry) (t : _root_.DY.Bytes),
      ve ∈ m.vis tr → ve.kind = .rng → ve.layout = .single → ve.terms = [t] →
      (gamma interp S g t).length = 32
  ppath_ok : ∀ (promote : Bool) (p : PreKeyFields),
    m.prekeyPath? = some promote → parsePreKeyWire ev.input = some p →
    (promote = true ↔ ∃ ek ∈ bobDoneBaseKeys tr,
      ecKey (gamma interp S g ek) = p.baseKey.take 33)
  dec_eq : m.decryptMsgIdx? = s.decryptMsgIdx?
  not_rej : ∀ ds, m ≠ .reject ds

theorem forall₂_append_join {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ l₂ : List α} {m₁ m₂ : List β},
      List.Forall₂ R l₁ m₁ → List.Forall₂ R l₂ m₂ → List.Forall₂ R (l₁ ++ l₂) (m₁ ++ m₂)
  | _, _, _, _, .nil, h₂ => h₂
  | _, _, _, _, .cons hab h₁, h₂ => .cons hab (forall₂_append_join h₁ h₂)

private theorem mem_snd_of_mem_zip {α β : Type} :
    ∀ {xs : List α} {ys : List β} {p : α × β}, p ∈ xs.zip ys → p.2 ∈ ys
  | [], _, _, h => nomatch h
  | _ :: _, [], _, h => nomatch h
  | _ :: _, _ :: _, _, h =>
    (List.mem_cons.mp h).elim (fun heq => heq ▸ List.mem_cons_self ..)
      (fun h' => List.mem_cons_of_mem _ (mem_snd_of_mem_zip h'))

private theorem readOKWith_of_readsFaithfully {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {tr : ExecTrace} (htr : runTraceMoves r ms = tr)
    {e : MachineEvent} {v : VisEntry} {b : HwBytes} (heb : eventBytes e = b)
    (h : ReadsFaithfully interp r S g tr v b) :
    ReadOKWith (recvRepresentations interp r S g ms) (preKeyRepresentations interp r S g ms) e v := by
  subst htr; subst heb; revert h
  unfold ReadOKWith ReadsFaithfully
  cases v.layout <;> exact id

private theorem rng32_of_ghostWF_single {interp : ExternInterpretation} {S : OpaqueSymbolSemantics}
    {g : Ghost} {v : List VisEntry} (hgwf : GhostWF g v)
    (hall32 : ∀ (ve : VisEntry) (t : _root_.DY.Bytes),
      ve ∈ v → ve.kind = .rng → ve.layout = .single → ve.terms = [t] → ∃ ts, t = randTerm ts 32) :
    ∀ (ve : VisEntry) (t : _root_.DY.Bytes),
      ve ∈ v → ve.kind = .rng → ve.layout = .single → ve.terms = [t] →
      (gamma interp S g t).length = 32 := by
  intro ve t hve hk hl ht
  obtain ⟨ts, rfl⟩ := hall32 ve t hve hk hl ht
  rw [gamma_randTerm_eq interp S g ts 32 (by decide)]
  exact hgwf.1 ve hve hk ts 32 (by decide) (by simp [ht])

private theorem encSend_none_eq_encSendEntry (tr tr' : ExecTrace) {stateIdx : Nat}
    (hppk : pendingPreKey tr stateIdx = none) :
    encSend tr tr' none = encSendEntry tr tr' stateIdx false := by
  unfold encSend encSendEntry
  rw [hppk]
  cases lastSent tr tr' <;> rfl

private theorem decVis_rng_32 {tr tr' : ExecTrace} {stateIdx msgIdx : Nat} {wrap : Bool}
    {ve : VisEntry} {t : _root_.DY.Bytes}
    (hnew : ∀ rd ∈ newRandoms tr tr', ∃ ts, rd = (randTerm ts 32, 32))
    (hve : ve ∈ decVis tr tr' stateIdx msgIdx wrap ++ exposures tr tr')
    (hk : ve.kind = .rng) (ht : ve.terms = [t]) :
    ∃ ts, t = randTerm ts 32 := by
  rcases List.mem_append.mp hve with hdv | hexp
  · unfold decVis at hdv
    rcases List.mem_append.mp hdv with h1 | hacc
    · rcases List.mem_append.mp h1 with hrcv | hrng
      · obtain ⟨_, _, rfl⟩ : ∃ a, tr.getMessageSentAt msgIdx = some a ∧ _ = ve := by
          simpa using hrcv
        cases hk
      · obtain ⟨rd, hrd, rfl⟩ := List.mem_map.mp hrng
        obtain ⟨ts, hrd_eq⟩ := hnew rd hrd
        rw [hrd_eq] at ht; simp [rngEntry] at ht
        exact ⟨ts, ht.symm⟩
    · obtain ⟨_, _, rfl⟩ : ∃ a, receivedPlaintext tr tr' = some a ∧ _ = ve := by
        simpa using hacc
      cases hk
  · have hk' := exposures_kind hexp; rw [hk] at hk'; cases hk'

private theorem exists_partyMoveBundle {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {s : Step} {ev : RunEvent} {v : List VisEntry}
    (hreach : tr.Reachable reachability) (hgwf_v : GhostWF g v)
    (hs_loc : s.LocalOk tr) (hrm : RunMatches interp r S g tr s ev v initIds) :
    ∃ m, PartyMoveBundle interp r S g tr s ev v m := by
  obtain ⟨hs_cls, hs_party, hs_fits, hs_peer, hs_ok, ⟨out, hexit⟩, hv_eq,
    inp, drs, outs, hv_split, _, _, houts_om, _, hpath_at⟩ := hrm
  cases s <;> try cases hs_cls
  case messageEncryptAbort me stateIdx =>
    have hc_send : ∃ peer, ev.cmd = .send peer := by
      cases hc : ev.cmd <;> simp [Step.FitsCmd, hc] at hs_fits; exact ⟨_, rfl⟩
    obtain ⟨peer, hc⟩ := hc_send
    unfold OutputsMatch at houts_om
    simp only [hexit, hc] at houts_om
    obtain ⟨vo, rfl, hvo_bme⟩ := houts_om
    have hvo_mem : vo ∈ stepView (.messageEncryptAbort me stateIdx) tr (runWrapped ev) := by
      rw [← hv_eq, hv_split]; simp
    simp only [stepView, hs_ok, ↓reduceIte, List.mem_append] at hvo_mem
    rcases hvo_mem with hd | he
    · rcases encDraws_kind hd with hk | hk <;> (rw [← hvo_bme.1] at hk; cases hk)
    · have hk := exposures_kind he; rw [← hvo_bme.1] at hk; cases hk
  case aliceStart a b idStateIdx regIdxB bh =>
    let m : Move := .aliceStart a b idStateIdx regIdxB bh 35
    obtain ⟨o, hnext_o⟩ := aliceStart_ok_trOfOut hs_ok
    have hnxt : m.next tr = (Step.aliceStart a b idStateIdx regIdxB bh).next tr := by
      dsimp only [m, Move.next, Move.act, Step.next, Step.toInput]
      erw [stepIn_next]; exact run_bind_pure_snd _ tr
    have hact_ok : (m.act.run tr).1.isSome =
        (Step.aliceStart a b idStateIdx regIdxB bh).ok tr := by
      dsimp only [m, Move.act, Step.ok, Step.toInput]
      erw [stepIn_ok]; exact run_bind_pure_isSome _ tr
    have hvis_o := Symbolic.Swarm.CREF.vis_aliceStart_35 hnext_o
    have hvis_eq : m.vis tr = v := by
      rw [hv_eq]
      dsimp only [m, Move.vis, stepView]
      simp only [hs_ok, ↓reduceIte]
      rw [← hnxt, hnext_o, Symbolic.Swarm.CREF.exposures_aliceStartTrOfOut,
        List.append_nil, List.append_nil]
      unfold aliceVis
      rw [Symbolic.Swarm.CREF.newRandoms_aliceStartTrOfOut,
        Symbolic.Swarm.CREF.eventIdx_isAliceDone_aliceStartTrOfOut]
      dsimp only [List.map, aliceDraws]
      have hlen : ((⟨.recv, received tr ([bh.spk, bh.spkSig, bh.pqpk, bh.pqpkSig] ++ bh.opk.toList),
          .bundle, none⟩ : VisEntry) ::
          (rngEntry (randTerm tr.length 32) :: kyberCoinEntries (randTerm (tr.length + 1) 32) ++
            [{ rngEntry (randTerm (tr.length + 2) 32) with anchor := some (tr.length + 5) }])).length =
          35 := by simp [kyberCoinEntries]
      exact List.take_of_length_le (Nat.le_of_eq hlen)
    have hdone : eventIdx isAliceDone tr (m.next tr) = some (tr.length + 5) := by
      rw [hnext_o]; exact Symbolic.Swarm.CREF.eventIdx_isAliceDone_aliceStartTrOfOut tr a b o
    have hanc : m.LogsSessionCompletion tr := by
      refine ⟨by decide, fun idx hidx => ?_⟩
      rw [hdone, Option.some.injEq] at hidx; subst hidx
      refine ⟨{ rngEntry (randTerm (tr.length + 2) 32) with anchor := some (tr.length + 5) },
        ?_, rfl⟩
      rw [hvis_o]; simp
    refine ⟨m, {
      vis_eq := hvis_eq
      next_eq := hnxt
      mok := ⟨rfl, hanc, hs_peer, trivial, trivial⟩
      party_eq := hs_party
      sload_eq := rfl
      act_ok := hact_ok
      hkeys_eq := rfl
      out2_ok := Or.inr (by rw [hdone]; rfl)
      rng32_ok := fun _ => by
        rw [hvis_eq]
        refine rng32_of_ghostWF_single hgwf_v fun ve t hve hk hl ht => ?_
        rw [← hvis_eq, hvis_o] at hve
        rcases List.mem_cons.mp hve with rfl | hve
        · cases hk
        · rcases List.mem_cons.mp hve with rfl | hve
          · simp [rngEntry] at ht; exact ⟨tr.length, ht.symm⟩
          · rcases List.mem_append.mp hve with hkyb | hdhs
            · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hkyb
              cases hl
            · rcases List.mem_singleton.mp hdhs with rfl
              simp [rngEntry] at ht; exact ⟨tr.length + 2, ht.symm⟩
      ppath_ok := fun _ _ hp => nomatch hp
      dec_eq := rfl
      not_rej := fun _ h => nomatch h
    }⟩
  case bobStart b a kh regIdxA mh pqIdx spqrMsgIdx =>
    let s0 := Step.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx
    let bv := bobVis tr (s0.next tr) mh (bobOpkPk b kh tr)
    let m : Move := .bobStart b a kh regIdxA mh pqIdx spqrMsgIdx bv.length
    have hnxt : m.next tr = s0.next tr := by
      dsimp only [m, s0, Move.next, Move.act, Step.next, Step.toInput]
      erw [stepIn_next]; exact run_bind_pure_snd _ tr
    have hact_ok : (m.act.run tr).1.isSome = s0.ok tr := by
      dsimp only [m, s0, Move.act, Step.ok, Step.toInput]
      erw [stepIn_ok]; exact run_bind_pure_isSome _ tr
    have hvis_eq : m.vis tr = v := by
      rw [hv_eq]
      change (bobVis tr (m.next tr) mh (bobOpkPk b kh tr)).take bv.length ++
          exposures tr (m.next tr) = stepView s0 tr (runWrapped ev)
      rw [hnxt]
      dsimp only [s0, stepView]
      simp only [hs_ok, ↓reduceIte]
      change bv.take bv.length ++ exposures tr (s0.next tr) = bv ++ exposures tr (s0.next tr)
      rw [List.take_length]
    have hc_recv : ∃ peer, ev.cmd = .recv peer := by
      cases hc : ev.cmd <;> simp [Step.FitsCmd, hc] at hs_fits; exact ⟨_, rfl⟩
    obtain ⟨peer, hc⟩ := hc_recv
    unfold OutputsMatch at houts_om
    simp only [hexit, hc] at houts_om
    obtain ⟨vo, rfl, hvo_bme⟩ := houts_om
    have hvo_mem : vo ∈ m.vis tr := by rw [hvis_eq, hv_split]; simp
    have hvo_kind : vo.kind = .accept := hvo_bme.1.symm
    have hanc : m.LogsSessionCompletion tr := by
      refine ⟨by simp [bv, bobVis], fun idx hidx => ⟨vo, hvo_mem, ?_⟩⟩
      have hvo_bv : vo ∈ bv ++ exposures tr (s0.next tr) := by
        have h1 : vo ∈ v := by rw [hv_split]; simp
        rw [hv_eq] at h1; dsimp only [s0, stepView] at h1
        simp only [hs_ok, ↓reduceIte] at h1; exact h1
      rcases List.mem_append.mp hvo_bv with hbv | hexp
      · dsimp only [bv, bobVis] at hbv
        rcases List.mem_cons.mp hbv with rfl | hbv
        · cases hvo_kind
        · rcases List.mem_append.mp hbv with hrng | hacc
          · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hrng
            cases hvo_kind
          · obtain ⟨pt, _, rfl⟩ : ∃ pt, receivedPlaintext tr (s0.next tr) = some pt ∧ _ = vo := by
              simpa using hacc
            rw [← hnxt]; exact hidx
      · have hk := exposures_kind hexp; rw [hvo_kind] at hk; cases hk
    refine ⟨m, {
      vis_eq := hvis_eq
      next_eq := hnxt
      mok := ⟨rfl, hanc, hs_peer, trivial, trivial⟩
      party_eq := hs_party
      sload_eq := rfl
      act_ok := hact_ok
      hkeys_eq := rfl
      out2_ok := Or.inl (List.any_eq_true.mpr ⟨vo, hvo_mem, by simp [hvo_kind]⟩)
      rng32_ok := fun _ => by
        rw [hvis_eq]
        refine rng32_of_ghostWF_single hgwf_v fun ve t hve hk _ ht => ?_
        have hve_bv : ve ∈ bv ++ exposures tr (s0.next tr) := by
          dsimp only [s0, stepView] at hv_eq
          simp only [hs_ok, ↓reduceIte] at hv_eq
          rwa [hv_eq] at hve
        rcases List.mem_append.mp hve_bv with hbv | hexp
        · dsimp only [bv, bobVis] at hbv
          rcases List.mem_cons.mp hbv with rfl | hbv
          · cases hk
          · rcases List.mem_append.mp hbv with hrng | hacc
            · obtain ⟨rd, hrd, rfl⟩ := List.mem_map.mp hrng
              obtain ⟨ts, hrd_eq⟩ := bobStart_newRandoms_32 b a kh regIdxA mh pqIdx spqrMsgIdx tr rd hrd
              rw [hrd_eq] at ht; simp [rngEntry] at ht
              exact ⟨ts, ht.symm⟩
            · obtain ⟨_, _, rfl⟩ : ∃ pt, receivedPlaintext tr (s0.next tr) = some pt ∧ _ = ve := by
                simpa using hacc
              cases hk
        · have hk' := exposures_kind hexp; rw [hk] at hk'; cases hk'
      ppath_ok := fun promote p hp hpw => by
        simp only [m, Move.prekeyPath?, Option.some.injEq] at hp
        subst hp
        have hnk := hpath_at p hpw
        exact ⟨fun h => Bool.noConfusion h, fun hk => False.elim (hnk hk)⟩
      dec_eq := rfl
      not_rej := fun _ h => nomatch h
    }⟩
  case messageEncrypt me stateIdx coinsLen pqIdx =>
    let s0 := Step.messageEncrypt me stateIdx coinsLen pqIdx
    have hpq : pqIdx = tr.length + 2 := by
      rcases hs_loc.2 with h2 | h3
      · exact h2
      · rw [show encryptAbortAfterSpqrIdx tr = tr.length + 3 from rfl] at h3
        subst h3
        have hf := messageEncrypt_fail_not_ok me stateIdx coinsLen tr
        rw [hs_ok] at hf; cases hf
    have hc_send : ∃ peer, ev.cmd = .send peer := by
      cases hc : ev.cmd <;> simp [Step.FitsCmd, hc] at hs_fits; exact ⟨_, rfl⟩
    obtain ⟨peer, hc⟩ := hc_send
    unfold OutputsMatch at houts_om
    simp only [hexit, hc] at houts_om
    obtain ⟨vo, rfl, hvo_bme⟩ := houts_om
    have hvo_kind : vo.kind = .send := hvo_bme.1.symm
    have hwrap_ex : ∃ wrap : Option (Nat × Nat),
        encSend tr (s0.next tr) wrap = encSendEntry tr (s0.next tr) stateIdx (runWrapped ev) := by
      have hvo_sv : vo ∈ stepView s0 tr (runWrapped ev) := by
        rw [← hv_eq, hv_split]; simp
      dsimp only [s0, stepView] at hvo_sv
      simp only [hs_ok, ↓reduceIte] at hvo_sv
      have hvo_ese : vo ∈ encSendEntry tr (s0.next tr) stateIdx (runWrapped ev) := by
        rcases List.mem_append.mp hvo_sv with h1 | hexp
        · rcases List.mem_append.mp h1 with hdr | hese
          · rcases encDraws_kind hdr with hk | hk <;> (rw [hvo_kind] at hk; cases hk)
          · exact hese
        · have hk := exposures_kind hexp; rw [hvo_kind] at hk; cases hk
      cases hw : runWrapped ev with
      | false =>
        rw [hw] at hvo_ese
        rcases hppk : pendingPreKey tr stateIdx with _ | _
        · exact ⟨none, encSend_none_eq_encSendEntry tr (s0.next tr) hppk⟩
        · unfold encSendEntry at hvo_ese
          rw [hppk] at hvo_ese
          split at hvo_ese <;> cases hvo_ese
      | true =>
        rw [hw] at hvo_ese
        rcases hppk : pendingPreKey tr stateIdx with _ | ⟨ek, ct⟩
        · unfold encSendEntry at hvo_ese
          rw [hppk] at hvo_ese
          split at hvo_ese <;> cases hvo_ese
        · obtain ⟨ekIdx, ctIdx, hek, hct⟩ := pendingPreKey_handles_of_reachable hreach hppk
          exact ⟨some (ekIdx, ctIdx), encSend_some_eq_encSendEntry tr (s0.next tr) hppk hek hct⟩
    obtain ⟨wrap, hwrap⟩ := hwrap_ex
    let m : Move := .encrypt me stateIdx coinsLen pqIdx wrap
    have hnxt : m.next tr = s0.next tr := by
      dsimp only [m, s0, Move.next, Move.act, Step.next, Step.toInput]
      erw [stepIn_next]; exact run_bind_pure_snd _ tr
    have hact_ok : (m.act.run tr).1.isSome = s0.ok tr := by
      dsimp only [m, s0, Move.act, Step.ok, Step.toInput]
      erw [stepIn_ok]; exact run_bind_pure_isSome _ tr
    have hvis_eq : m.vis tr = v := by
      rw [hv_eq]
      change encDraws (newRandoms tr (m.next tr)) ++ encSend tr (m.next tr) wrap ++
          exposures tr (m.next tr) = stepView s0 tr (runWrapped ev)
      rw [hnxt, hwrap]
      dsimp only [s0, stepView]
      simp only [hs_ok, ↓reduceIte]
    have hvo_mem : vo ∈ m.vis tr := by rw [hvis_eq, hv_split]; simp
    refine ⟨m, {
      vis_eq := hvis_eq
      next_eq := hnxt
      mok := ⟨rfl, trivial, trivial, trivial, hpq⟩
      party_eq := hs_party
      sload_eq := rfl
      act_ok := hact_ok
      hkeys_eq := by
        have hne3 : pqIdx ≠ tr.length + 3 := by omega
        simp [m, s0, honestKeysFrom, honestKeysOf, Step.publishedSpqrKey?,
          DY.Libsignal.Composed.Refinement.encryptAbortAfterSpqrIdx,
          DY.Libsignal.Composed.Refinement.encryptOwnSpqrKeyIdx, hne3, hnxt]
      out2_ok := Or.inl (List.any_eq_true.mpr ⟨vo, hvo_mem, by simp [hvo_kind]⟩)
      rng32_ok := fun hany => by
        obtain ⟨vr, hvr, hvr_k⟩ := List.any_eq_true.mp hany
        simp only [beq_iff_eq] at hvr_k
        dsimp only [m, Move.vis, encVis] at hvr
        rcases List.mem_append.mp hvr with h1 | hexp
        · rcases List.mem_append.mp h1 with hdr | hes
          · rcases encDraws_kind hdr with hk | hk <;> (rw [hvr_k] at hk; cases hk)
          · have hk := encSend_kind hes; rw [hvr_k] at hk; cases hk
        · have hk := exposures_kind hexp; rw [hvr_k] at hk; cases hk
      ppath_ok := fun _ _ hp => nomatch hp
      dec_eq := rfl
      not_rej := fun _ h => nomatch h
    }⟩
  case messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx =>
    let s0 := Step.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx
    let m : Move := .decrypt me stateIdx msgIdx pqIdx spqrMsgIdx (runWrapped ev)
    have hnxt : m.next tr = s0.next tr := by
      dsimp only [m, s0, Move.next, Move.act, Step.next, Step.toInput]
      erw [stepIn_next]; exact run_bind_pure_snd _ tr
    have hact_ok : (m.act.run tr).1.isSome = s0.ok tr := by
      dsimp only [m, s0, Move.act, Step.ok, Step.toInput]
      erw [stepIn_ok]; exact run_bind_pure_isSome _ tr
    have hvis_eq : m.vis tr = v := by
      rw [hv_eq]
      change decVis tr (m.next tr) stateIdx msgIdx (runWrapped ev) ++
          exposures tr (m.next tr) = stepView s0 tr (runWrapped ev)
      rw [hnxt]; dsimp only [s0, stepView]; simp only [hs_ok, ↓reduceIte]
    have hc_recv : ∃ peer, ev.cmd = .recv peer := by
      cases hc : ev.cmd <;> simp [Step.FitsCmd, hc] at hs_fits; exact ⟨_, rfl⟩
    obtain ⟨peer, hc⟩ := hc_recv
    unfold OutputsMatch at houts_om
    simp only [hexit, hc] at houts_om
    obtain ⟨vo, rfl, hvo_bme⟩ := houts_om
    have hvo_mem : vo ∈ m.vis tr := by rw [hvis_eq, hv_split]; simp
    refine ⟨m, {
      vis_eq := hvis_eq
      next_eq := hnxt
      mok := ⟨rfl, trivial, trivial, trivial, trivial⟩
      party_eq := hs_party
      sload_eq := rfl
      act_ok := hact_ok
      hkeys_eq := rfl
      out2_ok := Or.inl (List.any_eq_true.mpr ⟨vo, hvo_mem, by simp [← hvo_bme.1]⟩)
      rng32_ok := fun _ => by
        rw [hvis_eq]
        refine rng32_of_ghostWF_single hgwf_v fun ve t hve hk _ ht => ?_
        have hve_dv : ve ∈ decVis tr (s0.next tr) stateIdx msgIdx (runWrapped ev) ++
            exposures tr (s0.next tr) := by
          dsimp only [s0, stepView] at hv_eq
          simp only [hs_ok, ↓reduceIte] at hv_eq; rwa [hv_eq] at hve
        exact decVis_rng_32 (messageDecrypt_newRandoms_32 me stateIdx msgIdx pqIdx spqrMsgIdx tr)
          hve_dv hk ht
      ppath_ok := fun promote p hp hpw => by
        dsimp only [m, Move.prekeyPath?] at hp
        cases hw : runWrapped ev <;> simp [hw] at hp
        subst hp
        exact ⟨fun _ => hpath_at p hpw, fun _ => rfl⟩
      dec_eq := rfl
      not_rej := fun _ h => nomatch h
    }⟩
  case messageDecryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx =>
    let s0 := Step.messageDecryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx
    let m : Move := .decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx (runWrapped ev)
    have hnxt : m.next tr = s0.next tr := by
      dsimp only [m, s0, Move.next, Move.act, Step.next, Step.toInput]
      erw [stepIn_next]; exact run_bind_pure_snd _ tr
    have hact_ok : (m.act.run tr).1.isSome = s0.ok tr := by
      dsimp only [m, s0, Move.act, Step.ok, Step.toInput]
      erw [stepIn_ok]; exact run_bind_pure_isSome _ tr
    have hvis_eq : m.vis tr = v := by
      rw [hv_eq]
      change decVis tr (m.next tr) stateIdx msgIdx (runWrapped ev) ++
          exposures tr (m.next tr) = stepView s0 tr (runWrapped ev)
      rw [hnxt]; dsimp only [s0, stepView]; simp only [hs_ok, ↓reduceIte]
    have hc_recv : ∃ peer, ev.cmd = .recv peer := by
      cases hc : ev.cmd <;> simp [Step.FitsCmd, hc] at hs_fits; exact ⟨_, rfl⟩
    obtain ⟨peer, hc⟩ := hc_recv
    unfold OutputsMatch at houts_om
    simp only [hexit, hc] at houts_om
    obtain ⟨vo, rfl, hvo_bme⟩ := houts_om
    have hvo_mem : vo ∈ m.vis tr := by rw [hvis_eq, hv_split]; simp
    refine ⟨m, {
      vis_eq := hvis_eq
      next_eq := hnxt
      mok := ⟨rfl, trivial, trivial, trivial, trivial⟩
      party_eq := hs_party
      sload_eq := rfl
      act_ok := hact_ok
      hkeys_eq := rfl
      out2_ok := Or.inl (List.any_eq_true.mpr ⟨vo, hvo_mem, by simp [← hvo_bme.1]⟩)
      rng32_ok := fun _ => by
        rw [hvis_eq]
        refine rng32_of_ghostWF_single hgwf_v fun ve t hve hk _ ht => ?_
        have hve_dv : ve ∈ decVis tr (s0.next tr) stateIdx msgIdx (runWrapped ev) ++
            exposures tr (s0.next tr) := by
          dsimp only [s0, stepView] at hv_eq
          simp only [hs_ok, ↓reduceIte] at hv_eq; rwa [hv_eq] at hve
        exact decVis_rng_32
          (messageDecryptSkipped_newRandoms_32 me stateIdx msgIdx skIdx pqIdx spqrMsgIdx tr)
          hve_dv hk ht
      ppath_ok := fun promote p hp hpw => by
        dsimp only [m, Move.prekeyPath?] at hp
        cases hw : runWrapped ev <;> simp [hw] at hp
        subst hp
        exact ⟨fun _ => hpath_at p hpw, fun _ => rfl⟩
      dec_eq := rfl
      not_rej := fun _ h => nomatch h
    }⟩

private theorem accInv_step_run1 {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g : Ghost}
    {evs_acc evs_rem : List CliEvent} {ev : RunEvent} {s : Step} {v : List VisEntry}
    {ss_acc : List Step} {vis_acc : List VisEntry} {τ : List MachineEvent} {ms : List Move}
    (hsched : SchedFits (callsOf (evs_acc ++ .run ev :: evs_rem)) who ok)
    (hgwf_v : GhostWF g v)
    (hs_pre : s.PreCond (runTrace r ss_acc))
    (hs_loc : s.LocalOk (runTrace r ss_acc))
    (hrm : RunMatches interp r S g (runTrace r ss_acc) s ev v (activeBundleIds evs_acc))
    (hsf_step : ∀ (i : Nat) (si : Step) (p : Participant) (k : Nat) (b : Bool),
      ss_acc[i]? = some si → si.stateLoad? = some (p, k, true) →
      si.ok (runTrace r (ss_acc.take i)) = true → s.stateLoad? = some (p, k, b) → False)
    (hnrc_step : ∀ (out b : HwBytes) (msgIdx : Nat) (t : _root_.DY.Bytes),
      (∃ peer, ev.cmd = .recv peer) → ev.exit = some (0, out) → RecvBody ev.input b →
      s.decryptMsgIdx? = some msgIdx → (runTrace r ss_acc).getMessageSentAt msgIdx = some t →
      ¬ RecvCollisionOn interp r S g (runTrace r ss_acc) vis_acc (honestSaltsOf r ss_acc) t)
    (h : AccInv interp r S who ok g evs_acc ss_acc vis_acc τ ms) :
    ∃ τ' ms', AccInv interp r S who ok g (evs_acc ++ [.run ev]) (ss_acc ++ [s]) (vis_acc ++ v)
      τ' ms' := by
  have htr_m := h.tr_eq
  have hreach_tr : (runTrace r ss_acc).Reachable reachability := by
    rw [← htr_m]; exact h.clean.1.1.2.1.2.2.1.1
  obtain ⟨m, hb⟩ := exists_partyMoveBundle hreach_tr hgwf_v hs_loc hrm
  have hrm0 := hrm
  obtain ⟨_, _, hs_fits, _, _, ⟨out, hexit⟩, _, inp, drs, outs, hv_split,
    hinp_bme, ⟨pieces, hpieces_ne, hpieces_pref, hdrs_f2⟩, houts_om, hread_inp, _⟩ := hrm
  have hrok : runOk ev = true := by simp [runOk, hexit]
  have hfs : failedSend ev = false := by
    unfold failedSend; cases ev.cmd <;> simp [hrok]
  let e_in : MachineEvent :=
    match ev.cmd with
    | .send _ => .pt ev.input
    | _ => .recv ev.input
  let blk : List MachineEvent := e_in :: (pieces.map .rng ++ flatExit ev)
  have he_in_nrng : ∀ c, e_in ≠ .rng c := by
    dsimp only [e_in]; cases ev.cmd <;> intro _ hc <;> cases hc
  have he_in_bytes : eventBytes e_in = ev.input := by
    dsimp only [e_in]; cases ev.cmd <;> rfl
  have he_in_kind : eventKind e_in = inputKind ev := by
    dsimp only [e_in, inputKind]; cases ev.cmd <;> rfl
  have he_in_eme : EventMatchesEntry interp r S g e_in inp :=
    eventMatchesEntry_of_bytesMatchEntry (by rwa [he_in_kind, he_in_bytes])
  have hinp_kind : inp.kind = inputKind ev := hinp_bme.1.symm
  obtain ⟨hdrs_eme, hdrs_kind⟩ := forall₂_rng_of_bytesMatchEntry hdrs_f2
  have hexit_props :
      CoinSplit (flatExit ev) (flatExit ev) ∧
      List.Forall₂ (EventMatchesEntry interp r S g) (flatExit ev) outs ∧
      callStarts (flatExit ev) = [] ∧
      (∀ vo ∈ outs, vo.kind ≠ .recv) := by
    unfold OutputsMatch at houts_om
    unfold flatExit
    cases hc : ev.cmd with
    | init _ _ =>
      simp only [hexit, hc] at houts_om ⊢
      subst houts_om
      exact ⟨.nil, .nil, rfl, fun _ hvo => nomatch hvo⟩
    | send _ =>
      simp only [hexit, hc] at houts_om ⊢
      obtain ⟨vo, rfl, hvo_bme⟩ := houts_om
      exact ⟨.keep (fun _ h => by cases h) .nil,
        .cons (eventMatchesEntry_of_bytesMatchEntry (e := .send out) hvo_bme) .nil,
        rfl, fun vo' hvo' => by
          rcases List.mem_singleton.mp hvo' with rfl
          rw [← hvo_bme.1]; decide⟩
    | recv _ =>
      simp only [hexit, hc] at houts_om ⊢
      obtain ⟨vo, rfl, hvo_bme⟩ := houts_om
      exact ⟨.keep (fun _ h => by cases h) .nil,
        .cons (eventMatchesEntry_of_bytesMatchEntry (e := .accept out) hvo_bme) .nil,
        rfl, fun vo' hvo' => by
          rcases List.mem_singleton.mp hvo' with rfl
          rw [← hvo_bme.1]; decide⟩
  obtain ⟨hcs_exit, houts_eme, hcs_exit_nil, houts_nrecv⟩ := hexit_props
  have hfe : flatEvents [.run ev] = e_in :: .rng ev.coins :: flatExit ev := by
    simp only [flatEvents, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      flatEvent, hfs, Bool.false_eq_true, ↓reduceIte, flatEntry, e_in]
    cases ev.cmd <;> rfl
  have hcs_blk : CoinSplit (flatEvents [.run ev]) blk := by
    rw [hfe]
    exact .keep he_in_nrng (.split hpieces_ne hpieces_pref hcs_exit)
  have hm_vis_m : m.vis (runTraceMoves r ms) = v := by rw [htr_m, hb.vis_eq]
  have hF_blk : List.Forall₂ (EventMatchesEntry interp r S g) blk
      (runMoves [m] (runTraceMoves r ms)).2 := by
    simp only [runMoves, List.append_nil, hm_vis_m, hv_split, blk]
    exact .cons he_in_eme (forall₂_append_join hdrs_eme houts_eme)
  have hcalls_at : (callsOf (evs_acc ++ .run ev :: evs_rem))[(callsOf evs_acc).length]? =
      some (ev.party, true) := by
    rw [Symbolic.Proofs.Swarm.UA.Base.callsOf_append]
    simp [callsOf, hfs, hrok]
  have hcc_eq : callCount (runVis r ms) = (callsOf evs_acc).length := by
    rw [matchedPrefix_callCount_eq h.clean.1.1, callStarts_eq_of_coinSplit h.cs,
      Symbolic.Proofs.Swarm.UA.Base.callStarts_flatEvents_length]
  have hwho_k : who[callCount (runVis r ms)]? = some ev.party := by
    rw [hcc_eq]
    obtain ⟨w_rest, hw_eq⟩ := hsched.1
    have hmap_at : ((callsOf (evs_acc ++ .run ev :: evs_rem)).map Prod.fst)[(callsOf evs_acc).length]? =
        some ev.party := by
      simp [hcalls_at]
    have hlt_map : (callsOf evs_acc).length <
        ((callsOf (evs_acc ++ .run ev :: evs_rem)).map Prod.fst).length :=
      (List.getElem?_eq_some_iff.mp hmap_at).1
    rw [← hw_eq, List.getElem?_append_left hlt_map]
    exact hmap_at
  have hok_k : ok (callCount (runVis r ms)) = true := by
    rw [hcc_eq]; exact hsched.2 _ _ _ hcalls_at
  have hreach' : (runTraceMoves r (ms ++ [m])).Reachable reachability := by
    rw [runTrace_snoc, htr_m, hb.next_eq]
    exact step_reachable hreach_tr hs_pre
  have hrun' : ModelRun r (ms ++ [m]) :=
    modelRun_snoc h.clean.1.1.2.1 (by rw [htr_m]; exact hb.mok) hreach'
      (fun j mj p k b hmj hld hact hml => by
        obtain ⟨i, si, hsi, hsil, hok_eq⟩ := h.sload j mj p k true hmj hld
        rw [hok_eq] at hact
        rw [hb.sload_eq] at hml
        exact hsf_step i si p k b hsi hsil hact hml)
  have hcs_blk_starts : callStarts blk = [e_in] := by
    have h1 : blk = [e_in] ++ (pieces.map .rng ++ flatExit ev) := rfl
    rw [h1, callStarts_append]
    have h2 : callStarts [e_in] = [e_in] := by
      dsimp only [e_in]; cases ev.cmd <;> rfl
    have h3 : callStarts (pieces.map .rng ++ flatExit ev) = callStarts (flatExit ev) := by
      have hcs_tmp : CoinSplit (.rng ev.coins :: flatExit ev)
          (pieces.map .rng ++ flatExit ev) := .split hpieces_ne hpieces_pref hcs_exit
      rw [callStarts_eq_of_coinSplit hcs_tmp]; rfl
    rw [h2, h3, hcs_exit_nil, List.append_nil]
  have hpath_old := pathFaithful_append_of_prekeyCallsPos h.clean.1.1 h.ppos blk
  have hpath' : PathFaithful interp r S g (ms ++ [m]) (τ ++ blk) := by
    intro i mi promote b p hmi hp hcs_i hpw
    by_cases hlt : i < ms.length
    · rw [List.getElem?_append_left hlt] at hmi
      rw [List.take_append_of_le_length (Nat.le_of_lt hlt)] at hcs_i ⊢
      exact hpath_old i mi promote b p hmi hp hcs_i hpw
    · have hi_lt : i < (ms ++ [m]).length := (List.getElem?_eq_some_iff.mp hmi).1
      simp only [List.length_append, List.length_singleton] at hi_lt
      have hi_eq : i = ms.length := by omega
      subst hi_eq
      simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem?_cons_zero, Option.some.injEq] at hmi
      subst hmi
      have htkm : (ms ++ [m]).take ms.length = ms := by simp
      rw [htkm] at hcs_i ⊢
      rw [matchedPrefix_callCount_eq h.clean.1.1, callStarts_append, hcs_blk_starts,
        List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem?_cons_zero, Option.some.injEq] at hcs_i
      have hb_eq : b = ev.input := by
        have hbt : eventBytes e_in = eventBytes (.recv b) := congrArg eventBytes hcs_i
        rw [he_in_bytes] at hbt; exact hbt.symm
      subst hb_eq
      rw [htr_m]
      exact hb.ppath_ok promote p hp hpw
  have hread_blk : ∀ evz ∈ blk.zip (runMoves [m] (runTraceMoves r ms)).2, evz.2.kind = .recv →
      ReadOKWith (recvRepresentations interp r S g (ms ++ [m]))
        (preKeyRepresentations interp r S g (ms ++ [m])) evz.1 evz.2 := by
    simp only [runMoves, List.append_nil, hm_vis_m, hv_split, blk, List.zip_cons_cons]
    intro evz hevz hk
    rcases List.mem_cons.mp hevz with rfl | htail
    · exact ReadOKWith.mono (recvRepresentations_append_subset interp r S g ms [m])
        (preKeyRepresentations_append_subset interp r S g ms [m])
        (readOKWith_of_readsFaithfully htr_m he_in_bytes hread_inp)
    · rcases List.mem_append.mp (mem_snd_of_mem_zip htail) with hd | ho
      · rw [hdrs_kind _ hd] at hk; cases hk
      · exact False.elim (houts_nrecv _ ho hk)
  have hmp' : MatchedPrefix interp r S who g (ms ++ [m]) (τ ++ blk) :=
    matchedPrefix_append h.clean.1.1 hrun'
      (roleFaithful_snoc_party h.clean.1.1.2.2.1 hb.party_eq hwho_k)
      hpath' hread_blk hF_blk
  have hout' : OutcomeFaithful r ok (ms ++ [m]) := by
    refine outcomeFaithful_append h.clean.1.2 fun j mj hj => ?_
    rcases j with _ | j
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hj; subst hj
      simp only [List.take_zero, List.append_nil]
      exact ⟨fun ds hr => absurd hr (hb.not_rej ds), fun _ => hok_k⟩
    · simp at hj
  have hnr' : NoReadColAt interp r S g (ms ++ [m]) (τ ++ blk) := by
    refine noReadColAt_snoc (m := m) h.clean.1.1 h.nr fun e τ₂ hblk_eq hcol => ?_
    have he_eq : e = e_in := (List.cons.inj hblk_eq).1.symm
    subst he_eq
    obtain ⟨msgIdx, b_col, t_col, hm_dec, hrmb, hmsg, hrcol⟩ :=
      readColMove_iff_decryptMsgIdx?.mp hcol
    have hs_dec : s.decryptMsgIdx? = some msgIdx := hb.dec_eq ▸ hm_dec
    have hcmd_recv : ∃ peer, ev.cmd = .recv peer := by
      cases s <;> simp [Step.decryptMsgIdx?] at hs_dec <;>
        (cases hc : ev.cmd <;> simp [Step.FitsCmd, hc] at hs_fits; exact ⟨_, rfl⟩)
    obtain ⟨peer, hc_recv⟩ := hcmd_recv
    have he_in_r : e_in = .recv ev.input := by dsimp only [e_in]; rw [hc_recv]
    rw [he_in_r] at hrmb
    rw [htr_m] at hmsg
    have hrcol_on : RecvCollisionOn interp r S g (runTrace r ss_acc) vis_acc
        (honestSaltsOf r ss_acc) t_col :=
      (recvCollision_iff htr_m (congrArg (_root_.DY.Spqr.zeroKey :: ·) h.keys_eq)
        (prefixTerms_eq_of_visSendPtEq r _ h.vpt) (ptAtoms_eq_of_visSendPtEq h.vpt)).mp hrcol
    exact hnrc_step out b_col msgIdx t_col ⟨peer, hc_recv⟩ hexit
      ((recvBody_iff ev.input b_col).mpr hrmb) hs_dec hmsg hrcol_on
  refine ⟨τ ++ blk, ms ++ [m], {
    cs := by
      rw [Symbolic.Proofs.Swarm.UA.Base.flatEvents_append]
      exact Symbolic.Swarm.CREF.CliPure.coinSplit_append h.cs hcs_blk
    clean := ⟨⟨hmp', hout'⟩, not_readCollision_of_noReadColAt hnr'⟩
    nr := hnr'
    ppos := prekeyCallsPos_snoc h.ppos fun _ => by
      rw [hm_vis_m, hv_split]
      unfold callCount
      cases hc : ev.cmd <;> simp [hinp_kind, inputKind, hc]
    out2 := outcomeFaithfulCli2_snoc h.out2 fun _ _ => by simpa [htr_m] using hb.out2_ok
    rng32 := rngLengthsFaithfulCli_snoc h.rng32 (by simpa [htr_m] using hb.rng32_ok)
    tr_eq := by
      rw [runTrace_snoc, Symbolic.Proofs.Swarm.UA.Base.runTrace_append r ss_acc [s],
        htr_m, hb.next_eq]
      rfl
    keys_eq := by
      rw [honestKeysFrom_append, honestKeysOf_append]
      change honestKeysFrom (setupTrace r) ms ++ honestKeysFrom (runTraceMoves r ms) [m] =
        honestKeysOf (setupTrace r) ss_acc ++ honestKeysOf (runTrace r ss_acc) [s]
      rw [h.keys_eq, htr_m, hb.hkeys_eq]
    vpt := by
      rw [runVis_snoc, hm_vis_m]
      exact visSendPtEq_append h.vpt (visSendPtEq_refl v)
    mev := matchesEvents_snoc_run1 h.mev (by simpa [runTrace] using hrm0)
    sload := stateLoadSub_snoc_step h.sload hb.sload_eq (by rw [htr_m, hb.act_ok])
  }⟩

theorem schedFits_prefix {c₁ c₂ : List (Participant × Bool)}
    {who : List Participant} {ok : Nat → Bool}
    (h : SchedFits (c₁ ++ c₂) who ok) : SchedFits c₁ who ok := by
  refine ⟨?_, fun i p b hi => ?_⟩
  · have hpref := h.1
    rw [List.map_append] at hpref
    exact (List.prefix_append _ _).trans hpref
  · have hlt : i < c₁.length := (List.getElem?_eq_some_iff.mp hi).1
    exact h.2 i p b ((List.getElem?_append_left hlt).trans hi)

private theorem accInv_walk {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g : Ghost}
    {initIds₀ : Option BundlePreKeyIds}
    {tr₀ : ExecTrace} {ss_rem : List Step} {evs_rem : List CliEvent} {vs_rem : List VisEntry}
    (hmev : MatchesEventsClassicalAt interp r S g initIds₀ tr₀ ss_rem evs_rem vs_rem) :
    ∀ {evs_acc : List CliEvent} {ss_acc : List Step} {vis_acc : List VisEntry}
      {τ : List MachineEvent} {ms : List Move},
      initIds₀ = activeBundleIds evs_acc →
      tr₀ = runTrace r ss_acc →
      SchedFits (callsOf (evs_acc ++ evs_rem)) who ok →
      GhostWF g (vis_acc ++ vs_rem) →
      StepsWF ss_rem (runTrace r ss_acc) →
      StepsStateFaithful r (ss_acc ++ ss_rem) →
      ¬ ReadCollisionCliClassical interp r S g (ss_acc ++ ss_rem) (evs_acc ++ evs_rem) →
      AccInv interp r S who ok g evs_acc ss_acc vis_acc τ ms →
      ∃ τ' ms', AccInv interp r S who ok g (evs_acc ++ evs_rem) (ss_acc ++ ss_rem)
        (vis_acc ++ vs_rem) τ' ms' := by
  induction hmev with
  | nil hinv =>
    intro evs_acc ss_acc vis_acc τ ms _ _ _ _ hwf_rem _ _ hacc
    obtain ⟨ms', h1⟩ := accInv_step_invisible_list (rest := []) hinv (by simpa using hwf_rem) hacc
    exact ⟨τ, ms', by simpa using h1⟩
  | @run0 initIds tr_cur pre ss ev evs vs hinv hrej _ ih =>
    intro evs_acc ss_acc vis_acc τ ms hids₀ htr₀ hsched hgwf hwf_rem hsf_all hnrc_all hacc
    obtain ⟨ms₁, h1⟩ := accInv_step_invisible_list (rest := ss) hinv hwf_rem hacc
    obtain ⟨τ₂, ms₂, h2⟩ := accInv_step_run0 (evs_rem := evs) hsched hrej h1
    have hids₀' : initIds = activeBundleIds (evs_acc ++ [.run ev]) := by
      dsimp only [activeBundleIds] at hids₀ ⊢
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil,
        Symbolic.Proofs.Swarm.UA.Base.stepBundleIds_run_of_runRejected hrej, ← hids₀]
    have htr₀' : runSteps pre tr_cur = runTrace r (ss_acc ++ pre) := by
      rw [htr₀, Symbolic.Proofs.Swarm.UA.Base.runTrace_append]
    have hwf_ss : StepsWF ss (runTrace r (ss_acc ++ pre)) := by
      rw [Symbolic.Proofs.Swarm.UA.Base.runTrace_append]
      exact ((stepsWF_split_append pre ss (runTrace r ss_acc)).mp hwf_rem).2
    obtain ⟨τ', ms', h3⟩ := ih hids₀' htr₀'
      (by simpa [List.append_assoc] using hsched)
      hgwf hwf_ss
      (by simpa [List.append_assoc] using hsf_all)
      (by simpa [List.append_assoc] using hnrc_all) h2
    exact ⟨τ', ms', by simpa [List.append_assoc] using h3⟩
  | @env initIds tr_cur pre s ss ev evs v vs hinv hem _ ih =>
    intro evs_acc ss_acc vis_acc τ ms hids₀ htr₀ hsched hgwf hwf_rem hsf_all hnrc_all hacc
    obtain ⟨ms₁, h1⟩ := accInv_step_invisible_list (rest := s :: ss) hinv hwf_rem hacc
    have hwf_s : StepsWF (s :: ss) (runTrace r (ss_acc ++ pre)) := by
      rw [Symbolic.Proofs.Swarm.UA.Base.runTrace_append]
      exact ((stepsWF_split_append pre (s :: ss) (runTrace r ss_acc)).mp hwf_rem).2
    have hem' : EnvMatchesClassical interp r S g (runTrace r (ss_acc ++ pre)) s ev v := by
      rwa [Symbolic.Proofs.Swarm.UA.Base.runTrace_append, ← htr₀]
    obtain ⟨τ₂, ms₂, h2⟩ := accInv_step_env hwf_s.1 hwf_s.2.1 hem' h1
    have hids₀' : initIds = activeBundleIds (evs_acc ++ [.env ev]) := by
      dsimp only [activeBundleIds] at hids₀ ⊢
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]; exact hids₀
    have htr₀' : s.next (runSteps pre tr_cur) = runTrace r ((ss_acc ++ pre) ++ [s]) := by
      rw [htr₀, ← Symbolic.Proofs.Swarm.UA.Base.runTrace_append r ss_acc pre,
        Symbolic.Proofs.Swarm.UA.Base.runTrace_append r (ss_acc ++ pre) [s]]
      rfl
    have hwf_ss : StepsWF ss (runTrace r ((ss_acc ++ pre) ++ [s])) := by
      rw [Symbolic.Proofs.Swarm.UA.Base.runTrace_append r (ss_acc ++ pre) [s]]
      exact hwf_s.2.2
    obtain ⟨τ', ms', h3⟩ := ih hids₀' htr₀'
      (by simpa [List.append_assoc] using hsched)
      (by simpa [List.append_assoc] using hgwf)
      hwf_ss
      (by simpa [List.append_assoc] using hsf_all)
      (by simpa [List.append_assoc] using hnrc_all) h2
    exact ⟨τ', ms', by simpa [List.append_assoc] using h3⟩
  | @run1 initIds tr_cur pre s ss ev evs v vs hinv hrm _ ih =>
    intro evs_acc ss_acc vis_acc τ ms hids₀ htr₀ hsched hgwf hwf_rem hsf_all hnrc_all hacc
    obtain ⟨ms₁, h1⟩ := accInv_step_invisible_list (rest := s :: ss) hinv hwf_rem hacc
    have hwf_s : StepsWF (s :: ss) (runTrace r (ss_acc ++ pre)) := by
      rw [Symbolic.Proofs.Swarm.UA.Base.runTrace_append]
      exact ((stepsWF_split_append pre (s :: ss) (runTrace r ss_acc)).mp hwf_rem).2
    have hrm' : RunMatches interp r S g (runTrace r (ss_acc ++ pre)) s ev v (activeBundleIds evs_acc) := by
      rwa [Symbolic.Proofs.Swarm.UA.Base.runTrace_append, ← htr₀, ← hids₀]
    have hgwf_v : GhostWF g v :=
      ⟨fun ve hve => hgwf.1 ve (List.mem_append_right _ (List.mem_append_left _ hve)),
       hgwf.2.1,
       fun ve hve => hgwf.2.2 ve (List.mem_append_right _ (List.mem_append_left _ hve))⟩
    have hsf_step : ∀ (i : Nat) (si : Step) (p : Participant) (k : Nat) (b : Bool),
        (ss_acc ++ pre)[i]? = some si → si.stateLoad? = some (p, k, true) →
        si.ok (runTrace r ((ss_acc ++ pre).take i)) = true →
        s.stateLoad? = some (p, k, b) → False := by
      intro i si p k b hsi hsil hok hsl
      have hlt : i < (ss_acc ++ pre).length := (List.getElem?_eq_some_iff.mp hsi).1
      have htot : ss_acc ++ (pre ++ s :: ss) = (ss_acc ++ pre) ++ s :: ss := by
        simp [List.append_assoc]
      have hsi_all : (ss_acc ++ (pre ++ s :: ss))[i]? = some si := by
        rw [htot, List.getElem?_append_left hlt]; exact hsi
      have hsj_all : (ss_acc ++ (pre ++ s :: ss))[(ss_acc ++ pre).length]? = some s := by
        rw [htot]; simp
      have hok_all : si.ok (runTrace r ((ss_acc ++ (pre ++ s :: ss)).take i)) = true := by
        rw [htot, List.take_append_of_le_length (Nat.le_of_lt hlt)]; exact hok
      exact hsf_all i (ss_acc ++ pre).length si s p k b hlt hsi_all hsj_all hsil hok_all hsl
    have hnrc_step : ∀ (out b : HwBytes) (msgIdx : Nat) (t : _root_.DY.Bytes),
        (∃ peer, ev.cmd = .recv peer) → ev.exit = some (0, out) → RecvBody ev.input b →
        s.decryptMsgIdx? = some msgIdx →
        (runTrace r (ss_acc ++ pre)).getMessageSentAt msgIdx = some t →
        ¬ RecvCollisionOn interp r S g (runTrace r (ss_acc ++ pre)) vis_acc
            (honestSaltsOf r (ss_acc ++ pre)) t := by
      intro out b msgIdx t hcmd hexit hrb hdec hmsg hrcol
      exact hnrc_all ⟨evs_acc, ev, evs, ss_acc ++ pre, ss, s, vis_acc, msgIdx, out, b, t,
        rfl, by simp [List.append_assoc], hcmd, hexit, hrb, h1.mev, hdec, hmsg, hrcol⟩
    obtain ⟨τ₂, ms₂, h2⟩ := accInv_step_run1 hsched hgwf_v hwf_s.1 hwf_s.2.1 hrm'
      hsf_step hnrc_step h1
    have hids₀' : nextBundleIds initIds ev = activeBundleIds (evs_acc ++ [.run ev]) := by
      dsimp only [activeBundleIds] at hids₀ ⊢
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ← hids₀,
        Symbolic.Proofs.Swarm.UA.Base.stepBundleIds_run_of_runMatches hrm]
    have htr₀' : s.next (runSteps pre tr_cur) = runTrace r ((ss_acc ++ pre) ++ [s]) := by
      rw [htr₀, ← Symbolic.Proofs.Swarm.UA.Base.runTrace_append r ss_acc pre,
        Symbolic.Proofs.Swarm.UA.Base.runTrace_append r (ss_acc ++ pre) [s]]
      rfl
    have hwf_ss : StepsWF ss (runTrace r ((ss_acc ++ pre) ++ [s])) := by
      rw [Symbolic.Proofs.Swarm.UA.Base.runTrace_append r (ss_acc ++ pre) [s]]
      exact hwf_s.2.2
    obtain ⟨τ', ms', h3⟩ := ih hids₀' htr₀'
      (by simpa [List.append_assoc] using hsched)
      (by simpa [List.append_assoc] using hgwf)
      hwf_ss
      (by simpa [List.append_assoc] using hsf_all)
      (by simpa [List.append_assoc] using hnrc_all) h2
    exact ⟨τ', ms', by simpa [List.append_assoc] using h3⟩

/-- Every clean `ExplainsClassical` prefix explanation translates to a clean `ExplainsCli`
explanation with identical `runTrace`, `honestSalts`, `prefixTerms`, and `plaintextTerms`. -/
theorem xlate_inv : XlateInvSpec := by
  intro interp' r S who ok evs g ss vis hwf hS hsched hexp hnrc
  obtain ⟨hcompat, hgwf, ⟨_, _, hswf, hssf⟩, hmev⟩ := hexp
  obtain ⟨τ, ms, hf⟩ := accInv_walk hmev (evs_acc := []) (ss_acc := []) (vis_acc := [])
    rfl rfl (by simpa using hsched) (by simpa using hgwf) (by simpa [runTrace, runSteps] using hswf)
    (by simpa using hssf) (by simpa using hnrc) (accInv_nil hwf hS who ok hcompat)
  exact ⟨τ, ms,
    ⟨hf.cs, hf.clean.1.1, ⟨hf.clean.1.2, hf.out2⟩, hf.rng32⟩,
    hf.clean.2, hf.tr_eq,
    congrArg (_root_.DY.Spqr.zeroKey :: ·) hf.keys_eq,
    prefixTerms_eq_of_visSendPtEq r (runTrace r ss) hf.vpt,
    ptAtoms_eq_of_visSendPtEq hf.vpt⟩

end Symbolic.Proofs.Swarm.UA.XlateInv

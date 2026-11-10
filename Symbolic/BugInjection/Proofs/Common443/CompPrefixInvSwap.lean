/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Witnesses.CliShape
public import Symbolic.Proofs.Swarm.CREF.Prelude
public import Symbolic.Proofs.Swarm.CREF.ModelSplit
public import Symbolic.Proofs.Swarm.CREF.Xpl.InvCommon
public import Symbolic.Proofs.Swarm.CREF.Xpl.StepsMix
public import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1DecompSwap
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompPrefixInvSwap
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.HwEvents
open DY.Libsignal (HwBytes)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF ( NoSessionEffect noSessionEffect_of_no_accept)
open Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
cref_open
export Symbolic.BugInjection.Proofs.Common443.WsIdx1DecompSwap ( encrypt_act_eq_wrap encrypt_next_eq_wrap encrypt_isSetup_wrap encrypt_anchored_wrap encrypt_party?_wrap encrypt_stateLoad?_wrap encrypt_prekeyPath?_wrap encrypt_peerOk_wrap runMoves_fst_set_encrypt runTrace_set_wrap list_take_set_of_le list_take_set_of_gt runTrace_take_set_wrap encSend_map_kind encrypt_vis_map_kind runMoves_snd_map_kind_set_encrypt runVis_map_kind_set_wrap runVis_take_map_kind_set_wrap callCount_eq_of_map_kind_eq callCount_runVis_take_set_wrap list_eq_take_append_cons_drop list_set_eq_take_append_cons_drop runVis_set_wrap VisEntryRel VisEntryRel.refl VisEntryRel.eq_of_recv forall₂_append forall₂_visEntryRel_refl sendMatches_of_map_gamma_eq eventMatchesEntry_of_visEntryRel forall₂_eventMatchesEntry_of_visEntryRel forall₂_visEntryRel_encSend forall₂_visEntryRel_encrypt_vis forall₂_visEntryRel_runVis_set_wrap movesAnchored_set_encrypt compromisesCurrentFrom_set_encrypt ownSaltsFrom_set_encrypt getElem?_set_encrypt_props recvRepresentations_eq_of_runTrace_eq preKeyRepresentations_eq_of_runTrace_eq)
theorem peerFaithful_set_wrap {r : Records} {ms : List Move} {k : Nat} {me : Participant} {s cl pq : Nat} {w₂ : Option (Nat × Nat)} (hpeer : PeerFaithful r ms) : PeerFaithful r (ms.set k (.encrypt me s cl pq w₂)) :=
  fun m' hm' => (List.mem_or_eq_of_mem_set hm').elim (hpeer m') (fun h => h ▸ trivial)
theorem stateFaithful_set_wrap {r : Records} {ms : List Move} {k : Nat} {me : Participant} {s cl pq : Nat} {w₁ w₂ : Option (Nat × Nat)} (hk : ms[k]? = some (.encrypt me s cl pq w₁)) (hstate : StateFaithful r ms) : StateFaithful r (ms.set k (.encrypt me s cl pq w₂)) := by intro idx₁ idx₂ mi' mj' p stIdx b hlt hmi' hmj' hload₁ hrun hload₂; obtain ⟨mi, hmi, _, hst₁, _, hact₁, -⟩ := getElem?_set_encrypt_props hk hmi'; obtain ⟨mj, hmj, _, hst₂, -⟩ := getElem?_set_encrypt_props hk hmj'; rw [hact₁, runTrace_take_set_wrap hk idx₁] at hrun; exact hstate idx₁ idx₂ mi mj p stIdx b hlt hmi hmj (hst₁ ▸ hload₁) hrun (hst₂ ▸ hload₂)
theorem modelRun_set_wrap {r : Records} {ms : List Move} {k : Nat} {me : Participant} {s cl pq : Nat} {w₁ w₂ : Option (Nat × Nat)} (hk : ms[k]? = some (.encrypt me s cl pq w₁)) (hmr : DY.Libsignal.Composed.Refinement.ModelRun r ms) : DY.Libsignal.Composed.Refinement.ModelRun r (ms.set k (.encrypt me s cl pq w₂)) := by
  obtain ⟨hrnd, hsetup, ⟨hreach, hanc, hreach_take⟩, hcomp, hsalt, hpeer, hstate⟩ := hmr
  exact ⟨hrnd, fun m hm => (List.mem_or_eq_of_mem_set hm).elim (hsetup m) (fun h => h ▸ rfl), ⟨runTrace_set_wrap hk ▸ hreach, movesAnchored_set_encrypt ms (setupTrace r) k me s cl pq w₁ w₂ hk hanc,
    fun j => runTrace_take_set_wrap hk j ▸ hreach_take j⟩,
    compromisesCurrentFrom_set_encrypt ms (setupTrace r) k me s cl pq w₁ w₂ hk ▸ hcomp, ownSaltsFrom_set_encrypt ms (setupTrace r) k me s cl pq w₁ w₂ hk ▸ hsalt, peerFaithful_set_wrap hpeer, stateFaithful_set_wrap hk hstate⟩
theorem roleFaithful_set_wrap {r : Records} {who : List Participant} {ms : List Move} {k : Nat} {me : Participant} {s cl pq : Nat} {w₁ w₂ : Option (Nat × Nat)} (hk : ms[k]? = some (.encrypt me s cl pq w₁)) (hrole : RoleFaithful r who ms) : RoleFaithful r who (ms.set k (.encrypt me s cl pq w₂)) := by intro idx m' p hm' hp; obtain ⟨m, hm, hparty, -⟩ := getElem?_set_encrypt_props hk hm'; rw [callCount_runVis_take_set_wrap hk idx]; exact hrole idx m p hm (hparty ▸ hp)
theorem pathFaithful_set_wrap {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {τ₁ : List MachineEvent} {k : Nat} {me : Participant} {s cl pq : Nat} {w₁ w₂ : Option (Nat × Nat)} (hk : ms[k]? = some (.encrypt me s cl pq w₁)) (hpath : PathFaithful i r S g ms τ₁) : PathFaithful i r S g (ms.set k (.encrypt me s cl pq w₂)) τ₁ := by intro idx m' promote b p hm' hpp hcs hp; obtain ⟨m, hm, _, _, hpre, -⟩ := getElem?_set_encrypt_props hk hm'; rw [callCount_runVis_take_set_wrap hk idx] at hcs; rw [runTrace_take_set_wrap hk idx]; exact hpath idx m promote b p hm (hpre ▸ hpp) hcs hp
theorem outcomeFaithful_set_wrap {r : Records} {ok : Nat → Bool} {ms : List Move} {k : Nat} {me : Participant} {s cl pq : Nat} {w₁ w₂ : Option (Nat × Nat)} (hk : ms[k]? = some (.encrypt me s cl pq w₁)) (hout : OutcomeFaithful r ok ms) : OutcomeFaithful r ok (ms.set k (.encrypt me s cl pq w₂)) := by intro idx m' hm'; obtain ⟨m, hm, _, _, _, _, hnext, hrej⟩ := getElem?_set_encrypt_props hk hm'; dsimp only; rw [callCount_runVis_take_set_wrap hk idx, runTrace_take_set_wrap hk idx, hnext]; have ho := hout idx m hm; exact ⟨fun ds hds => ho.1 ds (hrej ds hds), ho.2⟩
private theorem mem_zip_of_visEntryRel_recv {i : ExternInterpretation} {S : Sem} {g : Ghost} {vs₁ vs₂ : List VisEntry} (hrel : List.Forall₂ (VisEntryRel i S g) vs₁ vs₂) : ∀ {τ : List MachineEvent} {ev : MachineEvent × VisEntry}, ev ∈ τ.zip vs₂ → ev.2.kind = .recv → ev ∈ τ.zip vs₁ := by
  induction hrel with
  | nil => intro τ ev hmem _; rw [List.zip_nil_right] at hmem; cases hmem
  | cons hr _ ih =>
    intro τ ev hmem hkind; cases τ with
    | nil => cases hmem
    | cons e τ' =>
      simp only [List.zip_cons_cons, List.mem_cons] at hmem ⊢
      rcases hmem with rfl | hmem
      · left; rw [VisEntryRel.eq_of_recv hr hkind]
      · right; exact ih hmem hkind
theorem readFaithful_set_wrap {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {τ₁ : List MachineEvent} {k : Nat} {me : Participant} {s cl pq e c e' c' : Nat} (hk : ms[k]? = some (.encrypt me s cl pq (some (e, c)))) (hγ : (received (runTraceMoves r (ms.take k)) [e, c]).map (gamma i S g) = (received (runTraceMoves r (ms.take k)) [e', c']).map (gamma i S g)) (hread : ReadFaithful i r S g ms τ₁) : ReadFaithful i r S g (ms.set k (.encrypt me s cl pq (some (e', c')))) τ₁ := by intro ev hev hkind; have htr := runTrace_set_wrap (r := r) (w₂ := some (e', c')) hk; rw [recvRepresentations_eq_of_runTrace_eq htr, preKeyRepresentations_eq_of_runTrace_eq htr]; exact hread ev (mem_zip_of_visEntryRel_recv (forall₂_visEntryRel_runVis_set_wrap hk hγ) hev hkind) hkind
theorem matchedPrefix_set_wrap {i : ExternInterpretation} {r : Records} {S : Sem} {who : List Participant} {g : Ghost} {ms : List Move} {τ₁ : List MachineEvent} {k : Nat} {me : Participant} {s cl pq e c e' c' : Nat} (hk : ms[k]? = some (.encrypt me s cl pq (some (e, c)))) (hγ : (received (runTraceMoves r (ms.take k)) [e, c]).map (gamma i S g) = (received (runTraceMoves r (ms.take k)) [e', c']).map (gamma i S g)) (hmp : DY.Libsignal.Composed.Refinement.MatchedPrefix i r S who g ms τ₁) : DY.Libsignal.Composed.Refinement.MatchedPrefix i r S who g (ms.set k (.encrypt me s cl pq (some (e', c')))) τ₁ := by obtain ⟨hcompat, hmr, hrole, hpath, hread, hvis⟩ := hmp; exact ⟨hcompat, modelRun_set_wrap hk hmr, roleFaithful_set_wrap hk hrole, pathFaithful_set_wrap hk hpath, readFaithful_set_wrap hk hγ hread, forall₂_eventMatchesEntry_of_visEntryRel hvis (forall₂_visEntryRel_runVis_set_wrap hk hγ)⟩
theorem explains_set_wrap {i : ExternInterpretation} {r : Records} {S : Sem} {who : List Participant} {ok : Nat → Bool} {g : Ghost} {ms : List Move} {τ₁ : List MachineEvent} {k : Nat} {me : Participant} {s cl pq e c e' c' : Nat} (hk : ms[k]? = some (.encrypt me s cl pq (some (e, c)))) (hγ : (received (runTraceMoves r (ms.take k)) [e, c]).map (gamma i S g) = (received (runTraceMoves r (ms.take k)) [e', c']).map (gamma i S g)) (hex : DY.Libsignal.Composed.Refinement.ExplainsMoves i r S who ok g ms τ₁) : DY.Libsignal.Composed.Refinement.ExplainsMoves i r S who ok g (ms.set k (.encrypt me s cl pq (some (e', c')))) τ₁ := ⟨matchedPrefix_set_wrap hk hγ hex.1, outcomeFaithful_set_wrap hk hex.2⟩
def NoBobDone (tr : ExecTrace) : Prop := ∀ j : Nat, ((tr.getEventAt DY.Libsignal.PQXDH.PQXDHEvent j).map isBobDone).getD false = false
theorem noBobDone_nil : NoBobDone (Trace.nil : ExecTrace) := by
  intro j; rw [getEventAt_eq_at?, Symbolic.Swarm.CREF.at?_ge_length Trace.nil (by simp [length_nil_eq])]; rfl
theorem bobDoneBaseKeys_eq_nil_of_noBobDone {tr : ExecTrace} (h : NoBobDone tr) : bobDoneBaseKeys tr = [] := by
  unfold bobDoneBaseKeys; rw [List.filterMap_eq_nil_iff]; intro j _
  have hj := h j; rcases hev : tr.getEventAt DY.Libsignal.PQXDH.PQXDHEvent j with _ | ev
  · rfl
  · cases ev <;> (try rfl); rw [hev] at hj; cases hj
theorem at?_append_eq_of_eq {T S : Type} [ExecTraceTypes.Has T] [ExecTraceTypes.Has S] (tr : ExecTrace) (x : S) {i : Nat} (hi : i = tr.length) : ((tr.append x).at? i : Option T) = TraceEntryHas.proj (TraceEntryHas.inj x : ExecTrace.Entry) := by
  subst hi; exact Symbolic.Swarm.CREF.at?_append_length tr x
theorem noBobDone_append_other {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} (h : NoBobDone tr) (e : E) (hnone : ((TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)).map (fun x => isBobDone x.ev)).getD false = false) : NoBobDone (tr.append e) := by
  intro j; rw [getEventAt_eq_at?]
  by_cases hj : j < tr.length
  · rw [at?_append_of_lt tr e hj, ← getEventAt_eq_at?]; exact h j
  · by_cases hjeq : j = tr.length
    · subst hjeq; rw [at?_append_eq_of_eq (T := DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent) tr e rfl]
      rcases hproj : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
        Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) with _ | ⟨ev⟩
      · rfl
      · rw [hproj] at hnone; exact hnone
    · rw [Symbolic.Swarm.CREF.at?_ge_length (tr.append e) (by rw [length_append_entry_eq]; omega)]; rfl
theorem noBobDone_of_quiet {α : Type} {x : Traceful α} (hq : Symbolic.Swarm.CREF.XplSteps.XQuiet x) : Preserves NoBobDone x := by
  intro tr htr j
  by_cases hj : j < tr.length
  · rw [Symbolic.Swarm.CREF.XplSteps.xgetEventAt_le_eq (Symbolic.Swarm.CREF.XplSteps.xrun_le x tr) hj]; exact htr j
  · rw [getEventAt_eq_at?, (hq tr j (by omega)).2.1]; rfl
theorem NoBobDone.preserves_storeLocalState_pq (me : Participant) (st : PQXDH.PQXDHState) : Preserves NoBobDone (DY.PersistentLocalState.storeLocalState me st) := by
  intro tr h; rw [storeLocalState_pq_snd_eq]; exact noBobDone_append_other h (PQStE me st) rfl
theorem NoBobDone.preserves_storeLocalState_tr (me : Participant) (st : DY.Libsignal.TripleRatchet.TRState) : Preserves NoBobDone (DY.PersistentLocalState.storeLocalState me st) := by
  intro tr h; rw [storeLocalState_tr_snd_eq]; exact noBobDone_append_other h (TRStE me st) rfl
theorem NoBobDone.preserves_logEvent_pq {ev : PQXDH.PQXDHEvent} (hev : isBobDone ev = false) : Preserves NoBobDone (DY.ProtocolEvent.logEvent ev) := by
  intro tr h; rw [logEvent_snd_eq]; exact noBobDone_append_other h (PQEvE ev) hev
theorem NoBobDone.preserves_logEvent_tr (ev : DY.Libsignal.TripleRatchet.TREvent) : Preserves NoBobDone (DY.ProtocolEvent.logEvent ev) := by
  intro tr h; rw [logEvent_snd_eq]; exact noBobDone_append_other h (TREvE ev) rfl
theorem NoBobDone.preserves_logEvent_c (ev : CEvent) : Preserves NoBobDone (DY.ProtocolEvent.logEvent ev) := by
  intro tr h; rw [logEvent_snd_eq]; exact noBobDone_append_other h (CEvE ev) rfl
theorem NoBobDone.preserves_logSkippedKeys (s : DY.Libsignal.TripleRatchet.SessionInfo) (pk : DY.Bytes) (r src : Nat) : ∀ (k : Nat) (ck : DY.Bytes) (n : UInt32), Preserves NoBobDone (DY.Libsignal.TripleRatchet.logSkippedKeys s pk r src ck n k)
  | 0, _, _ => Preserves.pure _
  | k + 1, _, _ => by
    rw [DY.Libsignal.TripleRatchet.logSkippedKeys]; exact Preserves.bind (NoBobDone.preserves_logEvent_tr _) fun _ =>
      NoBobDone.preserves_logSkippedKeys s pk r src k _ _
theorem NoBobDone.preserves_logMessageKeyAndStore (me : Participant) (s : DY.Libsignal.TripleRatchet.SessionInfo) (dir : DY.Libsignal.TripleRatchet.KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32) (r p : Nat) (st : DY.Libsignal.TripleRatchet.TRState) : Preserves NoBobDone (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n r p st) := by
  unfold DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  exact Preserves.bind (NoBobDone.preserves_logEvent_tr _) fun _ => NoBobDone.preserves_storeLocalState_tr _ _
local macro "nbd_step" : tactic =>
  `(tactic| first
    | with_reducible refine Preserves.bind ?_ fun _ => ?_
    | with_reducible exact NoBobDone.preserves_logEvent_tr _
    | with_reducible exact NoBobDone.preserves_logEvent_pq rfl
    | with_reducible exact NoBobDone.preserves_logEvent_c _
    | with_reducible exact NoBobDone.preserves_storeLocalState_tr _ _
    | with_reducible exact NoBobDone.preserves_storeLocalState_pq _ _
    | with_reducible exact NoBobDone.preserves_logSkippedKeys _ _ _ _ _ _ _
    | with_reducible exact NoBobDone.preserves_logMessageKeyAndStore _ _ _ _ _ _ _ _ _
    | with_reducible exact noBobDone_of_quiet (Symbolic.Swarm.CREF.XplSteps.xquiet_bobHandshake _ _ _ _ _ _)
    | with_reducible exact noBobDone_of_quiet (Symbolic.Swarm.CREF.XplSteps.xquiet_aliceHandshake _ _ _ _ _)
    | with_reducible exact noBobDone_of_quiet (Symbolic.Swarm.CREF.XplSteps.xquiet_receiveSignalMsg _)
    | with_reducible exact noBobDone_of_quiet (Symbolic.Swarm.CREF.XplSteps.xquiet_ensureReceiverChain _ _)
    | with_reducible exact noBobDone_of_quiet (Symbolic.Swarm.CREF.XplSteps.xquiet_verifyMacAndDecrypt _ _ _ _)
    | with_reducible exact noBobDone_of_quiet (Symbolic.Swarm.CREF.XplSteps.xquiet_genRand _)
    | with_reducible exact noBobDone_of_quiet (Symbolic.Swarm.CREF.XplSteps.xquiet_sendMessage _)
    | with_reducible exact noBobDone_of_quiet (Symbolic.Swarm.CREF.XplSteps.xquiet_of_fix (Symbolic.Swarm.CREF.XplSteps.xfix_receiveMessage _))
    | with_reducible exact noBobDone_of_quiet (Symbolic.Swarm.CREF.XplSteps.xquiet_of_fix (Symbolic.Swarm.CREF.XplSteps.xfix_getKey _ _ _))
    | with_reducible exact noBobDone_of_quiet (Symbolic.Swarm.CREF.XplSteps.xquiet_of_fix (Symbolic.Swarm.CREF.XplSteps.xfix_getLocalState _ _))
    | with_reducible exact noBobDone_of_quiet (Symbolic.Swarm.CREF.XplSteps.xquiet_of_fix (Symbolic.Swarm.CREF.XplSteps.xfix_getEntry _))
    | with_reducible exact noBobDone_of_quiet (Symbolic.Swarm.CREF.XplSteps.xquiet_of_fix (Symbolic.Swarm.CREF.XplSteps.xfix_guard _))
    | with_reducible exact noBobDone_of_quiet (Symbolic.Swarm.CREF.XplSteps.xquiet_of_fix Symbolic.Swarm.CREF.XplSteps.xfix_traceLength)
    | with_reducible exact noBobDone_of_quiet (Symbolic.Swarm.CREF.XplSteps.xquiet_of_fix (Symbolic.Swarm.CREF.XplSteps.xfix_guardOnTrace _))
    | with_reducible exact noBobDone_of_quiet (Symbolic.Swarm.CREF.XplSteps.xquiet_of_fix (Symbolic.Swarm.CREF.XplSteps.xfix_guardTrace _))
    | with_reducible exact noBobDone_of_quiet (Symbolic.Swarm.CREF.XplSteps.xquiet_of_fix (Symbolic.Swarm.CREF.XplSteps.xfix_pure _))
    | with_reducible exact noBobDone_of_quiet (Symbolic.Swarm.CREF.XplSteps.xquiet_of_fix Symbolic.Swarm.CREF.XplSteps.xfix_failure)
    | split)
theorem NoBobDone.preserves_registerIdentity (p : Participant) : Preserves NoBobDone (PQXDH.registerIdentity p) := by unfold PQXDH.registerIdentity; repeat' nbd_step
theorem NoBobDone.preserves_genSignedPrekey (b : Participant) (idStateIdx : Nat) : Preserves NoBobDone (PQXDH.genSignedPrekey b idStateIdx) := by unfold PQXDH.genSignedPrekey; repeat' nbd_step
theorem NoBobDone.preserves_genPQPrekey (b : Participant) (idStateIdx : Nat) : Preserves NoBobDone (PQXDH.genPQPrekey b idStateIdx) := by unfold PQXDH.genPQPrekey; repeat' nbd_step
theorem NoBobDone.preserves_genOneTimePrekey (b : Participant) : Preserves NoBobDone (PQXDH.genOneTimePrekey b) := by unfold PQXDH.genOneTimePrekey; repeat' nbd_step
theorem NoBobDone.preserves_setupAct (a b : Participant) (withOpk : Bool) : Preserves NoBobDone (setupAct a b withOpk) := by
  unfold setupAct
  refine Preserves.bind (NoBobDone.preserves_registerIdentity a) fun _ => ?_
  refine Preserves.bind (NoBobDone.preserves_registerIdentity b) fun hB => ?_
  refine Preserves.bind (NoBobDone.preserves_genSignedPrekey b hB) fun _ => ?_
  refine Preserves.bind (NoBobDone.preserves_genPQPrekey b hB) fun _ => ?_
  cases withOpk; · exact Preserves.pure ()
  · simp only [↓reduceIte]; exact Preserves.bind (NoBobDone.preserves_genOneTimePrekey b) fun _ => Preserves.pure ()
theorem noBobDone_setupTrace (r : Records) : NoBobDone (setupTrace r) := NoBobDone.preserves_setupAct r.alice r.bob r.withOpk Trace.nil noBobDone_nil
theorem NoBobDone.preserves_aliceStart (a b : Participant) (i r : Nat) (h : PQXDH.BundleHandles) : Preserves NoBobDone (DY.Libsignal.Composed.aliceStart a b i r h) := by simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]; repeat' nbd_step
theorem NoBobDone.preserves_messageEncrypt (me : Participant) (si cl pq : Nat) : Preserves NoBobDone (DY.Libsignal.TripleRatchet.messageEncrypt me si cl pq) := by unfold DY.Libsignal.TripleRatchet.messageEncrypt; repeat' nbd_step
theorem NoBobDone.preserves_messageEncryptAbort (me : Participant) (si : Nat) : Preserves NoBobDone (DY.Libsignal.TripleRatchet.messageEncryptAbort me si) := by unfold DY.Libsignal.TripleRatchet.messageEncryptAbort; repeat' nbd_step
theorem NoBobDone.preserves_compromiseIK (p : Participant) (si : Nat) : Preserves NoBobDone (PQXDH.compromiseIK p si) := by unfold PQXDH.compromiseIK; repeat' nbd_step
theorem NoBobDone.preserves_compromiseSPK (b : Participant) (si : Nat) : Preserves NoBobDone (PQXDH.compromiseSPK b si) := by unfold PQXDH.compromiseSPK; repeat' nbd_step
theorem NoBobDone.preserves_compromisePQSPK (b : Participant) (si : Nat) : Preserves NoBobDone (PQXDH.compromisePQSPK b si) := by unfold PQXDH.compromisePQSPK; repeat' nbd_step
theorem NoBobDone.preserves_compromiseOPK (b : Participant) (si : Nat) : Preserves NoBobDone (PQXDH.compromiseOPK b si) := by unfold PQXDH.compromiseOPK; repeat' nbd_step
theorem NoBobDone.preserves_exposeKey (me : Participant) (si : Nat) (k : DY.Libsignal.TripleRatchet.KeyComponent) : Preserves NoBobDone (DY.Libsignal.TripleRatchet.exposeKey me si k) := by unfold DY.Libsignal.TripleRatchet.exposeKey; repeat' nbd_step
theorem NoBobDone.preserves_exposeSpqr (me : Participant) (si : Nat) : Preserves NoBobDone (DY.Libsignal.TripleRatchet.exposeSpqr me si) := by unfold DY.Libsignal.TripleRatchet.exposeSpqr; repeat' nbd_step
theorem NoBobDone.preserves_exposeSkipped (si : Nat) : Preserves NoBobDone (DY.Libsignal.TripleRatchet.exposeSkipped si) := by unfold DY.Libsignal.TripleRatchet.exposeSkipped; repeat' nbd_step
theorem noBobDone_of_noSessionEffect {tr : ExecTrace} {m : Move} (htr : NoBobDone tr) (heff : NoSessionEffect tr m) : NoBobDone (m.next tr) := by
  intro j; have hle : tr ≤ m.next tr := m.le_next tr
  by_cases hj : j < tr.length
  · rw [getEventAt_eq_at?, Symbolic.Swarm.CREF.XplSteps.xat?_le_eq hle hj, ← getEventAt_eq_at?]; exact htr j
  · by_cases hj' : j < (m.next tr).length
    · have hmem : j ∈ newIndices tr (m.next tr) :=
        Symbolic.Swarm.CREF.XplSteps.xpl_mem_newIndices (by omega) hj'
      rw [getEventAt_eq_at?]
      cases hat : ((m.next tr).at? j : Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) with
      | none => rfl
      | some e =>
        have hbd := Symbolic.Proofs.Swarm.CREF.Cli.MoveBrkLemmas.nonSessionPQAt_pred_eq_false (heff j hmem).2.1 hat (p := isBobDone)
        simp [hbd]
    · rw [getEventAt_eq_at?, Symbolic.Swarm.CREF.at?_ge_length (m.next tr) (by omega)]; rfl
theorem noBobDone_move_of_noAccept {m : Move} {tr : ExecTrace} (hs : m.isSetup = false) (ha : m.LogsSessionCompletion tr) (hacc : ∀ v ∈ m.vis tr, v.kind ≠ .accept) (htr : NoBobDone tr) : NoBobDone (m.next tr) := by
  cases m
  case setup => cases hs
  case aliceStart a b i r h _ =>
    exact (Preserves.bind (NoBobDone.preserves_aliceStart a b i r h) fun _ => Preserves.pure _) tr htr
  case bobStart | decrypt | decryptSkipped | reject =>
    exact noBobDone_of_noSessionEffect htr (noSessionEffect_of_no_accept trivial ha hacc)
  case encrypt me si cl pq _ =>
    exact (Preserves.bind (NoBobDone.preserves_messageEncrypt me si cl pq) fun _ => Preserves.pure _) tr htr
  case encryptAbort me si =>
    exact (Preserves.bind (NoBobDone.preserves_messageEncryptAbort me si) fun _ => Preserves.pure _) tr htr
  case encryptFail me si cl =>
    exact (Preserves.bind Preserves.traceLength fun n =>
      Preserves.bind (NoBobDone.preserves_messageEncrypt me si cl (n + 3)) fun _ => Preserves.pure _) tr htr
  case compromiseIK p si =>
    exact (Preserves.bind (NoBobDone.preserves_compromiseIK p si) fun _ => Preserves.pure _) tr htr
  case compromiseSPK b si =>
    exact (Preserves.bind (NoBobDone.preserves_compromiseSPK b si) fun _ => Preserves.pure _) tr htr
  case compromisePQSPK b si =>
    exact (Preserves.bind (NoBobDone.preserves_compromisePQSPK b si) fun _ => Preserves.pure _) tr htr
  case compromiseOPK b si =>
    exact (Preserves.bind (NoBobDone.preserves_compromiseOPK b si) fun _ => Preserves.pure _) tr htr
  case exposeKey me si k =>
    exact (Preserves.bind (NoBobDone.preserves_exposeKey me si k) fun _ => Preserves.pure _) tr htr
  case exposeSpqr me si =>
    exact (Preserves.bind (NoBobDone.preserves_exposeSpqr me si) fun _ => Preserves.pure _) tr htr
  case exposeSkipped si =>
    exact (Preserves.bind (NoBobDone.preserves_exposeSkipped si) fun _ => Preserves.pure _) tr htr
  case attackerSend t =>
    exact noBobDone_of_noSessionEffect htr (Symbolic.Swarm.CREF.XplSteps.xpl_noEff_attackerSend t tr)
  case brkDH =>
    exact NoBobDone.preserves_logEvent_pq rfl tr htr
  case brkKEM =>
    exact NoBobDone.preserves_logEvent_pq rfl tr htr
theorem noBobDone_runMoves_of_noAccept : ∀ (ms : List Move) (tr : ExecTrace), (∀ m ∈ ms, m.isSetup = false) → MovesAnchored ms tr → (∀ v ∈ (runMoves ms tr).2, v.kind ≠ .accept) → NoBobDone tr → NoBobDone (runMoves ms tr).1
  | [], _, _, _, _, htr => htr
  | m :: ms, tr, hsetup, ⟨ha, hanc⟩, hacc, htr =>
    noBobDone_runMoves_of_noAccept ms (m.next tr) (fun m' hm' => hsetup m' (List.mem_cons_of_mem _ hm')) hanc (fun v hv => hacc v (List.mem_append_right _ hv))
      (noBobDone_move_of_noAccept (hsetup m (List.mem_cons_self ..)) ha (fun v hv => hacc v (List.mem_append_left _ hv)) htr)
private theorem vis_kind_ne_accept_of_forall₂ {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {τ : List MachineEvent} {vs : List VisEntry} (hm : List.Forall₂ (EventMatchesEntry i r S g) τ vs) (hna : ∀ e ∈ τ, eventKind e ≠ .accept) : ∀ v ∈ vs, v.kind ≠ .accept := by
  induction hm with
  | nil => intro v hv; cases hv
  | cons h1 _ ih =>
    intro v hv; rcases List.mem_cons.1 hv with rfl | hv
    · rw [← h1.1]; exact hna _ (List.mem_cons_self ..)
    · exact ih (fun e he => hna e (List.mem_cons_of_mem _ he)) v hv
theorem bobDone_nil_of_noAccept_matchedPrefix {i : ExternInterpretation} {r : Records} {S : Sem} {who : List Participant} {g : Ghost} {ms : List Move} {τ₁ : List MachineEvent} (hmp : DY.Libsignal.Composed.Refinement.MatchedPrefix i r S who g ms τ₁) (hna : ∀ e ∈ τ₁, eventKind e ≠ .accept) : bobDoneBaseKeys (runTraceMoves r ms) = [] := by
  obtain ⟨_, ⟨_, hsetup, ⟨_, hanc, _⟩, _⟩, _, _, _, hvis⟩ := hmp
  have hno_acc := vis_kind_ne_accept_of_forall₂ hvis hna
  apply bobDoneBaseKeys_eq_nil_of_noBobDone
  rw [Symbolic.Swarm.CREF.xpl_runTrace_eq]
  refine noBobDone_runMoves_of_noAccept ms (setupTrace r) hsetup hanc ?_ (noBobDone_setupTrace r)
  intro v hv; apply hno_acc v; unfold runVis; simp only [runMoves]; exact List.mem_append_right _ hv
theorem bobDone_nil_of_noAccept {i : ExternInterpretation} {r : Records} {S : Sem} {who : List Participant} {ok : Nat → Bool} {g : Ghost} {ms : List Move} {τ₁ : List MachineEvent} (hex : DY.Libsignal.Composed.Refinement.ExplainsMoves i r S who ok g ms τ₁) (hna : ∀ e ∈ τ₁, eventKind e ≠ .accept) : bobDoneBaseKeys (runTraceMoves r ms) = [] := bobDone_nil_of_noAccept_matchedPrefix hex.1 hna
end Symbolic.BugInjection.Proofs.Common443.CompPrefixInvSwap

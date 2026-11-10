/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop
public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts
public import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct
public import Symbolic.Proofs.Swarm.CREF.Xpl.InvIni
public import Symbolic.Proofs.Swarm.CREF.Xpl.InvSend
public import Symbolic.Proofs.Swarm.CREF.Xpl.InvRpk
public import Symbolic.Proofs.Swarm.CREF.Xpl.StepsMix
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.BobDone
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
open DY.Libsignal.PQXDH (PQXDHEvent)
open DY.Libsignal.TripleRatchet (TRState)
open Symbolic.BugInjection Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
theorem not_eventMatchesEntry_whisper_of_head (i : ExternInterpretation) (r : Records) (S : Sem) (g : Ghost) (b_wire : HwBytes) (ts : List DY.Bytes) (a : Option Nat) (hhead : b_wire.head? = some 0x03#8) : ¬ EventMatchesEntry i r S g (.recv b_wire) ⟨.recv, ts, .whisper, a⟩ := by rintro ⟨_, t, _, hb⟩; change b_wire = DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag :: gamma i S g t at hb; rw [hb] at hhead; cases hhead
theorem preKeyInner_rejected_of_foreign (i : ExternInterpretation) (r : Records) (S : Sem) (g : Ghost) (b : HwBytes) (p : PreKeyFields) (eks ts : List DY.Bytes) (a : Option Nat) (hp : parsePreKeyWire b = some p) (hne : ∀ ek ∈ eks, p.baseKey.take 33 ≠ ecKey (gamma i S g ek)) : ¬ EventMatchesEntry i r S g (.recv b) ⟨.recv, ts, .preKeyInner eks, a⟩ := by rintro ⟨-, _, p', -, hp', ⟨ek, hek, hbk⟩, -⟩; change parsePreKeyWire b = some p' at hp'; rw [hp] at hp'; cases hp'; exact hne ek hek hbk
theorem bobDoneBaseKeys_next_of_noSessionEffect {tr : ExecTrace} {m : Move} (h : Symbolic.Swarm.CREF.NoSessionEffect tr m) : bobDoneBaseKeys (m.next tr) = bobDoneBaseKeys tr :=
  Symbolic.Proofs.Swarm.CREF.Cli.MoveBrkLemmas.bobDoneBaseKeys_eq_of_nonSessionPQExt
    (m.le_next tr) fun i hlo hhi =>
      (h i (Symbolic.Swarm.CREF.XplSteps.xpl_mem_newIndices hlo hhi)).2.1
theorem bobDoneBaseKeys_runMoves_of_movesFrom :
    ∀ (tr : ExecTrace) (δ : List Move), Symbolic.Swarm.CREF.MovesFrom Symbolic.Swarm.CREF.InvisibleNoEffect tr δ → bobDoneBaseKeys (runMoves δ tr).1 = bobDoneBaseKeys tr
  | tr, [], _ => rfl
  | tr, m :: δ, ⟨⟨_, hm⟩, hδ⟩ => by simp only [runMoves]; rw [bobDoneBaseKeys_runMoves_of_movesFrom (m.next tr) δ hδ, bobDoneBaseKeys_next_of_noSessionEffect hm]
theorem rpkBlock_not_decrypt_or_skipped (i : ExternInterpretation) (r : Records) (S : Sem) (g : Ghost) (ms₀ : List Move) (tr_pre : ExecTrace) (b_wire b_rng b_pt : HwBytes) (p : PreKeyFields) (m : Move) (hhead : b_wire.head? = some 0x03#8) (hp : parsePreKeyWire b_wire = some p) (hunk : ¬ KnownBaseKey i r S g ms₀ p) (hbob_eq : bobDoneBaseKeys tr_pre = bobDoneBaseKeys (runTraceMoves r ms₀)) (hdec : ∃ p', Symbolic.Swarm.CREF.DecryptBy p' m) (hm : List.Forall₂ (EventMatchesEntry i r S g) [.recv b_wire, .rng b_rng, .accept b_pt] (m.vis tr_pre)) : False := by
  obtain ⟨v, u', hv, _, hvu⟩ := Symbolic.Swarm.CREF.xpl_forall₂_cons_left hm
  have hv_mem : v ∈ m.vis tr_pre := by rw [hvu]; exact List.mem_cons_self ..
  have hvk : v.kind = .recv := hv.1.symm; rw [Symbolic.Swarm.CREF.xpl_vis_eq] at hv_mem
  rcases List.mem_append.1 hv_mem with hown | hexp
  · rcases hdec with ⟨p', hp'⟩; unfold Symbolic.Swarm.CREF.DecryptBy at hp'
    cases m <;> try exact False.elim hp'
    all_goals
      dsimp only [Symbolic.Swarm.CREF.xpl_ownVis, decVis] at hown
      rcases List.mem_append.1 hown with h12 | h3
      · rcases List.mem_append.1 h12 with h1 | h2
        · rename_i wrapped; obtain ⟨b_msg, _, rfl⟩ := Option.map_eq_some_iff.1 (Option.mem_toList.1 h1)
          cases wrapped
          · exact not_eventMatchesEntry_whisper_of_head i r S g b_wire [b_msg] none hhead hv
          · refine preKeyInner_rejected_of_foreign i r S g b_wire p (sessionBaseKeys tr_pre _) [b_msg] none hp ?_ hv
            exact fun ek hek hbk => hunk ⟨ek, hbob_eq ▸ mem_bobDoneBaseKeys_of_mem_sessionBaseKeys hek, hbk⟩
        · obtain ⟨_, _, rfl⟩ := List.mem_map.1 h2; cases hvk
      · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 (Option.mem_toList.1 h3); cases hvk
  · have hk := Symbolic.Swarm.CREF.xpl_exposures_kind hexp; rw [hvk] at hk; cases hk
theorem rpkTriple_rpkShape (b_wire b_rng b_pt : HwBytes) :
    Symbolic.Swarm.CREF.RpkBlockShape [.recv b_wire, .rng b_rng, .accept b_pt] where
  head := ⟨b_wire, rfl⟩
  tail := by intro e he; simp only [List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at he; rcases he with rfl | rfl <;> [exact Or.inl rfl; exact Or.inr rfl]
  len := by simp
theorem matchedPrefix_rpk_bobStart_only (i : ExternInterpretation) (r : Records) (S : Sem) (g : Ghost) (τ_pre : List MachineEvent) (b_wire b_rng b_pt : HwBytes) (ms : List Move) (p : PreKeyFields) (hhead : b_wire.head? = some 0x03#8) (hp : parsePreKeyWire b_wire = some p) (hunk : ∀ ms₀, Swarm.CREF.MatchedPrefix i r S g ms₀ τ_pre → ¬ KnownBaseKey i r S g ms₀ p) (hmp : Swarm.CREF.MatchedPrefix i r S g ms (τ_pre ++ [.recv b_wire, .rng b_rng, .accept b_pt])) : ∃ ms₀ pre post b a kh regIdxA mh pqIdx spqrMsgIdx shown, ms = ms₀ ++ (pre ++ Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown :: post) ∧ Swarm.CREF.MatchedPrefix i r S g ms₀ τ_pre ∧ ModelRun r ms ∧ Symbolic.Swarm.CREF.MovesFrom Symbolic.Swarm.CREF.InvisibleNoEffect (runTraceMoves r ms₀) pre ∧ Symbolic.Swarm.CREF.MovesFrom Symbolic.Swarm.CREF.InvisibleNoEffect ((Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown).next (runMoves pre (runTraceMoves r ms₀)).1) post ∧ bobDoneBaseKeys (runMoves pre (runTraceMoves r ms₀)).1 = bobDoneBaseKeys (runTraceMoves r ms₀) ∧ List.Forall₂ (EventMatchesEntry i r S g) [.recv b_wire, .rng b_rng, .accept b_pt] ((Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown).vis (runMoves pre (runTraceMoves r ms₀)).1) := by
  obtain ⟨ms₀, δ, rfl, hpre₀, hfor⟩ := Symbolic.Swarm.CREF.matchedPrefix6_split hmp
    (by intro e he; simp at he; subst he; exact Or.inl rfl) (Symbolic.Swarm.CREF.matchedPrefix6_prefix_reachable hmp)
  obtain ⟨pre, m, post, rfl, hpre_inv, ⟨hs, ha, hm⟩, hpost_inv⟩ := Symbolic.Swarm.CREF.xpl6_oneMove ⟨hpre₀, hmp.2.1, hfor⟩
      (by intro e he; simp at he; subst he; exact Or.inl rfl) (by simp)
      (by intro e he; simp only [List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at he; rcases he with rfl | rfl <;> exact ⟨by nofun, by nofun, by nofun⟩)
  have hbob_eq := bobDoneBaseKeys_runMoves_of_movesFrom (runTraceMoves r ms₀) pre hpre_inv
  have hact : Symbolic.Swarm.CREF.ActorIn ((Symbolic.Swarm.CREF.moveActor m).getD r.bob) m := by
    unfold Symbolic.Swarm.CREF.ActorIn; rcases Symbolic.Swarm.CREF.moveActor m with _ | _ <;> simp
  have hstep := Symbolic.Swarm.CREF.xplStep_rpk hs ha hm (rpkTriple_rpkShape b_wire b_rng b_pt) hact
  rcases hstep.2.2 ⟨.accept b_pt, by simp, rfl⟩ with hbob | hdec
  · unfold Symbolic.Swarm.CREF.BobStartBy at hbob
    cases m with
    | bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown =>
      exact ⟨ms₀, pre, post, b, a, kh, regIdxA, mh, pqIdx, spqrMsgIdx, shown, rfl, hpre₀, hmp.2.1, hpre_inv, hpost_inv, hbob_eq, hm⟩
    | _ => exact False.elim hbob
  · exact False.elim (rpkBlock_not_decrypt_or_skipped i r S g ms₀ _ b_wire b_rng b_pt p m hhead hp (hunk ms₀ hpre₀) hbob_eq ⟨_, hdec⟩ hm)
theorem allBobDone_of_bobDoneBaseKeys {P : DY.Bytes → Prop} {tr : ExecTrace} (h : ∀ ek ∈ bobDoneBaseKeys tr, P ek) : AllBobDone P tr := by
  intro i ev ek hev hbd; apply h ek; unfold bobDoneBaseKeys
  refine List.mem_filterMap.2 ⟨i, List.mem_range.2 (Symbolic.Swarm.CREF.XplSteps.xlt_of_getEventAt hev), ?_⟩
  rw [hev]; cases ev <;> first | (cases hbd; rfl) | cases hbd
theorem allBobDone_nil (P : DY.Bytes → Prop) : AllBobDone P (Trace.nil : ExecTrace) :=
  fun _ _ _ hev _ => by rw [getEventAt_eq_at?, Symbolic.Swarm.CREF.at?_ge_length Trace.nil (by simp [length_nil_eq])] at hev; cases hev
theorem allBobDone_of_noSessionEffect {P : DY.Bytes → Prop} {tr : ExecTrace} {m : Move} (hm : Symbolic.Swarm.CREF.NoSessionEffect tr m) (h : AllBobDone P tr) : AllBobDone P (m.next tr) := by apply allBobDone_of_bobDoneBaseKeys; rw [bobDoneBaseKeys_next_of_noSessionEffect hm]; exact bobDoneBaseKeys_of_allBobDone h
theorem allBobDone_runMoves_of_movesFrom {P : DY.Bytes → Prop} {tr : ExecTrace} {δ : List Move} (hδ : Symbolic.Swarm.CREF.MovesFrom Symbolic.Swarm.CREF.InvisibleNoEffect tr δ) (h : AllBobDone P tr) : AllBobDone P (runMoves δ tr).1 := by apply allBobDone_of_bobDoneBaseKeys; rw [bobDoneBaseKeys_runMoves_of_movesFrom tr δ hδ]; exact bobDoneBaseKeys_of_allBobDone h
section XBobDoneWalks
open DY.Libsignal Symbolic.Swarm.CREF Symbolic.Swarm.CREF.XplSteps Symbolic.Swarm.COMPOSED.CompTrace
open DY.Libsignal.TripleRatchet (TREvent)
def XBD (P : DY.Bytes → Prop) (n : Nat) (t : ExecTrace) : Prop := ∀ i ev ek, n ≤ i → t.getEventAt PQXDHEvent i = some ev → bobDoneEk? ev = some ek → P ek
def XBobDone (P : DY.Bytes → Prop) {α : Type} (x : Traceful α) : Prop := ∀ tr, XBD P tr.length (x.run tr).2.val
theorem allBobDone_of_xbd {P : DY.Bytes → Prop} {tr t : ExecTrace} (hle : tr ≤ t) (htr : AllBobDone P tr) (hbd : XBD P tr.length t) : AllBobDone P t := by
  intro i ev ek hev hek; by_cases hi : i < tr.length
  · rw [xgetEventAt_le_eq hle hi] at hev; exact htr i ev ek hev hek
  · exact hbd i ev ek (by omega) hev hek
theorem xbd_of_quietFrom {P : DY.Bytes → Prop} {n : Nat} {t : ExecTrace} (h : XQuietFrom n t) : XBD P n t := by
  intro i ev _ hi hev _; have h2 := (h i hi).2.1; rw [getEventAt_eq_at?, h2] at hev; cases hev
theorem xbobDone_of_quiet {P : DY.Bytes → Prop} {α : Type} {x : Traceful α} (h : XQuiet x) : XBobDone P x := fun tr => xbd_of_quietFrom (h tr)
theorem xbd_trans {P : DY.Bytes → Prop} {n : Nat} {t t' : ExecTrace} (hle : t ≤ t') (h1 : XBD P n t) (h2 : XBD P t.length t') : XBD P n t' := by
  intro i ev ek hi hev hek; by_cases hlt : i < t.length
  · rw [xgetEventAt_le_eq hle hlt] at hev; exact h1 i ev ek hi hev hek
  · exact h2 i ev ek (by omega) hev hek
theorem xbobDone_bind {P : DY.Bytes → Prop} {α β : Type} {x : Traceful α} {f : α → Traceful β} (hx : XBobDone P x) (hf : ∀ a, XBobDone P (f a)) : XBobDone P (x >>= f) := by intro tr; rw [xrun_bind_snd]; split; exact xbd_trans (xrun_le _ _) (hx tr) (hf _ _); exact hx tr
theorem xbd_append {P : DY.Bytes → Prop} {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) (h : ∀ ev ek, ((tr.append e).at? tr.length : Option (ProtocolEvent.ExecEntryT PQXDHEvent)) = some ev → bobDoneEk? ev.ev = some ek → P ek) : XBD P tr.length (tr.append e) := by
  have hlen : (tr.append e).length = tr.length + 1 := length_append_entry_eq tr e
  intro i ev ek hi hev hek; have hlt := xlt_of_getEventAt hev; obtain rfl : i = tr.length := by omega
  rw [getEventAt_eq_at?] at hev
  rcases hx : ((tr.append e).at? tr.length : Option (ProtocolEvent.ExecEntryT PQXDHEvent)) with _ | x <;> rw [hx] at hev
  · cases hev
  · simp only [Option.some.injEq] at hev; subst hev; exact h x ek hx hek
theorem xbobDone_logEvent_pq {P : DY.Bytes → Prop} (ev : PQXDHEvent) (h : ∀ ek, bobDoneEk? ev = some ek → P ek) : XBobDone P (ProtocolEvent.logEvent ev : Traceful Unit) := by
  intro tr; rw [logEvent_snd_eq]; refine xbd_append tr (⟨ev⟩ : ProtocolEvent.ExecEntryT PQXDHEvent) (fun x ek hx hek => ?_)
  rw [Symbolic.Swarm.CREF.at?_append_length] at hx; cases hx; exact h ek hek
theorem xbobDone_logEvent_pq_none {P : DY.Bytes → Prop} (ev : PQXDHEvent) (h : bobDoneEk? ev = none) :
    XBobDone P (ProtocolEvent.logEvent ev : Traceful Unit) :=
  xbobDone_logEvent_pq ev (fun _ hek => by rw [h] at hek; cases hek)
theorem xbobDone_logEvent_tr {P : DY.Bytes → Prop} (ev : TREvent) : XBobDone P (ProtocolEvent.logEvent ev : Traceful Unit) := by
  intro tr; rw [logEvent_snd_eq]; refine xbd_append tr (⟨ev⟩ : ProtocolEvent.ExecEntryT TREvent) (fun x _ hx _ => ?_)
  rw [Symbolic.Swarm.CREF.at?_append_length] at hx; cases hx
theorem xbobDone_logEvent_c {P : DY.Bytes → Prop} (ev : CEvent) : XBobDone P (ProtocolEvent.logEvent ev : Traceful Unit) := by
  intro tr; rw [logEvent_snd_eq]; refine xbd_append tr (⟨ev⟩ : ProtocolEvent.ExecEntryT CEvent) (fun x _ hx _ => ?_)
  rw [Symbolic.Swarm.CREF.at?_append_length] at hx; cases hx
theorem xbobDone_storeLocalState_tr {P : DY.Bytes → Prop} (p : Participant) (st : TRState) : XBobDone P (PersistentLocalState.storeLocalState p st) := by
  intro tr; rw [storeLocalState_tr_snd_eq]; refine xbd_append tr (⟨⟨p, st⟩⟩ : PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState)) (fun x _ hx _ => ?_)
  rw [Symbolic.Swarm.CREF.at?_append_length] at hx; cases hx
theorem xbobDone_storeLocalState_pq {P : DY.Bytes → Prop} (p : Participant) (st : PQXDH.PQXDHState) : XBobDone P (PersistentLocalState.storeLocalState p st) := by
  intro tr; rw [storeLocalState_pq_snd_eq]; refine xbd_append tr (⟨⟨p, st⟩⟩ : PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState PQXDH.PQXDHState)) (fun x _ hx _ => ?_)
  rw [Symbolic.Swarm.CREF.at?_append_length] at hx; cases hx
theorem xbobDone_logSkippedKeys {P : DY.Bytes → Prop} (s : TripleRatchet.SessionInfo) (pk : DY.Bytes) (r src : Nat) :
    ∀ (k : Nat) (ck : DY.Bytes) (n : UInt32), XBobDone P (TripleRatchet.logSkippedKeys s pk r src ck n k)
  | 0, _, _ => xbobDone_of_quiet (xquiet_of_fix (xfix_pure _))
  | k + 1, _, _ => by rw [TripleRatchet.logSkippedKeys]; exact xbobDone_bind (xbobDone_logEvent_tr _) fun _ => xbobDone_logSkippedKeys s pk r src k _ _
theorem xbobDone_logMessageKeyAndStore {P : DY.Bytes → Prop} (me : Participant) (s : TripleRatchet.SessionInfo) (dir : TripleRatchet.KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32) (r p : Nat) (st : TRState) : XBobDone P (TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n r p st) := xbobDone_bind (xbobDone_logEvent_tr _) fun _ => xbobDone_storeLocalState_tr _ _
local macro "xbd_step" : tactic => `(tactic| first
  | with_reducible refine xbobDone_bind ?_ fun _ => ?_ | with_reducible exact xbobDone_logEvent_tr _
  | with_reducible refine xbobDone_logEvent_pq_none _ ?_ | with_reducible exact xbobDone_logEvent_c _
  | with_reducible exact xbobDone_storeLocalState_tr _ _ | with_reducible exact xbobDone_storeLocalState_pq _ _
  | with_reducible exact xbobDone_logSkippedKeys _ _ _ _ _ _ _ | with_reducible exact xbobDone_logMessageKeyAndStore _ _ _ _ _ _ _ _ _
  | with_reducible exact xbobDone_of_quiet (xquiet_bobHandshake _ _ _ _ _ _) | with_reducible exact xbobDone_of_quiet (xquiet_aliceHandshake _ _ _ _ _)
  | with_reducible exact xbobDone_of_quiet (xquiet_receiveSignalMsg _) | with_reducible exact xbobDone_of_quiet (xquiet_ensureReceiverChain _ _)
  | with_reducible exact xbobDone_of_quiet (xquiet_verifyMacAndDecrypt _ _ _ _) | with_reducible exact xbobDone_of_quiet (xquiet_genRand _)
  | with_reducible exact xbobDone_of_quiet (xquiet_sendMessage _) | with_reducible exact xbobDone_of_quiet (xquiet_of_fix (xfix_receiveMessage _))
  | with_reducible exact xbobDone_of_quiet (xquiet_of_fix (xfix_getKey _ _ _)) | with_reducible exact xbobDone_of_quiet (xquiet_of_fix (xfix_getLocalState _ _))
  | with_reducible exact xbobDone_of_quiet (xquiet_of_fix (xfix_getEntry _)) | with_reducible exact xbobDone_of_quiet (xquiet_of_fix (xfix_guard _))
  | with_reducible exact xbobDone_of_quiet (xquiet_of_fix xfix_traceLength) | with_reducible exact xbobDone_of_quiet (xquiet_of_fix (xfix_guardOnTrace _))
  | with_reducible exact xbobDone_of_quiet (xquiet_of_fix (xfix_guardTrace _)) | with_reducible exact xbobDone_of_quiet (xquiet_of_fix (xfix_pure _))
  | with_reducible exact xbobDone_of_quiet (xquiet_of_fix xfix_failure) | split)
theorem xbobDone_registerIdentity {P : DY.Bytes → Prop} (p : Participant) : XBobDone P (PQXDH.registerIdentity p) := by
  unfold PQXDH.registerIdentity; repeat' xbd_step
  all_goals rfl
theorem xbobDone_genSignedPrekey {P : DY.Bytes → Prop} (b : Participant) (idStateIdx : Nat) : XBobDone P (PQXDH.genSignedPrekey b idStateIdx) := by
  unfold PQXDH.genSignedPrekey; repeat' xbd_step
  all_goals rfl
theorem xbobDone_genPQPrekey {P : DY.Bytes → Prop} (b : Participant) (idStateIdx : Nat) : XBobDone P (PQXDH.genPQPrekey b idStateIdx) := by
  unfold PQXDH.genPQPrekey; repeat' xbd_step
  all_goals rfl
theorem xbobDone_genOneTimePrekey {P : DY.Bytes → Prop} (b : Participant) : XBobDone P (PQXDH.genOneTimePrekey b) := by
  unfold PQXDH.genOneTimePrekey; repeat' xbd_step
  all_goals rfl
theorem xbobDone_setupAct {P : DY.Bytes → Prop} (a b : Participant) (withOpk : Bool) : XBobDone P (setupAct a b withOpk) := by
  unfold setupAct
  refine xbobDone_bind (xbobDone_registerIdentity a) fun _ => ?_; refine xbobDone_bind (xbobDone_registerIdentity b) fun hB => ?_
  refine xbobDone_bind (xbobDone_genSignedPrekey b hB) fun _ => ?_; refine xbobDone_bind (xbobDone_genPQPrekey b hB) fun _ => ?_
  cases withOpk <;> [exact xbobDone_of_quiet (xquiet_of_fix (xfix_pure ()));
    (simp only [↓reduceIte]; exact xbobDone_bind (xbobDone_genOneTimePrekey b) fun _ => xbobDone_of_quiet (xquiet_of_fix (xfix_pure ())))]
theorem allBobDone_setupTrace (P : DY.Bytes → Prop) (r : Records) : AllBobDone P (setupTrace r) := allBobDone_of_xbd (xrun_le _ Trace.nil) (allBobDone_nil P) (xbobDone_setupAct r.alice r.bob r.withOpk Trace.nil)
theorem xbobDone_messageEncrypt {P : DY.Bytes → Prop} (me : Participant) (si cl pq : Nat) : XBobDone P (TripleRatchet.messageEncrypt me si cl pq) := by unfold TripleRatchet.messageEncrypt; repeat' xbd_step
theorem xbobDone_messageEncryptAbort {P : DY.Bytes → Prop} (me : Participant) (si : Nat) : XBobDone P (TripleRatchet.messageEncryptAbort me si) := by unfold TripleRatchet.messageEncryptAbort; repeat' xbd_step
theorem xbobDone_aliceStart {P : DY.Bytes → Prop} (a b : Participant) (i r : Nat) (h : PQXDH.BundleHandles) : XBobDone P (Composed.aliceStart a b i r h) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]; repeat' xbd_step
  all_goals rfl
theorem allBobDone_aliceStart {P : DY.Bytes → Prop} {tr : ExecTrace} (a b : Participant) (i r : Nat) (h : PQXDH.BundleHandles) (shown : Nat) (htr : AllBobDone P tr) : AllBobDone P ((Move.aliceStart a b i r h shown).next tr) := by unfold Move.next Move.act; rw [xrun_bind_unit]; exact allBobDone_of_xbd (xrun_le _ tr) htr (xbobDone_aliceStart a b i r h tr)
theorem allBobDone_reject {P : DY.Bytes → Prop} {tr : ExecTrace} (draws : List Nat) (htr : AllBobDone P tr) : AllBobDone P ((Move.reject draws).next tr) := by
  unfold Move.next Move.act; rw [traceful_run_pure_snd]; exact htr
theorem allBobDone_sendBy {P : DY.Bytes → Prop} {p : Participant} {m : Move} {tr : ExecTrace} (hsnd : SendBy p m) (htr : AllBobDone P tr) : AllBobDone P (m.next tr) := by
  cases m <;> try exact False.elim hsnd
  case encrypt me si cl pq _ => unfold Move.next Move.act; rw [xrun_bind_unit]; exact allBobDone_of_xbd (xrun_le _ tr) htr (xbobDone_messageEncrypt me si cl pq tr)
  case encryptAbort me si => unfold Move.next Move.act; rw [xrun_bind_unit]; exact allBobDone_of_xbd (xrun_le _ tr) htr (xbobDone_messageEncryptAbort me si tr)
  case encryptFail me si cl =>
    unfold Move.next Move.act
    exact allBobDone_of_xbd (xrun_le _ tr) htr (xbobDone_bind (xbobDone_of_quiet (xquiet_of_fix xfix_traceLength))
        (fun n => xbobDone_bind (xbobDone_messageEncrypt me si cl (n + 3)) (fun _ => xbobDone_of_quiet (xquiet_of_fix (xfix_pure ())))) tr)
theorem allBobDone_bobStart_of_netMsgAt {P : DY.Bytes → Prop} {tr : ExecTrace} (b a : Participant) (kh : PQXDH.BobKeyHandles) (regIdxA : Nat) (mh : PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) (shown : Nat) (htr : AllBobDone P tr) (hek : ∀ ek, NetMsgAt ek mh.ek tr → P ek) : AllBobDone P ((Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown).next tr) := by
  unfold Move.next Move.act; rw [xrun_bind_unit]; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine bind_bobHandshake_at b a kh regIdxA mh.ek mh.ct tr htr ?_
  intro ikB spkSk pqsk opkSk ikA vkA ek ct honest keys _ _ _ _ _ hek_net _ _ _; have hP : P ek := hek ek hek_net; apply allBobDone_of_xbd (xrun_le _ tr) htr
  generalize tr = tr₀; revert tr₀; change XBobDone P _
  repeat' (first | with_reducible refine xbobDone_logEvent_pq (PQXDHEvent.BobDone ..) ?_ | xbd_step)
  all_goals first | rfl | (intro ek' hek'; simp only [bobDoneEk?, Option.some.injEq] at hek'; subst hek'; exact hP)
theorem preKeyRecvOpkMatches_head_baseKey {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {b_wire : HwBytes} {p : PreKeyFields} {ek : DY.Bytes} {rest : List DY.Bytes} (hp : parsePreKeyWire b_wire = some p) (hm : PreKeyRecvOpkMatches i r S g b_wire (ek :: rest)) : ecKey (gamma i S g ek) = p.baseKey.take 33 := by
  rcases rest with _ | ⟨ct, _ | ⟨msg, _ | ⟨opk, _ | _⟩⟩⟩ <;> try exact False.elim hm
  all_goals (obtain ⟨⟨p', hp', hbk, _⟩, _⟩ := hm; change parsePreKeyWire b_wire = some p' at hp'; rw [hp] at hp'; cases hp'; exact hbk.symm)
theorem allBobDone_bobStart_vis {P : DY.Bytes → Prop} {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {tr : ExecTrace} {b_wire : HwBytes} {tail : List MachineEvent} {p : PreKeyFields} (b a : Participant) (kh : PQXDH.BobKeyHandles) (regIdxA : Nat) (mh : PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) (shown : Nat) (hp : parsePreKeyWire b_wire = some p) (hm : List.Forall₂ (EventMatchesEntry i r S g) (.recv b_wire :: tail) ((Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown).vis tr)) (htr : AllBobDone P tr) (hp_ek : ∀ ek, ecKey (gamma i S g ek) = p.baseKey.take 33 → P ek) : AllBobDone P ((Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown).next tr) := by
  refine allBobDone_bobStart_of_netMsgAt b a kh regIdxA mh pqIdx spqrMsgIdx shown htr (fun ek hek => hp_ek ek ?_)
  have hex : exposures tr ((Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown).next tr) = [] := exposures_nil_of_not_leakKind rfl (fun h => nomatch h)
  have hvis : (Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown).vis tr =
      (bobVis tr ((Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown).next tr) mh (bobOpkPk b kh tr)).take shown := by
    rw [xpl_vis_eq, hex, List.append_nil]; rfl
  rw [hvis] at hm; cases shown with
  | zero => cases hm
  | succ k =>
    simp only [bobVis, List.cons_append, List.take_succ_cons] at hm; rcases hm with _ | ⟨⟨_, hpre⟩, _⟩
    have hget : tr.getMessageSentAt mh.ek = some ek := by rw [getMessageSentAt_eq_at?, hek]
    simp only [received, List.filterMap_cons, hget, List.cons_append] at hpre; exact preKeyRecvOpkMatches_head_baseKey hp hpre
theorem movesFrom_invisibleNoEffect_of_matchedPrefix_nil {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms₀ : List Move} (hmp₀ : Swarm.CREF.MatchedPrefix i r S g ms₀ []) : MovesFrom InvisibleNoEffect (setupTrace r) ms₀ := by
  obtain ⟨_, ⟨_, hs₀, ⟨_, hanc₀, _⟩, _⟩, hfor₀⟩ := hmp₀; have hrv₀ : runVis r ms₀ = [] := List.forall₂_nil_left_iff.1 hfor₀
  have hvis₀ : (runMoves ms₀ (setupTrace r)).2 = [] := by have h1 : runVis r ms₀ = r.setupMove.vis Trace.nil ++ (runMoves ms₀ (setupTrace r)).2 := rfl; rw [h1] at hrv₀; exact (List.append_eq_nil_iff.1 hrv₀).2
  exact xpl_movesFrom_invisible ms₀ (setupTrace r) (xpl_movesFrom_of ms₀ (setupTrace r) hs₀ hanc₀) hvis₀
theorem allBobDone_xplBlock_ini {P : DY.Bytes → Prop} {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms₀ δ : List Move} {acc : List MachineEvent} {bun : HwBytes} {rs : List MachineEvent} (hB : XplBlock6 i r S g ms₀ δ acc (.recv bun :: rs)) (hrs : ∀ e ∈ rs, eventKind e = .rng) (htr : AllBobDone P (runTraceMoves r ms₀)) : AllBobDone P (runTraceMoves r (ms₀ ++ δ)) := by
  obtain ⟨pre, m, post, rfl, hpre_inv, ⟨hs, ha, hm⟩, hpost_inv⟩ :=
    xpl6_oneMove hB (by intro e he; simp at he; subst he; exact Or.inl rfl) (by simp) (by intro e he; rw [hrs e he]; decide)
  have hact : ActorIn ((moveActor m).getD r.alice) m := by unfold ActorIn; cases moveActor m <;> simp
  have hstep := xplStep_ini hs ha hm ⟨⟨bun, rfl⟩, hrs⟩ hact; have htr_pre := allBobDone_runMoves_of_movesFrom hpre_inv htr
  have htr_m : AllBobDone P (m.next (runMoves pre (runTraceMoves r ms₀)).1) := by
    rcases hstep.2 with hini | hneff
    · unfold IniKind at hini; cases m <;> try exact False.elim hini
      case aliceStart a b idS regB hb shown => exact allBobDone_aliceStart a b idS regB hb shown htr_pre
      case reject draws => exact allBobDone_reject draws htr_pre
      case attackerSend msg =>
        unfold Move.next Move.act; rw [xrun_bind_unit]; exact allBobDone_of_xbd (xrun_le _ _) htr_pre (xbobDone_of_quiet (xquiet_sendMessage msg) _)
    · exact allBobDone_of_noSessionEffect hneff htr_pre
  rw [Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct.runTrace_append, Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct.runMoves_append_fst, runMoves_cons_fst]; exact allBobDone_runMoves_of_movesFrom hpost_inv htr_m
theorem allBobDone_xplBlock_send {P : DY.Bytes → Prop} {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms₀ δ : List Move} {acc : List MachineEvent} {b_pt : HwBytes} {tail : List MachineEvent} (hB : XplBlock6 i r S g ms₀ δ acc (.pt b_pt :: tail)) (htail : ∀ e ∈ tail, eventKind e = .rng ∨ eventKind e = .send) (htr : AllBobDone P (runTraceMoves r ms₀)) : AllBobDone P (runTraceMoves r (ms₀ ++ δ)) := by
  obtain ⟨pre, m, post, rfl, hpre_inv, ⟨hs, _, hm⟩, hpost_inv⟩ :=
    xpl6_oneMove hB (by intro e he; simp at he; subst he; exact Or.inr rfl) (by simp) (by intro e he; rcases htail e he with h | h <;> rw [h] <;> decide)
  have hact : ActorIn ((moveActor m).getD r.alice) m := by unfold ActorIn; cases moveActor m <;> simp
  have hstep := xplStep_send hs hm ⟨⟨b_pt, rfl⟩, htail⟩ hact; have htr_m := allBobDone_sendBy hstep.1 (allBobDone_runMoves_of_movesFrom hpre_inv htr); rw [Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct.runTrace_append, Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct.runMoves_append_fst, runMoves_cons_fst]; exact allBobDone_runMoves_of_movesFrom hpost_inv htr_m
theorem allBobDone_matchedPrefix_nil {P : DY.Bytes → Prop} {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms₀ : List Move} (hmp : Swarm.CREF.MatchedPrefix i r S g ms₀ []) : AllBobDone P (runTraceMoves r ms₀) := by rw [xpl_runTrace_eq]; exact allBobDone_runMoves_of_movesFrom (movesFrom_invisibleNoEffect_of_matchedPrefix_nil hmp) (allBobDone_setupTrace P r)
theorem allBobDone_matchedPrefix_ini_rs {P : DY.Bytes → Prop} {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {τ_pre : List MachineEvent} {bun : HwBytes} {rs : List MachineEvent} {ms : List Move} (hrs : ∀ e ∈ rs, eventKind e = .rng) (hpre_bd : ∀ ms₀, Swarm.CREF.MatchedPrefix i r S g ms₀ τ_pre → AllBobDone P (runTraceMoves r ms₀)) (hmp : Swarm.CREF.MatchedPrefix i r S g ms (τ_pre ++ (.recv bun :: rs))) : AllBobDone P (runTraceMoves r ms) := by
  obtain ⟨ms₀, δ, rfl, hmp₀, hfor⟩ := matchedPrefix6_split hmp (by intro e he; simp at he; subst he; exact Or.inl rfl) (matchedPrefix6_prefix_reachable hmp)
  exact allBobDone_xplBlock_ini ⟨hmp₀, hmp.2.1, hfor⟩ hrs (hpre_bd ms₀ hmp₀)
theorem allBobDone_matchedPrefix_send_tail {P : DY.Bytes → Prop} {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {τ_pre : List MachineEvent} {b_pt : HwBytes} {tail : List MachineEvent} {ms : List Move} (htail : ∀ e ∈ tail, eventKind e = .rng ∨ eventKind e = .send) (hpre_bd : ∀ ms₀, Swarm.CREF.MatchedPrefix i r S g ms₀ τ_pre → AllBobDone P (runTraceMoves r ms₀)) (hmp : Swarm.CREF.MatchedPrefix i r S g ms (τ_pre ++ (.pt b_pt :: tail))) : AllBobDone P (runTraceMoves r ms) := by
  obtain ⟨ms₀, δ, rfl, hmp₀, hfor⟩ := matchedPrefix6_split hmp (by intro e he; simp at he; subst he; exact Or.inr rfl) (matchedPrefix6_prefix_reachable hmp)
  exact allBobDone_xplBlock_send ⟨hmp₀, hmp.2.1, hfor⟩ htail (hpre_bd ms₀ hmp₀)
theorem allBobDone_matchedPrefix_ini_map {P : DY.Bytes → Prop} {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {τ_pre blk : List MachineEvent} {ks : List Kind} {ms : List Move} (hmap : blk.map eventKind = .recv :: ks) (hks : ∀ k ∈ ks, k = .rng) (hpre_bd : ∀ ms₀, Swarm.CREF.MatchedPrefix i r S g ms₀ τ_pre → AllBobDone P (runTraceMoves r ms₀)) (hmp : Swarm.CREF.MatchedPrefix i r S g ms (τ_pre ++ blk)) : AllBobDone P (runTraceMoves r ms) := by
  obtain ⟨bun, rs, rfl, hrs⟩ := iniShape_of_map_eventKind hmap hks
  exact allBobDone_matchedPrefix_ini_rs hrs hpre_bd hmp
theorem allBobDone_matchedPrefix_send_map {P : DY.Bytes → Prop} {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {τ_pre blk : List MachineEvent} {ks : List Kind} {ms : List Move} (hmap : blk.map eventKind = .pt :: ks) (hks : ∀ k ∈ ks, k = .rng ∨ k = .send) (hpre_bd : ∀ ms₀, Swarm.CREF.MatchedPrefix i r S g ms₀ τ_pre → AllBobDone P (runTraceMoves r ms₀)) (hmp : Swarm.CREF.MatchedPrefix i r S g ms (τ_pre ++ blk)) : AllBobDone P (runTraceMoves r ms) := by
  obtain ⟨b_pt, tail, rfl, htail⟩ := sendShape_of_map_eventKind hmap hks
  exact allBobDone_matchedPrefix_send_tail htail hpre_bd hmp
theorem allBobDone_matchedPrefix_rpk {P : DY.Bytes → Prop} {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {τ_pre : List MachineEvent} {b_wire b_rng b_pt : HwBytes} {ms : List Move} {p : PreKeyFields} (hhead : b_wire.head? = some 0x03#8) (hp : parsePreKeyWire b_wire = some p) (hunk : ∀ ms₀, Swarm.CREF.MatchedPrefix i r S g ms₀ τ_pre → ¬ KnownBaseKey i r S g ms₀ p) (hpre_bd : ∀ ms₀, Swarm.CREF.MatchedPrefix i r S g ms₀ τ_pre → AllBobDone P (runTraceMoves r ms₀)) (hp_ek : ∀ ek, ecKey (gamma i S g ek) = p.baseKey.take 33 → P ek) (hmp : Swarm.CREF.MatchedPrefix i r S g ms (τ_pre ++ [.recv b_wire, .rng b_rng, .accept b_pt])) : AllBobDone P (runTraceMoves r ms) := by
  obtain ⟨ms₀, pre, post, b, a, kh, regIdxA, mh, pqIdx, spqrMsgIdx, shown, rfl, hmp₀, _, hpre_inv, hpost_inv, _, hm⟩ := matchedPrefix_rpk_bobStart_only i r S g τ_pre b_wire b_rng b_pt ms p hhead hp hunk hmp; have htr_m := allBobDone_bobStart_vis b a kh regIdxA mh pqIdx spqrMsgIdx shown hp hm (allBobDone_runMoves_of_movesFrom hpre_inv (hpre_bd ms₀ hmp₀)) hp_ek; rw [Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct.runTrace_append, Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct.runMoves_append_fst, runMoves_cons_fst]
  exact allBobDone_runMoves_of_movesFrom hpost_inv htr_m
theorem take35_allBobDone {P : DY.Bytes → Prop} {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} (hmp : Swarm.CREF.MatchedPrefix i r S g ms (trace.take 35)) : AllBobDone P (runTraceMoves r ms) := by rw [take35_eq] at hmp; exact allBobDone_matchedPrefix_ini_map seg0_kinds (replicate_rng 34) (fun _ => allBobDone_matchedPrefix_nil) hmp
theorem take38_allBobDone {P : DY.Bytes → Prop} {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} (hmp : Swarm.CREF.MatchedPrefix i r S g ms (trace.take 38)) : AllBobDone P (runTraceMoves r ms) := by rw [take38_eq] at hmp; exact allBobDone_matchedPrefix_send_map seg35_kinds (fun _ hk => rng_send_of_mem_rng_send hk) (fun _ => take35_allBobDone) hmp
theorem take40_allBobDone {P : DY.Bytes → Prop} {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} (hmp : Swarm.CREF.MatchedPrefix i r S g ms (trace.take 40)) : AllBobDone P (runTraceMoves r ms) := by rw [take40_eq] at hmp; exact allBobDone_matchedPrefix_send_map seg38_kinds (fun _ hk => rng_send_of_mem_send hk) (fun _ => take38_allBobDone) hmp
theorem take40_not_knownBaseKey {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {p : PreKeyFields} (hmp : Swarm.CREF.MatchedPrefix i r S g ms (trace.take 40)) : ¬ KnownBaseKey i r S g ms p := not_knownBaseKey_of_allBobDone_false (take40_allBobDone hmp)
theorem take43_allBobDone_ek1 {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} (hmp : Swarm.CREF.MatchedPrefix i r S g ms (trace.take 43)) : AllBobDone (fun ek => ecKey (gamma i S g ek) = ecKey ek1PubKey) (runTraceMoves r ms) := by
  rw [take43_eq] at hmp; obtain ⟨b_rng, b_pt, hseg⟩ := seg40_eq; rw [hseg] at hmp; obtain ⟨p, hp⟩ := wireAt40_parses; have hbk : p.baseKey.take 33 = ecKey ek1PubKey := baseKey_of_map wireAt40_baseKey hp
  exact allBobDone_matchedPrefix_rpk wireAt40_head? hp (fun _ hmp₀ => take40_not_knownBaseKey hmp₀)
    (fun _ hmp₀ => take40_allBobDone hmp₀) (fun ek hek => by rw [hek, hbk]) hmp
theorem take78_allBobDone_ek1 {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} (hmp : Swarm.CREF.MatchedPrefix i r S g ms (trace.take 78)) : AllBobDone (fun ek => ecKey (gamma i S g ek) = ecKey ek1PubKey) (runTraceMoves r ms) := by rw [take78_eq] at hmp; exact allBobDone_matchedPrefix_ini_map seg43_kinds (replicate_rng 34) (fun _ => take43_allBobDone_ek1) hmp
theorem take81_allBobDone_ek1 {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} (hmp : Swarm.CREF.MatchedPrefix i r S g ms (trace.take 81)) : AllBobDone (fun ek => ecKey (gamma i S g ek) = ecKey ek1PubKey) (runTraceMoves r ms) := by rw [take81_eq] at hmp; exact allBobDone_matchedPrefix_send_map seg78_kinds (fun _ hk => rng_send_of_mem_rng_send hk) (fun _ => take78_allBobDone_ek1) hmp
theorem take81_not_knownBaseKey {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {p : PreKeyFields} (hmp : Swarm.CREF.MatchedPrefix i r S g ms (trace.take 81)) (hp : parsePreKeyWire (wireAt 81) = some p) : ¬ KnownBaseKey i r S g ms p := wireAt81_not_knownBaseKey_of_allBobDone_ek1 hp (take81_allBobDone_ek1 hmp)
end XBobDoneWalks
theorem notKnown : ∀ n, n = 40 ∨ n = 81 → SpecTop.NotKnownBaseKeyAt n := by
  rintro n (rfl | rfl) r S g ms p _ hex hp
  · exact take40_not_knownBaseKey (Swarm.CREF.MatchedPrefix.of_composed hex.1)
  · exact take81_not_knownBaseKey (Swarm.CREF.MatchedPrefix.of_composed hex.1) hp
end Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.BobDone

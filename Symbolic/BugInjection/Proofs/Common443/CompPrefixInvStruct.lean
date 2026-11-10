/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Prelude
public import Symbolic.Proofs.Swarm.CREF.ModelSplit
public import Symbolic.Proofs.Swarm.CREF.ModelMono
public import Symbolic.Proofs.Swarm.CREF.Xpl.InvCommon
public import Symbolic.Proofs.Swarm.CREF.Xpl.StepsMix
public import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil
public import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
public import Symbolic.Proofs.Swarm.COMPOSED.CompInvDefs
public import Symbolic.Proofs.SpecLemmas.Refinement.Composed.MatchedPrefix
public import Symbolic.BugInjection.Proofs.Common.DefsCompI0

@[expose] public section
set_option autoImplicit false
abbrev DY.Libsignal.Composed.Refinement.Move.Anchored := DY.Libsignal.Composed.Refinement.Move.LogsSessionCompletion
abbrev DY.Libsignal.Composed.Refinement.Move.PeerOk := DY.Libsignal.Composed.Refinement.Move.MatchesSetupPeer
cref_hide_foreign_instances
namespace Symbolic.Swarm.CREF
open DY.Libsignal.Composed.Refinement
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (MachineEvent)
open DY DY.Libsignal DY.Libsignal.Composed
def MatchedPrefix (interpretation : ExternInterpretation) (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (τ : List MachineEvent) : Prop := Compat interpretation r S g ∧ ModelRun r ms ∧ List.Forall₂ (EventMatchesEntry interpretation r S g) τ (runVis r ms)
theorem MatchedPrefix.of_composed {interpretation : ExternInterpretation} {r : Records} {S : Sem} {who} {g : Ghost} {ms : List Move} {τ : List MachineEvent} (h : DY.Libsignal.Composed.Refinement.MatchedPrefix interpretation r S who g ms τ) : Symbolic.Swarm.CREF.MatchedPrefix interpretation r S g ms τ := ⟨h.1, h.2.1, h.2.2.2.2.2⟩
theorem matchedPrefix6_prefix_reachable {interpretation : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {τ : List MachineEvent} (h : MatchedPrefix interpretation r S g ms τ) : ∀ ms₀ δ, ms = ms₀ ++ δ → (runTraceMoves r ms₀).Reachable reachability := by intro ms₀ δ he; have := h.2.1.2.2.1.2.2 ms₀.length; rwa [he, List.take_left] at this
theorem matchedPrefix6_split_of_noCut {interpretation : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {acc blk : List MachineEvent} (B : VisEntry → VisEntry → Prop) (h : MatchedPrefix interpretation r S g ms (acc ++ blk)) (hnc : b5_NoCutFrom B (r.setupMove :: ms) Trace.nil) (hcut : ∀ a b, 0 < acc.length → (runVis r ms)[acc.length - 1]? = some a → (runVis r ms)[acc.length]? = some b → B a b) (hnil : acc = [] → runVis r [] = []) (hreach : ∀ ms₀ δ, ms = ms₀ ++ δ → (runTraceMoves r ms₀).Reachable reachability) : ∃ ms₀ δ, ms = ms₀ ++ δ ∧ MatchedPrefix interpretation r S g ms₀ acc ∧ List.Forall₂ (EventMatchesEntry interpretation r S g) blk (runMoves δ (runTraceMoves r ms₀)).2 := by
  obtain ⟨hc, hrun, hfor⟩ := h; have hlen : (acc ++ blk).length = (runVis r ms).length := b5_forall₂_length hfor; have hV : runVis r ms = (runMoves (r.setupMove :: ms) Trace.nil).2 := rfl
  obtain ⟨L₀, L₁, hL, hL₀⟩ := b5_split_core B (r.setupMove :: ms) Trace.nil acc.length hnc (by rw [← hV, ← hlen, List.length_append]; omega) hcut
  cases L₀ with
  | nil =>
    have hacc : acc = [] := List.eq_nil_of_length_eq_zero hL₀.symm; subst hacc; have h0 := hnil rfl; have hsplit := runVis_append r [] ms; rw [List.nil_append, h0, List.nil_append] at hsplit
    exact ⟨[], ms, rfl, ⟨hc, modelRun_prefix_of_reachable (δ := ms) hrun (hreach [] ms rfl), h0 ▸ List.Forall₂.nil⟩, hsplit ▸ hfor⟩
  | cons m L₀ =>
    simp only [List.cons_append, List.cons.injEq] at hL; obtain ⟨rfl, rfl⟩ := hL; obtain ⟨h1, h2⟩ := eventsMatch_append_split hfor
    have hL₀' : (runVis r L₀).length = acc.length := hL₀; rw [hL₀', List.take_left] at h1; rw [hL₀', List.drop_left] at h2
    exact ⟨L₀, L₁, rfl, ⟨hc, modelRun_prefix_of_reachable hrun (hreach L₀ L₁ rfl), h1⟩, h2⟩
theorem matchedPrefix6_split {interpretation : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {acc blk : List MachineEvent} (h : MatchedPrefix interpretation r S g ms (acc ++ blk)) (hblk : ∀ e ∈ blk.head?, eventKind e = .recv ∨ eventKind e = .pt) (hreach : ∀ ms₀ δ, ms = ms₀ ++ δ → (runTraceMoves r ms₀).Reachable reachability) : ∃ ms₀ δ, ms = ms₀ ++ δ ∧ MatchedPrefix interpretation r S g ms₀ acc ∧ List.Forall₂ (EventMatchesEntry interpretation r S g) blk (runMoves δ (runTraceMoves r ms₀)).2 := by
  have hfor := h.2.2
  refine matchedPrefix6_split_of_noCut (fun _ b => b.kind = .recv ∨ b.kind = .pt) h (b5_noCutFrom_of_mem _ _ (fun m _ tr k a b hk _ hb hB => (vis_tail_not_recv_pt m tr b (b5_mem_tail_of_getElem? hk hb)).elim (fun h1 h2 => hB.elim h1 h2)) _) ?_ ?_ hreach
  · intro a b _ _ hb; obtain ⟨e, he, hk, -⟩ := b5_forall₂_getElem? hfor hb; rw [b5_getElem?_append_length] at he; exact hk ▸ hblk e (Option.mem_def.2 he)
  · rintro rfl; rcases hv : runVis r [] with _ | ⟨x, rest⟩; · rfl
    exfalso; have hx : (runVis r ms)[0]? = some x := by have hsplit := runVis_append r [] ms; rw [List.nil_append, hv, List.cons_append] at hsplit; simp [hsplit]
    obtain ⟨e, he, hk, -⟩ := b5_forall₂_getElem? hfor hx
    have h0 : runVis r [] = r.setupMove.vis Trace.nil := List.append_nil _
    have hxl : x.kind = .leak := b5_setup_vis_leak r Trace.nil x (by rw [← h0, hv]; exact List.mem_cons_self)
    have := hblk e (Option.mem_def.2 ((b5_getElem?_append_length [] blk).symm.trans he)); simp [hk, hxl] at this
structure XplBlock6 (interpretation : ExternInterpretation) (r : Records) (S : Sem) (g : Ghost) (ms₀ δ : List Move) (acc blk : List MachineEvent) : Prop where
  pre : MatchedPrefix interpretation r S g ms₀ acc
  run : ModelRun r (ms₀ ++ δ)
  matched : List.Forall₂ (EventMatchesEntry interpretation r S g) blk (runMoves δ (runTraceMoves r ms₀)).2
theorem xpl6_oneMove {interpretation : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms₀ δ : List Move} {acc blk : List MachineEvent} (hB : XplBlock6 interpretation r S g ms₀ δ acc blk) (_hhead : ∀ e ∈ blk.head?, eventKind e = .recv ∨ eventKind e = .pt) (hne : blk ≠ []) (htail : ∀ e ∈ blk.tail, eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak) : OneMove (fun tr m => m.isSetup = false ∧ m.Anchored tr ∧ List.Forall₂ (EventMatchesEntry interpretation r S g) blk (m.vis tr)) (runTraceMoves r ms₀) δ := by
  obtain ⟨_, hs, ⟨_, hanc, _⟩, _, _⟩ := hB.run; have hanc' := xpl_runTrace_eq r ms₀ ▸ xpl_movesAnchored_append_right ms₀ δ (setupTrace r) hanc
  exact xpl_oneMove_aux δ (runTraceMoves r ms₀) blk (xpl_movesFrom_of δ _ (fun m hm => hs m (List.mem_append_right _ hm)) hanc') hB.matched hne htail
end Symbolic.Swarm.CREF
namespace Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct
open Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open TripleRatchet (TREvent TRState)
open PQXDH (PQXDHEvent BundleHandles)
def NoTRState (tr : ExecTrace) : Prop := ∀ j : Nat, (tr.at? j : Option TRStEntry) = none
theorem noTRState_nil : NoTRState (Trace.nil : ExecTrace) := by
  intro j
  cases h : ((Trace.nil : ExecTrace).at? j : Option TRStEntry) with
  | none => rfl
  | some x =>
    rcases x with ⟨⟨me, st⟩⟩
    exact (Symbolic.Swarm.COMPOSED.CompInv.trStoredAt_nil h).elim
theorem noTRState_append_other {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} (h : NoTRState tr) (e : E) (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option TRStEntry) = none) : NoTRState (tr.append e) := by
  intro j; rcases hex : ((tr.append e).at? j : Option TRStEntry) with _ | x; · rfl
  · exfalso; rcases CompTrace.at?_append_cases hex with ⟨_, h0⟩ | ⟨_, hp⟩
    · rw [h j] at h0; cases h0
    · rw [hnone] at hp; cases hp
theorem NoTRState.preserves_genRand (n : Nat) : CompTrace.Preserves NoTRState (DY.Random.genRand n) :=
  fun tr h => (TR.Runs.genRand tr n).2.symm ▸ noTRState_append_other h (RndE n) rfl
theorem NoTRState.preserves_sendMessage (msg : DY.Bytes) : CompTrace.Preserves NoTRState (DY.Network.sendMessage msg) :=
  fun tr h => (TR.Runs.sendMessage tr msg).2.symm ▸ noTRState_append_other h (NetE msg) rfl
theorem NoTRState.preserves_logEvent_pq (ev : PQXDHEvent) : CompTrace.Preserves NoTRState (DY.ProtocolEvent.logEvent ev) :=
  fun tr h => (TR.Runs.logEvent tr ev).2.symm ▸ noTRState_append_other h (PQEvE ev) rfl
theorem NoTRState.preserves_storeLocalState_pq (me : Participant) (st : PQXDH.PQXDHState) : CompTrace.Preserves NoTRState (DY.PersistentLocalState.storeLocalState me st) :=
  fun tr h => (TR.Runs.storeLocalState tr me st).2.symm ▸ noTRState_append_other h (PQStE me st) rfl
theorem NoTRState.preserves_getKey (p : Participant) (stateIdx : Nat) (kind : PQXDH.KeyKind) : CompTrace.Preserves NoTRState (PQXDH.getKey p stateIdx kind) := by
  unfold PQXDH.getKey; refine CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_pq p stateIdx) fun _ => ?_
  exact CompTrace.Preserves.bind (CompTrace.Preserves.guardP _) fun _ => CompTrace.Preserves.pure _
theorem NoTRState.preserves_registerIdentity (p : Participant) : CompTrace.Preserves NoTRState (PQXDH.registerIdentity p) := by
  unfold PQXDH.registerIdentity
  refine CompTrace.Preserves.bind (CompTrace.Preserves.requireTracePredicate _) fun _ => ?_
  refine CompTrace.Preserves.bind (NoTRState.preserves_genRand 32) fun _ => ?_
  refine CompTrace.Preserves.bind (NoTRState.preserves_logEvent_pq _) fun _ => ?_
  refine CompTrace.Preserves.bind (NoTRState.preserves_sendMessage _) fun _ => ?_
  refine CompTrace.Preserves.bind (NoTRState.preserves_sendMessage _) fun _ => ?_
  exact NoTRState.preserves_storeLocalState_pq p _
theorem NoTRState.preserves_genSignedPrekey (b : Participant) (idStateIdx : Nat) : CompTrace.Preserves NoTRState (PQXDH.genSignedPrekey b idStateIdx) := by
  unfold PQXDH.genSignedPrekey
  refine CompTrace.Preserves.bind (NoTRState.preserves_getKey b idStateIdx .identity) fun _ => ?_
  refine CompTrace.Preserves.bind (NoTRState.preserves_genRand 32) fun _ => ?_
  refine CompTrace.Preserves.bind (NoTRState.preserves_genRand 64) fun _ => ?_
  refine CompTrace.Preserves.bind (NoTRState.preserves_logEvent_pq _) fun _ => ?_
  refine CompTrace.Preserves.bind (NoTRState.preserves_storeLocalState_pq b _) fun _ => ?_
  refine CompTrace.Preserves.bind (NoTRState.preserves_sendMessage _) fun _ => ?_
  refine CompTrace.Preserves.bind (NoTRState.preserves_sendMessage _) fun _ => ?_
  exact CompTrace.Preserves.pure _
theorem NoTRState.preserves_genPQPrekey (b : Participant) (idStateIdx : Nat) : CompTrace.Preserves NoTRState (PQXDH.genPQPrekey b idStateIdx) := by
  unfold PQXDH.genPQPrekey
  refine CompTrace.Preserves.bind (NoTRState.preserves_getKey b idStateIdx .identity) fun _ => ?_
  refine CompTrace.Preserves.bind (NoTRState.preserves_genRand 64) fun _ => ?_
  refine CompTrace.Preserves.bind (NoTRState.preserves_genRand 64) fun _ => ?_
  refine CompTrace.Preserves.bind (NoTRState.preserves_logEvent_pq _) fun _ => ?_
  refine CompTrace.Preserves.bind (NoTRState.preserves_storeLocalState_pq b _) fun _ => ?_
  refine CompTrace.Preserves.bind (NoTRState.preserves_sendMessage _) fun _ => ?_
  refine CompTrace.Preserves.bind (NoTRState.preserves_sendMessage _) fun _ => ?_
  exact CompTrace.Preserves.pure _
theorem NoTRState.preserves_genOneTimePrekey (b : Participant) : CompTrace.Preserves NoTRState (PQXDH.genOneTimePrekey b) := by
  unfold PQXDH.genOneTimePrekey
  refine CompTrace.Preserves.bind (NoTRState.preserves_genRand 32) fun _ => ?_
  refine CompTrace.Preserves.bind (NoTRState.preserves_logEvent_pq _) fun _ => ?_
  refine CompTrace.Preserves.bind (NoTRState.preserves_storeLocalState_pq b _) fun _ => ?_
  exact CompTrace.Preserves.bind (NoTRState.preserves_sendMessage _) fun _ => CompTrace.Preserves.pure _
theorem NoTRState.preserves_setupAct (a b : Participant) (withOpk : Bool) : CompTrace.Preserves NoTRState (setupAct a b withOpk) := by
  unfold setupAct
  refine CompTrace.Preserves.bind (NoTRState.preserves_registerIdentity a) fun _ => ?_
  refine CompTrace.Preserves.bind (NoTRState.preserves_registerIdentity b) fun hB => ?_
  refine CompTrace.Preserves.bind (NoTRState.preserves_genSignedPrekey b hB) fun _ => ?_
  refine CompTrace.Preserves.bind (NoTRState.preserves_genPQPrekey b hB) fun _ => ?_
  cases withOpk
  · exact CompTrace.Preserves.pure ()
  · simp only [↓reduceIte]; exact CompTrace.Preserves.bind (NoTRState.preserves_genOneTimePrekey b) fun _ => CompTrace.Preserves.pure ()
theorem noTRState_setupTrace (r : Records) : NoTRState (setupTrace r) := NoTRState.preserves_setupAct r.alice r.bob r.withOpk Trace.nil noTRState_nil
theorem noTRState_of_noSessionEffect {tr : ExecTrace} {m : Move} (htr : NoTRState tr) (heff : NoSessionEffect tr m) : NoTRState (m.next tr) := by
  intro j; have hle : tr ≤ m.next tr := m.le_next tr
  by_cases hj : j < tr.length
  · rw [XplSteps.xat?_le_eq hle hj, htr j]
  · by_cases hj' : j < (m.next tr).length
    · exact (heff j (List.mem_range'.2 ⟨j - tr.length, by omega, by omega⟩)).1
    · exact (XplSteps.xnone_of_ge (by omega)).1
theorem noTRState_of_movesFrom_noSessionEffect {tr : ExecTrace} {δ : List Move} (htr : NoTRState tr) (hδ : MovesFrom NoSessionEffect tr δ) : NoTRState (runMoves δ tr).1 := by
  induction δ generalizing tr with
  | nil => exact htr
  | cons m δ ih => exact ih (noTRState_of_noSessionEffect htr hδ.1) hδ.2
theorem noTRState_of_movesFrom_invisibleNoEffect {tr : ExecTrace} {δ : List Move} (htr : NoTRState tr) (hδ : MovesFrom InvisibleNoEffect tr δ) : NoTRState (runMoves δ tr).1 :=
  noTRState_of_movesFrom_noSessionEffect htr (movesFrom_mono (fun _ _ h => h.2) tr δ hδ)
theorem encrypt_next_eq_of_noTRState {tr : ExecTrace} (htr : NoTRState tr) (me : Participant) (sIdx cl pq : Nat) (wrap : Option (Nat × Nat)) : (Move.encrypt me sIdx cl pq wrap).next tr = tr := by
  unfold Move.next Move.act; rw [XplSteps.xrun_bind_unit]; unfold TripleRatchet.messageEncrypt
  rw [CompTrace.run_bind_snd, CompTrace.getLocalState_tr_fst, CompTrace.getLocalState_tr_snd, htr sIdx]
theorem encrypt_lastSent_none_of_noTRState {tr : ExecTrace} (htr : NoTRState tr) (me : Participant) (sIdx cl pq : Nat) (wrap : Option (Nat × Nat)) : lastSent tr ((Move.encrypt me sIdx cl pq wrap).next tr) = none := by rw [encrypt_next_eq_of_noTRState htr]; unfold lastSent; simp
export Symbolic.Swarm.CREF (matchedPrefix6_prefix_reachable)
theorem runMoves_append_fst : ∀ (ms₁ ms₂ : List Move) (tr : ExecTrace), (runMoves (ms₁ ++ ms₂) tr).1 = (runMoves ms₂ (runMoves ms₁ tr).1).1
  | [], _, _ => rfl
  | m :: ms₁, ms₂, tr => by simp only [List.cons_append, runMoves_cons_fst, runMoves_append_fst ms₁ ms₂ (m.next tr)]
theorem runMoves_append_snd : ∀ (ms₁ ms₂ : List Move) (tr : ExecTrace), (runMoves (ms₁ ++ ms₂) tr).2 = (runMoves ms₁ tr).2 ++ (runMoves ms₂ (runMoves ms₁ tr).1).2
  | [], _, _ => rfl
  | m :: ms₁, ms₂, tr => by simp only [List.cons_append, runMoves_cons_snd, runMoves_cons_fst, runMoves_append_snd ms₁ ms₂ (m.next tr), List.append_assoc]
theorem runTrace_append (r : Records) (ms₁ ms₂ : List Move) : runTraceMoves r (ms₁ ++ ms₂) = (runMoves ms₂ (runTraceMoves r ms₁)).1 := by rw [xpl_runTrace_eq, xpl_runTrace_eq, runMoves_append_fst]
theorem aliceDraws_length_le (done : Option Nat) (L : List DY.Bytes) : (aliceDraws done L).length ≤ 34 := by
  rcases L with _ | ⟨ek, _ | ⟨entropy, rest⟩⟩
  · simp [aliceDraws]
  · simp [aliceDraws]
  · simp only [aliceDraws, List.length_cons, List.length_append, List.length_map, List.length_take, kyberCoinEntries, List.length_range]; omega
theorem aliceVis_length_le (tr tr' : ExecTrace) (hb : BundleHandles) : (aliceVis tr tr' hb).length ≤ 35 := by
  unfold aliceVis; have := aliceDraws_length_le (eventIdx isAliceDone tr tr') ((newRandoms tr tr').map (·.1))
  simp only [List.length_cons]; omega
theorem aliceStart_vis_eq_aliceVis_of_length_35 {a b : Participant} {idS regB : Nat} {hb : BundleHandles} {shown : Nat} {tr : ExecTrace} (hlen : ((Move.aliceStart a b idS regB hb shown).vis tr).length = 35) : 35 ≤ shown ∧ (Move.aliceStart a b idS regB hb shown).vis tr = aliceVis tr ((Move.aliceStart a b idS regB hb shown).next tr) hb := by have hex : exposures tr ((Move.aliceStart a b idS regB hb shown).next tr) = [] := exposures_nil_of_not_leakKind rfl (fun h => nomatch h); have hvis : (Move.aliceStart a b idS regB hb shown).vis tr = (aliceVis tr ((Move.aliceStart a b idS regB hb shown).next tr) hb).take shown := (by rw [xpl_vis_eq, hex, List.append_nil]; rfl); rw [hvis] at hlen ⊢; have hle := aliceVis_length_le tr ((Move.aliceStart a b idS regB hb shown).next tr) hb; rw [List.length_take] at hlen; refine ⟨by omega, List.take_of_length_le (by omega)⟩
theorem aliceStart_isAliceDone_of_not_noSessionEffect {a b : Participant} {idS regB : Nat} {hb : BundleHandles} {shown : Nat} {tr : ExecTrace} (hneff : ¬ NoSessionEffect tr (.aliceStart a b idS regB hb shown)) : (eventIdx isAliceDone tr ((Move.aliceStart a b idS regB hb shown).next tr)).isSome = true := by
  rcases XplSteps.xmix_move_aliceStart tr (a := a) (b := b) (i := idS) (r := regB) (h := hb) (shown := shown) with hq | hev
  · exact absurd (XplSteps.xpl_noEff_of_quietFrom hq) hneff
  · exact Option.isSome_iff_ne_none.mpr (XplSteps.xpl_eventIdx_ne_none hev)
theorem invert_ini_move_of_not_noSessionEffect {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {tr : ExecTrace} {m : Move} {bun : HwBytes} {rs : List MachineEvent} (hs : m.isSetup = false) (ha : m.Anchored tr) (hm : List.Forall₂ (EventMatchesEntry i r S g) (.recv bun :: rs) (m.vis tr)) (hrs_len : rs.length = 34) (hrs_kind : ∀ e ∈ rs, eventKind e = .rng) (hneff : ¬ NoSessionEffect tr m) : ∃ a b idS regB hb shown, m = .aliceStart a b idS regB hb shown ∧ 35 ≤ shown ∧ (eventIdx isAliceDone tr (m.next tr)).isSome = true ∧ List.Forall₂ (EventMatchesEntry i r S g) (.recv bun :: rs) (aliceVis tr (m.next tr) hb) := by
  obtain ⟨v₀, hv₀, hvk₀, _⟩ := xpl_head_entry hm (e := .recv bun) rfl; have hrk : RecvHeadKind m := xpl_recvHeadKind m tr hv₀ hvk₀
  have hnoacc : ∀ w ∈ m.vis tr, w.kind ≠ .accept := by
    intro w hw hwk; obtain ⟨e, he, hew⟩ := xpl_forall₂_mem_right hm w hw
    have hek : eventKind e = .accept := by rw [← xpl_kind_of_matches hew, hwk]
    rcases List.mem_cons.1 he with rfl | he' <;> [cases hek; (have := hrs_kind e he'; rw [hek] at this; cases this)]
  cases m with
  | aliceStart a b idS regB hb shown =>
    have hlen : ((Move.aliceStart a b idS regB hb shown).vis tr).length = 35 := (by have := (xpl_forall₂_length hm).symm; simpa [hrs_len] using this); obtain ⟨hshown, hvis⟩ := aliceStart_vis_eq_aliceVis_of_length_35 hlen; rw [hvis] at hm; exact ⟨a, b, idS, regB, hb, shown, rfl, hshown, aliceStart_isAliceDone_of_not_noSessionEffect hneff, hm⟩
  | bobStart b a kh rIdx mh pq sp shown =>
    exact absurd (noSessionEffect_of_no_accept (m := .bobStart b a kh rIdx mh pq sp shown) trivial ha hnoacc) hneff
  | decrypt me si mi pq sp w => exact absurd (noSessionEffect_of_no_accept (m := .decrypt me si mi pq sp w) trivial ha hnoacc) hneff
  | decryptSkipped me si mi k pq sp w =>
    exact absurd (noSessionEffect_of_no_accept (m := .decryptSkipped me si mi k pq sp w) trivial ha hnoacc) hneff
  | reject draws => exact absurd (noSessionEffect_of_no_accept (m := .reject draws) trivial ha hnoacc) hneff
  | setup => cases hs
  | encrypt | encryptAbort | encryptFail | compromiseIK | compromiseSPK | compromisePQSPK | compromiseOPK | exposeKey | exposeSpqr | exposeSkipped
  | attackerSend | brkDH | brkKEM => exact False.elim hrk
theorem invert_send_move {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {tr : ExecTrace} {m : Move} {pt c w : HwBytes} (hm : List.Forall₂ (EventMatchesEntry i r S g) [.pt pt, .rng c, .send w] (m.vis tr)) : ∃ me sIdx cl pq wrap, m = .encrypt me sIdx cl pq wrap ∧ lastSent tr (m.next tr) ≠ none ∧ (wrap = none → w.head? = some TripleRatchet.Refinement.wireWhisperTag) ∧ List.Forall₂ (EventMatchesEntry i r S g) [.pt pt, .rng c, .send w] (encVis tr (m.next tr) wrap true) := by
  have hmem_send : MachineEvent.send w ∈ ([.pt pt, .rng c, .send w] : List MachineEvent) := by simp
  obtain ⟨v_s, hv_s, hev_s⟩ := xpl_forall₂_mem_left hm (.send w) hmem_send; have hvk_s : v_s.kind = .send := xpl_kind_of_matches hev_s
  obtain ⟨me, sIdx, cl, pq, wrap, rfl⟩ : ∃ me sIdx cl pq wrap, m = .encrypt me sIdx cl pq wrap := by
    rcases xpl_vis_kind m tr hv_s with h | ⟨_, h⟩ | ⟨_, h⟩
    · rw [hvk_s] at h; cases h
    · rcases h with h | h | ⟨_, h⟩
      · rw [hvk_s] at h; cases h
      · rw [hvk_s] at h; cases h
      · exact h
    · rw [hvk_s] at h; rcases h with h | h | h <;> cases h
  have hex : exposures tr ((Move.encrypt me sIdx cl pq wrap).next tr) = [] := exposures_nil_of_not_leakKind rfl (fun h => nomatch h); have hvis : (Move.encrypt me sIdx cl pq wrap).vis tr = encVis tr ((Move.encrypt me sIdx cl pq wrap).next tr) wrap true := (by rw [xpl_vis_eq, hex, List.append_nil]; rfl); rw [hvis] at hm hv_s
  have hls : lastSent tr ((Move.encrypt me sIdx cl pq wrap).next tr) ≠ none ∧
      (wrap = none → w.head? = some TripleRatchet.Refinement.wireWhisperTag) := by
    unfold encVis at hv_s; simp only [↓reduceIte, List.mem_append] at hv_s
    rcases hv_s with hd | hsnd
    · rcases encDraws_kind _ hd with hk | hk <;> (rw [hvk_s] at hk; cases hk)
    · unfold encSend at hsnd
      rcases hls_eq : lastSent tr ((Move.encrypt me sIdx cl pq wrap).next tr) with _ | wt
      · rw [hls_eq] at hsnd; cases hsnd
      · refine ⟨by simp, fun hw_none => ?_⟩; rw [hls_eq, hw_none, List.mem_singleton] at hsnd; subst hsnd; obtain ⟨_, t, _, hw_eq⟩ := hev_s; change w = _ at hw_eq; rw [hw_eq]; rfl
  exact ⟨me, sIdx, cl, pq, wrap, rfl, hls.1, hls.2, hm⟩
theorem movesFrom_invisibleNoEffect_of_matchedPrefix_nil {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms₀ : List Move} (hmp₀ : Symbolic.Swarm.CREF.MatchedPrefix i r S g ms₀ []) : MovesFrom InvisibleNoEffect (setupTrace r) ms₀ := by obtain ⟨_, ⟨_, hs₀, ⟨_, hanc₀, _⟩, _, _⟩, hfor₀⟩ := hmp₀; have hrv₀ : runVis r ms₀ = [] := List.forall₂_nil_left_iff.1 hfor₀; have hvis₀ : (runMoves ms₀ (setupTrace r)).2 = [] := (by have h1 : runVis r ms₀ = r.setupMove.vis Trace.nil ++ (runMoves ms₀ (setupTrace r)).2 := rfl; rw [h1] at hrv₀; exact (List.append_eq_nil_iff.1 hrv₀).2); exact xpl_movesFrom_invisible ms₀ (setupTrace r) (xpl_movesFrom_of ms₀ (setupTrace r) hs₀ hanc₀) hvis₀
theorem matchedPrefix_ini_send_struct_opt {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {bun : HwBytes} {rs : List MachineEvent} {pt c w : HwBytes} (hmp : Symbolic.Swarm.CREF.MatchedPrefix i r S g ms ((.recv bun :: rs) ++ [.pt pt, .rng c, .send w])) (hrs_len : rs.length = 34) (hrs_kind : ∀ e ∈ rs, eventKind e = .rng) : ∃ pre a b idS regB hb shown mid me sIdx cl pq wrap post, ms = pre ++ .aliceStart a b idS regB hb shown :: mid ++ .encrypt me sIdx cl pq wrap :: post ∧ let tr₁ := (runMoves pre (setupTrace r)).1;
      let m₀ := Move.aliceStart a b idS regB hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let m₁ := Move.encrypt me sIdx cl pq wrap;
      MovesFrom InvisibleNoEffect (setupTrace r) pre ∧
      MovesFrom InvisibleNoEffect (m₀.next tr₁) mid ∧
      MovesFrom InvisibleNoEffect (m₁.next tr₂) post ∧
      35 ≤ shown ∧ (eventIdx isAliceDone tr₁ (m₀.next tr₁)).isSome = true ∧ lastSent tr₂ (m₁.next tr₂) ≠ none ∧
      (wrap = none → w.head? = some TripleRatchet.Refinement.wireWhisperTag) ∧
      List.Forall₂ (EventMatchesEntry i r S g) (.recv bun :: rs) (aliceVis tr₁ (m₀.next tr₁) hb) ∧
      List.Forall₂ (EventMatchesEntry i r S g) [.pt pt, .rng c, .send w] (encVis tr₂ (m₁.next tr₂) wrap true) := by
  let blk₁ : List MachineEvent := .recv bun :: rs; let blk₂ : List MachineEvent := [.pt pt, .rng c, .send w];
  have hhead₂ : ∀ e ∈ blk₂.head?, eventKind e = .recv ∨ eventKind e = .pt := by intro e he; simp [blk₂] at he; subst he; exact Or.inr rfl
  obtain ⟨ms₁, δ₂, hms, hmp₁, hfor₂⟩ := matchedPrefix6_split hmp hhead₂ (matchedPrefix6_prefix_reachable hmp); have hB₂ : XplBlock6 i r S g ms₁ δ₂ blk₁ blk₂ := ⟨hmp₁, hms ▸ hmp.2.1, hfor₂⟩
  have hhead₁ : ∀ e ∈ blk₁.head?, eventKind e = .recv ∨ eventKind e = .pt := by intro e he; simp [blk₁] at he; subst he; exact Or.inl rfl
  have hmp₁' : Symbolic.Swarm.CREF.MatchedPrefix i r S g ms₁ ([] ++ blk₁) := by simpa using hmp₁
  obtain ⟨ms₀, δ₁, hms₁, hmp₀, hfor₁⟩ := matchedPrefix6_split hmp₁' hhead₁ (matchedPrefix6_prefix_reachable hmp₁'); have hB₁ : XplBlock6 i r S g ms₀ δ₁ [] blk₁ := ⟨hmp₀, hms₁ ▸ hmp₁.2.1, hfor₁⟩
  have hne₁ : blk₁ ≠ [] := by simp [blk₁]
  have htail₁ : ∀ e ∈ blk₁.tail, eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak := (by intro e he; have hk := hrs_kind e he; rw [hk]; decide); obtain ⟨pre₁, m₀, post₁, rfl, hpre₁, ⟨hs₀, ha₀, hm₀⟩, hpost₁⟩ := xpl6_oneMove hB₁ hhead₁ hne₁ htail₁
  have hne₂ : blk₂ ≠ [] := by simp [blk₂]
  have htail₂ : ∀ e ∈ blk₂.tail, eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak := by
    intro e he; simp only [blk₂, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> { dsimp [eventKind]; decide }
  obtain ⟨pre₂, m₁, post₂, rfl, hpre₂, ⟨_, _, hm₁⟩, hpost₂⟩ := xpl6_oneMove hB₂ hhead₂ hne₂ htail₂; let pre := ms₀ ++ pre₁; let mid := post₁ ++ pre₂; let tr₁ := (runMoves pre (setupTrace r)).1;
  have htr₁_eq : (runMoves pre₁ (runTraceMoves r ms₀)).1 = tr₁ := by dsimp [tr₁, pre]; rw [runMoves_append_fst, ← xpl_runTrace_eq]
  rw [htr₁_eq] at ha₀ hm₀ hpost₁; have hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre := (by rw [movesFrom_append, ← xpl_runTrace_eq]; exact ⟨movesFrom_invisibleNoEffect_of_matchedPrefix_nil hmp₀, hpre₁⟩); let tr₂ := (runMoves mid (m₀.next tr₁)).1;
  have hms₁_eq : ms₁ = pre ++ m₀ :: post₁ := by simp [hms₁, pre, List.append_assoc]
  have hrun_ms₁ : runTraceMoves r ms₁ = (runMoves post₁ (m₀.next tr₁)).1 := by rw [hms₁_eq, xpl_runTrace_eq, runMoves_append_fst, runMoves_cons_fst]
  have htr₂_eq : (runMoves pre₂ (runTraceMoves r ms₁)).1 = tr₂ := by dsimp [tr₂, mid]; rw [runMoves_append_fst, ← hrun_ms₁]
  rw [htr₂_eq] at hm₁ hpost₂
  have hmid : MovesFrom InvisibleNoEffect (m₀.next tr₁) mid := by rw [movesFrom_append, ← hrun_ms₁]; exact ⟨hpost₁, hpre₂⟩
  obtain ⟨me, sIdx, cl, pq, wrap, rfl, hls, hwrap_none, hm₁_vis⟩ := invert_send_move hm₁; have hneff : ¬ NoSessionEffect tr₁ m₀ := (by intro heff; have hno₁ : NoTRState tr₁ := noTRState_of_movesFrom_invisibleNoEffect (noTRState_setupTrace r) hpre; have hno_m₀ : NoTRState (m₀.next tr₁) := noTRState_of_noSessionEffect hno₁ heff; have hno₂ : NoTRState tr₂ := noTRState_of_movesFrom_invisibleNoEffect hno_m₀ hmid; exact hls (encrypt_lastSent_none_of_noTRState hno₂ me sIdx cl pq wrap)); obtain ⟨a, b, idS, regB, hb, shown, rfl, hshown, hdone, hm₀_vis⟩ := invert_ini_move_of_not_noSessionEffect hs₀ ha₀ hm₀ hrs_len hrs_kind hneff; refine ⟨pre, a, b, idS, regB, hb, shown, mid, me, sIdx, cl, pq, wrap, post₂, ?_, hpre, hmid, hpost₂, hshown, hdone, hls, hwrap_none, hm₀_vis, hm₁_vis⟩; simp [hms, hms₁, pre, mid, List.append_assoc]
theorem matchedPrefix_ini_send_struct {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {bun : HwBytes} {rs : List MachineEvent} {pt c w : HwBytes} (hmp : Symbolic.Swarm.CREF.MatchedPrefix i r S g ms ((.recv bun :: rs) ++ [.pt pt, .rng c, .send w])) (hrs_len : rs.length = 34) (hrs_kind : ∀ e ∈ rs, eventKind e = .rng) (hw : w.head? ≠ some TripleRatchet.Refinement.wireWhisperTag) : ∃ pre a b idS regB hb shown mid me sIdx cl pq wr post, ms = pre ++ .aliceStart a b idS regB hb shown :: mid ++ .encrypt me sIdx cl pq (some wr) :: post ∧ let tr₁ := (runMoves pre (setupTrace r)).1;
      let m₀ := Move.aliceStart a b idS regB hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let m₁ := Move.encrypt me sIdx cl pq (some wr);
      MovesFrom InvisibleNoEffect (setupTrace r) pre ∧
      MovesFrom InvisibleNoEffect (m₀.next tr₁) mid ∧
      MovesFrom InvisibleNoEffect (m₁.next tr₂) post ∧
      35 ≤ shown ∧ (eventIdx isAliceDone tr₁ (m₀.next tr₁)).isSome = true ∧ lastSent tr₂ (m₁.next tr₂) ≠ none ∧
      List.Forall₂ (EventMatchesEntry i r S g) (.recv bun :: rs) (aliceVis tr₁ (m₀.next tr₁) hb) ∧
      List.Forall₂ (EventMatchesEntry i r S g) [.pt pt, .rng c, .send w] (encVis tr₂ (m₁.next tr₂) (some wr) true) := by
  obtain ⟨pre, a, b, idS, regB, hb, shown, mid, me, sIdx, pq, cl, wrap, post, hms, hpre, hmid, hpost, hshown, hdone, hls, hwrap_none, hm₀_vis, hm₁_vis⟩ := matchedPrefix_ini_send_struct_opt hmp hrs_len hrs_kind
  cases wrap with
  | none => exact absurd (hwrap_none rfl) hw
  | some wr =>
    exact ⟨pre, a, b, idS, regB, hb, shown, mid, me, sIdx, pq, cl, wr, post, hms, hpre, hmid, hpost, hshown, hdone, hls, hm₀_vis, hm₁_vis⟩
end Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct

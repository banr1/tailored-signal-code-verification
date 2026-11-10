/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1Cli
public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv78b
public import Symbolic.BugInjection.Proofs.Common443.CliCoinSplitClose
import Symbolic.Proofs.Swarm.COMPOSED.CompPresTRExp
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CliBridge

open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.Composed.Refinement.Cli
open Symbolic.BugInjection

attribute [local irreducible] Symbolic.BugInjection.hexBytes

abbrev cliCompFitsPinned := Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable.cliCompFitsPinned

theorem cliCompFitsPinned_imp_cliCompFits (w : PQXDHSpqrSetup)
    (iw : ExternInterpretation × CryptoVerification.SignalSession.CliHooks)
    (r : Records)
    (h : cliCompFitsPinned w iw r) : cliCompFits w iw r :=
  ⟨h.1.1, h.2.1, h.2.2⟩

theorem coinSplit_nonRng_cons {e : MachineEvent} {σ τ : List MachineEvent}
    (hne : ∀ c, e ≠ .rng c) (hcs : CoinSplit (e :: σ) τ) :
    ∃ τ', τ = e :: τ' ∧ CoinSplit σ τ' := by
  cases hcs with
  | keep _ hrest => exact ⟨_, rfl, hrest⟩
  | split => exfalso; exact hne _ rfl

theorem coinSplit_rng_cons {c : HwBytes} {σ τ : List MachineEvent}
    (hcs : CoinSplit (.rng c :: σ) τ) :
    ∃ (pieces : List HwBytes) (τ' : List MachineEvent),
      (∀ p ∈ pieces, p ≠ []) ∧ pieces.flatten <+: c ∧
      τ = pieces.map MachineEvent.rng ++ τ' ∧ CoinSplit σ τ' := by
  cases hcs with
  | keep hne _ => exact absurd rfl (hne c)
  | split hne hpref hrest => exact ⟨_, _, hne, hpref, rfl, hrest⟩

private theorem map_rng_kind {pieces : List HwBytes} :
    ∀ e ∈ pieces.map MachineEvent.rng, eventKind e = .rng := by
  intro e he
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp he
  rfl

private theorem map_rng_snoc_send_kind {pieces : List HwBytes} {w : HwBytes} :
    ∀ e ∈ pieces.map MachineEvent.rng ++ [MachineEvent.send w],
      eventKind e = .rng ∨ eventKind e = .send := by
  intro e he
  rcases List.mem_append.mp he with h1 | h2
  · exact Or.inl (map_rng_kind e h1)
  · simp only [List.mem_singleton] at h2
    subst h2; exact Or.inr rfl

private theorem coinSplit_no_leak {σ τ : List MachineEvent}
    (hcs : CoinSplit σ τ) (hσ : ∀ e ∈ σ, eventKind e ≠ .leak) :
    ∀ e ∈ τ, eventKind e ≠ .leak := by
  induction hcs with
  | nil => intro _ h; nomatch h
  | keep _ _ ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he'
    · exact hσ _ (List.mem_cons_self ..)
    · exact ih (fun x hx => hσ x (List.mem_cons_of_mem _ hx)) e he'
  | split _ _ _ ih =>
    intro e he
    rcases List.mem_append.mp he with h1 | h2
    · rw [map_rng_kind e h1]; decide
    · exact ih (fun x hx => hσ x (List.mem_cons_of_mem _ hx)) e h2

open Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace in
@[simp] private theorem length_append_entry {T : Type} [ExecTraceTypes.Has T] (tr : ExecTrace) (x : T) :
    (tr.append x).length = tr.length + 1 :=
  Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.length_append_entry_eq tr x

open Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace in
private theorem newRandoms_logSkippedKeys (s : DY.Libsignal.TripleRatchet.SessionInfo)
    (pk : DY.Bytes) (rIdx srcIdx : Nat) :
    ∀ (k : Nat) (ck : DY.Bytes) (idx : UInt32) (tr₀ tr : ExecTrace),
      tr₀.length ≤ tr.length →
      newRandoms tr₀ ((DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx srcIdx ck idx k).run tr).2.val =
        newRandoms tr₀ tr
  | 0, ck, idx, tr₀, tr, _ => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.traceful_run_pure_snd]
  | k + 1, ck, idx, tr₀, tr, hle => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    rw [CompPresTRExp.run_logEvent_bind_snd (Ev := DY.Libsignal.TripleRatchet.TREvent)]
    let tr₁ := tr.append (CompTrace.TREvE
      (.SkippedKeyStored s pk idx (DY.Libsignal.TripleRatchet.kdfCk ck).2 rIdx srcIdx))
    have hle₁ : tr₀.length ≤ tr₁.length := by
      dsimp [tr₁]; rw [length_append_entry]; omega
    change newRandoms tr₀ ((DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx srcIdx
      (DY.Libsignal.TripleRatchet.kdfCk ck).1 (idx + 1) k).run tr₁).2.val = newRandoms tr₀ tr
    rw [newRandoms_logSkippedKeys s pk rIdx srcIdx k _ _ tr₀ tr₁ hle₁,
      newRandoms_append_of_proj hle _ rfl]

open Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace in
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv78a in
private theorem bobStartPreSkipTr_length_le (tr : ExecTrace) (b a : Participant)
    (o : DY.Libsignal.PQXDH.BobHandshakeOut) (msg : DY.Libsignal.TripleRatchet.TRSignalMsg)
    (key : DY.Bytes) : tr.length ≤ (bobStartPreSkipTr tr b a o msg key).length :=
  Nat.le_of_lt (length_bobStartPreSkipTr tr b a o msg key)

open Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace in
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv78a in
private theorem newRandoms_bobStartPreSkipTr (tr : ExecTrace) (b a : Participant)
    (o : DY.Libsignal.PQXDH.BobHandshakeOut) (msg : DY.Libsignal.TripleRatchet.TRSignalMsg)
    (key : DY.Bytes) :
    newRandoms tr (bobStartPreSkipTr tr b a o msg key) = [(randTerm tr.length 32, 32)] := by
  unfold bobStartPreSkipTr
  cases o.opk with
  | none =>
    dsimp only
    rw [newRandoms_append_of_proj (by simp only [length_append_entry]; omega) _ rfl,
      newRandoms_append_of_proj (by simp only [length_append_entry]; omega) _ rfl,
      newRandoms_append_of_proj (by simp only [length_append_entry]; omega) _ rfl,
      newRandoms_append_of_proj (by simp only [length_append_entry]; omega) _ rfl,
      newRandoms_append_of_proj (by simp only [length_append_entry]; omega) _ rfl,
      newRandoms_append_rnd (Nat.le_refl _) 32, newRandoms_self, List.nil_append]
  | some opkPk =>
    dsimp only
    rw [newRandoms_append_of_proj (by simp only [length_append_entry]; omega) _ rfl,
      newRandoms_append_of_proj (by simp only [length_append_entry]; omega) _ rfl,
      newRandoms_append_of_proj (by simp only [length_append_entry]; omega) _ rfl,
      newRandoms_append_of_proj (by simp only [length_append_entry]; omega) _ rfl,
      newRandoms_append_of_proj (by simp only [length_append_entry]; omega) _ rfl,
      newRandoms_append_of_proj (by simp only [length_append_entry]; omega) _ rfl,
      newRandoms_append_rnd (Nat.le_refl _) 32, newRandoms_self, List.nil_append]

open Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace in
private theorem logSkippedKeys_length_le (s : DY.Libsignal.TripleRatchet.SessionInfo) (pk : DY.Bytes)
    (rIdx srcIdx : Nat) (ck : DY.Bytes) (idx : UInt32) (n : Nat) (tr₀ tr : ExecTrace)
    (hle : tr₀.length ≤ tr.length) :
    tr₀.length ≤ ((DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx srcIdx ck idx n).run tr).2.val.length :=
  Nat.le_trans hle (DY.Trace.length_le _ _
    ((DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx srcIdx ck idx n).run tr).2.property)

open Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace in
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv78a in
private theorem newRandoms_bobStartTr (tr : ExecTrace) (b a : Participant)
    {kh : DY.Libsignal.PQXDH.BobKeyHandles} {regA : Nat}
    {mh : DY.Libsignal.PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32}
    (w : Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy.BobStartOk tr b a kh regA mh pqIdx spqrMsgIdx) :
    newRandoms tr (bobStartTr tr b a w) =
      [(randTerm tr.length 32, 32)] := by
  unfold bobStartTr; dsimp only
  have hpre := bobStartPreSkipTr_length_le tr b a (bobOutOf w.ikB w.spk w.pqsk w.opk w.ikAPk w.ek w.ct w.keys) w.msg w.key
  have hskip : tr.length ≤ (bobStartSkipTr tr b a w).length := by
    unfold bobStartSkipTr; dsimp only
    exact logSkippedKeys_length_le _ _ _ _ _ _ _ tr _ hpre
  rw [newRandoms_append_of_proj (by simp only [length_append_entry]; omega) _ rfl,
    newRandoms_append_of_proj (by simp only [length_append_entry]; omega) _ rfl,
    newRandoms_append_of_proj hskip _ rfl]
  unfold bobStartSkipTr; dsimp only
  rw [newRandoms_logSkippedKeys _ _ _ _ _ _ _ tr _ hpre,
    newRandoms_bobStartPreSkipTr]

open Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace in
open Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct in
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop in
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts in
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.BobDone in
private theorem rs_eq_singleton_rng_of_rpk
    (r : Records) (S : Sem) (g : Ghost) (τ₀ : List MachineEvent)
    (b_wire b_pt : HwBytes) (rs : List MachineEvent) (ms : List Move) (p : PreKeyFields)
    (hrs : ∀ e ∈ rs, eventKind e = .rng)
    (hw : b_wire.head? = some 3#8) (hp : parsePreKeyWire b_wire = some p)
    (hnk : ∀ ms₀, Symbolic.Swarm.CREF.MatchedPrefix SpecTop.compI0 r S g ms₀ τ₀ →
      ¬ DY.Libsignal.Composed.Refinement.KnownBaseKey SpecTop.compI0 r S g ms₀ p)
    (hmp : Symbolic.Swarm.CREF.MatchedPrefix SpecTop.compI0 r S g ms
      (τ₀ ++ (.recv b_wire :: rs ++ [.accept b_pt]))) :
    ∃ b_rng : HwBytes, rs = [.rng b_rng] := by
  have hhead : ∀ e ∈ ((.recv b_wire :: (rs ++ [.accept b_pt])) : List MachineEvent).head?,
      eventKind e = .recv ∨ eventKind e = .pt := by
    intro e he; simp at he; subst he; exact Or.inl rfl
  have htail : ∀ e ∈ ((.recv b_wire :: (rs ++ [.accept b_pt])) : List MachineEvent).tail,
      eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak := by
    intro e he; simp only [List.tail_cons, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · rw [hrs e he]; exact ⟨by decide, by decide, by decide⟩
    · exact ⟨by nofun, by nofun, by nofun⟩
  have hmp' : Symbolic.Swarm.CREF.MatchedPrefix SpecTop.compI0 r S g ms
      (τ₀ ++ (.recv b_wire :: (rs ++ [.accept b_pt]))) := by
    simpa using hmp
  obtain ⟨ms₀, δ, hms, hmp₀, hfor⟩ :=
    matchedPrefix6_split hmp' hhead (matchedPrefix6_prefix_reachable hmp')
  have hB : XplBlock6 SpecTop.compI0 r S g ms₀ δ _ (.recv b_wire :: (rs ++ [.accept b_pt])) :=
    ⟨hmp₀, hms ▸ hmp'.2.1, hfor⟩
  obtain ⟨pre₁, m, post₁, rfl, hpre, ⟨hs, ha, hm⟩, hpost⟩ :=
    xpl6_oneMove hB hhead (by simp) htail
  let tr_pre := (runMoves pre₁ (runTraceMoves r ms₀)).1
  have hbob_eq := bobDoneBaseKeys_runMoves_of_movesFrom (runTraceMoves r ms₀) pre₁ hpre
  have hact : ActorIn ((moveActor m).getD r.bob) m := by
    unfold ActorIn; rcases moveActor m with _ | _ <;> simp
  have hmem_acc : MachineEvent.accept b_pt ∈ (.recv b_wire :: (rs ++ [.accept b_pt])) := by simp
  obtain ⟨v_acc, hv_acc, hev_acc⟩ := xpl_forall₂_mem_left hm (.accept b_pt) hmem_acc
  have hk_acc : v_acc.kind = .accept := by rw [xpl_kind_of_matches hev_acc]; rfl
  rcases xpl_accept_by m tr_pre hv_acc hk_acc hact with hbob | hdec
  · unfold BobStartBy at hbob
    cases m with
    | bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown =>
      obtain ⟨w_ok⟩ := Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy.bobStart_accept_ok hv_acc hk_acc
      have hnr : newRandoms tr_pre
          ((Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown).next tr_pre) =
          [(randTerm tr_pre.length 32, 32)] := by
        rw [Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv78a.bobStart_next_eq w_ok]
        exact newRandoms_bobStartTr _ _ _ w_ok
      have hexp : exposures tr_pre
          ((Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown).next tr_pre) = [] :=
        exposures_nil_of_not_leakKind rfl (fun h => nomatch h)
      rcases hpt : receivedPlaintext tr_pre
          ((Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown).next tr_pre) with _ | pt_m
      · exfalso
        have hvis0 : (Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown).vis tr_pre =
            ([⟨.recv, received tr_pre [mh.ek, mh.ct, mh.msg] ++ (bobOpkPk b kh tr_pre).toList,
                .preKeyRecv, none⟩,
              rngEntry (randTerm tr_pre.length 32)] : List VisEntry).take shown := by
          rw [xpl_vis_eq, hexp, List.append_nil]
          dsimp only [xpl_ownVis, bobVis]
          rw [hnr, hpt]
          rfl
        rw [hvis0] at hv_acc
        rcases List.mem_cons.mp (List.mem_of_mem_take hv_acc) with rfl | h1
        · cases hk_acc
        · rw [List.mem_singleton] at h1; subst h1; cases hk_acc
      · have hvis : (Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown).vis tr_pre =
            ([⟨.recv, received tr_pre [mh.ek, mh.ct, mh.msg] ++ (bobOpkPk b kh tr_pre).toList,
                .preKeyRecv, none⟩,
              rngEntry (randTerm tr_pre.length 32),
              ⟨.accept, [pt_m], .single,
                eventIdx isBobDone tr_pre
                  ((Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown).next tr_pre)⟩] :
                List VisEntry).take shown := by
          rw [xpl_vis_eq, hexp, List.append_nil]
          dsimp only [xpl_ownVis, bobVis]
          rw [hnr, hpt]
          rfl
        rw [hvis] at hm
        rcases rs with _ | ⟨e₁, _ | ⟨e₂, rs_tl'⟩⟩
        · rcases shown with _ | _ | shown'
          · cases hm
          · cases hm with | cons _ hm₁ => cases hm₁
          · cases hm with | cons _ hm₁ => cases hm₁ with | cons hm_rng _ =>
              have hk := hm_rng.1
              simp [eventKind, rngEntry] at hk
        · have hk1 := hrs e₁ (List.mem_cons_self ..)
          cases e₁ <;> try cases hk1
          exact ⟨_, rfl⟩
        · have hlen := hm.length_eq
          simp only [List.cons_append, List.length_cons, List.length_append,
            List.length_take, List.length_nil] at hlen
          omega
    | _ => exact False.elim hbob
  · exfalso
    obtain ⟨v, u', hv, _, hvu⟩ := xpl_forall₂_cons_left hm
    have hv_mem : v ∈ m.vis tr_pre := by rw [hvu]; exact List.mem_cons_self ..
    have hvk : v.kind = .recv := hv.1.symm
    rw [xpl_vis_eq] at hv_mem
    rcases List.mem_append.1 hv_mem with hown | hexp
    · unfold DecryptBy at hdec
      cases m <;> try exact False.elim hdec
      all_goals
        dsimp only [xpl_ownVis, decVis] at hown
        rcases List.mem_append.1 hown with h12 | h3
        · rcases List.mem_append.1 h12 with h1 | h2
          · rename_i wrapped
            obtain ⟨b_msg, _, rfl⟩ := Option.map_eq_some_iff.1 (Option.mem_toList.1 h1)
            cases wrapped
            · exact not_eventMatchesEntry_whisper_of_head SpecTop.compI0 r S g b_wire [b_msg] none hw hv
            · refine preKeyInner_rejected_of_foreign SpecTop.compI0 r S g b_wire p
                (sessionBaseKeys tr_pre _) [b_msg] none hp ?_ hv
              exact fun ek hek hbk =>
                hnk ms₀ hmp₀ ⟨ek, hbob_eq ▸ mem_bobDoneBaseKeys_of_mem_sessionBaseKeys hek, hbk⟩
          · obtain ⟨_, _, rfl⟩ := List.mem_map.1 h2; cases hvk
        · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 (Option.mem_toList.1 h3); cases hvk
    · have hk := xpl_exposures_kind hexp; rw [hvk] at hk; cases hk

open Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace in
open Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct in
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop in
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.MacGuardGen in
private theorem invert_send_move_rs {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost}
    {tr : ExecTrace} {m : Move} {pt w : HwBytes} {rs : List MachineEvent}
    (hm : List.Forall₂ (EventMatchesEntry i r S g) (.pt pt :: (rs ++ [.send w])) (m.vis tr)) :
    ∃ me sIdx cl pq wrap,
      m = .encrypt me sIdx cl pq wrap ∧
      lastSent tr (m.next tr) ≠ none ∧
      (wrap = none → w.head? = some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag) ∧
      List.Forall₂ (EventMatchesEntry i r S g) (.pt pt :: (rs ++ [.send w]))
        (encVis tr (m.next tr) wrap true) := by
  have hmem_send : MachineEvent.send w ∈ (.pt pt :: (rs ++ [.send w]) : List MachineEvent) := by simp
  obtain ⟨v_s, hv_s, hev_s⟩ := xpl_forall₂_mem_left hm (.send w) hmem_send
  have hvk_s : v_s.kind = .send := xpl_kind_of_matches hev_s
  obtain ⟨me, sIdx, cl, pq, wrap, rfl⟩ : ∃ me sIdx cl pq wrap, m = .encrypt me sIdx cl pq wrap := by
    rcases xpl_vis_kind m tr hv_s with h | ⟨_, h⟩ | ⟨_, h⟩
    · rw [hvk_s] at h; cases h
    · rcases h with h | h | ⟨_, h⟩
      · rw [hvk_s] at h; cases h
      · rw [hvk_s] at h; cases h
      · exact h
    · rw [hvk_s] at h; rcases h with h | h | h <;> cases h
  have hex : exposures tr ((Move.encrypt me sIdx cl pq wrap).next tr) = [] :=
    exposures_nil_of_not_leakKind rfl (fun h => nomatch h)
  have hvis : (Move.encrypt me sIdx cl pq wrap).vis tr =
      encVis tr ((Move.encrypt me sIdx cl pq wrap).next tr) wrap true := by
    rw [xpl_vis_eq, hex, List.append_nil]; rfl
  rw [hvis] at hm hv_s
  have hls : lastSent tr ((Move.encrypt me sIdx cl pq wrap).next tr) ≠ none ∧
      (wrap = none → w.head? = some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag) := by
    unfold encVis at hv_s; simp only [↓reduceIte, List.mem_append] at hv_s
    rcases hv_s with hd | hsnd
    · rcases encDraws_kind _ hd with hk | hk <;> (rw [hvk_s] at hk; cases hk)
    · unfold encSend at hsnd
      rcases hls_eq : lastSent tr ((Move.encrypt me sIdx cl pq wrap).next tr) with _ | wt
      · rw [hls_eq] at hsnd; cases hsnd
      · refine ⟨by simp, fun hw_none => ?_⟩
        rw [hls_eq, hw_none, List.mem_singleton] at hsnd; subst hsnd
        obtain ⟨_, t, _, hw_eq⟩ := hev_s; change w = _ at hw_eq; rw [hw_eq]; rfl
  exact ⟨me, sIdx, cl, pq, wrap, rfl, hls.1, hls.2, hm⟩

open Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace in
open Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct in
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop in
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.MacGuardGen in
private theorem allSentNet_xplBlock_send_rs
    {n₀ : Nat} {P : DY.Bytes → Prop} {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost}
    {ms₀ δ : List Move} {acc : List MachineEvent} {pt0 w : HwBytes} {rs : List MachineEvent}
    {q₀ : PreKeyFields}
    (hB : XplBlock6 i r S g ms₀ δ acc (.pt pt0 :: (rs ++ [.send w])))
    (hrs : ∀ e ∈ rs, eventKind e = .rng)
    (hw : w.head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag)
    (hlen : w.length < 2 ^ 63)
    (hq₀ : parsePreKeyWire w = some q₀)
    (htr : AllSentNet n₀ P (runTraceMoves r ms₀))
    (hpw : ∀ raw, gamma i S g raw = q₀.message → P raw) :
    AllSentNet n₀ P (runTraceMoves r (ms₀ ++ δ)) := by
  have hhead : ∀ e ∈ ((.pt pt0 :: (rs ++ [.send w])) : List MachineEvent).head?,
      eventKind e = .recv ∨ eventKind e = .pt := by
    intro e he; simp at he; subst he; exact Or.inr rfl
  have htail : ∀ e ∈ ((.pt pt0 :: (rs ++ [.send w])) : List MachineEvent).tail,
      eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak := by
    intro e he; simp only [List.tail_cons, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · rw [hrs e he]; exact ⟨by decide, by decide, by decide⟩
    · exact ⟨by nofun, by nofun, by nofun⟩
  obtain ⟨pre, m, post, rfl, hpre_inv, ⟨_, _, hm⟩, hpost_inv⟩ :=
    xpl6_oneMove hB hhead (by simp) htail
  let tr_pre := (runMoves pre (runTraceMoves r ms₀)).1
  have htr_pre : AllSentNet n₀ P tr_pre := allSentNet_runMoves_of_movesFrom hpre_inv htr
  obtain ⟨me, sIdx, cl, pq, wrap, rfl, _, hwrap_none, hm_vis⟩ := invert_send_move_rs hm
  rcases wrap with _ | ⟨e, c'⟩
  · exact False.elim (hw (hwrap_none rfl))
  · have htr_m : AllSentNet n₀ P ((Move.encrypt me sIdx cl pq (some (e, c'))).next tr_pre) :=
      allSentNet_encrypt me sIdx cl pq (some (e, c')) tr_pre htr_pre (fun raw hls => by
        obtain ⟨v, hv, hev⟩ := xpl_forall₂_mem_left hm_vis (.send w) (by simp)
        have hvk : v.kind = .send := xpl_kind_of_matches hev
        unfold encVis at hv; simp only [↓reduceIte, List.mem_append] at hv
        rcases hv with hd | hsnd
        · rcases encDraws_kind _ hd with hk | hk <;> (rw [hvk] at hk; cases hk)
        · unfold encSend at hsnd; rw [hls, List.mem_singleton] at hsnd; subst hsnd
          obtain ⟨_, hsm⟩ : Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire.SendMatchesMoves i r S g w (received tr_pre [e, c'] ++ [raw]) := hev.2
          have hgamma : gamma i S g raw = q₀.message := by
            match received tr_pre [e, c'], hsm with
            | [_, _], ⟨_, _, _, _, hw'⟩ =>
              exact (Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire.parsePreKeyWire_preKeyWire_inv hw' hlen hq₀).2.2.2.symm
            | [], hsm => exact (hsm : False).elim
            | [_], hsm => exact (hsm : False).elim
            | _ :: _ :: _ :: t, hsm => cases t <;> exact (hsm : False).elim
          exact hpw raw hgamma)
    rw [Symbolic.Swarm.CREF.runTrace_append, runMoves_append_fst, runMoves_cons_fst]
    exact allSentNet_runMoves_of_movesFrom hpost_inv htr_m

def rngAt (n : Nat) : HwBytes :=
  match ((Witnesses.Cheval26WeakStateIdx1.trace)[n]? : Option MachineEvent) with
  | some (.rng b) => b | _ => []

def acceptAt (n : Nat) : HwBytes :=
  match ((Witnesses.Cheval26WeakStateIdx1.trace)[n]? : Option MachineEvent) with
  | some (.accept b) => b | _ => []

def cliCoins0 : HwBytes :=
  hexBytes "88ef4feb90ec69ba4b03602e8598de9c67586885aa24c66e7fabfd4b50fe9fd4ff91d5721bf86f00fecbae95097de418882e165dddb43f523ab6a064d0532ae296ac2db9bfb580a6d27dfe1834fd212e60f6c946b15100bfd1f8edb4ba40bf1ed23026698c9c94e50d3c44d7dd6de1b16b8ef87ab00d185968c0ea13679592542dc069155c69f909d7890acd2148bd09c81f2ef6641feb397c9d9022a1bb8ef7252906877bd8902b3e109ef6a906769994a821adacd827f6f247ecc436154612"

def cliCoins2 : HwBytes :=
  hexBytes "6769f5a26b972ffcb5ecbcdb5cb25773bc2f2bad93f90ac95a0837b831dbc22bfd086eb731e0656977e48159f273359cb6521870f8270d31c7e8fc0ad6c72a27"

def cliCoins4 : HwBytes :=
  hexBytes "1296715b07f2295cb62053e3bf6dee627f02179ee7f00e5c99fdfd9602e6627f875c643f976e46bd0352b10ccc9f5a8794c795e846b51ea20213b4dbc9346496bf684447dba0f3036fa0b5d52584140ae4cef975bfc469c0e4f438ed8b928e5672619eaa23c74d70ca07937f309599090546d9a22250f118aef790bf0955e53d2dcff3e1e5c6abe9d2348295d30d5558df6dc1422cf3d6a65eeb77456758934a1be22b43f4760cb125c052270befcc37a8c178def1c55b9f5e550520c2e90de4"

open Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED.CompInv
open Symbolic.BugInjection.Proofs.Common443
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.BobDone
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.MacGuardGen
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.Wire80
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.NoFull

def cliTrace : List MachineEvent :=
  [ .recv (wireAt 0), .rng cliCoins0,
    .pt (ptAt 35), .rng (rngAt 36), .send (sendAt 37),
    .pt (ptAt 38), .rng cliCoins2, .send (wireAt 40),
    .recv (wireAt 40), .rng (rngAt 41), .accept (acceptAt 42),
    .recv (wireAt 43), .rng cliCoins4,
    .pt (ptAt 78), .rng (rngAt 79), .send (sendAt 80),
    .recv (wireAt 81), .rng (rngAt 82), .accept (acceptAt 83) ]

private theorem cliTrace_no_leak' :
    ∀ e ∈ cliTrace, eventKind e ≠ .leak := by
  decide

theorem no_coinSplit_matchedPrefix
    {r : Records} {S : Sem} {who : List Participant} {g : Ghost} {ms : List Move}
    {τhw : List MachineEvent}
    (_hfits : compFitsPinned Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.setup SpecTop.compI0 r)
    (hnb : CompSetupSecrecy.NoBrk r ms)
    (hcs : CoinSplit cliTrace τhw)
    (hmp : DY.Libsignal.Composed.Refinement.MatchedPrefix SpecTop.compI0 r S who g ms τhw) : False := by
  have hno_leak : ∀ e ∈ τhw, eventKind e ≠ .leak :=
    coinSplit_no_leak hcs cliTrace_no_leak'
  have htr_eq : cliTrace =
      [.recv (wireAt 0), .rng cliCoins0,
       .pt (ptAt 35), .rng (rngAt 36), .send (sendAt 37),
       .pt (ptAt 38), .rng cliCoins2, .send (wireAt 40),
       .recv (wireAt 40), .rng (rngAt 41), .accept (acceptAt 42),
       .recv (wireAt 43), .rng cliCoins4,
       .pt (ptAt 78), .rng (rngAt 79), .send (sendAt 80),
       .recv (wireAt 81), .rng (rngAt 82), .accept (acceptAt 83)] := rfl
  rw [htr_eq] at hcs
  obtain ⟨τ1, rfl, hcs1⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs
  obtain ⟨p0, τ2, _, _, rfl, hcs2⟩ := coinSplit_rng_cons hcs1
  obtain ⟨τ3, rfl, hcs3⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs2
  obtain ⟨p1, τ4, _, _, rfl, hcs4⟩ := coinSplit_rng_cons hcs3
  obtain ⟨τ5, rfl, hcs5⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs4
  obtain ⟨τ6, rfl, hcs6⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs5
  obtain ⟨p2, τ7, _, _, rfl, hcs7⟩ := coinSplit_rng_cons hcs6
  obtain ⟨τ8, rfl, hcs8⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs7
  obtain ⟨τ9, rfl, hcs9⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs8
  obtain ⟨p3, τ10, _, _, rfl, hcs10⟩ := coinSplit_rng_cons hcs9
  obtain ⟨τ11, rfl, hcs11⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs10
  obtain ⟨τ12, rfl, hcs12⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs11
  obtain ⟨p4, τ13, _, _, rfl, hcs13⟩ := coinSplit_rng_cons hcs12
  obtain ⟨τ14, rfl, hcs14⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs13
  obtain ⟨p5, τ15, _, _, rfl, hcs15⟩ := coinSplit_rng_cons hcs14
  obtain ⟨τ16, rfl, hcs16⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs15
  obtain ⟨τ17, rfl, hcs17⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs16
  obtain ⟨p6, τ18, _, _, rfl, hcs18⟩ := coinSplit_rng_cons hcs17
  obtain ⟨τ19, rfl, hcs19⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs18
  cases hcs19
  let b0 : List MachineEvent := .recv (wireAt 0) :: p0.map .rng
  let b1 : List MachineEvent := .pt (ptAt 35) :: (p1.map .rng ++ [.send (sendAt 37)])
  let b2 : List MachineEvent := .pt (ptAt 38) :: (p2.map .rng ++ [.send (wireAt 40)])
  let b3 : List MachineEvent := .recv (wireAt 40) :: p3.map .rng ++ [.accept (acceptAt 42)]
  let b4 : List MachineEvent := .recv (wireAt 43) :: p4.map .rng
  let b5 : List MachineEvent := .pt (ptAt 78) :: (p5.map .rng ++ [.send (sendAt 80)])
  let b6 : List MachineEvent := .recv (wireAt 81) :: p6.map .rng ++ [.accept (acceptAt 83)]
  have hmp_cref : Symbolic.Swarm.CREF.MatchedPrefix SpecTop.compI0 r S g ms
      ((((((b0 ++ b1) ++ b2) ++ b3) ++ b4) ++ b5) ++ b6) := by
    have h0 := Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp
    simpa [b0, b1, b2, b3, b4, b5, b6, List.append_assoc] using h0
  have hno_leak' : ∀ e ∈ ((((((b0 ++ b1) ++ b2) ++ b3) ++ b4) ++ b5) ++ b6),
      eventKind e ≠ .leak := by
    intro e he
    apply hno_leak e
    simpa [b0, b1, b2, b3, b4, b5, b6, List.append_assoc] using he
  obtain ⟨p40, hp40⟩ := wireAt40_parses
  obtain ⟨p80, hp80⟩ := sendAt80_parses
  obtain ⟨p81, hp81⟩ := wireAt81_parses
  have hp40_bk : p40.baseKey.take 33 = ecKey ek1PubKey := baseKey_of_map wireAt40_baseKey hp40
  have hp81_bk : p81.baseKey.take 33 = ecKey ek2PubKey := baseKey_of_map wireAt81_baseKey hp81
  have hb0 : ∀ ms₀, Symbolic.Swarm.CREF.MatchedPrefix SpecTop.compI0 r S g ms₀ b0 →
      AllBobDone (fun _ => False) (runTraceMoves r ms₀) := by
    intro ms₀ h
    have h' : Symbolic.Swarm.CREF.MatchedPrefix SpecTop.compI0 r S g ms₀ ([] ++ b0) := h
    obtain ⟨ms_nil, δ₀, rfl, hmp_nil, hfor₀⟩ :=
      matchedPrefix6_split h' (by intro e he; simp [b0] at he; subst he; exact Or.inl rfl)
        (matchedPrefix6_prefix_reachable h')
    exact allBobDone_xplBlock_ini ⟨hmp_nil, h.2.1, hfor₀⟩ map_rng_kind
      (allBobDone_matchedPrefix_nil hmp_nil)
  have hb1 : ∀ ms₀, Symbolic.Swarm.CREF.MatchedPrefix SpecTop.compI0 r S g ms₀ (b0 ++ b1) →
      AllBobDone (fun _ => False) (runTraceMoves r ms₀) := by
    intro ms₀ h
    obtain ⟨ms_0, δ₁, rfl, hmp_0, hfor₁⟩ :=
      matchedPrefix6_split h (by intro e he; simp [b1] at he; subst he; exact Or.inr rfl)
        (matchedPrefix6_prefix_reachable h)
    exact allBobDone_xplBlock_send ⟨hmp_0, h.2.1, hfor₁⟩ map_rng_snoc_send_kind (hb0 ms_0 hmp_0)
  have hb2 : ∀ ms₀, Symbolic.Swarm.CREF.MatchedPrefix SpecTop.compI0 r S g ms₀ ((b0 ++ b1) ++ b2) →
      AllBobDone (fun _ => False) (runTraceMoves r ms₀) := by
    intro ms₀ h
    obtain ⟨ms_1, δ₂, rfl, hmp_1, hfor₂⟩ :=
      matchedPrefix6_split h (by intro e he; simp [b2] at he; subst he; exact Or.inr rfl)
        (matchedPrefix6_prefix_reachable h)
    exact allBobDone_xplBlock_send ⟨hmp_1, h.2.1, hfor₂⟩ map_rng_snoc_send_kind (hb1 ms_1 hmp_1)
  have hnk40 : ∀ ms₀, Symbolic.Swarm.CREF.MatchedPrefix SpecTop.compI0 r S g ms₀ ((b0 ++ b1) ++ b2) →
      ¬ KnownBaseKey SpecTop.compI0 r S g ms₀ p40 :=
    fun ms₀ h => not_knownBaseKey_of_allBobDone_false (hb2 ms₀ h)
  have hb3 : ∀ ms₀, Symbolic.Swarm.CREF.MatchedPrefix SpecTop.compI0 r S g ms₀ (((b0 ++ b1) ++ b2) ++ b3) →
      AllBobDone (fun ek => ecKey (gamma SpecTop.compI0 S g ek) = ecKey ek1PubKey) (runTraceMoves r ms₀) := by
    intro ms₀ h
    obtain ⟨c3, hc3⟩ := rs_eq_singleton_rng_of_rpk r S g ((b0 ++ b1) ++ b2)
      (wireAt 40) (acceptAt 42) (p3.map .rng) ms₀ p40 map_rng_kind wireAt40_head? hp40 hnk40 h
    have hb3_eq : b3 = [.recv (wireAt 40), .rng c3, .accept (acceptAt 42)] := by
      dsimp [b3]; rw [hc3]; rfl
    rw [hb3_eq] at h
    exact allBobDone_matchedPrefix_rpk wireAt40_head? hp40 hnk40
      (fun m₀ hm₀ => allBobDone_of_bobDoneBaseKeys fun ek hek => False.elim (bobDoneBaseKeys_of_allBobDone (hb2 m₀ hm₀) ek hek))
      (fun ek hek => by rw [hek, hp40_bk]) h
  have hb4 : ∀ ms₀, Symbolic.Swarm.CREF.MatchedPrefix SpecTop.compI0 r S g ms₀ ((((b0 ++ b1) ++ b2) ++ b3) ++ b4) →
      AllBobDone (fun ek => ecKey (gamma SpecTop.compI0 S g ek) = ecKey ek1PubKey) (runTraceMoves r ms₀) := by
    intro ms₀ h
    obtain ⟨ms_3, δ_4, rfl, hmp_3, hfor_4⟩ :=
      matchedPrefix6_split h (by intro e he; simp [b4] at he; subst he; exact Or.inl rfl)
        (matchedPrefix6_prefix_reachable h)
    exact allBobDone_xplBlock_ini ⟨hmp_3, h.2.1, hfor_4⟩ map_rng_kind (hb3 ms_3 hmp_3)
  have hb5 : ∀ ms₀, Symbolic.Swarm.CREF.MatchedPrefix SpecTop.compI0 r S g ms₀ (((((b0 ++ b1) ++ b2) ++ b3) ++ b4) ++ b5) →
      AllBobDone (fun ek => ecKey (gamma SpecTop.compI0 S g ek) = ecKey ek1PubKey) (runTraceMoves r ms₀) := by
    intro ms₀ h
    obtain ⟨ms_4, δ_5, rfl, hmp_4, hfor_5⟩ :=
      matchedPrefix6_split h (by intro e he; simp [b5] at he; subst he; exact Or.inr rfl)
        (matchedPrefix6_prefix_reachable h)
    exact allBobDone_xplBlock_send ⟨hmp_4, h.2.1, hfor_5⟩ map_rng_snoc_send_kind (hb4 ms_4 hmp_4)
  have hnk81 : ∀ ms₀, Symbolic.Swarm.CREF.MatchedPrefix SpecTop.compI0 r S g ms₀ (((((b0 ++ b1) ++ b2) ++ b3) ++ b4) ++ b5) →
      ¬ KnownBaseKey SpecTop.compI0 r S g ms₀ p81 :=
    fun ms₀ h => wireAt81_not_knownBaseKey_of_allBobDone_ek1 hp81 (hb5 ms₀ h)
  obtain ⟨c6, hc6⟩ := rs_eq_singleton_rng_of_rpk r S g (((((b0 ++ b1) ++ b2) ++ b3) ++ b4) ++ b5)
    (wireAt 81) (acceptAt 83) (p6.map .rng) ms p81 map_rng_kind wireAt81_head? hp81 hnk81 hmp_cref
  have hb6_eq : b6 = [.recv (wireAt 81), .rng c6, .accept (acceptAt 83)] := by
    dsimp [b6]; rw [hc6]; rfl
  have hmp_rpk6 : Symbolic.Swarm.CREF.MatchedPrefix SpecTop.compI0 r S g ms
      ((((((b0 ++ b1) ++ b2) ++ b3) ++ b4) ++ b5) ++ [.recv (wireAt 81), .rng c6, .accept (acceptAt 83)]) := by
    rwa [← hb6_eq]
  obtain ⟨ms₈₁, pre6, post6, b_6, a_6, kh_6, regIdxA_6, mh_6, pqIdx_6, spqrMsgIdx_6, shown_6,
      hms_eq, hmp₈₁, _, hpre6_inv, _, _, hm6⟩ :=
    BobDone.matchedPrefix_rpk_bobStart_only SpecTop.compI0 r S g
      (((((b0 ++ b1) ++ b2) ++ b3) ++ b4) ++ b5)
      (wireAt 81) c6 (acceptAt 83) ms p81 wireAt81_head? hp81 hnk81 hmp_rpk6
  obtain ⟨ms₇₈, δ₅, rfl, hmp₇₈, hfor₅⟩ :=
    matchedPrefix6_split hmp₈₁ (by intro e he; simp [b5] at he; subst he; exact Or.inr rfl)
      (matchedPrefix6_prefix_reachable hmp₈₁)
  obtain ⟨ms₄₃, δ₄, rfl, hmp₄₃, hfor₄⟩ :=
    matchedPrefix6_split hmp₇₈ (by intro e he; simp [b4] at he; subst he; exact Or.inl rfl)
      (matchedPrefix6_prefix_reachable hmp₇₈)
  obtain ⟨c3, hc3⟩ := rs_eq_singleton_rng_of_rpk r S g ((b0 ++ b1) ++ b2)
    (wireAt 40) (acceptAt 42) (p3.map .rng) ms₄₃ p40 map_rng_kind wireAt40_head? hp40 hnk40 hmp₄₃
  have hb3_eq : b3 = [.recv (wireAt 40), .rng c3, .accept (acceptAt 42)] := by
    dsimp [b3]; rw [hc3]; rfl
  have hmp₄₃_rpk : Symbolic.Swarm.CREF.MatchedPrefix SpecTop.compI0 r S g ms₄₃
      (((b0 ++ b1) ++ b2) ++ [.recv (wireAt 40), .rng c3, .accept (acceptAt 42)]) := by
    rwa [← hb3_eq]
  obtain ⟨ms₄₀, pre3, post3, b_3, a_3, kh_3, regA_3, mh_3, pqIdx_3, spqrMsgIdx_3, shown_3,
      hms₄₃_eq, hmp₄₀, _, hpre3_inv, hpost3_inv, _, hm3⟩ :=
    BobDone.matchedPrefix_rpk_bobStart_only SpecTop.compI0 r S g ((b0 ++ b1) ++ b2)
      (wireAt 40) c3 (acceptAt 42) ms₄₃ p40 wireAt40_head? hp40 hnk40 hmp₄₃_rpk
  have h40_ad : ∃ ek₀, AllAliceDone (· = ek₀) (runTraceMoves r ms₄₀) := by
    obtain ⟨ms₃₈, δ₂, rfl, hmp₃₈, hfor₂⟩ :=
      matchedPrefix6_split hmp₄₀ (by intro e he; simp [b2] at he; subst he; exact Or.inr rfl)
        (matchedPrefix6_prefix_reachable hmp₄₀)
    obtain ⟨ms₃₅, δ₁, rfl, hmp₃₅, hfor₁⟩ :=
      matchedPrefix6_split hmp₃₈ (by intro e he; simp [b1] at he; subst he; exact Or.inr rfl)
        (matchedPrefix6_prefix_reachable hmp₃₈)
    have hNe := CompSetupSecrecy.alice_ne_bob_of_modelRun hmp₃₅.2.1
    have hmp₃₅' : Symbolic.Swarm.CREF.MatchedPrefix SpecTop.compI0 r S g ms₃₅ ([] ++ b0) := hmp₃₅
    obtain ⟨ms₀, δ₀, rfl, hmp₀, hfor₀⟩ :=
      matchedPrefix6_split hmp₃₅' (by intro e he; simp [b0] at he; subst he; exact Or.inl rfl)
        (matchedPrefix6_prefix_reachable hmp₃₅')
    have hnil : AllAliceDone (fun _ => False) (runTraceMoves r ms₀) := by
      rw [xpl_runTrace_eq]
      exact allAliceDone_of_movesFrom_invisible
        (BobDone.movesFrom_invisibleNoEffect_of_matchedPrefix_nil hmp₀)
        (allAliceDone_setupTrace hNe _)
    obtain ⟨ek₀, h₃₅⟩ := allAliceDone_xplBlock_ini ⟨hmp₀, hmp₃₅.2.1, hfor₀⟩ map_rng_kind hnil
    exact ⟨ek₀, allAliceDone_xplBlock_send ⟨hmp₃₈, hmp₄₀.2.1, hfor₂⟩ map_rng_snoc_send_kind
      (allAliceDone_xplBlock_send ⟨hmp₃₅, hmp₃₈.2.1, hfor₁⟩ map_rng_snoc_send_kind h₃₅)⟩
  obtain ⟨ek₀, h40_ad⟩ := h40_ad
  have htr3_eq : (runMoves pre3 (runTraceMoves r ms₄₀)).1 = runTraceMoves r (ms₄₀ ++ pre3) :=
    (Symbolic.Swarm.CREF.runTrace_append r ms₄₀ pre3).symm
  have htr3_pre : AllAliceDone (· = ek₀) (runTraceMoves r (ms₄₀ ++ pre3)) :=
    htr3_eq ▸ allAliceDone_of_movesFrom_invisible hpre3_inv h40_ad
  have hno_leak43 : ∀ e ∈ (((b0 ++ b1) ++ b2) ++ b3), eventKind e ≠ .leak := by
    intro e he
    exact hno_leak' e (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ he)))
  have hnb43 : CompSetupSecrecy.NoBrk r ms₄₃ := by
    refine CompSetupSecrecy.noBrk_of_le ?_ hnb
    rw [hms_eq, List.append_assoc, List.append_assoc, Symbolic.Swarm.CREF.runTrace_append r ms₄₃]
    exact Symbolic.Swarm.CREF.runMoves_le _ _
  have ⟨hNe3, hns3, hreach3, hnb3, hnoleak3⟩ :=
    prefix_clean_hyps_of_matchedPrefix
      (ms₁ := ms₄₀ ++ pre3)
      (ms₂ := Move.bobStart b_3 a_3 kh_3 regA_3 mh_3 pqIdx_3 spqrMsgIdx_3 shown_3 :: post3)
      hmp₄₃ hnb43 hno_leak43 (by simp [hms₄₃_eq, List.append_assoc])
  rw [htr3_eq] at hm3
  obtain ⟨w3, hbk3, _⟩ := bobStartOk_of_rpk_forall2 hp40 hm3
  obtain ⟨_, _, a', b', spk', opk', _, _, _, hAlice3, _⟩ :=
    w3.aliceMatch_and_ek_dhPk_of_no_leak hNe3 hns3 hreach3 hnoleak3 hnb3
  have hek₀ : w3.ek = ek₀ := htr3_pre _ _ _ _ _ _ _ _ _ _ _ hAlice3
  have htr3_ek1 : AllAliceDone (fun ek => ecKey (gamma SpecTop.compI0 S g ek) = ecKey ek1PubKey)
      (runMoves pre3 (runTraceMoves r ms₄₀)).1 :=
    fun a1 b1 ikA1 ikB1 spk1 pqpk1 opk1 e1 ct1 keys1 j1 hev1 => by
      dsimp only
      rw [allAliceDone_of_movesFrom_invisible hpre3_inv h40_ad a1 b1 ikA1 ikB1 spk1 pqpk1 opk1 e1 ct1 keys1 j1 hev1,
        ← hek₀, hbk3, hp40_bk]
  have had43 : AllAliceDone (fun ek => ecKey (gamma SpecTop.compI0 S g ek) = ecKey ek1PubKey)
      (runTraceMoves r ms₄₃) := by
    rw [hms₄₃_eq, Symbolic.Swarm.CREF.runTrace_append, Symbolic.Swarm.CREF.b5_runMoves_append_fst,
      runMoves_cons_fst]
    exact allAliceDone_of_movesFrom_invisible hpost3_inv
      (allAliceDone_bobStart b_3 a_3 kh_3 regA_3 mh_3 pqIdx_3 spqrMsgIdx_3 shown_3 htr3_ek1)
  have hSent₈₁ : AllSentNet (runTraceMoves r ms₄₃).length
      (fun raw => gamma SpecTop.compI0 S g raw = p80.message)
      (runTraceMoves r ((ms₄₃ ++ δ₄) ++ δ₅)) :=
    allSentNet_xplBlock_send_rs ⟨hmp₇₈, hmp₈₁.2.1, hfor₅⟩ map_rng_kind
      sendAt80_head_ne_whisper sendAt80_length_lt hp80
      (allSentNet_xplBlock_ini ⟨hmp₄₃, hmp₇₈.2.1, hfor₄⟩ map_rng_kind
        (allSentNet_self _ (runTraceMoves r ms₄₃)))
      (fun _ h => h)
  have hSent_pre6 := allSentNet_runMoves_of_movesFrom hpre6_inv hSent₈₁
  have htr6_eq : (runMoves pre6 (runTraceMoves r ((ms₄₃ ++ δ₄) ++ δ₅))).1 =
      runTraceMoves r (((ms₄₃ ++ δ₄) ++ δ₅) ++ pre6) :=
    (Symbolic.Swarm.CREF.runTrace_append r ((ms₄₃ ++ δ₄) ++ δ₅) pre6).symm
  rw [htr6_eq] at hm6 hSent_pre6
  obtain ⟨w6, hbk81, hraw81⟩ := bobStartOk_of_rpk_forall2 hp81 hm6
  have ⟨hNe6, hns6, hreach6, hnb6, hnoleak6⟩ :=
    prefix_clean_hyps_of_matchedPrefix
      (ms₁ := ((ms₄₃ ++ δ₄) ++ δ₅) ++ pre6)
      (ms₂ := Move.bobStart b_6 a_6 kh_6 regIdxA_6 mh_6 pqIdx_6 spqrMsgIdx_6 shown_6 :: post6)
      hmp_cref hnb hno_leak' (by simp [hms_eq, List.append_assoc])
  obtain ⟨t, me, peer, dhs, ns, m_pt, _, hsent_ev, hnet_raw, hAlice⟩ :=
    MacGuardGen.BobStartOk.sentMac_of_no_leak hNe6 hns6 hreach6 hnb6 hnoleak6 w6
  by_cases hk : (runTraceMoves r ms₄₃).length ≤ t + 3
  · have hget_sent : (runTraceMoves r (((ms₄₃ ++ δ₄) ++ δ₅) ++ pre6)).getEventAt
        DY.Libsignal.TripleRatchet.TREvent (t + 3) =
        some (DY.Libsignal.TripleRatchet.TREvent.Sent me peer dhs ns m_pt) := by
      rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.getEventAt_eq_at?,
        (Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.eventLoggedAt_iff_at? _ _ _ _).mp hsent_ev]
    obtain ⟨raw', _, hnet_raw', hp80_raw'⟩ := hSent_pre6 (t + 3) _ hk hget_sent rfl
    have hraw_eq : w6.raw = raw' := by
      unfold Symbolic.Swarm.COMPOSED.CompInv.NetAt at hnet_raw hnet_raw'
      rw [show t + 3 + 3 = t + 6 by omega, hnet_raw] at hnet_raw'
      cases hnet_raw'; rfl
    have hmsg_eq : p81.message = p80.message := by rw [← hraw81, hraw_eq, hp80_raw']
    exact wireAt81_inner_ne_sendAt80_inner hp81 hp80
      (congrArg (fun x => x.take (x.length - 8)) hmsg_eq)
  · obtain ⟨j, a'', b'', spk'', opk'', hjt, hAlice_ev⟩ := hAlice
    have hj₄₃ : j < (runTraceMoves r ms₄₃).length := by omega
    have hle₄₃ : runTraceMoves r ms₄₃ ≤ runTraceMoves r (((ms₄₃ ++ δ₄) ++ δ₅) ++ pre6) := by
      rw [List.append_assoc, List.append_assoc, Symbolic.Swarm.CREF.runTrace_append]
      exact Symbolic.Swarm.CREF.runMoves_le _ _
    have hAlice₄₃_ev : (runTraceMoves r ms₄₃).EventLoggedAt
        (DY.Libsignal.PQXDH.PQXDHEvent.AliceDone a'' b'' w6.ikAPk
          (DY.DiffieHellman.dhPk w6.ikB) spk'' (DY.PQKem.kemPk w6.pqsk) opk'' w6.ek w6.ct w6.keys) j := by
      rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.eventLoggedAt_iff_at?] at hAlice_ev ⊢
      rwa [← CompSetupSecrecy.at?_eq_of_le_of_lt hle₄₃ hj₄₃]
    have hek1 := had43 a'' b'' _ _ spk'' _ opk'' w6.ek w6.ct w6.keys j hAlice₄₃_ev
    exact ek1_ne_ek2 (hek1.symm.trans (hbk81.trans hp81_bk))


end Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CliBridge

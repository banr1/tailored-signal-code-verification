/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.Top
public import Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct
public import Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct
public import Symbolic.BugInjection.Proofs.Common443.CompSmallSubgroupTrace
public import Symbolic.BugInjection.Proofs.Fixtures.Cheval26SmallSubgroupTorsionComp
public import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC Symbolic.BugInjection.Proofs.Common443 Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitComp
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse (getEventAt_eq_at? eventLoggedAt_iff_at?)
attribute [local irreducible] Symbolic.BugInjection.hexBytes
theorem mem_sessionBaseKeys_ek_dhPk_of_no_leak {r : Records} {ms : List Move} {si : Nat} {ek : DY.Bytes} (hNe : r.alice ≠ r.bob) (hns : ∀ m ∈ ms, m.isSetup = false) (hreach : (runTraceMoves r ms).Reachable reachability) (hnb : CompSetupSecrecy.NoBrk r ms) (hnoleak : ∀ v ∈ runVis r ms, v.kind ≠ .leak) (hek : ek ∈ sessionBaseKeys (runTraceMoves r ms) si) : ∃ t, ek = DY.DiffieHellman.dhPk (randTerm t 32) := by
  unfold sessionBaseKeys DY.ExecTrace.getLocalStateAt
    DY.Libsignal.Composed.Refinement.sessionHandshakeEvents at hek
  cases hst : ((runTraceMoves r ms).at? si :
      Option (DY.PersistentGlobalState.State.ExecEntryT
        (DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState))) with
  | none => simp [hst] at hek
  | some e =>
    simp only [hst, Option.map_some, List.mem_filterMap] at hek
    obtain ⟨ev, ⟨i, _, hi⟩, hev_ek⟩ := hek
    rcases hcev : (runTraceMoves r ms).getEventAt CEvent i with _ | ⟨s, d⟩ <;> rw [hcev] at hi
    · cases hi
    · dsimp only at hi
      split at hi
      · rcases hat : ((runTraceMoves r ms).at? d :
            Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) with _ | ev_ent
        · rw [getEventAt_eq_at?, hat] at hi; cases hi
        · rcases ev_ent with ⟨ev'⟩
          have hget : (runTraceMoves r ms).getEventAt DY.Libsignal.PQXDH.PQXDHEvent d = some ev' := (by rw [getEventAt_eq_at?, hat]); rw [hget] at hi
          injection hi with hev_eq; subst hev_eq
          cases ev' <;> simp only [Option.some.injEq, reduceCtorEq] at hev_ek
          subst hev_ek; obtain ⟨_, t, _, _, _, _, _, _, _, hek_eq⟩ := CompSetupSecrecy.bobDone_ek_dhPk_of_no_leak hNe hns hreach hnoleak hnb ((eventLoggedAt_iff_at? _ _ _ _).mpr hat); exact ⟨t, hek_eq⟩
      · cases hi
open Symbolic.Swarm.CREF in
private theorem decVis_ek_dhPk_of_no_leak {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {tr' : ExecTrace} {si mi : Nat} {wrapped : Bool} {wire : HwBytes} {v₀ : VisEntry} {vs : List VisEntry} {q} (hNe : r.alice ≠ r.bob) (hns : ∀ m' ∈ ms, m'.isSetup = false) (hreach : (runTraceMoves r ms).Reachable reachability) (hnb : CompSetupSecrecy.NoBrk r ms) (hnoleak : ∀ v ∈ runVis r ms, v.kind ≠ .leak) (hdec : decVis (runTraceMoves r ms) tr' si mi wrapped = v₀ :: vs) (hv₀ : EventMatchesEntry i r S g (.recv wire) v₀) (hhead_ne : wire.head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag) (hq : parsePreKeyWire wire = some q) : ∃ t, ecKey (gamma i S g (DY.DiffieHellman.dhPk (randTerm t 32))) = q.baseKey.take 33 := by
  let tr := runTraceMoves r ms; have hvk₀ : v₀.kind = .recv := hv₀.1.symm; have hv₀_in : v₀ ∈ decVis tr tr' si mi wrapped := (by rw [hdec]; exact List.mem_cons_self ..)
  rcases hmsg : tr.getMessageSentAt mi with _ | raw
  · simp only [decVis, hmsg, Option.map_none, Option.toList_none, List.nil_append, List.mem_append, List.mem_map] at hv₀_in
    rcases hv₀_in with ⟨_, _, rfl⟩ | hacc_mem
    · cases hvk₀
    · rcases hp : receivedPlaintext tr tr' with _ | m_pt <;>
        simp [hp] at hacc_mem
      subst hacc_mem; cases hvk₀
  · unfold decVis at hdec; rw [hmsg] at hdec; simp only [Option.map_some, Option.toList_some, List.cons_append, List.cons.injEq] at hdec; obtain ⟨rfl, _⟩ := hdec
    cases wrapped with
    | false =>
      obtain ⟨_, _, hw_eq⟩ := hv₀.2; change wire = _ at hw_eq; rw [hw_eq] at hhead_ne; exact absurd rfl hhead_ne
    | true =>
      obtain ⟨_, p, _, hp, ⟨ek, hek_mem, hek_ec⟩, _⟩ := hv₀.2; change parsePreKeyWire wire = some p at hp; rw [hq] at hp
      injection hp with hp_eq
      subst hp_eq; obtain ⟨t, rfl⟩ := mem_sessionBaseKeys_ek_dhPk_of_no_leak hNe hns hreach hnb hnoleak hek_mem; exact ⟨t, hek_ec.symm⟩
open Symbolic.Swarm.CREF in
theorem recv_accept_move_ek_dhPk_of_no_leak {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {m : Move} {wire : HwBytes} {rest : List MachineEvent} {q} (hNe : r.alice ≠ r.bob) (hns : ∀ m' ∈ ms, m'.isSetup = false) (hreach : (runTraceMoves r ms).Reachable reachability) (hnb : CompSetupSecrecy.NoBrk r ms) (hnoleak : ∀ v ∈ runVis r ms, v.kind ≠ .leak) (hm : List.Forall₂ (EventMatchesEntry i r S g) (.recv wire :: rest) (m.vis (runTraceMoves r ms))) (hacc : ∃ e ∈ rest, eventKind e = .accept) (hnoleak_m : ∀ v ∈ m.vis (runTraceMoves r ms), v.kind ≠ .leak) (hhead_ne : wire.head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag) (hq : parsePreKeyWire wire = some q) : ∃ t, ecKey (gamma i S g (DY.DiffieHellman.dhPk (randTerm t 32))) = q.baseKey.take 33 := by
  let tr := runTraceMoves r ms; obtain ⟨v₀, vs, hv₀, hrest_m, hvis⟩ := xpl_forall₂_cons_left hm; obtain ⟨e_acc, he_acc, he_kind⟩ := hacc; obtain ⟨v_acc, hv_acc_vs, hev_acc⟩ := xpl_forall₂_mem_left hrest_m e_acc he_acc; have hv_acc : v_acc ∈ m.vis tr := (by rw [hvis]; exact List.mem_cons_of_mem _ hv_acc_vs); have hv_acc_kind : v_acc.kind = .accept := (xpl_kind_of_matches hev_acc).trans he_kind; have hexp : exposures tr (m.next tr) = [] := (by apply List.eq_nil_iff_forall_not_mem.mpr; intro v hv; have hmem : v ∈ m.vis tr := (by rw [xpl_vis_eq]; exact List.mem_append_right _ hv); exact hnoleak_m v hmem (xpl_exposures_kind hv)); have hown_acc : v_acc ∈ xpl_ownVis m tr := (by have h := hv_acc; rw [xpl_vis_eq, hexp, List.append_nil] at h; exact h); have hown_vis : xpl_ownVis m tr = v₀ :: vs := (by rw [← List.append_nil (xpl_ownVis m tr), ← hexp, ← xpl_vis_eq, hvis])
  cases m with
  | bobStart b a kh regA mh pqIdx spqrMsgIdx shown =>
    obtain ⟨w⟩ := CompSetupSecrecy.bobStart_accept_ok hv_acc hv_acc_kind; have hpm := w.preKeyRecvMatches_of_vis hvis (hvis ▸ hnoleak_m) hv₀; obtain ⟨_, t, _, _, _, _, _, _, _, _, hek_eq⟩ := w.aliceMatch_and_ek_dhPk_of_no_leak hNe hns hreach hnoleak hnb; obtain ⟨p, hp, hbase, _⟩ := hpm; rw [hq] at hp
    injection hp with hp_eq
    subst hp_eq; refine ⟨t, ?_⟩; rw [← hek_eq]; exact hbase.symm
  | decrypt me si mi pq sp wrapped =>
    exact decVis_ek_dhPk_of_no_leak hNe hns hreach hnb hnoleak hown_vis hv₀ hhead_ne hq
  | decryptSkipped me si mi k pq sp wrapped =>
    exact decVis_ek_dhPk_of_no_leak hNe hns hreach hnb hnoleak hown_vis hv₀ hhead_ne hq
  | aliceStart =>
    rcases xpl_aliceVis_kind (List.mem_of_mem_take hown_acc) with h | h <;> (rw [hv_acc_kind] at h; cases h)
  | reject =>
    simp only [xpl_ownVis, List.mem_cons, List.mem_map] at hown_acc
    rcases hown_acc with rfl | ⟨_, _, rfl⟩ <;> cases hv_acc_kind
  | encrypt =>
    rcases xpl_encVis_kind hown_acc with h | h | ⟨_, h⟩ <;> (rw [hv_acc_kind] at h; cases h)
  | encryptAbort =>
    rcases xpl_encVis_kind hown_acc with h | h | ⟨_, h⟩ <;> (rw [hv_acc_kind] at h; cases h)
  | encryptFail =>
    rcases xpl_encVis_kind hown_acc with h | h | ⟨_, h⟩ <;> (rw [hv_acc_kind] at h; cases h)
  | _ => simp [xpl_ownVis] at hown_acc
open Symbolic.Swarm.CREF in
theorem runVis_append (r : Records) (ms₁ ms₂ : List Move) : runVis r (ms₁ ++ ms₂) = runVis r ms₁ ++ (runMoves ms₂ (runTraceMoves r ms₁)).2 := by change (runMoves (r.setupMove :: (ms₁ ++ ms₂)) Trace.nil).2 = _; rw [← List.cons_append, CompPrefixInvStruct.runMoves_append_snd]; rfl
open Symbolic.Swarm.CREF in
theorem not_matchedPrefix_of_recv_accept_tail {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {τ₁ : List MachineEvent} {wire : HwBytes} {rest : List MachineEvent} (hi : i = Interp0.compI0) (hmp : Symbolic.Swarm.CREF.MatchedPrefix i r S g ms (τ₁ ++ (.recv wire :: rest))) (hnb : CompSetupSecrecy.NoBrk r ms) (hnoleak : ∀ e ∈ τ₁ ++ (.recv wire :: rest), eventKind e ≠ .leak) (hrest_ne : ∀ e ∈ rest, eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak) (hacc : ∃ e ∈ rest, eventKind e = .accept) (hhead_ne : wire.head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag) (hq_some : (parsePreKeyWire wire).isSome = true) (hbase_ne : ∀ o : Option (Fin 12), (parsePreKeyWire wire).map (fun p => p.baseKey.take 33) ≠ some (ecKey (Interp0.compPubOfOpt o))) : False := by
  let blk : List MachineEvent := .recv wire :: rest; have hhead : ∀ e ∈ blk.head?, eventKind e = .recv ∨ eventKind e = .pt := (by intro e he; simp [blk] at he; subst he; exact Or.inl rfl); obtain ⟨ms₁, δ, hms, hmp₁, hfor⟩ := matchedPrefix6_split hmp hhead (CompPrefixInvStruct.matchedPrefix6_prefix_reachable hmp); have hB : XplBlock6 i r S g ms₁ δ τ₁ blk := ⟨hmp₁, hms ▸ hmp.2.1, hfor⟩
  obtain ⟨pre, m, post, rfl, _, ⟨_, _, hm⟩, _⟩ :=
    xpl6_oneMove hB hhead (by simp [blk]) hrest_ne
  let ms_pre := ms₁ ++ pre; have hms_eq : ms = ms_pre ++ (m :: post) := (by simp [hms, ms_pre, List.append_assoc]); have htr_eq : (runMoves pre (runTraceMoves r ms₁)).1 = runTraceMoves r ms_pre := (CompPrefixInvStruct.runTrace_append r ms₁ pre).symm; rw [htr_eq] at hm; have hNe : r.alice ≠ r.bob := CompSetupSecrecy.alice_ne_bob_of_modelRun hmp.2.1; have hns : ∀ m' ∈ ms_pre, m'.isSetup = false := (by intro m' hm'; exact hmp.2.1.2.1 m' (by rw [hms_eq]; exact List.mem_append_left _ hm')); have hreach : (runTraceMoves r ms_pre).Reachable reachability := CompPrefixInvStruct.matchedPrefix6_prefix_reachable hmp ms_pre (m :: post) hms_eq; have hnb_pre : CompSetupSecrecy.NoBrk r ms_pre := CompSetupSecrecy.noBrk_of_le (by rw [hms_eq, CompPrefixInvStruct.runTrace_append r ms_pre (m :: post)]; exact Symbolic.Swarm.CREF.runMoves_le _ _) hnb; have hnoleak_all : ∀ v ∈ runVis r ms, v.kind ≠ .leak := CompSetupSecrecy.crit_noleak_of_forall2 hnoleak hmp.2.2
  have hvis_split : runVis r ms = runVis r ms_pre ++ (m.vis (runTraceMoves r ms_pre) ++
        (runMoves post (m.next (runTraceMoves r ms_pre))).2) := by
    rw [hms_eq, runVis_append, runMoves_cons_snd]
  have hnoleak_pre : ∀ v ∈ runVis r ms_pre, v.kind ≠ .leak := (by intro v hv; exact hnoleak_all v (by rw [hvis_split]; exact List.mem_append_left _ hv))
  have hnoleak_m : ∀ v ∈ m.vis (runTraceMoves r ms_pre), v.kind ≠ .leak := by
    intro v hv
    exact hnoleak_all v (by
      rw [hvis_split]
      exact List.mem_append_right _ (List.mem_append_left _ hv))
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hq_some; obtain ⟨t, hec⟩ := recv_accept_move_ek_dhPk_of_no_leak hNe hns hreach hnb_pre hnoleak_pre hm hacc hnoleak_m hhead_ne hq; subst hi; rw [CompFreshDistinct.gamma_dhPk_compI0] at hec
  have hmap : (parsePreKeyWire wire).map (fun p => p.baseKey.take 33) =
      some (ecKey (Interp0.compPubOfOpt
        (Interp0.compSecretIdx (clamp (gamma Interp0.compI0 S g (randTerm t 32)))))) := by
    rw [hq, Option.map_some, ← hec]; rfl
  exact hbase_ne _ hmap
private theorem highBitWireFast_baseKey_ne_compPubOfOpt (o : Option (Fin 12)) : (parsePreKeyWire CompSmallSubgroupTrace.highBitWireFast).map (fun p => p.baseKey.take 33) ≠ some (ecKey (Interp0.compPubOfOpt o)) := by
  cases o with
  | none => decide +kernel
  | some k => revert k; decide +kernel
theorem highBitWireBytes_baseKey_ne_compPubOfOpt (o : Option (Fin 12)) : (parsePreKeyWire CompSmallSubgroupTrace.highBitWireBytes).map (fun p => p.baseKey.take 33) ≠ some (ecKey (Interp0.compPubOfOpt o)) := by rw [CompSmallSubgroupTrace.highBitWireBytes_eq]; exact highBitWireFast_baseKey_ne_compPubOfOpt o
private theorem highBitWireFast_props : CompSmallSubgroupTrace.highBitWireFast.head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag ∧ (parsePreKeyWire CompSmallSubgroupTrace.highBitWireFast).isSome = true := by decide +kernel
theorem highBitWireBytes_props : CompSmallSubgroupTrace.highBitWireBytes.head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag ∧ (parsePreKeyWire CompSmallSubgroupTrace.highBitWireBytes).isSome = true := by rw [CompSmallSubgroupTrace.highBitWireBytes_eq]; exact highBitWireFast_props
private theorem torsionWireFast_baseKey_ne_compPubOfOpt (o : Option (Fin 12)) : (parsePreKeyWire CompSmallSubgroupTrace.torsionWireFast).map (fun p => p.baseKey.take 33) ≠ some (ecKey (Interp0.compPubOfOpt o)) := by
  cases o with
  | none => decide +kernel
  | some k => revert k; decide +kernel
theorem torsionWireBytes_baseKey_ne_compPubOfOpt (o : Option (Fin 12)) : (parsePreKeyWire CompSmallSubgroupTrace.torsionWireBytes).map (fun p => p.baseKey.take 33) ≠ some (ecKey (Interp0.compPubOfOpt o)) := by rw [CompSmallSubgroupTrace.torsionWireBytes_eq]; exact torsionWireFast_baseKey_ne_compPubOfOpt o
private theorem torsionWireFast_props : CompSmallSubgroupTrace.torsionWireFast.head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag ∧ (parsePreKeyWire CompSmallSubgroupTrace.torsionWireFast).isSome = true := by decide +kernel
theorem torsionWireBytes_props : CompSmallSubgroupTrace.torsionWireBytes.head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag ∧ (parsePreKeyWire CompSmallSubgroupTrace.torsionWireBytes).isSome = true := by rw [CompSmallSubgroupTrace.torsionWireBytes_eq]; exact torsionWireFast_props
private theorem recv_eventBytes_of_kind {e : MachineEvent} (h : eventKind e = .recv) : MachineEvent.recv (CompSmallSubgroupTrace.eventBytes e) = e := by cases e <;> first | rfl | cases h
private theorem cons_headD_tail_of_length_pos {α : Type} {l : List α} (d : α) (h : 0 < l.length) : l = l.headD d :: l.tail := by
  cases l with
  | nil => simp at h
  | cons x xs => rfl
theorem highBitComp_trace_eq_split : Witnesses.Cheval26SmallSubgroupHighBitComp.trace = (CompSmallSubgroupTrace.call0Trace ++ CompSmallSubgroupTrace.call1Trace) ++ (.recv CompSmallSubgroupTrace.highBitWireBytes :: CompSmallSubgroupTrace.highBitCall2Trace.tail) := CompSmallSubgroupTrace.highBitComp_trace_decomp.trans
    (congrArg ((CompSmallSubgroupTrace.call0Trace ++ CompSmallSubgroupTrace.call1Trace) ++ ·)
      ((cons_headD_tail_of_length_pos (.recv []) (by decide)).trans
        (congrFun (congrArg List.cons (recv_eventBytes_of_kind (by decide)).symm) _)))
theorem torsionComp_trace_eq_split : Witnesses.Cheval26SmallSubgroupTorsionComp.trace = (CompSmallSubgroupTrace.call0Trace ++ CompSmallSubgroupTrace.call1Trace) ++ (.recv CompSmallSubgroupTrace.torsionWireBytes :: CompSmallSubgroupTrace.torsionCall2Trace.tail) := CompSmallSubgroupTrace.torsionComp_trace_decomp.trans
    (congrArg ((CompSmallSubgroupTrace.call0Trace ++ CompSmallSubgroupTrace.call1Trace) ++ ·)
      ((cons_headD_tail_of_length_pos (.recv []) (by decide)).trans
        (congrFun (congrArg List.cons (recv_eventBytes_of_kind (by decide)).symm) _)))
theorem not_matchedPrefix_highBitComp_cref {r : Records} {S : Sem} {g : Ghost} {ms : List Move} (hnb : CompSetupSecrecy.NoBrk r ms) : ¬ Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms Witnesses.Cheval26SmallSubgroupHighBitComp.trace := by
  intro hmp; rw [highBitComp_trace_eq_split] at hmp
  exact not_matchedPrefix_of_recv_accept_tail rfl hmp hnb
    (by rw [← highBitComp_trace_eq_split]; decide)
    (by decide) (by decide)
    highBitWireBytes_props.1 highBitWireBytes_props.2
    highBitWireBytes_baseKey_ne_compPubOfOpt
theorem not_matchedPrefix_torsionComp_cref {r : Records} {S : Sem} {g : Ghost} {ms : List Move} (hnb : CompSetupSecrecy.NoBrk r ms) : ¬ Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms Witnesses.Cheval26SmallSubgroupTorsionComp.trace := by
  intro hmp; rw [torsionComp_trace_eq_split] at hmp
  exact not_matchedPrefix_of_recv_accept_tail rfl hmp hnb
    (by rw [← torsionComp_trace_eq_split]; decide)
    (by decide) (by decide)
    torsionWireBytes_props.1 torsionWireBytes_props.2
    torsionWireBytes_baseKey_ne_compPubOfOpt
theorem not_matchedPrefix_highBitComp {r : Records} {S : Sem} {who₀ : List Participant} {g : Ghost} {ms : List Move} (hnb : CompSetupSecrecy.NoBrk r ms) : ¬ MatchedPrefix compI0 r S who₀ g ms Witnesses.Cheval26SmallSubgroupHighBitComp.trace :=
  fun hmp => not_matchedPrefix_highBitComp_cref hnb (Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp)
theorem not_matchedPrefix_torsionComp {r : Records} {S : Sem} {who₀ : List Participant} {g : Ghost} {ms : List Move} (hnb : CompSetupSecrecy.NoBrk r ms) : ¬ MatchedPrefix compI0 r S who₀ g ms Witnesses.Cheval26SmallSubgroupTorsionComp.trace :=
  fun hmp => not_matchedPrefix_torsionComp_cref hnb (Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp)
theorem noFullMatchHB : NoFullMatchHB :=
  fun _ _ _ _ _ hnb hmp => not_matchedPrefix_highBitComp hnb hmp
theorem noFullMatchTC : ∀ (r : Records) (S : Sem) (g : Ghost) (ms : List Move), compFitsPinned Witnesses.Cheval26SmallSubgroupTorsionComp.setup compI0 r → CompSetupSecrecy.NoBrk r ms → ¬ MatchedPrefix compI0 r S Witnesses.Cheval26SmallSubgroupTorsionComp.who g ms Witnesses.Cheval26SmallSubgroupTorsionComp.trace :=
  fun _ _ _ _ _ hnb hmp => not_matchedPrefix_torsionComp hnb hmp
end Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.Census443Memo
public import Symbolic.BugInjection.Proofs.Common443.CompRMemoKnown
public import Symbolic.BugInjection.Proofs.Common443.CompRNoBSC
public import Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvFresh

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompRVariantFree38
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.HwEvents Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.Census443Memo Symbolic.BugInjection.Proofs.Common443.CompExcuse Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvFresh Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvSwap Symbolic.BugInjection.Proofs.Common443.CompRMemoKnown Symbolic.BugInjection.Proofs.Common443.CompRNoBSC Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
export Symbolic.BugInjection.Proofs.Common443.Census443Memo ( NotVariant VariantFree nv_lit variantFree_lit variantFree_mem_bool variantFree_mem_slowNat variantFree_mem_slowString
)
theorem serialize_local_pqxdh_eq (ls : DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState) : (Comparse.serialize ls : DY.Bytes) = Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.slowString.serialize ls.participant ++ (Comparse.NonExtensibleMessageFormat.bool.serialize ls.state.kind.toBits.1 ++ Comparse.NonExtensibleMessageFormat.bool.serialize ls.state.kind.toBits.2)) ls.state.sk :=
  Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.serialize_local_pqxdh_eq_bridge ls
theorem mem_storedSecrets_iff {tr : ExecTrace} {u : DY.Bytes} : u ∈ storedSecrets tr ↔ ∃ j < tr.length, ∃ ls : DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState, (tr.at? j : Option PQXDHStEntry) = some ⟨ls⟩ ∧ u = Comparse.serialize ls := by
  unfold storedSecrets DY.ExecTrace.getLocalStateAt; simp only [Option.map_map, Function.comp_def, List.mem_filterMap, List.mem_range, Option.map_eq_some_iff]; constructor
  · rintro ⟨j, hj, ⟨ls⟩, hat, hser⟩; exact ⟨j, hj, ls, hat, hser.symm⟩
  · rintro ⟨j, hj, ls, hat, rfl⟩; exact ⟨j, hj, ⟨ls⟩, hat, rfl⟩
theorem exists_randTerm_of_kindOK {tr : ExecTrace} {me : Participant} {st : DY.Libsignal.PQXDH.PQXDHState} (h : CompInv.KindOK tr me st) : ∃ idx sz, st.sk = randTerm idx sz := by
  rcases st with ⟨kind, sk⟩
  cases kind <;> (dsimp only [CompInv.KindOK] at h; obtain ⟨t, hsk, _⟩ := h; exact ⟨t, _, hsk⟩)
section Prim
variable {i : ExternInterpretation} {S : Sem} {g : Ghost}
end Prim
theorem iniAliceStartState_ns_ne_u32Max (tr : ExecTrace) (b : Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) : (iniAliceStartState tr b o).ns ≠ DY.Libsignal.TripleRatchet.u32Max := by change (0 : UInt32) ≠ DY.Libsignal.TripleRatchet.u32Max; decide
theorem encrypt_next_split38_eq {r : Records} {tr₁ tr₂ : ExecTrace} {m₀ : Move} {mid : List Move} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} {cl : Nat} (wrap : Option (Nat × Nat)) (hm₀ : m₀.next tr₁ = iniAliceStartTr tr₁ r.alice r.bob o) (hmid : MovesFrom InvisibleNoEffect (m₀.next tr₁) mid) (htr₂ : tr₂ = (runMoves mid (m₀.next tr₁)).1) : (Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) wrap).next tr₂ = encNextTr tr₂ r.alice (tr₁.length + 8) (iniAliceStartState tr₁ r.bob o) cl (tr₂.length + 2) := by
  have hst : (tr₂.at? (tr₁.length + 8) : Option TRStEntry) =
      some (TRStE r.alice (iniAliceStartState tr₁ r.bob o)) := by
    rw [htr₂, at?_trSt_of_movesFrom_invisibleNoEffect hmid, hm₀]; exact trStateStoredAt_iniAliceStartTr tr₁ r.alice r.bob o
  exact encrypt_next_eq_encNextTr_of_ownSalt hst (iniAliceStartState_ns_ne_u32Max tr₁ r.bob o) rfl
theorem trStateStoredAt_encNextTr (tr₂ : ExecTrace) (me : Participant) (sIdx : Nat) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : ((encNextTr tr₂ me sIdx stA cl pq).at? (tr₂.length + 5) : Option TRStEntry) = some (TRStE me (encSt tr₂ stA cl)) := by
  unfold encNextTr encPreSaltTr; dsimp only; rw [CompPrefixInvAlice.at?_append_other_eq _ _ rfl]
  have hlen : (((((tr₂.append (RndE 32)).append (RndE cl)).append
      (NetE (DY.Spqr.spqrSend stA.spqr (randTerm (tr₂.length + 1) cl)).2.1)).append
      (TREvE (.Sent me stA.peer (DY.DiffieHellman.dhPk stA.dhs) stA.ns (randTerm tr₂.length 32)))).append
      (TREvE (.MessageKey (stA.sinfo me) .sender
        (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2 (encSalt tr₂ stA cl pq) stA.ns stA.rIdx sIdx))).length = tr₂.length + 5 := by
    simp only [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.length_append_entry_eq]
  exact Symbolic.Swarm.CREF.TR.at?_append_eq _ _ hlen.symm
theorem at?_trSt_encNextTr (tr₂ : ExecTrace) (me : Participant) (sIdx : Nat) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq j : Nat) : ((encNextTr tr₂ me sIdx stA cl pq).at? j : Option TRStEntry) = if j = tr₂.length + 5 then some (TRStE me (encSt tr₂ stA cl)) else (tr₂.at? j : Option TRStEntry) := by
  by_cases hj : j = tr₂.length + 5
  · subst hj; simp only [↓reduceIte]; exact trStateStoredAt_encNextTr tr₂ me sIdx stA cl pq
  · simp only [hj, ↓reduceIte]; unfold encNextTr encPreSaltTr; dsimp only; rw [CompPrefixInvAlice.at?_append_other_eq _ _ rfl]
    by_cases hlt : j < tr₂.length + 5
    · rw [CompTrace.at?_append_of_lt _ _ (by simp only [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.length_append_entry_eq]; omega), CompPrefixInvAlice.at?_append_other_eq _ _ rfl,
        CompPrefixInvAlice.at?_append_other_eq _ _ rfl, CompPrefixInvAlice.at?_append_other_eq _ _ rfl,
        CompPrefixInvAlice.at?_append_other_eq _ _ rfl, CompPrefixInvAlice.at?_append_other_eq _ _ rfl]
    · rw [Symbolic.Swarm.CREF.at?_ge_length _ (by simp only [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.length_append_entry_eq]; omega),
          Symbolic.Swarm.CREF.at?_ge_length tr₂ (by omega)]
theorem mem_storedStates_iff {r : Records} {tr : ExecTrace} {ls : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState} : ls ∈ storedStates r tr ↔ ∃ j, (setupTrace r).length ≤ j ∧ j < tr.length ∧ (tr.at? j : Option TRStEntry) = some ⟨ls⟩ := by
  unfold storedStates newIndices DY.ExecTrace.getLocalStateAt; simp only [List.mem_filterMap, List.mem_range'_1, Option.map_eq_some_iff]; constructor
  · rintro ⟨j, ⟨hge, hlt⟩, ⟨ls'⟩, hat, rfl⟩; exact ⟨j, hge, by omega, hat⟩
  · rintro ⟨j, hge, hlt, hat⟩; exact ⟨j, ⟨hge, by omega⟩, ⟨ls⟩, hat, rfl⟩
theorem storedStates_split38_cases {r : Records} {pre mid post : List Move} {hb : DY.Libsignal.PQXDH.BundleHandles} {shown cl : Nat} {wrap : Option (Nat × Nat)} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} (ho : o = iniAliceOut (runMoves pre (setupTrace r)).1 (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none) (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre) (hmid : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1) mid) (hpost : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) wrap).next (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1) post) (hm₀ : (Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1 = iniAliceStartTr (runMoves pre (setupTrace r)).1 r.alice r.bob o) {ls : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState} (hls : ls ∈ storedStates r (runTraceMoves r (pre ++ Move.aliceStart r.alice r.bob 4 6 hb shown :: mid ++ Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) wrap :: post))) : let tr₁ := (runMoves pre (setupTrace r)).1;
    let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let stA := iniAliceStartState tr₁ r.bob o;
    ls = ⟨r.alice, stA⟩ ∨ ls = ⟨r.alice, encSt tr₂ stA cl⟩ := by
  let tr₁ := (runMoves pre (setupTrace r)).1; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let stA := iniAliceStartState tr₁ r.bob o; let m₁ := Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) wrap;
  have henc : m₁.next tr₂ = encNextTr tr₂ r.alice (tr₁.length + 8) stA cl (tr₂.length + 2) := by subst ho; exact encrypt_next_split38_eq wrap hm₀ hmid rfl
  have htr :
      runTraceMoves r (pre ++ m₀ :: mid ++ m₁ :: post) =
        (runMoves post (m₁.next tr₂)).1 := by
    rw [xpl_runTrace_eq]; simp only [runMoves_append_fst, runMoves]; rfl
  rw [htr] at hls; obtain ⟨j, _, _, hat⟩ := mem_storedStates_iff.mp hls; rw [at?_trSt_of_movesFrom_invisibleNoEffect hpost j, henc, at?_trSt_encNextTr, at?_trSt_of_movesFrom_invisibleNoEffect hmid j, hm₀, at?_trSt_iniAliceStartTr_of_noTRState (noTRState_of_movesFrom_invisibleNoEffect (noTRState_setupTrace r) hpre)] at hat
  split_ifs at hat with hj₂ hj₁
  · cases hat; exact Or.inr rfl
  · cases hat; exact Or.inl rfl
theorem runMoves_snd_of_movesFrom_invisibleNoEffect {tr : ExecTrace} {δ : List Move} (hδ : MovesFrom InvisibleNoEffect tr δ) : (runMoves δ tr).2 = [] := by induction δ generalizing tr with | nil => rfl | cons _ _ ih => simp only [runMoves, hδ.1.1, ih hδ.2, List.append_nil]
theorem setupMove_vis_nil {r : Records} (hNe : r.alice ≠ r.bob) : r.setupMove.vis Trace.nil = [] := by
  unfold Move.vis; change [] ++ exposures Trace.nil (setupTrace r) = []
  rw [List.nil_append]
  refine Symbolic.Swarm.CREF.exposures_eq_nil fun j _ => ⟨?_, ?_⟩
  · unfold pqExposureAt
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.getEventAt_eq_at? DY.Libsignal.PQXDH.PQXDHEvent]
    rcases hev : ((setupTrace r).at? j : Option PQXDHEntry) with _ | ⟨⟨ev⟩⟩
    · rfl
    · have hlog : (setupTrace r).EventLoggedAt ev j :=
        (Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.eventLoggedAt_iff_at?
          DY.Libsignal.PQXDH.PQXDHEvent _ _ _).mpr hev
      rcases setupTrace_eventLoggedAt_cases hNe hlog with
        ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl
  · refine Symbolic.Swarm.CREF.trExposureAt_of_getEventAt_none ?_
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.getEventAt_eq_at? DY.Libsignal.TripleRatchet.TREvent]
    rcases hev : ((setupTrace r).at? j : Option CompTrace.TREntry) with _ | ⟨⟨ev⟩⟩
    · rfl
    · exfalso
      have hlog : (setupTrace r).EventLoggedAt ev j :=
        (Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.eventLoggedAt_iff_at?
          DY.Libsignal.TripleRatchet.TREvent _ _ _).mpr hev
      rw [Symbolic.Swarm.CREF.TR.setupTrace_eq r hNe] at hlog
      have hstep : ∀ {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} (e : E),
          (∀ ev' k, ¬ tr.EventLoggedAt (EventT := DY.Libsignal.TripleRatchet.TREvent) ev' k) →
          (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option CompTrace.TREntry) = none →
          ∀ ev' k, ¬ (tr.append e).EventLoggedAt (EventT := DY.Libsignal.TripleRatchet.TREvent) ev' k :=
        fun _ h hnone ev' k hk => h ev' k (CompTrace.eventLoggedAt_append_other hnone hk)
      have hnil : ∀ ev' k, ¬ (Trace.nil : ExecTrace).EventLoggedAt (EventT := DY.Libsignal.TripleRatchet.TREvent) ev' k :=
        fun _ _ hk => Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.not_eventLoggedAt_nil hk
      have h1 : ∀ ev' k, ¬ (Symbolic.Swarm.CREF.TR.setupTr1 r.alice).EventLoggedAt (EventT := DY.Libsignal.TripleRatchet.TREvent) ev' k := by
        unfold Symbolic.Swarm.CREF.TR.setupTr1
        exact hstep _ (hstep _ (hstep _ (hstep _ (hstep _ hnil rfl) rfl) rfl) rfl) rfl
      have h2 : ∀ ev' k, ¬ (Symbolic.Swarm.CREF.TR.setupTr2 r.alice r.bob).EventLoggedAt (EventT := DY.Libsignal.TripleRatchet.TREvent) ev' k := by
        unfold Symbolic.Swarm.CREF.TR.setupTr2
        exact hstep _ (hstep _ (hstep _ (hstep _ (hstep _ h1 rfl) rfl) rfl) rfl) rfl
      have h3 : ∀ ev' k, ¬ (Symbolic.Swarm.CREF.TR.setupTr3 r.alice r.bob).EventLoggedAt (EventT := DY.Libsignal.TripleRatchet.TREvent) ev' k := by
        unfold Symbolic.Swarm.CREF.TR.setupTr3
        exact hstep _ (hstep _ (hstep _ (hstep _ (hstep _ (hstep _ h2 rfl) rfl) rfl) rfl) rfl) rfl
      have h4 : ∀ ev' k, ¬ (Symbolic.Swarm.CREF.TR.setupTr4 r.alice r.bob).EventLoggedAt (EventT := DY.Libsignal.TripleRatchet.TREvent) ev' k := by
        unfold Symbolic.Swarm.CREF.TR.setupTr4
        exact hstep _ (hstep _ (hstep _ (hstep _ (hstep _ (hstep _ h3 rfl) rfl) rfl) rfl) rfl) rfl
      have h5 : ∀ ev' k, ¬ (Symbolic.Swarm.CREF.TR.setupTr5 r.alice r.bob).EventLoggedAt (EventT := DY.Libsignal.TripleRatchet.TREvent) ev' k := by
        unfold Symbolic.Swarm.CREF.TR.setupTr5
        exact hstep _ (hstep _ (hstep _ (hstep _ h4 rfl) rfl) rfl) rfl
      cases hw : r.withOpk <;> rw [hw] at hlog
      · exact h4 ev j hlog
      · exact h5 ev j hlog
theorem runVis_split38_eq {r : Records} (hNe : r.alice ≠ r.bob) {pre mid post : List Move} {hb : DY.Libsignal.PQXDH.BundleHandles} {shown cl : Nat} {wrap : Option (Nat × Nat)} (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre) (hmid : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1) mid) (hpost : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) wrap).next (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1) post) : let tr₁ := (runMoves pre (setupTrace r)).1;
    let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let m₁ := Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) wrap;
    runVis r (pre ++ m₀ :: mid ++ m₁ :: post) = m₀.vis tr₁ ++ m₁.vis tr₂ := by
  dsimp only; let tr₁ := (runMoves pre (setupTrace r)).1; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let m₁ := Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) wrap; have h1 : (runMoves pre (setupTrace r)).2 = [] := runMoves_snd_of_movesFrom_invisibleNoEffect hpre; have h2 : (runMoves mid (m₀.next tr₁)).2 = [] := runMoves_snd_of_movesFrom_invisibleNoEffect hmid; have h3 : (runMoves post (m₁.next tr₂)).2 = [] := runMoves_snd_of_movesFrom_invisibleNoEffect hpost; change r.setupMove.vis Trace.nil ++ (runMoves ((pre ++ m₀ :: mid) ++ m₁ :: post) (setupTrace r)).2 = m₀.vis tr₁ ++ m₁.vis tr₂; rw [setupMove_vis_nil hNe, List.nil_append, runMoves_append_snd, runMoves_append_fst, runMoves_append_snd, runMoves, runMoves]; dsimp only [tr₁, tr₂, m₀, m₁] at h1 h2 h3 ⊢; rw [h1, h2, h3, List.nil_append, List.append_nil, List.append_nil]
theorem aliceStart_vis_eq (tr₁ : ExecTrace) (a b : Participant) (spkIdx pqpkIdx : Nat) (hb : DY.Libsignal.PQXDH.BundleHandles) (shown : Nat) : (Move.aliceStart a b spkIdx pqpkIdx hb shown).vis tr₁ = (aliceVis tr₁ ((Move.aliceStart a b spkIdx pqpkIdx hb shown).next tr₁) hb).take shown := by
  have hexp := exposures_nil_of_not_leakKind (tr := tr₁) (m := Move.aliceStart a b spkIdx pqpkIdx hb shown) rfl (fun h => nomatch h)
  unfold Move.vis; dsimp only; rw [hexp, List.append_nil]
theorem encrypt_vis_eq (tr₂ : ExecTrace) (me : Participant) (sIdx cl pq : Nat) (wrap : Option (Nat × Nat)) : (Move.encrypt me sIdx cl pq wrap).vis tr₂ = encVis tr₂ ((Move.encrypt me sIdx cl pq wrap).next tr₂) wrap true := by
  have hexp := exposures_nil_of_not_leakKind (tr := tr₂) (m := Move.encrypt me sIdx cl pq wrap) rfl (fun h => nomatch h)
  unfold Move.vis; dsimp only; rw [hexp, List.append_nil]
theorem mem_encDraws_encNextTr {tr₂ : ExecTrace} {me : Participant} {sIdx : Nat} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {v : VisEntry} (hv : v ∈ encDraws (newRandoms tr₂ (encNextTr tr₂ me sIdx stA cl pq))) : v = ⟨.pt, [randTerm tr₂.length 32], .single, none⟩ ∨ v = rngEntry (randTerm (tr₂.length + 1) cl) := by
  rw [CompPrefixInvFresh.newRandoms_encNextTr] at hv
  by_cases hcl : (cl != 0) = true
  · simp only [encDraws, List.filter_cons, hcl, ↓reduceIte, List.filter_nil, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hv
    exact hv
  · have hcl' : (cl != 0) = false := Bool.eq_false_iff.mpr hcl
    simp only [encDraws, List.filter_cons, hcl', Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hv; exact Or.inl hv
theorem mem_encSend_encNextTr_none {tr₂ : ExecTrace} {me : Participant} {sIdx : Nat} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {v : VisEntry} (hv : v ∈ encSend tr₂ (encNextTr tr₂ me sIdx stA cl pq) none) : v = ⟨.send, [encOut tr₂ stA cl pq], .whisper, none⟩ := by unfold encSend at hv; rw [lastSent_encNextTr] at hv; exact List.mem_singleton.mp hv
theorem mem_encSend_encNextTr_some {tr₂ : ExecTrace} {me : Participant} {sIdx : Nat} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq e c : Nat} {v : VisEntry} (hv : v ∈ encSend tr₂ (encNextTr tr₂ me sIdx stA cl pq) (some (e, c))) : v = ⟨.send, received tr₂ [e, c] ++ [encOut tr₂ stA cl pq], .preKeySend, none⟩ := by unfold encSend at hv; rw [lastSent_encNextTr] at hv; exact List.mem_singleton.mp hv
theorem pt_terms_split38_mem {r : Records} (hNe : r.alice ≠ r.bob) {pre mid post : List Move} {hb : DY.Libsignal.PQXDH.BundleHandles} {shown cl : Nat} {wrap : Option (Nat × Nat)} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} (ho : o = iniAliceOut (runMoves pre (setupTrace r)).1 (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none) (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre) (hmid : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1) mid) (hpost : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) wrap).next (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1) post) (hm₀ : (Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1 = iniAliceStartTr (runMoves pre (setupTrace r)).1 r.alice r.bob o) {v : VisEntry} (hv : v ∈ runVis r (pre ++ Move.aliceStart r.alice r.bob 4 6 hb shown :: mid ++ Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) wrap :: post)) (hkind : v.kind = .pt) {u : DY.Bytes} (hu : u ∈ v.terms) : u = randTerm ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1).length 32 := by
  let tr₁ := (runMoves pre (setupTrace r)).1; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let stA := iniAliceStartState tr₁ r.bob o; let m₁ := Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) wrap;
  have henc : m₁.next tr₂ = encNextTr tr₂ r.alice (tr₁.length + 8) stA cl (tr₂.length + 2) := by subst ho; exact encrypt_next_split38_eq wrap hm₀ hmid rfl
  rw [runVis_split38_eq hNe hpre hmid hpost, aliceStart_vis_eq, encrypt_vis_eq, henc, List.mem_append] at hv
  rcases hv with hv₀ | hv₁
  · rcases xpl_aliceVis_kind (List.mem_of_mem_take hv₀) with hk | hk <;> (rw [hkind] at hk; cases hk)
  · unfold encVis at hv₁; rw [List.mem_append] at hv₁
    rcases hv₁ with hv_draws | hv_send
    · rcases mem_encDraws_encNextTr hv_draws with rfl | rfl
      · exact List.mem_singleton.mp hu
      · cases hkind
    · cases wrap with
      | none =>
        rw [mem_encSend_encNextTr_none hv_send] at hkind; cases hkind
      | some ec =>
        rcases ec with ⟨e, c⟩
        rw [mem_encSend_encNextTr_some hv_send] at hkind; cases hkind
theorem getMessageSentAt_of_netMsgAt {m : DY.Bytes} {idx : Nat} {tr : ExecTrace} (h : NetMsgAt m idx tr) : tr.getMessageSentAt idx = some m := CompPrefixInvAlice.getMessageSentAt_of_netMsgAt h
theorem send_terms_split38_mem {r : Records} (hNe : r.alice ≠ r.bob) {pre mid post : List Move} {hb : DY.Libsignal.PQXDH.BundleHandles} {shown cl : Nat} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} (ho : o = iniAliceOut (runMoves pre (setupTrace r)).1 (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none) (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre) (hmid : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1) mid) (hpost : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some ((runMoves pre (setupTrace r)).1.length + 3, (runMoves pre (setupTrace r)).1.length + 4))).next (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1) post) (hm₀ : (Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1 = iniAliceStartTr (runMoves pre (setupTrace r)).1 r.alice r.bob o) {v : VisEntry} (hv : v ∈ runVis r (pre ++ Move.aliceStart r.alice r.bob 4 6 hb shown :: mid ++ Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some ((runMoves pre (setupTrace r)).1.length + 3, (runMoves pre (setupTrace r)).1.length + 4)) :: post)) (hkind : v.kind = .send) {u : DY.Bytes} (hu : u ∈ v.terms) : let tr₁ := (runMoves pre (setupTrace r)).1;
    let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let stA := iniAliceStartState tr₁ r.bob o;
    u = o.ek ∨ u = o.ct ∨ u = encOut tr₂ stA cl (tr₂.length + 2) := by
  dsimp only; let tr₁ := (runMoves pre (setupTrace r)).1; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let stA := iniAliceStartState tr₁ r.bob o; let wrap := some (tr₁.length + 3, tr₁.length + 4); let m₁ := Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) wrap;
  have henc : m₁.next tr₂ = encNextTr tr₂ r.alice (tr₁.length + 8) stA cl (tr₂.length + 2) := by subst ho; exact encrypt_next_split38_eq wrap hm₀ hmid rfl
  have hek_net : NetMsgAt o.ek (tr₁.length + 3) tr₂ :=
    (hm₀ ▸ netMsgAt_ek_iniAliceStartTr tr₁ r.alice r.bob o).mono (CompPrefixInvEnc.runMoves_le mid (m₀.next tr₁))
  have hct_net : NetMsgAt o.ct (tr₁.length + 4) tr₂ :=
    (hm₀ ▸ netMsgAt_ct_iniAliceStartTr tr₁ r.alice r.bob o).mono (CompPrefixInvEnc.runMoves_le mid (m₀.next tr₁))
  have hrec : received tr₂ [tr₁.length + 3, tr₁.length + 4] = [o.ek, o.ct] := (by unfold received; simp only [List.filterMap_cons, List.filterMap_nil, getMessageSentAt_of_netMsgAt hek_net, getMessageSentAt_of_netMsgAt hct_net]); rw [runVis_split38_eq hNe hpre hmid hpost, aliceStart_vis_eq, encrypt_vis_eq, henc, List.mem_append] at hv
  rcases hv with hv₀ | hv₁
  · rcases xpl_aliceVis_kind (List.mem_of_mem_take hv₀) with hk | hk <;> (rw [hkind] at hk; cases hk)
  · unfold encVis at hv₁; rw [List.mem_append] at hv₁
    rcases hv₁ with hv_draws | hv_send
    · rcases mem_encDraws_encNextTr hv_draws with rfl | rfl <;> cases hkind
    · rw [mem_encSend_encNextTr_some hv_send] at hu; dsimp only at hu; rw [hrec] at hu; simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hu; exact hu
structure TRStateVF (i : ExternInterpretation) (S : Sem) (g : Ghost)
    (st : DY.Libsignal.TripleRatchet.TRState) : Prop where
  myIk : VariantFree i S g st.myIk
  peerIk : VariantFree i S g st.peerIk
  rk : VariantFree i S g st.rk
  dhs : VariantFree i S g st.dhs
  cks : VariantFree i S g st.cks
  sid : VariantFree i S g st.sid
  spqr : VariantFree i S g st.spqr
  recv : ∀ d ∈ st.recv, VariantFree i S g d.ratchetKey ∧ VariantFree i S g d.chainKey
section TR
variable {i : ExternInterpretation} {S : Sem} {g : Ghost}
end TR
section Split38
variable {i : ExternInterpretation} {S : Sem} {g : Ghost}
theorem runTrace_split38_swap_eq (r : Records) (pre mid post : List Move) (m₀ : Move) (me : Participant) (s cl pq : Nat) (w₁ w₂ : Option (Nat × Nat)) : runTraceMoves r (pre ++ m₀ :: mid ++ Move.encrypt me s cl pq w₁ :: post) = runTraceMoves r (pre ++ m₀ :: mid ++ Move.encrypt me s cl pq w₂ :: post) := by rw [xpl_runTrace_eq, xpl_runTrace_eq]; simp only [runMoves_append_fst, runMoves]; rfl
end Split38
end Symbolic.BugInjection.Proofs.Common443.CompRVariantFree38

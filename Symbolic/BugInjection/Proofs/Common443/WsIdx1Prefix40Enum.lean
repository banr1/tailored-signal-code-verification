/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompRVariantFree38
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40EnumDefs
public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40Enum
open CryptoProofLib.Refinement (ExternInterpretation) open DY.Libsignal (HwBytes)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.HwEvents Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.Census443Memo Symbolic.BugInjection.Proofs.Common443.CompExcuse Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvFresh Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvSwap Symbolic.BugInjection.Proofs.Common443.CompRMemoKnown Symbolic.BugInjection.Proofs.Common443.CompRNoBSC Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy Symbolic.BugInjection.Proofs.Common443.CompRVariantFree38 Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40EnumDefs Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
theorem census_iniAliceOut_eq : @Census443Defs.iniAliceOut = @CompPrefixInvAlice.iniAliceOut := rfl
theorem census_iniAliceStartState_eq : @Census443Defs.iniAliceStartState = @CompPrefixInvAlice.iniAliceStartState := rfl
theorem census_iniAliceStartTr_eq : @Census443Defs.iniAliceStartTr = @CompPrefixInvAlice.iniAliceStartTr := rfl
theorem census_encOut_eq : @Census443Defs.encOut = @CompPrefixInvEnc.encOut := rfl
theorem census_encSt_eq : @Census443Defs.encSt = @CompPrefixInvEnc.encSt := rfl
theorem census_encNextTr_eq : @Census443Defs.encNextTr = @CompPrefixInvEnc.encNextTr := rfl
attribute [local irreducible] setupPublic setupSecret
theorem pt_term_of_mem_encVis {tr : ExecTrace} {me : Participant} {sIdx : Nat} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {w : Option (Nat × Nat)} {v : VisEntry} (hv : v ∈ encVis tr (encNextTr tr me sIdx stA cl pq) w true) (hkind : v.kind = .pt) {u : DY.Bytes} (hu : u ∈ v.terms) : u = randTerm tr.length 32 := by
  unfold encVis at hv; rcases List.mem_append.mp hv with hv_draws | hv_send
  · exact (mem_encDraws_encNextTr hv_draws).elim
      (fun h => by rw [h] at hu; exact List.mem_singleton.mp hu)
      (fun h => by rw [h] at hkind; cases hkind)
  · cases w with
    | none => rw [mem_encSend_encNextTr_none hv_send] at hkind; cases hkind
    | some ec => rw [mem_encSend_encNextTr_some (e := ec.1) (c := ec.2) hv_send] at hkind; cases hkind
theorem send_term_of_mem_encVis_some {tr : ExecTrace} {me : Participant} {sIdx : Nat} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq e c : Nat} {ek ct : DY.Bytes} {v : VisEntry} (hek : NetMsgAt ek e tr) (hct : NetMsgAt ct c tr) (hv : v ∈ encVis tr (encNextTr tr me sIdx stA cl pq) (some (e, c)) true) (hkind : v.kind = .send) {u : DY.Bytes} (hu : u ∈ v.terms) : u = ek ∨ u = ct ∨ u = encOut tr stA cl pq := by
  unfold encVis at hv; rcases List.mem_append.mp hv with hv_draws | hv_send
  · rcases mem_encDraws_encNextTr hv_draws with rfl | rfl <;> cases hkind
  · rw [mem_encSend_encNextTr_some hv_send] at hu
    dsimp only [received, List.filterMap_cons, List.filterMap_nil] at hu; rw [CompRVariantFree38.getMessageSentAt_of_netMsgAt hek, CompRVariantFree38.getMessageSentAt_of_netMsgAt hct] at hu
    simpa only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] using hu
section Decomp
variable {r : Records} {pre mid₁ mid₂ post : List Move}
  {hb : DY.Libsignal.PQXDH.BundleHandles} {sh s₁ s₂ cl₁ cl₂ : Nat}
  {w₁ w₂ : Option (Nat × Nat)} {tr₁ tr₂ tr₃ : ExecTrace}
theorem runTrace_split40 (htr₁ : tr₁ = (runMoves pre (setupTrace r)).1) (htr₂ : tr₂ = (runMoves mid₁ ((Move.aliceStart r.alice r.bob 4 6 hb sh).next tr₁)).1) (htr₃ : tr₃ = (runMoves mid₂ ((Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) w₁).next tr₂)).1) : runTraceMoves r (pre ++ Move.aliceStart r.alice r.bob 4 6 hb sh :: mid₁ ++ Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) w₁ :: mid₂ ++ Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) w₂ :: post) = (runMoves post ((Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) w₂).next tr₃)).1 := by subst htr₃ htr₂ htr₁; rw [xpl_runTrace_eq]; simp only [runMoves_append_fst, runMoves]
theorem runVis_split40 (hNe : r.alice ≠ r.bob) (htr₁ : tr₁ = (runMoves pre (setupTrace r)).1) (htr₂ : tr₂ = (runMoves mid₁ ((Move.aliceStart r.alice r.bob 4 6 hb sh).next tr₁)).1) (htr₃ : tr₃ = (runMoves mid₂ ((Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) w₁).next tr₂)).1) (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre) (hmid₁ : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb sh).next tr₁) mid₁) (hmid₂ : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) w₁).next tr₂) mid₂) (hpost : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) w₂).next tr₃) post) : runVis r (pre ++ Move.aliceStart r.alice r.bob 4 6 hb sh :: mid₁ ++ Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) w₁ :: mid₂ ++ Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) w₂ :: post) = (Move.aliceStart r.alice r.bob 4 6 hb sh).vis tr₁ ++ (Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) w₁).vis tr₂ ++ (Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) w₂).vis tr₃ := by
  have h1 := runMoves_snd_of_movesFrom_invisibleNoEffect hpre; have h2 := runMoves_snd_of_movesFrom_invisibleNoEffect hmid₁; have h3 := runMoves_snd_of_movesFrom_invisibleNoEffect hmid₂; have h4 := runMoves_snd_of_movesFrom_invisibleNoEffect hpost; subst htr₃ htr₂ htr₁; change r.setupMove.vis Trace.nil ++ (runMoves _ (setupTrace r)).2 = _; rw [setupMove_vis_nil hNe, List.nil_append]
  simp only [runMoves_append_snd, runMoves, h1, h2, h3, h4, List.nil_append, List.append_nil, List.append_assoc]
theorem storedStates_split40_cases {o : DY.Libsignal.PQXDH.AliceHandshakeOut} {stA₁ stA₁' : DY.Libsignal.TripleRatchet.TRState} (htr₁ : tr₁ = (runMoves pre (setupTrace r)).1) (htr₂ : tr₂ = (runMoves mid₁ ((Move.aliceStart r.alice r.bob 4 6 hb sh).next tr₁)).1) (htr₃ : tr₃ = (runMoves mid₂ ((Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) w₁).next tr₂)).1) (hstA₁ : stA₁ = iniAliceStartState tr₁ r.bob o) (hstA₁' : stA₁' = encSt tr₂ stA₁ cl₁) (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre) (hmid₁ : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb sh).next tr₁) mid₁) (hmid₂ : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) w₁).next tr₂) mid₂) (hpost : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) w₂).next tr₃) post) (hm₀ : (Move.aliceStart r.alice r.bob 4 6 hb sh).next tr₁ = iniAliceStartTr tr₁ r.alice r.bob o) (hm₁ : (Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) w₁).next tr₂ = encNextTr tr₂ r.alice s₁ stA₁ cl₁ (tr₂.length + 2)) (hm₂ : (Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) w₂).next tr₃ = encNextTr tr₃ r.alice s₂ stA₁' cl₂ (tr₃.length + 2)) {ls : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState} (hls : ls ∈ storedStates r (runTraceMoves r (pre ++ Move.aliceStart r.alice r.bob 4 6 hb sh :: mid₁ ++ Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) w₁ :: mid₂ ++ Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) w₂ :: post))) : ls = ⟨r.alice, stA₁⟩ ∨ ls = ⟨r.alice, stA₁'⟩ ∨ ls = ⟨r.alice, encSt tr₃ stA₁' cl₂⟩ := by
  rw [runTrace_split40 htr₁ htr₂ htr₃] at hls; obtain ⟨j, _, _, hat⟩ := mem_storedStates_iff.mp hls; have hno₁ : NoTRState tr₁ := htr₁ ▸ noTRState_of_movesFrom_invisibleNoEffect (noTRState_setupTrace r) hpre
  rw [at?_trSt_of_movesFrom_invisibleNoEffect hpost j, hm₂, at?_trSt_encNextTr, htr₃, at?_trSt_of_movesFrom_invisibleNoEffect hmid₂ j, hm₁, at?_trSt_encNextTr, htr₂, at?_trSt_of_movesFrom_invisibleNoEffect hmid₁ j, hm₀, at?_trSt_iniAliceStartTr_of_noTRState hno₁] at hat
  split_ifs at hat
  · cases hat; rw [← hm₀, ← htr₂, ← hm₁, ← htr₃]; exact .inr (.inr rfl)
  · cases hat; rw [← hm₀, ← htr₂, hstA₁']; exact .inr (.inl rfl)
  · cases hat; exact .inl (hstA₁ ▸ rfl)
theorem pt_terms_split40_mem (hNe : r.alice ≠ r.bob) {o : DY.Libsignal.PQXDH.AliceHandshakeOut} {stA₁ stA₁' : DY.Libsignal.TripleRatchet.TRState} (htr₁ : tr₁ = (runMoves pre (setupTrace r)).1) (htr₂ : tr₂ = (runMoves mid₁ ((Move.aliceStart r.alice r.bob 4 6 hb sh).next tr₁)).1) (htr₃ : tr₃ = (runMoves mid₂ ((Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) w₁).next tr₂)).1) (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre) (hmid₁ : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb sh).next tr₁) mid₁) (hmid₂ : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) w₁).next tr₂) mid₂) (hpost : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) w₂).next tr₃) post) (hm₀ : (Move.aliceStart r.alice r.bob 4 6 hb sh).next tr₁ = iniAliceStartTr tr₁ r.alice r.bob o) (hm₁ : (Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) w₁).next tr₂ = encNextTr tr₂ r.alice s₁ stA₁ cl₁ (tr₂.length + 2)) (hm₂ : (Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) w₂).next tr₃ = encNextTr tr₃ r.alice s₂ stA₁' cl₂ (tr₃.length + 2)) {v : VisEntry} (hv : v ∈ runVis r (pre ++ Move.aliceStart r.alice r.bob 4 6 hb sh :: mid₁ ++ Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) w₁ :: mid₂ ++ Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) w₂ :: post)) (hkind : v.kind = .pt) {u : DY.Bytes} (hu : u ∈ v.terms) : u = randTerm tr₂.length 32 ∨ u = randTerm tr₃.length 32 := by
  rw [runVis_split40 hNe htr₁ htr₂ htr₃ hpre hmid₁ hmid₂ hpost, aliceStart_vis_eq, encrypt_vis_eq, encrypt_vis_eq, hm₀, hm₁, hm₂, List.mem_append, List.mem_append] at hv
  rcases hv with (hv₀ | hv₁) | hv₂
  · rcases xpl_aliceVis_kind (List.mem_of_mem_take hv₀) with hk | hk <;> (rw [hkind] at hk; cases hk)
  · exact .inl (pt_term_of_mem_encVis hv₁ hkind hu)
  · exact .inr (pt_term_of_mem_encVis hv₂ hkind hu)
theorem send_terms_split40_mem (hNe : r.alice ≠ r.bob) {o : DY.Libsignal.PQXDH.AliceHandshakeOut} {stA₁ stA₁' : DY.Libsignal.TripleRatchet.TRState} (htr₁ : tr₁ = (runMoves pre (setupTrace r)).1) (htr₂ : tr₂ = (runMoves mid₁ ((Move.aliceStart r.alice r.bob 4 6 hb sh).next tr₁)).1) (htr₃ : tr₃ = (runMoves mid₂ ((Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4))).next tr₂)).1) (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre) (hmid₁ : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb sh).next tr₁) mid₁) (hmid₂ : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4))).next tr₂) mid₂) (hpost : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) (some (tr₁.length + 3, tr₁.length + 4))).next tr₃) post) (hm₀ : (Move.aliceStart r.alice r.bob 4 6 hb sh).next tr₁ = iniAliceStartTr tr₁ r.alice r.bob o) (hm₁ : (Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4))).next tr₂ = encNextTr tr₂ r.alice s₁ stA₁ cl₁ (tr₂.length + 2)) (hm₂ : (Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) (some (tr₁.length + 3, tr₁.length + 4))).next tr₃ = encNextTr tr₃ r.alice s₂ stA₁' cl₂ (tr₃.length + 2)) {v : VisEntry} (hv : v ∈ runVis r (pre ++ Move.aliceStart r.alice r.bob 4 6 hb sh :: mid₁ ++ Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: mid₂ ++ Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: post)) (hkind : v.kind = .send) {u : DY.Bytes} (hu : u ∈ v.terms) : u = o.ek ∨ u = o.ct ∨ u = encOut tr₂ stA₁ cl₁ (tr₂.length + 2) ∨ u = encOut tr₃ stA₁' cl₂ (tr₃.length + 2) := by
  have hek₂ : NetMsgAt o.ek (tr₁.length + 3) tr₂ := htr₂ ▸ (hm₀ ▸ netMsgAt_ek_iniAliceStartTr tr₁ r.alice r.bob o).mono (CompPrefixInvEnc.runMoves_le mid₁ _); have hct₂ : NetMsgAt o.ct (tr₁.length + 4) tr₂ := htr₂ ▸ (hm₀ ▸ netMsgAt_ct_iniAliceStartTr tr₁ r.alice r.bob o).mono (CompPrefixInvEnc.runMoves_le mid₁ _); have hek₃ : NetMsgAt o.ek (tr₁.length + 3) tr₃ := htr₃ ▸ (hek₂.mono (Move.le_next _ _)).mono (CompPrefixInvEnc.runMoves_le mid₂ _)
  have hct₃ : NetMsgAt o.ct (tr₁.length + 4) tr₃ := htr₃ ▸ (hct₂.mono (Move.le_next _ _)).mono (CompPrefixInvEnc.runMoves_le mid₂ _); rw [runVis_split40 hNe htr₁ htr₂ htr₃ hpre hmid₁ hmid₂ hpost, aliceStart_vis_eq, encrypt_vis_eq, encrypt_vis_eq, hm₀, hm₁, hm₂, List.mem_append, List.mem_append] at hv
  rcases hv with (hv₀ | hv₁) | hv₂
  · rcases xpl_aliceVis_kind (List.mem_of_mem_take hv₀) with hk | hk <;> (rw [hkind] at hk; cases hk)
  · rcases send_term_of_mem_encVis_some hek₂ hct₂ hv₁ hkind hu with rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr (.inl rfl)
    · exact .inr (.inr (.inl rfl))
  · rcases send_term_of_mem_encVis_some hek₃ hct₃ hv₂ hkind hu with rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr (.inl rfl)
    · exact .inr (.inr (.inr rfl))
theorem split40PrefixEnumOn_of_shape (hNe : r.alice ≠ r.bob) (htr₁ : tr₁ = (runMoves pre (setupTrace r)).1) (htr₂ : tr₂ = (runMoves mid₁ ((Move.aliceStart r.alice r.bob 4 6 hb sh).next tr₁)).1) (htr₃ : tr₃ = (runMoves mid₂ ((Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4))).next tr₂)).1) (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre) (hmid₁ : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb sh).next tr₁) mid₁) (hmid₂ : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4))).next tr₂) mid₂) (hpost : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) (some (tr₁.length + 3, tr₁.length + 4))).next tr₃) post) (hm₀ : (Move.aliceStart r.alice r.bob 4 6 hb sh).next tr₁ = iniAliceStartTr tr₁ r.alice r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) (hm₁ : (Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4))).next tr₂ = encNextTr tr₂ r.alice s₁ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁ (tr₂.length + 2)) (hm₂ : (Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) (some (tr₁.length + 3, tr₁.length + 4))).next tr₃ = encNextTr tr₃ r.alice s₂ (encSt tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁) cl₂ (tr₃.length + 2)) : Split40PrefixEnumOn r (pre ++ Move.aliceStart r.alice r.bob 4 6 hb sh :: mid₁ ++ Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: mid₂ ++ Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: post) tr₁ tr₂ tr₃ cl₁ cl₂ := by
  intro u hu; unfold Split40PrefixAtom; rw [census_iniAliceOut_eq, census_iniAliceStartState_eq, census_encOut_eq, census_encSt_eq]; unfold prefixTerms principalTerms plaintextTerms at hu; simp only [List.mem_append, List.mem_flatMap, List.mem_filter, List.mem_map, beq_iff_eq] at hu
  rcases hu with ((⟨v, ⟨hv_mem, hv_kind⟩, hu_v⟩ | ⟨ls, hls, rfl⟩) | hsec) | ⟨v, ⟨hv_mem, hv_kind⟩, hu_v⟩
  · rcases send_terms_split40_mem hNe htr₁ htr₂ htr₃ hpre hmid₁ hmid₂ hpost hm₀ hm₁ hm₂ hv_mem hv_kind hu_v with
      h1 | h2 | h3 | h4
    · exact .inl (.inl h1)
    · exact .inl (.inr (.inl h2))
    · exact .inl (.inr (.inr (.inl h3)))
    · exact .inl (.inr (.inr (.inr (.inl h4))))
  · rcases storedStates_split40_cases htr₁ htr₂ htr₃ rfl rfl hpre hmid₁ hmid₂ hpost hm₀ hm₁ hm₂ hls with
      rfl | rfl | rfl
    · exact .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl)))))))
    · exact .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))))
    · exact .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr rfl))))))))
  · exact .inr hsec
  · rcases pt_terms_split40_mem hNe htr₁ htr₂ htr₃ hpre hmid₁ hmid₂ hpost hm₀ hm₁ hm₂ hv_mem hv_kind hu_v with
      h1 | h2
    · exact .inl (.inr (.inr (.inr (.inr (.inl h1)))))
    · exact .inl (.inr (.inr (.inr (.inr (.inr (.inl h2))))))
end Decomp
theorem noSessionEffect_of_movesFrom_invisibleNoEffect {tr : ExecTrace} {δ : List Move} (hδ : MovesFrom InvisibleNoEffect tr δ) {k : Nat} {m : Move} (hk : δ[k]? = some m) : NoSessionEffect (runMoves (δ.take k) tr).1 m := by
  induction δ generalizing tr k with
  | nil => cases hk
  | cons d δ ih => cases k with | zero => cases hk; exact hδ.1.2 | succ k => exact ih hδ.2 hk
theorem take_append_cons_of_gt {α : Type} (pre rest : List α) (m₀ : α) {k : Nat} (h : pre.length + 1 ≤ k) : (pre ++ m₀ :: rest).take k = pre ++ m₀ :: rest.take (k - (pre.length + 1)) := by
  have hk : k = pre.length + ((k - (pre.length + 1)) + 1) := by omega
  conv => lhs; rw [hk]
  rw [List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left]; rfl
theorem mem_or_of_not_noSessionEffect_append {tr : ExecTrace} {pre rest : List Move} {m₀ : Move} (hpre : MovesFrom InvisibleNoEffect tr pre) {k : Nat} {m : Move} (hk : (pre ++ m₀ :: rest)[k]? = some m) (hneff : ¬ NoSessionEffect (runMoves ((pre ++ m₀ :: rest).take k) tr).1 m) : k = pre.length ∨ (pre.length + 1 ≤ k ∧ rest[k - (pre.length + 1)]? = some m ∧ ¬ NoSessionEffect (runMoves (rest.take (k - (pre.length + 1))) (m₀.next (runMoves pre tr).1)).1 m) := by
  by_cases hlt : k < pre.length
  · rw [List.getElem?_append_left hlt] at hk; rw [List.take_append_of_le_length (Nat.le_of_lt hlt)] at hneff
    exact False.elim (hneff (noSessionEffect_of_movesFrom_invisibleNoEffect hpre hk))
  · by_cases heq : k = pre.length
    · exact .inl heq
    · refine .inr ⟨by omega, ?_, fun heff => hneff ?_⟩
      · rw [List.getElem?_append_right (by omega)] at hk
        obtain ⟨j, hj⟩ : ∃ j, k - pre.length = j + 1 := ⟨k - (pre.length + 1), by omega⟩
        rw [hj, List.getElem?_cons_succ] at hk
        rwa [← show j = k - (pre.length + 1) by omega]
      · rw [take_append_cons_of_gt pre rest m₀ (by omega), runMoves_append_fst, runMoves]; exact heff
theorem not_noSessionEffect_of_next_eq_iniAliceStartTr {tr : ExecTrace} {m : Move} {a b : Participant} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} (hnext : m.next tr = iniAliceStartTr tr a b o) : ¬ NoSessionEffect tr m := by
  intro heff
  have h1 := CompPrefixInvEnc.at?_trSt_of_noSessionEffect heff (tr.length + 8)
  rw [hnext, trStateStoredAt_iniAliceStartTr, (XplSteps.xnone_of_ge (by omega)).1] at h1; cases h1
theorem not_noSessionEffect_of_next_eq_encNextTr {tr : ExecTrace} {m : Move} {me : Participant} {sIdx : Nat} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} (hnext : m.next tr = encNextTr tr me sIdx stA cl pq) : ¬ NoSessionEffect tr m := by
  intro heff
  have h1 := CompPrefixInvEnc.at?_trSt_of_noSessionEffect heff (tr.length + 5)
  rw [hnext, trStateStoredAt_encNextTr, (XplSteps.xnone_of_ge (by omega)).1] at h1; cases h1
theorem effect_index_split40 {r : Records} {pre mid₁ mid₂ post : List Move} {m₀ m₁ m₂ : Move} (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre) (hmid₁ : MovesFrom InvisibleNoEffect (m₀.next (runMoves pre (setupTrace r)).1) mid₁) (hmid₂ : MovesFrom InvisibleNoEffect (m₁.next (runMoves mid₁ (m₀.next (runMoves pre (setupTrace r)).1)).1) mid₂) (hpost : MovesFrom InvisibleNoEffect (m₂.next (runMoves mid₂ (m₁.next (runMoves mid₁ (m₀.next (runMoves pre (setupTrace r)).1)).1)).1) post) {k : Nat} {m : Move} (hk : (pre ++ m₀ :: mid₁ ++ m₁ :: mid₂ ++ m₂ :: post)[k]? = some m) (hneff : ¬ NoSessionEffect (runTraceMoves r ((pre ++ m₀ :: mid₁ ++ m₁ :: mid₂ ++ m₂ :: post).take k)) m) : k = pre.length ∨ k = pre.length + 1 + mid₁.length ∨ k = pre.length + 1 + mid₁.length + 1 + mid₂.length := by
  rw [xpl_runTrace_eq] at hneff
  have hassoc : pre ++ m₀ :: mid₁ ++ m₁ :: mid₂ ++ m₂ :: post =
      pre ++ m₀ :: (mid₁ ++ m₁ :: (mid₂ ++ m₂ :: post)) := by simp only [List.append_assoc, List.cons_append]
  rw [hassoc] at hk hneff
  rcases mem_or_of_not_noSessionEffect_append hpre hk hneff with rfl | ⟨_, hk₁, hneff₁⟩
  · exact .inl rfl
  · rcases mem_or_of_not_noSessionEffect_append hmid₁ hk₁ hneff₁ with _ | ⟨_, hk₂, hneff₂⟩
    · exact .inr (.inl (by omega))
    · rcases mem_or_of_not_noSessionEffect_append hmid₂ hk₂ hneff₂ with _ | ⟨_, hk₃, hneff₃⟩
      · exact .inr (.inr (by omega))
      · exact False.elim (hneff₃ (noSessionEffect_of_movesFrom_invisibleNoEffect hpost hk₃))
theorem matchedPrefix_split_seg {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {τ₁ blk : List MachineEvent} {k₀ : Kind} {ks : List Kind} (hmp : Symbolic.Swarm.CREF.MatchedPrefix i r S g ms (τ₁ ++ blk)) (hmap : blk.map eventKind = k₀ :: ks) (hk₀ : k₀ = .recv ∨ k₀ = .pt) (hks : ∀ k ∈ ks, k = .rng ∨ k = .send) : ∃ (ms₁ pre post : List Move) (m : Move), ms = ms₁ ++ pre ++ m :: post ∧ Symbolic.Swarm.CREF.MatchedPrefix i r S g ms₁ τ₁ ∧ MovesFrom InvisibleNoEffect (runTraceMoves r ms₁) pre ∧ List.Forall₂ (EventMatchesEntry i r S g) blk (m.vis (runTraceMoves r (ms₁ ++ pre))) ∧ MovesFrom InvisibleNoEffect (m.next (runTraceMoves r (ms₁ ++ pre))) post := by
  have hne : blk ≠ [] := fun hnil => by rw [hnil] at hmap; cases hmap
  have hhead : ∀ e ∈ blk.head?, eventKind e = .recv ∨ eventKind e = .pt := by
    cases blk with
    | nil => contradiction
    | cons hd tl =>
      intro e he; simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at he; subst he
      simp only [List.map_cons, List.cons.injEq] at hmap; exact hmap.1 ▸ hk₀
  have htail : ∀ e ∈ blk.tail, eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak := by
    cases blk with
    | nil => contradiction
    | cons hd tl =>
      intro e he; simp only [List.tail_cons] at he; simp only [List.map_cons, List.cons.injEq] at hmap
      rcases hks (eventKind e) (hmap.2 ▸ List.mem_map_of_mem he) with hk | hk <;> (rw [hk]; decide)
  obtain ⟨ms₁, δ, hms, hmp₁, hfor⟩ := matchedPrefix6_split hmp hhead (CompPrefixInvStruct.matchedPrefix6_prefix_reachable hmp); obtain ⟨pre, m, post, rfl, hpre, ⟨-, -, hm⟩, hpost⟩ := xpl6_oneMove ⟨hmp₁, hms ▸ hmp.2.1, hfor⟩ hhead hne htail
  refine ⟨ms₁, pre, post, m, by rw [hms, List.append_assoc], hmp₁, hpre, ?_, ?_⟩ <;>
    rwa [CompPrefixInvStruct.runTrace_append]
theorem coinSplit_kinds {pt coins w : HwBytes} {b : List MachineEvent}
    (hc : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt pt, .rng coins, .send w] b) :
    ∃ ks, b.map eventKind = .pt :: ks ∧ ∀ k ∈ ks, k = .rng ∨ k = .send := by
  cases hc with
  | keep _ h1 =>
    cases h1 with
    | keep hne _ => exact absurd rfl (hne coins)
    | @split _ bs _ _ _ _ h2 =>
      cases h2 with
      | keep _ h3 =>
        cases h3
        refine ⟨(bs.map MachineEvent.rng).map eventKind ++ [.send], by simp [List.map_append]; exact ⟨rfl, rfl⟩, fun k hk => ?_⟩
        rcases List.mem_append.mp hk with hk1 | hk2
        · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk1
          obtain ⟨c, -, rfl⟩ := List.mem_map.mp he
          exact .inl rfl
        · exact .inr (List.mem_singleton.mp hk2)

theorem decomp40_moves {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {b1 b2 : List MachineEvent}
    (hc1 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit (seg 35 3) b1)
    (hc2 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit WsIdx1CensusDefs.seg38SplitSrc b2)
    (hmp : Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms' ((seg 0 35 ++ b1) ++ b2)) :
    ∃ (pre mid₁ mid₂ post : List Move) (m₀ m₁ m₂ : Move), ms' = pre ++ m₀ :: mid₁ ++ m₁ :: mid₂ ++ m₂ :: post ∧
      let tr₁ := (runMoves pre (setupTrace r)).1
      let tr₂ := (runMoves mid₁ (m₀.next tr₁)).1
      let tr₃ := (runMoves mid₂ (m₁.next tr₂)).1
      MovesFrom InvisibleNoEffect (setupTrace r) pre ∧
      MovesFrom InvisibleNoEffect (m₀.next tr₁) mid₁ ∧
      MovesFrom InvisibleNoEffect (m₁.next tr₂) mid₂ ∧
      MovesFrom InvisibleNoEffect (m₂.next tr₃) post ∧
      List.Forall₂ (EventMatchesEntry compI0 r S g) (seg 0 35) (m₀.vis tr₁) ∧
      List.Forall₂ (EventMatchesEntry compI0 r S g) b1 (m₁.vis tr₂) ∧
      List.Forall₂ (EventMatchesEntry compI0 r S g) b2 (m₂.vis tr₃) := by
  obtain ⟨ks1, hks1_eq, hks1⟩ := coinSplit_kinds (show DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt _, .rng _, .send _] b1 from hc1)
  obtain ⟨ks2, hks2_eq, hks2⟩ := coinSplit_kinds hc2
  obtain ⟨ms₂, pre₃, post, m₂, hms', hmp38, hpre₃, hm₂, hpost⟩ :=
    matchedPrefix_split_seg hmp hks2_eq (.inr rfl) hks2
  obtain ⟨ms₁, pre₂, post₂, m₁, hms₂, hmp35, hpre₂, hm₁, hpost₂⟩ :=
    matchedPrefix_split_seg hmp38 hks1_eq (.inr rfl) hks1
  have hmp35' : Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms₁ ([] ++ seg 0 35) := hmp35
  obtain ⟨ms₀, pre₁, post₁, m₀, hms₁, hmp0, hpre₁, hm₀, hpost₁⟩ :=
    matchedPrefix_split_seg hmp35' seg0_kinds (.inl rfl) (fun k hk => .inl (replicate_rng 34 k hk))
  let pre := ms₀ ++ pre₁; let mid₁ := post₁ ++ pre₂; let mid₂ := post₂ ++ pre₃
  let tr₁ := (runMoves pre (setupTrace r)).1
  have htr₁ : runTraceMoves r (ms₀ ++ pre₁) = tr₁ := by rw [xpl_runTrace_eq]
  rw [htr₁] at hm₀ hpost₁
  have hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre := by rw [movesFrom_append, ← xpl_runTrace_eq]; exact ⟨movesFrom_invisibleNoEffect_of_matchedPrefix_nil hmp0, hpre₁⟩
  let tr₂ := (runMoves mid₁ (m₀.next tr₁)).1
  have htr_ms₁ : runTraceMoves r ms₁ = (runMoves post₁ (m₀.next tr₁)).1 := by rw [hms₁, xpl_runTrace_eq, runMoves_append_fst]; rfl
  have htr₂ : runTraceMoves r (ms₁ ++ pre₂) = tr₂ := by rw [CompPrefixInvStruct.runTrace_append, htr_ms₁]; dsimp [tr₂, mid₁]; rw [runMoves_append_fst]
  rw [htr₂] at hm₁ hpost₂
  have hmid₁ : MovesFrom InvisibleNoEffect (m₀.next tr₁) mid₁ := by dsimp [mid₁]; rw [movesFrom_append, ← htr_ms₁]; exact ⟨hpost₁, hpre₂⟩
  let tr₃ := (runMoves mid₂ (m₁.next tr₂)).1
  have hms₂_eq : ms₂ = pre ++ m₀ :: mid₁ ++ m₁ :: post₂ := by dsimp [pre, mid₁]; rw [hms₂, hms₁]; simp only [List.append_assoc, List.cons_append]
  have htr_ms₂ : runTraceMoves r ms₂ = (runMoves post₂ (m₁.next tr₂)).1 := by rw [hms₂_eq, xpl_runTrace_eq, runMoves_append_fst, runMoves_append_fst]; rfl
  have htr₃ : runTraceMoves r (ms₂ ++ pre₃) = tr₃ := by rw [CompPrefixInvStruct.runTrace_append, htr_ms₂]; dsimp [tr₃, mid₂]; rw [runMoves_append_fst]
  rw [htr₃] at hm₂ hpost
  have hmid₂ : MovesFrom InvisibleNoEffect (m₁.next tr₂) mid₂ := by dsimp [mid₂]; rw [movesFrom_append, ← htr_ms₂]; exact ⟨hpost₂, hpre₃⟩
  have hms'_eq : ms' = pre ++ m₀ :: mid₁ ++ m₁ :: mid₂ ++ m₂ :: post := by dsimp [mid₂]; rw [hms', hms₂_eq]; simp only [List.append_assoc, List.cons_append]
  exact ⟨pre, mid₁, mid₂, post, m₀, m₁, m₂, hms'_eq, hpre, hmid₁, hmid₂, hpost, hm₀, hm₁, hm₂⟩
theorem getElem?_middle {α : Type} (xs ys : List α) (x : α) : (xs ++ x :: ys)[xs.length]? = some x := by rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
theorem take_middle {α : Type} (xs ys : List α) (x : α) : (xs ++ x :: ys).take xs.length = xs := by rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length]
theorem decomp40_of_mp_links {r : Records} {S : Sem} {g : Ghost} {ms' : List Move}
    {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} {b1 b2 : List MachineEvent}
    (hc1 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit (seg 35 3) b1)
    (hc2 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit WsIdx1CensusDefs.seg38SplitSrc b2)
    (hmp : Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms' ((seg 0 35 ++ b1) ++ b2))
    (hlinks : Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂) :
    ∃ (pre mid₁ mid₂ post : List Move) (hb₁ : DY.Libsignal.PQXDH.BundleHandles) (sh₁ s₁ s₂ : Nat),
      let m₀ := Move.aliceStart r.alice r.bob 4 6 hb₁ sh₁
      let w := some (tr₁.length + 3, tr₁.length + 4)
      let m₁ := Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) w
      let m₂ := Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) w
      let o₁ := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
      let stA₁ := iniAliceStartState tr₁ r.bob o₁
      let stA₁' := encSt tr₂ stA₁ cl₁
      ms' = pre ++ m₀ :: mid₁ ++ m₁ :: mid₂ ++ m₂ :: post ∧
      tr₁ = (runMoves pre (setupTrace r)).1 ∧
      tr₂ = (runMoves mid₁ (m₀.next tr₁)).1 ∧
      tr₃ = (runMoves mid₂ (m₁.next tr₂)).1 ∧
      MovesFrom InvisibleNoEffect (setupTrace r) pre ∧
      MovesFrom InvisibleNoEffect (m₀.next tr₁) mid₁ ∧
      MovesFrom InvisibleNoEffect (m₁.next tr₂) mid₂ ∧
      MovesFrom InvisibleNoEffect (m₂.next tr₃) post ∧
      m₀.next tr₁ = iniAliceStartTr tr₁ r.alice r.bob o₁ ∧
      m₁.next tr₂ = encNextTr tr₂ r.alice s₁ stA₁ cl₁ (tr₂.length + 2) ∧
      m₂.next tr₃ = encNextTr tr₃ r.alice s₂ stA₁' cl₂ (tr₃.length + 2) ∧
      List.Forall₂ (EventMatchesEntry compI0 r S g) (seg 0 35) (m₀.vis tr₁) ∧
      List.Forall₂ (EventMatchesEntry compI0 r S g) b1 (m₁.vis tr₂) ∧
      List.Forall₂ (EventMatchesEntry compI0 r S g) b2 (m₂.vis tr₃) := by
  obtain ⟨pre, mid₁, mid₂, post, m₀, m₁, m₂, hms', hpre, hmid₁, hmid₂, hpost, hvis₀, hvis₁, hvis₂⟩ := decomp40_moves hc1 hc2 hmp; obtain ⟨k₁, k₂, k₃, hb₁, sh₁, s₁, s₂, hk₁₂, hk₂₃, htr₁_k, hget₁, htr₂_k, hget₂, htr₃_k, hget₃, hnext₀, hnext₁, hnext₂⟩ := hlinks; rw [census_iniAliceStartTr_eq, census_iniAliceOut_eq] at hnext₀; rw [census_encNextTr_eq, census_iniAliceStartState_eq, census_iniAliceOut_eq] at hnext₁
  rw [census_encNextTr_eq, census_encSt_eq, census_iniAliceStartState_eq, census_iniAliceOut_eq] at hnext₂
  let m₀' := Move.aliceStart r.alice r.bob 4 6 hb₁ sh₁
  let w := some (tr₁.length + 3, tr₁.length + 4)
  let m₁' := Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) w
  let m₂' := Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) w
  have hneff₁ : ¬ NoSessionEffect (runTraceMoves r (ms'.take k₁)) m₀' := htr₁_k ▸ not_noSessionEffect_of_next_eq_iniAliceStartTr hnext₀; have hneff₂ : ¬ NoSessionEffect (runTraceMoves r (ms'.take k₂)) m₁' := htr₂_k ▸ not_noSessionEffect_of_next_eq_encNextTr hnext₁; have hneff₃ : ¬ NoSessionEffect (runTraceMoves r (ms'.take k₃)) m₂' := htr₃_k ▸ not_noSessionEffect_of_next_eq_encNextTr hnext₂; rw [hms'] at hget₁ hget₂ hget₃ hneff₁ hneff₂ hneff₃
  have hor₁ := effect_index_split40 hpre hmid₁ hmid₂ hpost hget₁ hneff₁; have hor₂ := effect_index_split40 hpre hmid₁ hmid₂ hpost hget₂ hneff₂; have hor₃ := effect_index_split40 hpre hmid₁ hmid₂ hpost hget₃ hneff₃
  have hk₁_eq : k₁ = pre.length := by omega
  have hk₂_eq : k₂ = (pre ++ m₀ :: mid₁).length := by simp only [List.length_append, List.length_cons]; omega
  have hk₃_eq : k₃ = (pre ++ m₀ :: mid₁ ++ m₁ :: mid₂).length := by simp only [List.length_append, List.length_cons]; omega
  subst hk₁_eq hk₂_eq hk₃_eq
  have hm₀_eq : m₀ = m₀' := by
    have h := getElem?_middle pre (mid₁ ++ m₁ :: mid₂ ++ m₂ :: post) m₀
    simp only [List.append_assoc, List.cons_append] at h hget₁; exact Option.some.inj (h.symm.trans hget₁)
  have hm₁_eq : m₁ = m₁' := by
    have h := getElem?_middle (pre ++ m₀ :: mid₁) (mid₂ ++ m₂ :: post) m₁
    simp only [List.append_assoc, List.cons_append] at h hget₂; exact Option.some.inj (h.symm.trans hget₂)
  have hm₂_eq : m₂ = m₂' := by
    have h := getElem?_middle (pre ++ m₀ :: mid₁ ++ m₁ :: mid₂) post m₂
    simp only [List.append_assoc, List.cons_append] at h hget₃; exact Option.some.inj (h.symm.trans hget₃)
  subst hm₀_eq hm₁_eq hm₂_eq
  have htr₁_eq : tr₁ = (runMoves pre (setupTrace r)).1 := by rw [← htr₁_k, hms']; have h := take_middle pre (mid₁ ++ m₁' :: mid₂ ++ m₂' :: post) m₀'; simp only [List.append_assoc, List.cons_append] at h ⊢; rw [h, xpl_runTrace_eq]
  have htr₂_eq : tr₂ = (runMoves mid₁ (m₀'.next tr₁)).1 := by
    rw [← htr₂_k, hms']; have h := take_middle (pre ++ m₀' :: mid₁) (mid₂ ++ m₂' :: post) m₁'
    have hassoc : pre ++ m₀' :: mid₁ ++ m₁' :: mid₂ ++ m₂' :: post =
        (pre ++ m₀' :: mid₁) ++ m₁' :: (mid₂ ++ m₂' :: post) := by simp only [List.append_assoc, List.cons_append]
    rw [hassoc, h, xpl_runTrace_eq, runMoves_append_fst, ← htr₁_eq]; rfl
  have htr₃_eq : tr₃ = (runMoves mid₂ (m₁'.next tr₂)).1 := by
    rw [← htr₃_k, hms', take_middle (pre ++ m₀' :: mid₁ ++ m₁' :: mid₂) post m₂', xpl_runTrace_eq, runMoves_append_fst, runMoves_append_fst, ← htr₁_eq]
    change (runMoves mid₂ (m₁'.next (runMoves mid₁ (m₀'.next tr₁)).1)).1 = _; rw [← htr₂_eq]
  rw [← htr₁_eq] at hmid₁ hmid₂ hpost hvis₀ hvis₁ hvis₂; rw [← htr₂_eq] at hmid₂ hpost hvis₁ hvis₂; rw [← htr₃_eq] at hpost hvis₂; exact ⟨pre, mid₁, mid₂, post, hb₁, sh₁, s₁, s₂, hms', htr₁_eq, htr₂_eq, htr₃_eq, hpre, hmid₁, hmid₂, hpost, hnext₀, hnext₁, hnext₂, hvis₀, hvis₁, hvis₂⟩
theorem split40PrefixEnumOn_of_mp_links {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} {b1 b2 : List MachineEvent} (hNe : r.alice ≠ r.bob) (hc1 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit (seg 35 3) b1) (hc2 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit WsIdx1CensusDefs.seg38SplitSrc b2) (hmp : Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms' ((seg 0 35 ++ b1) ++ b2)) (hlinks : Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂) : Split40PrefixEnumOn r ms' tr₁ tr₂ tr₃ cl₁ cl₂ := by obtain ⟨pre, mid₁, mid₂, post, hb₁, sh₁, s₁, s₂, hms', htr₁, htr₂, htr₃, hpre, hmid₁, hmid₂, hpost, hnext₀, hnext₁, hnext₂, -⟩ := decomp40_of_mp_links hc1 hc2 hmp hlinks; rw [hms']; exact split40PrefixEnumOn_of_shape hNe htr₁ htr₂ htr₃ hpre hmid₁ hmid₂ hpost hnext₀ hnext₁ hnext₂
theorem split40PrefixEnum : Split40PrefixEnum := by
  intro _ _ _ _ _ _ _ _ _ _ hfits _ hinv hlinks
  obtain ⟨b1, b2, hc1, hc2, hmp⟩ := hinv.mp.2.2.2.2.2
  exact split40PrefixEnumOn_of_mp_links hfits.1.1.1 hc1 hc2 (Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp) hlinks
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40Enum

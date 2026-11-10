/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixSteps
public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.Wire80
public import Symbolic.BugInjection.Proofs.Common443.CompRX0Decomp
public import Symbolic.BugInjection.Proofs.Common443.CompRX0Join
public import Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvFresh
public import Symbolic.BugInjection.Proofs.Common443.CompRVariantFree38

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv38
open CryptoProofLib.Refinement (ExternInterpretation)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443 Symbolic.BugInjection.Proofs.Common443.CompI0Laws Symbolic.BugInjection.Proofs.Common443.CompMemoInjGt
open Symbolic.BugInjection.Proofs.Common443.CompRMemoKnown hiding bytes_rec_gAll
open Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvFresh Symbolic.BugInjection.Proofs.Common443.CompRX0Decomp Symbolic.BugInjection.Proofs.Common443.CompRX0Join Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38 Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.Wire80
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop hiding compI0
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead35 Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead38 Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv35 Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixReach Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixSteps Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
theorem trStateStoredAt_encNextTr (tr₂ : ExecTrace) (me : Participant) (sIdx : Nat) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : ((encNextTr tr₂ me sIdx stA cl pq).at? (tr₂.length + 5) : Option TRStEntry) = some (TRStE me (encSt tr₂ stA cl)) :=
  CompRVariantFree38.trStateStoredAt_encNextTr tr₂ me sIdx stA cl pq
theorem at?_trSt_encNextTr (tr₂ : ExecTrace) (me : Participant) (sIdx : Nat) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq j : Nat) : ((encNextTr tr₂ me sIdx stA cl pq).at? j : Option TRStEntry) = if j = tr₂.length + 5 then some (TRStE me (encSt tr₂ stA cl)) else (tr₂.at? j : Option TRStEntry) :=
  CompRVariantFree38.at?_trSt_encNextTr tr₂ me sIdx stA cl pq j
theorem encrypt_next_split38_eq_gen {r : Records} {a : Participant} {tr₁ tr₂ : ExecTrace} {m₀ : Move} {mid : List Move} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} {cl : Nat} (wrap : Option (Nat × Nat)) (hm₀ : m₀.next tr₁ = iniAliceStartTr tr₁ a r.bob o) (hmid : MovesFrom InvisibleNoEffect (m₀.next tr₁) mid) (htr₂ : tr₂ = (runMoves mid (m₀.next tr₁)).1) : (Move.encrypt a (tr₁.length + 8) cl (tr₂.length + 2) wrap).next tr₂ = encNextTr tr₂ a (tr₁.length + 8) (iniAliceStartState tr₁ r.bob o) cl (tr₂.length + 2) := by
  have hst : (tr₂.at? (tr₁.length + 8) : Option TRStEntry) = some (TRStE a (iniAliceStartState tr₁ r.bob o)) := by
    rw [htr₂, at?_trSt_of_movesFrom_invisibleNoEffect hmid, hm₀]; exact trStateStoredAt_iniAliceStartTr tr₁ a r.bob o
  exact encrypt_next_eq_encNextTr_of_ownSalt hst (iniAliceStartState_ns_ne_u32Max tr₁ r.bob o) rfl
theorem storedStates_split38_cases_gen
    {r : Records} {a : Participant} {idS : Nat} {pre mid post : List Move}
    {hb : DY.Libsignal.PQXDH.BundleHandles} {shown cl : Nat} {wrap : Option (Nat × Nat)} {o : DY.Libsignal.PQXDH.AliceHandshakeOut}
    (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre)
    (hmid : MovesFrom InvisibleNoEffect ((Move.aliceStart a r.bob idS 6 hb shown).next (runMoves pre (setupTrace r)).1) mid)
    (hpost : MovesFrom InvisibleNoEffect ((Move.encrypt a ((runMoves pre (setupTrace r)).1.length + 8) cl
      ((runMoves mid ((Move.aliceStart a r.bob idS 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) wrap).next
      (runMoves mid ((Move.aliceStart a r.bob idS 6 hb shown).next (runMoves pre (setupTrace r)).1)).1) post)
    (hm₀ : (Move.aliceStart a r.bob idS 6 hb shown).next (runMoves pre (setupTrace r)).1 =
      iniAliceStartTr (runMoves pre (setupTrace r)).1 a r.bob o)
    {ls : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState}
    (hls : ls ∈ storedStates r (runTraceMoves r (pre ++ Move.aliceStart a r.bob idS 6 hb shown :: mid ++ Move.encrypt a ((runMoves pre (setupTrace r)).1.length + 8) cl
        ((runMoves mid ((Move.aliceStart a r.bob idS 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) wrap :: post))) :
    let tr₁ := (runMoves pre (setupTrace r)).1
    let m₀ := Move.aliceStart a r.bob idS 6 hb shown
    let tr₂ := (runMoves mid (m₀.next tr₁)).1
    let stA := iniAliceStartState tr₁ r.bob o
    ls = ⟨a, stA⟩ ∨ ls = ⟨a, encSt tr₂ stA cl⟩ := by
  let tr₁ := (runMoves pre (setupTrace r)).1
  let m₀ := Move.aliceStart a r.bob idS 6 hb shown
  let tr₂ := (runMoves mid (m₀.next tr₁)).1
  let stA := iniAliceStartState tr₁ r.bob o
  let m₁ := Move.encrypt a (tr₁.length + 8) cl (tr₂.length + 2) wrap
  have henc : m₁.next tr₂ = encNextTr tr₂ a (tr₁.length + 8) stA cl (tr₂.length + 2) := encrypt_next_split38_eq_gen wrap hm₀ hmid rfl
  have htr : runTraceMoves r (pre ++ m₀ :: mid ++ m₁ :: post) = (runMoves post (m₁.next tr₂)).1 := by rw [xpl_runTrace_eq]; simp only [runMoves_append_fst, runMoves]; rfl
  rw [htr] at hls; obtain ⟨j, _, _, hat⟩ := mem_storedStates_iff.mp hls
  rw [at?_trSt_of_movesFrom_invisibleNoEffect hpost j, henc, at?_trSt_encNextTr, at?_trSt_of_movesFrom_invisibleNoEffect hmid j, hm₀, at?_trSt_iniAliceStartTr_of_noTRState (noTRState_of_movesFrom_invisibleNoEffect (noTRState_setupTrace r) hpre)] at hat
  split_ifs at hat with hj₂ hj₁
  · cases hat; exact Or.inr rfl
  · cases hat; exact Or.inl rfl
theorem runMoves_snd_of_movesFrom_invisibleNoEffect {tr : ExecTrace} {δ : List Move} (hδ : MovesFrom InvisibleNoEffect tr δ) : (runMoves δ tr).2 = [] := by induction δ generalizing tr with | nil => rfl | cons _ _ ih => simp only [runMoves, hδ.1.1, ih hδ.2, List.append_nil]
theorem setupMove_vis_nil {r : Records} (hNe : r.alice ≠ r.bob) : r.setupMove.vis Trace.nil = [] :=
  CompRVariantFree38.setupMove_vis_nil hNe
theorem runVis_split38_eq_gen
    {r : Records} (hNe : r.alice ≠ r.bob) {a : Participant} {idS : Nat} {pre mid post : List Move}
    {hb : DY.Libsignal.PQXDH.BundleHandles} {shown cl : Nat} {wrap : Option (Nat × Nat)}
    (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre)
    (hmid : MovesFrom InvisibleNoEffect ((Move.aliceStart a r.bob idS 6 hb shown).next (runMoves pre (setupTrace r)).1) mid)
    (hpost : MovesFrom InvisibleNoEffect ((Move.encrypt a ((runMoves pre (setupTrace r)).1.length + 8) cl
      ((runMoves mid ((Move.aliceStart a r.bob idS 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) wrap).next
      (runMoves mid ((Move.aliceStart a r.bob idS 6 hb shown).next (runMoves pre (setupTrace r)).1)).1) post) :
    let tr₁ := (runMoves pre (setupTrace r)).1
    let m₀ := Move.aliceStart a r.bob idS 6 hb shown
    let tr₂ := (runMoves mid (m₀.next tr₁)).1
    let m₁ := Move.encrypt a (tr₁.length + 8) cl (tr₂.length + 2) wrap
    runVis r (pre ++ m₀ :: mid ++ m₁ :: post) = m₀.vis tr₁ ++ m₁.vis tr₂ := by
  dsimp only
  let tr₁ := (runMoves pre (setupTrace r)).1
  let m₀ := Move.aliceStart a r.bob idS 6 hb shown
  let tr₂ := (runMoves mid (m₀.next tr₁)).1
  let m₁ := Move.encrypt a (tr₁.length + 8) cl (tr₂.length + 2) wrap
  have h1 := runMoves_snd_of_movesFrom_invisibleNoEffect hpre; have h2 := runMoves_snd_of_movesFrom_invisibleNoEffect hmid; have h3 := runMoves_snd_of_movesFrom_invisibleNoEffect hpost; change r.setupMove.vis Trace.nil ++ (runMoves ((pre ++ m₀ :: mid) ++ m₁ :: post) (setupTrace r)).2 = m₀.vis tr₁ ++ m₁.vis tr₂; rw [setupMove_vis_nil hNe, List.nil_append, runMoves_append_snd, runMoves_append_fst, runMoves_append_snd, runMoves, runMoves]
  dsimp only [tr₁, tr₂, m₀, m₁] at h1 h2 h3 ⊢; rw [h1, h2, h3, List.nil_append, List.append_nil, List.append_nil]
theorem aliceStart_vis_eq (tr₁ : ExecTrace) (a b : Participant) (spkIdx pqpkIdx : Nat) (hb : DY.Libsignal.PQXDH.BundleHandles) (shown : Nat) : (Move.aliceStart a b spkIdx pqpkIdx hb shown).vis tr₁ = (aliceVis tr₁ ((Move.aliceStart a b spkIdx pqpkIdx hb shown).next tr₁) hb).take shown := by
  have hexp := exposures_nil_of_not_leakKind (tr := tr₁) (m := Move.aliceStart a b spkIdx pqpkIdx hb shown) rfl (fun h => nomatch h)
  unfold Move.vis; dsimp only; rw [hexp, List.append_nil]
theorem encrypt_vis_eq (tr₂ : ExecTrace) (me : Participant) (sIdx cl pq : Nat) (wrap : Option (Nat × Nat)) : (Move.encrypt me sIdx cl pq wrap).vis tr₂ = encVis tr₂ ((Move.encrypt me sIdx cl pq wrap).next tr₂) wrap true := by
  have hexp := exposures_nil_of_not_leakKind (tr := tr₂) (m := Move.encrypt me sIdx cl pq wrap) rfl (fun h => nomatch h)
  unfold Move.vis; dsimp only; rw [hexp, List.append_nil]
theorem vis_kind_ne_leak_split38_gen {r : Records} (hNe : r.alice ≠ r.bob) {a : Participant} {idS : Nat} {pre mid post : List Move} {hb : DY.Libsignal.PQXDH.BundleHandles} {shown cl : Nat} {wrap : Option (Nat × Nat)} (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre) (hmid : MovesFrom InvisibleNoEffect ((Move.aliceStart a r.bob idS 6 hb shown).next (runMoves pre (setupTrace r)).1) mid) (hpost : MovesFrom InvisibleNoEffect ((Move.encrypt a ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart a r.bob idS 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) wrap).next (runMoves mid ((Move.aliceStart a r.bob idS 6 hb shown).next (runMoves pre (setupTrace r)).1)).1) post) : ∀ v ∈ runVis r (pre ++ Move.aliceStart a r.bob idS 6 hb shown :: mid ++ Move.encrypt a ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart a r.bob idS 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) wrap :: post), v.kind ≠ .leak := by
  rw [runVis_split38_eq_gen hNe hpre hmid hpost, aliceStart_vis_eq, encrypt_vis_eq]
  intro v hv; rw [List.mem_append] at hv; rcases hv with hv₀ | hv₁
  · rcases xpl_aliceVis_kind (List.mem_of_mem_take hv₀) with hk | hk <;> rw [hk] <;> decide
  · rcases xpl_encVis_kind hv₁ with hk | hk | ⟨_, hk⟩ <;> rw [hk] <;> decide
theorem mem_encDraws_encNextTr {tr₂ : ExecTrace} {me : Participant} {sIdx : Nat} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {v : VisEntry} (hv : v ∈ encDraws (newRandoms tr₂ (encNextTr tr₂ me sIdx stA cl pq))) : v = ⟨.pt, [randTerm tr₂.length 32], .single, none⟩ ∨ v = rngEntry (randTerm (tr₂.length + 1) cl) := by
  rw [CompPrefixInvFresh.newRandoms_encNextTr] at hv
  by_cases hcl : (cl != 0) = true
  · simp only [encDraws, List.filter_cons, hcl, ↓reduceIte, List.filter_nil, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hv
    exact hv
  · have hcl' : (cl != 0) = false := Bool.eq_false_iff.mpr hcl
    simp only [encDraws, List.filter_cons, hcl', Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hv; exact Or.inl hv
theorem mem_encSend_encNextTr_none {tr₂ : ExecTrace} {me : Participant} {sIdx : Nat} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {v : VisEntry} (hv : v ∈ encSend tr₂ (encNextTr tr₂ me sIdx stA cl pq) none) : v = ⟨.send, [encOut tr₂ stA cl pq], .whisper, none⟩ := by unfold encSend at hv; rw [lastSent_encNextTr] at hv; exact List.mem_singleton.mp hv
theorem mem_encSend_encNextTr_some {tr₂ : ExecTrace} {me : Participant} {sIdx : Nat} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq e c : Nat} {v : VisEntry} (hv : v ∈ encSend tr₂ (encNextTr tr₂ me sIdx stA cl pq) (some (e, c))) : v = ⟨.send, received tr₂ [e, c] ++ [encOut tr₂ stA cl pq], .preKeySend, none⟩ := by unfold encSend at hv; rw [lastSent_encNextTr] at hv; exact List.mem_singleton.mp hv
theorem send_terms_split38_mem_wrap_gen
    {r : Records} (hNe : r.alice ≠ r.bob) {a : Participant} {idS : Nat} {pre mid post : List Move}
    {hb : DY.Libsignal.PQXDH.BundleHandles} {shown cl e c' : Nat} {o : DY.Libsignal.PQXDH.AliceHandshakeOut}
    (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre)
    (hmid : MovesFrom InvisibleNoEffect ((Move.aliceStart a r.bob idS 6 hb shown).next (runMoves pre (setupTrace r)).1) mid)
    (hpost : MovesFrom InvisibleNoEffect ((Move.encrypt a ((runMoves pre (setupTrace r)).1.length + 8) cl
      ((runMoves mid ((Move.aliceStart a r.bob idS 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some (e, c'))).next
      (runMoves mid ((Move.aliceStart a r.bob idS 6 hb shown).next (runMoves pre (setupTrace r)).1)).1) post)
    (hm₀ : (Move.aliceStart a r.bob idS 6 hb shown).next (runMoves pre (setupTrace r)).1 =
      iniAliceStartTr (runMoves pre (setupTrace r)).1 a r.bob o)
    {v : VisEntry}
    (hv : v ∈ runVis r (pre ++ Move.aliceStart a r.bob idS 6 hb shown :: mid ++ Move.encrypt a ((runMoves pre (setupTrace r)).1.length + 8) cl
        ((runMoves mid ((Move.aliceStart a r.bob idS 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some (e, c')) :: post))
    (hkind : v.kind = .send) {u : DY.Bytes} (hu : u ∈ v.terms) :
    let tr₁ := (runMoves pre (setupTrace r)).1
    let m₀ := Move.aliceStart a r.bob idS 6 hb shown
    let tr₂ := (runMoves mid (m₀.next tr₁)).1
    let stA := iniAliceStartState tr₁ r.bob o
    u ∈ received tr₂ [e, c'] ∨ u = encOut tr₂ stA cl (tr₂.length + 2) := by
  dsimp only
  let tr₁ := (runMoves pre (setupTrace r)).1
  let m₀ := Move.aliceStart a r.bob idS 6 hb shown
  let tr₂ := (runMoves mid (m₀.next tr₁)).1
  let stA := iniAliceStartState tr₁ r.bob o
  let wrap := some (e, c')
  let m₁ := Move.encrypt a (tr₁.length + 8) cl (tr₂.length + 2) wrap
  have henc := encrypt_next_split38_eq_gen (cl := cl) wrap hm₀ hmid rfl; rw [runVis_split38_eq_gen hNe hpre hmid hpost, aliceStart_vis_eq, encrypt_vis_eq, henc, List.mem_append] at hv
  rcases hv with hv₀ | hv₁
  · rcases xpl_aliceVis_kind (List.mem_of_mem_take hv₀) with hk | hk <;> (rw [hkind] at hk; cases hk)
  · unfold encVis at hv₁; rw [List.mem_append] at hv₁; rcases hv₁ with hv_draws | hv_send
    · rcases mem_encDraws_encNextTr hv_draws with rfl | rfl <;> cases hkind
    · rw [mem_encSend_encNextTr_some hv_send] at hu; dsimp only at hu; rw [List.mem_append, List.mem_singleton] at hu; exact hu
theorem pt_terms_split38_mem_gen {r : Records} (hNe : r.alice ≠ r.bob) {a : Participant} {idS : Nat} {pre mid post : List Move} {hb : DY.Libsignal.PQXDH.BundleHandles} {shown cl : Nat} {wrap : Option (Nat × Nat)} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre) (hmid : MovesFrom InvisibleNoEffect ((Move.aliceStart a r.bob idS 6 hb shown).next (runMoves pre (setupTrace r)).1) mid) (hpost : MovesFrom InvisibleNoEffect ((Move.encrypt a ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart a r.bob idS 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) wrap).next (runMoves mid ((Move.aliceStart a r.bob idS 6 hb shown).next (runMoves pre (setupTrace r)).1)).1) post) (hm₀ : (Move.aliceStart a r.bob idS 6 hb shown).next (runMoves pre (setupTrace r)).1 = iniAliceStartTr (runMoves pre (setupTrace r)).1 a r.bob o) {v : VisEntry} (hv : v ∈ runVis r (pre ++ Move.aliceStart a r.bob idS 6 hb shown :: mid ++ Move.encrypt a ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart a r.bob idS 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) wrap :: post)) (hkind : v.kind = .pt) {u : DY.Bytes} (hu : u ∈ v.terms) : u = randTerm ((runMoves mid ((Move.aliceStart a r.bob idS 6 hb shown).next (runMoves pre (setupTrace r)).1)).1).length 32 := by
  let tr₁ := (runMoves pre (setupTrace r)).1
  let m₀ := Move.aliceStart a r.bob idS 6 hb shown
  let tr₂ := (runMoves mid (m₀.next tr₁)).1
  let stA := iniAliceStartState tr₁ r.bob o
  let m₁ := Move.encrypt a (tr₁.length + 8) cl (tr₂.length + 2) wrap
  have henc := encrypt_next_split38_eq_gen (cl := cl) wrap hm₀ hmid rfl; rw [runVis_split38_eq_gen hNe hpre hmid hpost, aliceStart_vis_eq, encrypt_vis_eq, henc, List.mem_append] at hv
  rcases hv with hv₀ | hv₁
  · rcases xpl_aliceVis_kind (List.mem_of_mem_take hv₀) with hk | hk <;> (rw [hkind] at hk; cases hk)
  · unfold encVis at hv₁; rw [List.mem_append] at hv₁; rcases hv₁ with hv_draws | hv_send
    · rcases mem_encDraws_encNextTr hv_draws with rfl | rfl
      · exact List.mem_singleton.mp hu
      · cases hkind
    · cases wrap with
      | none => rw [mem_encSend_encNextTr_none hv_send] at hkind; cases hkind
      | some ec => rcases ec with ⟨e, c⟩; rw [mem_encSend_encNextTr_some hv_send] at hkind; cases hkind
theorem tr₂_le_runTrace_split38 (r : Records) (pre mid post : List Move) (m₀ m₁ : Move) : (runMoves mid (m₀.next (runMoves pre (setupTrace r)).1)).1 ≤ runTraceMoves r (pre ++ m₀ :: mid ++ m₁ :: post) := by
  have htr : runTraceMoves r (pre ++ m₀ :: mid ++ m₁ :: post) =
      (runMoves post (m₁.next (runMoves mid (m₀.next (runMoves pre (setupTrace r)).1)).1)).1 := by
    rw [xpl_runTrace_eq]; simp only [runMoves_append_fst, runMoves]
  rw [htr]; exact Trace.le_trans _ _ _ (m₁.le_next _) (Symbolic.Swarm.CREF.runMoves_le post _)
theorem attackerKnows_of_mem_received {tr tr' : ExecTrace} {hs : List Nat} {u : DY.Bytes} (hle : tr ≤ tr') (hu : u ∈ received tr hs) : u.AttackerKnows tr' := by
  unfold received at hu; obtain ⟨idx, -, hidx⟩ := List.mem_filterMap.mp hu
  have hnet : NetMsgAt u idx tr := by
    unfold NetMsgAt; rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.getMessageSentAt_eq_at?] at hidx
    rcases hat : (tr.at? idx : Option DY.Network.ExecEntryT) with _ | ⟨m⟩ <;> rw [hat] at hidx
    · cases hidx
    · injection hidx with h; subst h; rfl
  exact (hnet.mono hle).attackerKnows
theorem forall2_append_inv' {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ l₂ : List α} {r₁ r₂ : List β}, l₁.length = r₁.length → List.Forall₂ R (l₁ ++ l₂) (r₁ ++ r₂) → List.Forall₂ R l₁ r₁ ∧ List.Forall₂ R l₂ r₂
  | [], _, [], _, _, h => ⟨List.Forall₂.nil, h⟩
  | _ :: _, _, [], _, hlen, _ => by simp at hlen
  | [], _, _ :: _, _, hlen, _ => by simp at hlen
  | _ :: _, _, _ :: _, _, hlen, List.Forall₂.cons hab hrest => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen; obtain ⟨h1, h2⟩ := forall2_append_inv' hlen hrest; exact ⟨List.Forall₂.cons hab h1, h2⟩
theorem encVis_encNextTr_length_le_three' (tr₂ : ExecTrace) (me : Participant) (sIdx : Nat) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) (wrap : Option (Nat × Nat)) : (encVis tr₂ (encNextTr tr₂ me sIdx stA cl pq) wrap true).length ≤ 3 := by
  unfold encVis encDraws encSend; rw [CompPrefixInvFresh.newRandoms_encNextTr, lastSent_encNextTr]
  cases wrap <;> by_cases hcl : (cl != 0) = true <;> simp [hcl]
theorem split38_forall2_vis_inv_gen
    {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} (hNe : r.alice ≠ r.bob)
    {a : Participant} {idS : Nat} {pre mid post : List Move} {hb : DY.Libsignal.PQXDH.BundleHandles}
    {shown cl e c' : Nat} {o : DY.Libsignal.PQXDH.AliceHandshakeOut}
    (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre)
    (hmid : MovesFrom InvisibleNoEffect ((Move.aliceStart a r.bob idS 6 hb shown).next (runMoves pre (setupTrace r)).1) mid)
    (hpost : MovesFrom InvisibleNoEffect ((Move.encrypt a ((runMoves pre (setupTrace r)).1.length + 8) cl
      ((runMoves mid ((Move.aliceStart a r.bob idS 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2)
      (some (e, c'))).next (runMoves mid ((Move.aliceStart a r.bob idS 6 hb shown).next (runMoves pre (setupTrace r)).1)).1) post)
    (hm₀ : (Move.aliceStart a r.bob idS 6 hb shown).next (runMoves pre (setupTrace r)).1 =
      iniAliceStartTr (runMoves pre (setupTrace r)).1 a r.bob o)
    {bun pt c w : HwBytes} {rs : List MachineEvent} (hrs : rs.length = 34)
    (hvis : List.Forall₂ (EventMatchesEntry i r S g) ((.recv bun :: rs) ++ [.pt pt, .rng c, .send w]) (runVis r (pre ++ Move.aliceStart a r.bob idS 6 hb shown :: mid ++ Move.encrypt a ((runMoves pre (setupTrace r)).1.length + 8) cl
          ((runMoves mid ((Move.aliceStart a r.bob idS 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2)
          (some (e, c')) :: post))) :
    let tr₁ := (runMoves pre (setupTrace r)).1
    let m₀ := Move.aliceStart a r.bob idS 6 hb shown
    let tr₂ := (runMoves mid (m₀.next tr₁)).1
    let stA := iniAliceStartState tr₁ r.bob o
    List.Forall₂ (EventMatchesEntry i r S g) (.recv bun :: rs) (aliceVis tr₁ (iniAliceStartTr tr₁ a r.bob o) hb) ∧
    List.Forall₂ (EventMatchesEntry i r S g) [.pt pt, .rng c, .send w]
      (encVis tr₂ (encNextTr tr₂ a (tr₁.length + 8) stA cl (tr₂.length + 2)) (some (e, c')) true) := by
  let tr₁ := (runMoves pre (setupTrace r)).1
  let m₀ := Move.aliceStart a r.bob idS 6 hb shown
  let tr₂ := (runMoves mid (m₀.next tr₁)).1
  let stA := iniAliceStartState tr₁ r.bob o
  let m₁ := Move.encrypt a (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c'))
  change List.Forall₂ (EventMatchesEntry i r S g) ((.recv bun :: rs) ++ [.pt pt, .rng c, .send w]) (runVis r (pre ++ m₀ :: mid ++ m₁ :: post)) at hvis; have henc := encrypt_next_split38_eq_gen (cl := cl) (some (e, c')) hm₀ hmid rfl
  have halice : m₀.vis tr₁ = (aliceVis tr₁ (iniAliceStartTr tr₁ a r.bob o) hb).take shown := by rw [aliceStart_vis_eq, hm₀]
  rw [runVis_split38_eq_gen hNe hpre hmid hpost, halice, encrypt_vis_eq, henc] at hvis
  have halice_len : (aliceVis tr₁ (iniAliceStartTr tr₁ a r.bob o) hb).length = 35 := by rw [CompPrefixInvAlice.aliceVis_iniAliceStartTr]; simp [kyberCoinEntries]
  have htake_le : ((aliceVis tr₁ (iniAliceStartTr tr₁ a r.bob o) hb).take shown).length ≤ 35 := by rw [List.length_take, halice_len]; exact Nat.min_le_right shown 35
  have henc_le := encVis_encNextTr_length_le_three' tr₂ a (tr₁.length + 8) stA cl (tr₂.length + 2) (some (e, c')); have htot := hvis.length_eq; rw [List.length_append, List.length_append] at htot
  have hlhs_len : (.recv bun :: rs : List MachineEvent).length = 35 := by simp [hrs]
  have hrhs_len : ([.pt pt, .rng c, .send w] : List MachineEvent).length = 3 := rfl; rw [hlhs_len, hrhs_len] at htot
  have htake_len : ((aliceVis tr₁ (iniAliceStartTr tr₁ a r.bob o) hb).take shown).length = 35 := by dsimp only [stA, tr₂, m₀, tr₁] at henc_le htake_le htot ⊢; omega
  have hshown : 35 ≤ shown := by rw [List.length_take, halice_len] at htake_len; omega
  have htake_eq : (aliceVis tr₁ (iniAliceStartTr tr₁ a r.bob o) hb).take shown = aliceVis tr₁ (iniAliceStartTr tr₁ a r.bob o) hb :=
    List.take_of_length_le (by omega)
  rw [htake_eq] at hvis; exact forall2_append_inv' (by rw [hlhs_len, halice_len]) hvis
theorem gamma_of_single {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ev : MachineEvent} {v : VisEntry} {t : DY.Bytes} (hl : v.layout = .single) (ht : v.terms = [t]) (hem : EventMatchesEntry i r S g ev v) : gamma i S g t = eventBytes ev := by
  obtain ⟨_, hmap⟩ := hem; rcases v with ⟨k, ts, lay, anc⟩; dsimp only at hl ht hmap; subst hl ht
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hmap; exact hmap
theorem encVis_coin_pin {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {tr₂ : ExecTrace} {me : Participant} {sIdx : Nat} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq e c' : Nat} {pt c w : HwBytes} (hm₁ : List.Forall₂ (EventMatchesEntry i r S g) [.pt pt, .rng c, .send w] (encVis tr₂ (encNextTr tr₂ me sIdx stA cl pq) (some (e, c')) true)) : cl ≠ 0 ∧ [gamma i S g (randTerm (tr₂.length + 1) cl)] = [c] := by
  unfold encVis encDraws encSend at hm₁; rw [CompPrefixInvFresh.newRandoms_encNextTr, lastSent_encNextTr] at hm₁
  by_cases hcl : (cl != 0) = true
  · simp only [List.filter_cons, hcl, ↓reduceIte, List.filter_nil, List.map_cons, List.map_nil, List.cons_append, List.nil_append] at hm₁
    obtain ⟨_, hm₂⟩ := List.forall₂_cons.mp hm₁; obtain ⟨hc, _⟩ := List.forall₂_cons.mp hm₂; exact ⟨bne_iff_ne.mp hcl, hc.2⟩
  · have hcl' : (cl != 0) = false := Bool.eq_false_iff.mpr hcl
    have hlen_eq := hm₁.length_eq; simp [hcl'] at hlen_eq
theorem encVis_pt_pin {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {tr₂ : ExecTrace} {me : Participant} {sIdx : Nat} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq e c' : Nat} {pt c w : HwBytes} (hm₁ : List.Forall₂ (EventMatchesEntry i r S g) [.pt pt, .rng c, .send w] (encVis tr₂ (encNextTr tr₂ me sIdx stA cl pq) (some (e, c')) true)) : gamma i S g (randTerm tr₂.length 32) = pt := by unfold encVis encDraws at hm₁; rw [CompPrefixInvFresh.newRandoms_encNextTr] at hm₁; obtain ⟨hem, -⟩ := List.forall₂_cons.mp hm₁; exact gamma_of_single rfl rfl hem
theorem newRandoms_attackerSend (t : DY.Bytes) (tr : ExecTrace) : newRandoms tr ((Move.attackerSend t).next tr) = [] := by
  have hn : (Move.attackerSend t).next tr = tr.append (⟨t⟩ : Network.ExecEntryT) := by
    unfold Move.next Move.act; rw [XplSteps.xrun_bind_unit]; exact (TR.Runs.sendMessage tr t).2
  rw [hn]
  have hlen : (tr.append (⟨t⟩ : Network.ExecEntryT)).length - tr.length = 1 := by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.length_append_entry_eq]; omega
  unfold newRandoms newIndices; rw [hlen]; simp only [List.range'_one, List.filterMap_cons, List.filterMap_nil, Symbolic.Swarm.CREF.at?_append_length]; rfl
theorem newRandoms_nil_of_leak {m : Move} {tr : ExecTrace} (hk : LeakKind m) (hex : exposures tr (m.next tr) = []) : newRandoms tr (m.next tr) = [] := by
  rcases XplSteps.xpl_leak_shape hk tr with h | h
  · rw [h]; exact XplSteps.xpl_newRandoms_self tr
  · exact absurd hex (XplSteps.xpl_exposures_ne_nil h)
theorem newRandoms_nil_of_vis_nil {m : Move} {tr : ExecTrace} (hs : m.isSetup = false) (ha : m.Anchored tr) (hv : m.vis tr = []) : newRandoms tr (m.next tr) = [] := by
  rcases CompPrefixInvBundle.next_of_isSetup_false_vis_nil hs ha hv with h | ⟨t, h⟩ | ⟨ev, h⟩
  · rw [h]; exact XplSteps.xpl_newRandoms_self tr
  · rw [h]
    have hlen : (tr.append (⟨t⟩ : Network.ExecEntryT)).length - tr.length = 1 := by
      rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.length_append_entry_eq]; omega
    unfold newRandoms newIndices; rw [hlen]; simp only [List.range'_one, List.filterMap_cons, List.filterMap_nil, Symbolic.Swarm.CREF.at?_append_length]; rfl
  · rw [h]
    have hlen : (tr.append (⟨ev⟩ : ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)).length - tr.length = 1 := by
      rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.length_append_entry_eq]; omega
    unfold newRandoms newIndices; rw [hlen]; simp only [List.range'_one, List.filterMap_cons, List.filterMap_nil, Symbolic.Swarm.CREF.at?_append_length]; rfl
theorem mem_newRandoms_of_randAt {tr t : ExecTrace} {j n : Nat} (h : RandAt t j n) (hj : tr.length ≤ j) : (randTerm j n, n) ∈ newRandoms tr t := by
  have hlt : j < t.length := XplSteps.xlt_of_at?_some h
  unfold newRandoms newIndices; refine List.mem_filterMap.mpr ⟨j, ?_, ?_⟩
  · rw [List.mem_range'_1]; omega
  · unfold RandAt at h; rw [h]; rfl
theorem randAt_or_mem_newRandoms {tr t : ExecTrace} (hle : tr ≤ t) {j n : Nat} (h : RandAt t j n) : RandAt tr j n ∨ (randTerm j n, n) ∈ newRandoms tr t := by
  by_cases hj : j < tr.length
  · left; have hlt : j < t.length := XplSteps.xlt_of_at?_some h; unfold RandAt at h ⊢; rw [← at?_eq_of_le_of_lt hle hj hlt]; exact h
  · exact Or.inr (mem_newRandoms_of_randAt h (by omega))
theorem randAt_of_next {m : Move} {tr : ExecTrace} (hs : m.isSetup = false) (ha : m.Anchored tr) (hv : m.vis tr = []) {j n : Nat} (h : RandAt (m.next tr) j n) : RandAt tr j n := by
  rcases randAt_or_mem_newRandoms (XplSteps.xrun_le m.act tr) h with h' | h'
  · exact h'
  · have h0 := newRandoms_nil_of_vis_nil hs ha hv
    change (randTerm j n, n) ∈ newRandoms tr (m.next tr) at h'; rw [h0] at h'; cases h'
theorem randAt_of_runMoves :
    ∀ (δ : List Move) (tr : ExecTrace), MovesFrom InvisibleNoEffect tr δ → MovesAnchored δ tr → (∀ m ∈ δ, m.isSetup = false) → ∀ {j n : Nat}, RandAt (runMoves δ tr).1 j n → RandAt tr j n
  | [], _, _, _, _, _, _, h => h
  | m :: δ, tr, ⟨hm, hδ⟩, ⟨ha, haδ⟩, hs, _, _, h =>
    randAt_of_next (hs m (List.mem_cons_self ..)) ha hm.1
      (randAt_of_runMoves δ (m.next tr) hδ haδ (fun m' hm' => hs m' (List.mem_cons_of_mem _ hm')) h)
theorem aesSafe_of_mem_newRandoms {i : ExternInterpretation} {S : Sem} {g : Ghost} {b : HwBytes} {tr t : ExecTrace} (hall : ∀ p ∈ newRandoms tr t, p.2 ≠ 0 → AesSafe b (gamma i S g p.1)) {j n : Nat} (hmem : (randTerm j n, n) ∈ newRandoms tr t) (hn : n ≠ 0) : AesSafe b (g.σ j n) := by
  have := hall _ hmem hn; rwa [gamma_randTerm_eq_σ j n hn] at this
theorem aesSafe_setup {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {b : HwBytes} (hc : Compat i r S g) (hwf : RecordsWF r) (hb6 : b.length ≤ 6) {j n : Nat} (hj : RandAt (setupTrace r) j n) (hn : n ≠ 0) : AesSafe b (g.σ j n) := by
  have hmem : randTerm j n ∈ setupRandoms r := List.mem_map.mpr ⟨_, mem_newRandoms_of_randAt (tr := Trace.nil) hj (by rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.length_nil_eq]; exact Nat.zero_le _), rfl⟩
  have key : ∀ ts sz : Nat, (ts, sz) ∈ setupRandomsAt r → (sz = 32 ∨ sz = 64) → randTerm j n = randTerm ts sz → AesSafe b (g.σ j n) := by
    intro ts sz hp hsz heq; have hsz0 : sz ≠ 0 := by omega
    have hγ : g.σ j n = g.σ ts sz := by rw [← gamma_randTerm_eq_σ (i := i) (S := S) j n hn, ← gamma_randTerm_eq_σ (i := i) (S := S) ts sz hsz0, heq]
    rw [hγ, hc.1 _ hp]; show AesSafe b (r.fresh ts sz); have hl : (r.fresh ts sz).length = sz := hwf.2.1 _ hp
    exact aesSafe_of_len hb6 (by rcases hsz with h | h <;> omega) (by rcases hsz with h | h <;> omega)
  rw [Symbolic.Swarm.CREF.TR.setupRandoms_eq r hwf.1] at hmem
  have hA : ∀ p ∈ ([(0, 32), (5, 32), (10, 32), (11, 64), (16, 64), (17, 64)] : List (Nat × Nat)),
      p ∈ setupRandomsAt r := fun p hp => by
    rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hwf.1]; exact List.mem_append_left _ hp
  split at hmem
  · have hopk : ((22 : Nat), (32 : Nat)) ∈ setupRandomsAt r := by
      rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hwf.1]; simp [*]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h | h | h | h | h
    · exact key 0 32 (hA _ (by simp)) (.inl rfl) h
    · exact key 5 32 (hA _ (by simp)) (.inl rfl) h
    · exact key 10 32 (hA _ (by simp)) (.inl rfl) h
    · exact key 11 64 (hA _ (by simp)) (.inr rfl) h
    · exact key 16 64 (hA _ (by simp)) (.inr rfl) h
    · exact key 17 64 (hA _ (by simp)) (.inr rfl) h
    · exact key 22 32 hopk (.inl rfl) h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h | h | h | h
    · exact key 0 32 (hA _ (by simp)) (.inl rfl) h
    · exact key 5 32 (hA _ (by simp)) (.inl rfl) h
    · exact key 10 32 (hA _ (by simp)) (.inl rfl) h
    · exact key 11 64 (hA _ (by simp)) (.inr rfl) h
    · exact key 16 64 (hA _ (by simp)) (.inr rfl) h
    · exact key 17 64 (hA _ (by simp)) (.inr rfl) h
theorem forall2_exists_left' {α β : Type} {R : α → β → Prop} {as : List α} {bs : List β} (h : List.Forall₂ R as bs) {y : β} (hy : y ∈ bs) : ∃ x ∈ as, R x y := by
  induction h with
  | nil => cases hy
  | cons hhead _ ih =>
    rcases List.mem_cons.mp hy with rfl | hmem
    · exact ⟨_, List.mem_cons_self .., hhead⟩
    · obtain ⟨x, hx, hr⟩ := ih hmem; exact ⟨x, List.mem_cons_of_mem _ hx, hr⟩
theorem forall2_append_drop_exists_left' {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys zs : List β}, List.Forall₂ R xs (ys ++ zs) → ∀ z ∈ zs, ∃ x ∈ xs.drop ys.length, R x z
  | _, [], _, h, _, hz => forall2_exists_left' h hz
  | _ :: _, _ :: _, _, .cons _ h, _, hz => forall2_append_drop_exists_left' h _ hz
theorem aliceDraws_aesSafe {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {tr₁ : ExecTrace} {a pB : Participant} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} {hb_h : DY.Libsignal.PQXDH.BundleHandles} {bun : HwBytes} {rs : List MachineEvent} {b : HwBytes} (hb6 : b.length ≤ 6) (hm₀ : List.Forall₂ (EventMatchesEntry i r S g) (.recv bun :: rs) (aliceVis tr₁ (CompPrefixInvAlice.iniAliceStartTr tr₁ a pB o) hb_h)) (hrs_ek : ∀ ev ∈ rs.take 1, AesSafe b (eventBytes ev)) (hrs_dhs : ∀ ev ∈ rs.drop 33, AesSafe b (eventBytes ev)) : ∀ p ∈ newRandoms tr₁ (CompPrefixInvAlice.iniAliceStartTr tr₁ a pB o), p.2 ≠ 0 → AesSafe b (gamma i S g p.1) := by
  rw [CompPrefixInvAlice.aliceVis_iniAliceStartTr] at hm₀; rw [CompPrefixInvAlice.newRandoms_iniAliceStartTr]
  cases hm₀ with
  | cons _ hm₁ =>
    cases hm₁ with
    | cons hem_ek hm_rest =>
      rename_i ev_ek rs_tail; intro p hp _; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · rw [gamma_of_single rfl rfl hem_ek]; exact hrs_ek ev_ek (by simp)
      · have hmem_ent : ({ kind := .rng, terms := [randTerm (tr₁.length + 1) 32], layout := .kyberCoin 0, anchor := none } : VisEntry) ∈
            kyberCoinEntries (randTerm (tr₁.length + 1) 32) ++ [{ rngEntry (randTerm (tr₁.length + 2) 32) with anchor := some (tr₁.length + 5) }] := by
          refine List.mem_append_left _ ?_; unfold kyberCoinEntries; exact List.mem_map.mpr ⟨0, by decide, rfl⟩
        obtain ⟨_, _, _, _, t, ht, hlen, _⟩ := forall2_exists_left' hm_rest hmem_ent
        injection ht with ht_eq; subst ht_eq; show AesSafe b (gamma i S g (randTerm (tr₁.length + 1) 32))
        have hlen' : (gamma i S g (randTerm (tr₁.length + 1) 32)).length = 32 := hlen
        exact aesSafe_of_len hb6 (by omega) (by omega)
      · obtain ⟨ev_dhs, hev_dhs_mem, hem_dhs⟩ := forall2_append_drop_exists_left' hm_rest
          ({ rngEntry (randTerm (tr₁.length + 2) 32) with anchor := some (tr₁.length + 5) } : VisEntry) (List.mem_singleton_self _)
        have hkl : (kyberCoinEntries (randTerm (tr₁.length + 1) 32)).length = 32 := by unfold kyberCoinEntries; simp
        rw [hkl] at hev_dhs_mem; rw [gamma_of_single rfl rfl hem_dhs]; exact hrs_dhs ev_dhs (by simpa using hev_dhs_mem)
theorem encDraws_aesSafe {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {tr₂ : ExecTrace} {me : Participant} {sIdx : Nat} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq e c' : Nat} {pt c w b : HwBytes} (hm₁ : List.Forall₂ (EventMatchesEntry i r S g) [.pt pt, .rng c, .send w] (encVis tr₂ (encNextTr tr₂ me sIdx stA cl pq) (some (e, c')) true)) (hpt : AesSafe b pt) (hc : AesSafe b c) : ∀ p ∈ newRandoms tr₂ (encNextTr tr₂ me sIdx stA cl pq), p.2 ≠ 0 → AesSafe b (gamma i S g p.1) := by
  obtain ⟨-, hcpin⟩ := encVis_coin_pin hm₁; have hptγ := encVis_pt_pin hm₁; rw [CompPrefixInvFresh.newRandoms_encNextTr]; intro p hp _; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · rw [hptγ]; exact hpt
  · rw [(List.cons.inj hcpin).1]; exact hc
theorem movesAnchored_append' :
    ∀ (ms₁ ms₂ : List Move) (tr : ExecTrace), MovesAnchored (ms₁ ++ ms₂) tr → MovesAnchored ms₁ tr ∧ MovesAnchored ms₂ (runMoves ms₁ tr).1
  | [], _, _, h => ⟨trivial, h⟩
  | m :: ms₁, ms₂, tr, ⟨ha, h⟩ => by obtain ⟨h1, h2⟩ := movesAnchored_append' ms₁ ms₂ (m.next tr) h; exact ⟨⟨ha, h1⟩, h2⟩
theorem randAt_or_mem_next {m : Move} {tr : ExecTrace} {j n : Nat} (h : RandAt (m.next tr) j n) : RandAt tr j n ∨ (randTerm j n, n) ∈ newRandoms tr (m.next tr) := randAt_or_mem_newRandoms (XplSteps.xrun_le m.act tr) h
attribute [local irreducible] Symbolic.BugInjection.hexBytes
theorem trace_take_38_eq : (Witnesses.Cheval26WeakStateIdx1.trace).take 38 = (.recv bundle0 :: call0Rng) ++ [.pt (ptAt 35), .rng (rngAt 36), .send (sendAt 37)] := rfl
def wire37Chars : List Char := chars_of_hex (sendAt 37)
theorem sendAt37_eq_hex : sendAt 37 = hexBytes (str_of_hex (sendAt 37)) := rfl
set_option maxRecDepth 200000 in theorem wire37Str_eq : (str_of_hex (sendAt 37)) = String.ofList wire37Chars := rfl
def wire37Fast : HwBytes := hexBytes.go hexDigit wire37Chars
theorem sendAt37_eq_fast : sendAt 37 = wire37Fast := by change sendAt 37 = hexBytes.go hexDigit wire37Chars; rw [sendAt37_eq_hex, wire37Str_eq, hexBytes_ofList]
set_option maxRecDepth 200000 in theorem wire37Fast_head? : wire37Fast.head? = some 0x03#8 := by decide +kernel
theorem sendAt37_head_ne_whisper : (sendAt 37).head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag := by rw [sendAt37_eq_fast, wire37Fast_head?]; decide
theorem call0Rng_take_1_ne_16 : ∀ e ∈ call0Rng.take 1, (eventBytes e).length ≠ 16 := by
  intro e he; rw [call0Rng_take_1_eq, List.mem_singleton] at he; subst he; show (rngAt 1).length ≠ 16; rw [rngAt1_length]; decide
theorem call0Rng_drop_33_ne_16 : ∀ e ∈ call0Rng.drop 33, (eventBytes e).length ≠ 16 := by
  intro e he; rw [call0Rng_drop_33_eq, List.mem_singleton] at he; subst he; show (rngAt 34).length ≠ 16; rw [rngAt34_length]; decide
theorem rngAt36_gt_6 : 6 < (rngAt 36).length := by rw [rngAt36_length]; decide
theorem rngAt36_ne_16 : (rngAt 36).length ≠ 16 := by rw [rngAt36_length]; decide
theorem eventBytes_eq_census443 (e : MachineEvent) : eventBytes e = Census443Defs.eventBytes e := by cases e <;> rfl
attribute [local irreducible] bundle0 call0Rng ptAt rngAt sendAt setupPublic setupSecret
theorem ptAvoidFull_prefixTerms_of_pre38PrefixInv_cref {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (hcompat : Compat compI0 r S g) (hwf : RecordsWF r) (hb : b = ptAt 38 ∨ b = ptAt 78) (hinv : Pre38PrefixInv r S g ms b) : ∀ u ∈ prefixTerms r (runTraceMoves r ms) (runVis r ms), PtAvoidFull compI0 r S g ms b u := by
  obtain ⟨hb6, _, hb32⟩ := ptAt38_or_ptAt78_len hb
  have hrs_ek : ∀ e ∈ call0Rng.take 1, b.length < (Common443.Census443Defs.eventBytes e).length :=
    fun e he => Nat.lt_of_le_of_lt hb6 (call0Rng_take_1_gt_6 e he)
  have hrs_dhs : ∀ e ∈ call0Rng.drop 33, b.length < (Common443.Census443Defs.eventBytes e).length :=
    fun e he => Nat.lt_of_le_of_lt hb6 (call0Rng_drop_33_gt_6 e he)
  refine ptAvoidFull_prefixTerms ?_ ?_ (ptAvoidFull_storedSecrets_of_inv hcompat hwf hb32 hinv.1) (ptAvoidFull_ptVis_of_randTermsInv hinv.2.2.2)
  · intro v hv hk u hu
    rcases hinv.2.2.1 v hv hk u hu with hav | ⟨tr₁, tr₂, a, ikA, hb_h, cl₁, hid, hm₀_vis, hpt_pin, hcpin, rfl⟩
    · exact hav
    · exact ptAvoidFull_encOut_of_aliceVis hcompat hwf hb hid hm₀_vis hrs_ek hrs_dhs (ptAvoidFull_randTerm_of_mem_rng36_inits hb hcpin) hpt_pin
  · intro ls hls
    obtain ⟨tr₁, a, ikA, hb_h, hid, hm₀_vis, hcases⟩ := hinv.2.1 ls hls
    rcases hcases with rfl | ⟨tr₂, cl₁, hcpin, rfl⟩
    · exact ptAvoidFull_iniAliceStartState_of_aliceVis hcompat hwf hb32 hid hm₀_vis hrs_ek hrs_dhs
    · exact ptAvoidFull_encSt_of_aliceVis hcompat hwf hb32 hid hm₀_vis hrs_ek hrs_dhs (ptAvoidFull_randTerm_of_mem_rng36_inits hb hcpin)
theorem invert_send_rs_move_opt {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {tr : ExecTrace} {m : Move} {pt w : HwBytes} {rs₁ : List MachineEvent} (hm : List.Forall₂ (EventMatchesEntry i r S g) (.pt pt :: (rs₁ ++ [.send w])) (m.vis tr)) : ∃ me sIdx cl pq wrap, m = .encrypt me sIdx cl pq wrap ∧ lastSent tr (m.next tr) ≠ none ∧ (wrap = none → w.head? = some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag) ∧ List.Forall₂ (EventMatchesEntry i r S g) (.pt pt :: (rs₁ ++ [.send w])) (encVis tr (m.next tr) wrap true) := by
  obtain ⟨v_s, hv_s, hev_s⟩ := xpl_forall₂_mem_left hm (.send w) (by simp); have hvk_s : v_s.kind = .send := xpl_kind_of_matches hev_s
  obtain ⟨me, sIdx, cl, pq, wrap, rfl⟩ : ∃ me sIdx cl pq wrap, m = .encrypt me sIdx cl pq wrap := by
    rcases xpl_vis_kind m tr hv_s with h | ⟨_, h | h | ⟨_, h⟩⟩ | ⟨_, h | h | h⟩ <;>
      first | exact h | (rw [hvk_s] at h; cases h)
  have hvis : (Move.encrypt me sIdx cl pq wrap).vis tr =
      encVis tr ((Move.encrypt me sIdx cl pq wrap).next tr) wrap true := by
    rw [xpl_vis_eq, exposures_nil_of_not_leakKind (m := .encrypt me sIdx cl pq wrap) rfl (fun h => nomatch h), List.append_nil]; rfl
  rw [hvis] at hm hv_s
  have hls : lastSent tr ((Move.encrypt me sIdx cl pq wrap).next tr) ≠ none ∧
      (wrap = none → w.head? = some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag) := by
    unfold encVis at hv_s; simp only [↓reduceIte, List.mem_append] at hv_s
    rcases hv_s with hd | hsnd
    · rcases encDraws_kind _ hd with hk | hk <;> (rw [hvk_s] at hk; cases hk)
    · unfold encSend at hsnd
      rcases hls_eq : lastSent tr ((Move.encrypt me sIdx cl pq wrap).next tr) with _ | wt
      · rw [hls_eq] at hsnd; cases hsnd
      · refine ⟨by simp, fun hw_none => ?_⟩; rw [hls_eq, hw_none, List.mem_singleton] at hsnd; subst hsnd; obtain ⟨_, t, _, hw_eq⟩ := hev_s; change w = _ at hw_eq; rw [hw_eq]; rfl
  exact ⟨me, sIdx, cl, pq, wrap, rfl, hls.1, hls.2, hm⟩
open CompPrefixInvStruct CompPrefixInvAlice CompPrefixInvBundle CompPrefixInvEnc in
theorem pia_x0_decomp_rs {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {bun : HwBytes} {rs rs₁ : List MachineEvent} {pt w : HwBytes} (hNe : r.alice ≠ r.bob) (hnb : CompSetupSecrecy.NoBrk r ms) (hmp : Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms ((.recv bun :: rs) ++ (.pt pt :: (rs₁ ++ [.send w])))) (hrs_len : rs.length = 34) (hrs_kind : ∀ e ∈ rs, eventKind e = .rng) (hrs₁_kind : ∀ e ∈ rs₁, eventKind e = .rng) (hbun4 : bun[4]? ≠ some 1#8) (hw : w.head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag) :
    ∃ (pre : List Move) (a : Participant) (idS : Nat) (hb : DY.Libsignal.PQXDH.BundleHandles) (shown : Nat) (mid : List Move) (cl e c' : Nat) (post : List Move) (ikA : DY.Bytes) (tr₁ tr₂ : ExecTrace) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (stA : DY.Libsignal.TripleRatchet.TRState),
      tr₁ = (runMoves pre (setupTrace r)).1 ∧ o = iniAliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none ∧
      stA = iniAliceStartState tr₁ r.bob o ∧ tr₂ = (runMoves mid ((Move.aliceStart a r.bob idS 6 hb shown).next tr₁)).1 ∧
      ms = pre ++ .aliceStart a r.bob idS 6 hb shown :: mid ++ .encrypt a (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c')) :: post ∧
      (ikA = setupSecret r 0 ∨ ikA = setupSecret r 1) ∧
      List.Forall₂ (EventMatchesEntry compI0 r S g) (.recv bun :: rs) (aliceVis tr₁ ((Move.aliceStart a r.bob idS 6 hb shown).next tr₁) hb) ∧
      List.Forall₂ (EventMatchesEntry compI0 r S g) (.pt pt :: (rs₁ ++ [.send w])) (encVis tr₂ (encNextTr tr₂ a (tr₁.length + 8) stA cl (tr₂.length + 2)) (some (e, c')) true) ∧
      (Move.aliceStart a r.bob idS 6 hb shown).next tr₁ = iniAliceStartTr tr₁ a r.bob o ∧
      MovesFrom InvisibleNoEffect (setupTrace r) pre ∧
      MovesFrom InvisibleNoEffect ((Move.aliceStart a r.bob idS 6 hb shown).next tr₁) mid ∧
      MovesFrom InvisibleNoEffect ((Move.encrypt a (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c'))).next tr₂) post := by
  let blk₁ : List MachineEvent := .recv bun :: rs
  let blk₂ : List MachineEvent := .pt pt :: (rs₁ ++ [.send w])
  have hhead₂ : ∀ e ∈ blk₂.head?, eventKind e = .recv ∨ eventKind e = .pt := by intro e he; simp [blk₂] at he; subst he; exact Or.inr rfl
  obtain ⟨ms₁, δ₂, hms, hmp₁, hfor₂⟩ := matchedPrefix6_split hmp hhead₂ (matchedPrefix6_prefix_reachable hmp)
  have hB₂ : XplBlock6 compI0 r S g ms₁ δ₂ blk₁ blk₂ := ⟨hmp₁, hms ▸ hmp.2.1, hfor₂⟩
  have hhead₁ : ∀ e ∈ blk₁.head?, eventKind e = .recv ∨ eventKind e = .pt := by intro e he; simp [blk₁] at he; subst he; exact Or.inl rfl
  have hmp₁' : Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms₁ ([] ++ blk₁) := by simpa using hmp₁
  obtain ⟨ms₀, δ₁, hms₁, hmp₀, hfor₁⟩ := matchedPrefix6_split hmp₁' hhead₁ (matchedPrefix6_prefix_reachable hmp₁')
  have hB₁ : XplBlock6 compI0 r S g ms₀ δ₁ [] blk₁ := ⟨hmp₀, hms₁ ▸ hmp₁.2.1, hfor₁⟩
  have htail₁ : ∀ e ∈ blk₁.tail, eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak := by intro e he; rw [hrs_kind e he]; decide
  obtain ⟨pre₁, m₀, post₁, rfl, hpre₁, ⟨hs₀, ha₀, hm₀⟩, hpost₁⟩ := xpl6_oneMove hB₁ hhead₁ (by simp [blk₁]) htail₁
  have htail₂ : ∀ e ∈ blk₂.tail, eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak := by
    intro e he; simp only [blk₂, List.tail_cons, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · rw [hrs₁_kind e he]; decide
    · dsimp [eventKind]; decide
  obtain ⟨pre₂, m₁, post₂, rfl, hpre₂, ⟨_, _, hm₁⟩, hpost₂⟩ := xpl6_oneMove hB₂ hhead₂ (by simp [blk₂]) htail₂
  let pre := ms₀ ++ pre₁; let mid := post₁ ++ pre₂; let tr₁ := (runMoves pre (setupTrace r)).1
  have htr₁_eq : (runMoves pre₁ (runTraceMoves r ms₀)).1 = tr₁ := by dsimp [tr₁, pre]; rw [runMoves_append_fst, ← xpl_runTrace_eq]
  rw [htr₁_eq] at ha₀ hm₀ hpost₁
  have hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre := by rw [movesFrom_append, ← xpl_runTrace_eq]; exact ⟨movesFrom_invisibleNoEffect_of_matchedPrefix_nil hmp₀, hpre₁⟩
  let tr₂ := (runMoves mid (m₀.next tr₁)).1
  have hms₁_eq : ms₁ = pre ++ m₀ :: post₁ := by simp [hms₁, pre, List.append_assoc]
  have hrun_ms₁ : runTraceMoves r ms₁ = (runMoves post₁ (m₀.next tr₁)).1 := by rw [hms₁_eq, xpl_runTrace_eq, runMoves_append_fst, runMoves_cons_fst]
  have htr₂_eq : (runMoves pre₂ (runTraceMoves r ms₁)).1 = tr₂ := by dsimp [tr₂, mid]; rw [runMoves_append_fst, ← hrun_ms₁]
  rw [htr₂_eq] at hm₁ hpost₂
  have hmid : MovesFrom InvisibleNoEffect (m₀.next tr₁) mid := by rw [movesFrom_append, ← hrun_ms₁]; exact ⟨hpost₁, hpre₂⟩
  obtain ⟨me, sIdx, cl, pq, wrap, rfl, hls, hwrap_none, hm₁_vis⟩ := invert_send_rs_move_opt hm₁
  rcases wrap with _ | ⟨e, c'⟩
  · exact absurd (hwrap_none rfl) hw
  have hneff : ¬ NoSessionEffect tr₁ m₀ := by
    intro heff
    have hno₁ : NoTRState tr₁ := noTRState_of_movesFrom_invisibleNoEffect (noTRState_setupTrace r) hpre
    have hno_m₀ : NoTRState (m₀.next tr₁) := noTRState_of_noSessionEffect hno₁ heff
    have hno₂ : NoTRState tr₂ := noTRState_of_movesFrom_invisibleNoEffect hno_m₀ hmid
    exact hls (encrypt_lastSent_none_of_noTRState hno₂ me sIdx cl pq (some (e, c')))
  obtain ⟨a, b, idS, regB, hb, shown, rfl, _, hdone, hm₀_vis⟩ := invert_ini_move_of_not_noSessionEffect hs₀ ha₀ hm₀ hrs_len hrs_kind hneff
  have hms_eq : ms = pre ++ .aliceStart a b idS regB hb shown :: mid ++ .encrypt me sIdx cl pq (some (e, c')) :: post₂ := by simp [hms, hms₁, pre, mid, List.append_assoc]
  have hms_split : ms = pre ++ (.aliceStart a b idS regB hb shown :: mid ++ .encrypt me sIdx cl pq (some (e, c')) :: post₂) := by simp [hms_eq, List.append_assoc]
  have hreach₁ : tr₁.Reachable reachability := by change (runMoves pre (setupTrace r)).1.Reachable reachability; rw [← xpl_runTrace_eq]; exact matchedPrefix6_prefix_reachable hmp pre _ hms_split
  have hs_pre : ∀ m ∈ pre, m.isSetup = false := fun m hm => hmp.2.1.2.1 m (by rw [hms_split]; exact List.mem_append_left _ hm)
  have ha_pre : MovesAnchored pre (setupTrace r) := by have ha_all := hmp.2.1.2.2.1.2.1; rw [hms_split] at ha_all; exact (movesAnchored_append' pre _ (setupTrace r) ha_all).1
  have hnb_pre : CompSetupSecrecy.NoBrk r pre := CompSetupSecrecy.noBrk_of_le (by rw [hms_split, CompPrefixInvStruct.runTrace_append r pre]; exact Symbolic.Swarm.CREF.runMoves_le _ _) hnb
  obtain ⟨rfl, rfl, _, _, ikA, _, _, hdisj, _, _, _, _, _, _, _, hnext₀⟩ := pia_bundle_inv hNe hnb_pre hs_pre ha_pre hpre hreach₁ hdone hm₀_vis hbun4
  rw [CompRX0NBSC38.aliceStartTrOfOut_eq_ini] at hnext₀; rw [CompRX0Join.aliceOut_eq_iniAliceOut] at hnext₀
  have hid : ikA = setupSecret r 0 ∨ ikA = setupSecret r 1 := by rcases hdisj with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> [exact .inl h; exact .inr h]
  let o := iniAliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
  let stA := iniAliceStartState tr₁ r.bob o
  have hown : ownSaltsFrom (setupTrace r) ms = true := hmp.2.1.2.2.2.2.1
  have hntr : NoTRState tr₁ := noTRState_of_movesFrom_invisibleNoEffect (noTRState_setupTrace r) hpre
  have hek₁ : NetMsgAt o.ek (tr₁.length + 3) ((Move.aliceStart a r.bob idS 6 hb shown).next tr₁) := by rw [hnext₀]; exact netMsgAt_ek_iniAliceStartTr _ _ _ _
  have hct₁ : NetMsgAt o.ct (tr₁.length + 4) ((Move.aliceStart a r.bob idS 6 hb shown).next tr₁) := by rw [hnext₀]; exact netMsgAt_ct_iniAliceStartTr _ _ _ _
  have hst₁ : ∀ j : Nat, (((Move.aliceStart a r.bob idS 6 hb shown).next tr₁).at? j : Option TRStEntry) = if j = tr₁.length + 8 then some (TRStE a stA) else none := by rw [hnext₀]; exact at?_trSt_iniAliceStartTr_of_noTRState hntr _ _ _
  obtain ⟨_, hme, hsIdx, hpq, _, hnext₁, _, _, _, _, _, _, _, _, _, _⟩ := pia_enc_inv (stA := stA) hms_eq hpre hmid hpost₂ hown hek₁ hct₁ hst₁ hls
  subst hme hsIdx hpq; rw [hnext₁] at hm₁_vis
  exact ⟨pre, me, idS, hb, shown, mid, cl, e, c', post₂, ikA, tr₁, tr₂, o, stA, rfl, rfl, rfl, rfl, hms_eq, hid, hm₀_vis, hm₁_vis, hnext₀, hpre, hmid, hpost₂⟩
theorem encVis_rs_cases {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {tr₂ : ExecTrace} {me : Participant} {sIdx : Nat} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {wrap : Option (Nat × Nat)} {pt w : HwBytes} {rs₁ : List MachineEvent} (hrs₁_kind : ∀ e ∈ rs₁, eventKind e = .rng) (hm₁ : List.Forall₂ (EventMatchesEntry i r S g) (.pt pt :: (rs₁ ++ [.send w])) (encVis tr₂ (encNextTr tr₂ me sIdx stA cl pq) wrap true)) : gamma i S g (randTerm tr₂.length 32) = pt ∧ ((cl = 0 ∧ rs₁ = []) ∨ (cl ≠ 0 ∧ ∃ c : HwBytes, rs₁ = [.rng c] ∧ [gamma i S g (randTerm (tr₂.length + 1) cl)] = [c])) := by
  unfold encVis encDraws encSend at hm₁; rw [CompPrefixInvFresh.newRandoms_encNextTr, lastSent_encNextTr] at hm₁
  obtain ⟨hem_pt, hm_rest⟩ := List.forall₂_cons.mp hm₁
  refine ⟨gamma_of_single rfl rfl hem_pt, ?_⟩
  by_cases hcl : (cl != 0) = true
  · simp only [List.filter_cons, hcl, ↓reduceIte, List.filter_nil, List.map_cons, List.map_nil] at hm_rest
    have hlen := hm_rest.length_eq
    rcases rs₁ with _ | ⟨ev_c, _ | ⟨ev2, _⟩⟩
    · exfalso; cases wrap <;> simp at hlen
    · obtain ⟨hc, _⟩ := List.forall₂_cons.mp hm_rest
      have hk : eventKind ev_c = .rng := hrs₁_kind ev_c (List.mem_singleton_self _)
      cases ev_c <;> try cases hk
      rename_i c
      exact Or.inr ⟨bne_iff_ne.mp hcl, c, rfl, hc.2⟩
    · exfalso; cases wrap <;> simp at hlen
  · have hcl' : (cl != 0) = false := Bool.eq_false_iff.mpr hcl
    have hcl0 : cl = 0 := by rcases Nat.eq_zero_or_pos cl with rfl | hpos; rfl; exfalso; apply hcl; simp [Nat.ne_of_gt hpos]
    simp only [List.filter_cons, hcl', Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.map_nil] at hm_rest
    have hlen := hm_rest.length_eq
    have hrs₁_nil : rs₁ = [] := by cases wrap <;> simp at hlen <;> exact hlen
    exact Or.inl ⟨hcl0, hrs₁_nil⟩
theorem encDraws_aesSafe_rs {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {tr₂ : ExecTrace} {me : Participant} {sIdx : Nat} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {wrap : Option (Nat × Nat)} {pt w b : HwBytes} {rs₁ : List MachineEvent} (hrs₁_kind : ∀ e ∈ rs₁, eventKind e = .rng) (hm₁ : List.Forall₂ (EventMatchesEntry i r S g) (.pt pt :: (rs₁ ++ [.send w])) (encVis tr₂ (encNextTr tr₂ me sIdx stA cl pq) wrap true)) (hpt : AesSafe b pt) (hc_safe : ∀ c, .rng c ∈ rs₁ → AesSafe b c) : ∀ p ∈ newRandoms tr₂ (encNextTr tr₂ me sIdx stA cl pq), p.2 ≠ 0 → AesSafe b (gamma i S g p.1) := by
  obtain ⟨hptγ, ⟨hcl0, _⟩ | ⟨_, c, hrs₁_eq, hcpin⟩⟩ := encVis_rs_cases hrs₁_kind hm₁ <;>
    (rw [CompPrefixInvFresh.newRandoms_encNextTr]; intro p hp hn0; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl)
  · rw [hptγ]; exact hpt
  · exact absurd hcl0 hn0
  · rw [hptγ]; exact hpt
  · rw [(List.cons.inj hcpin).1]; exact hc_safe c (by rw [hrs₁_eq]; simp)
theorem take38_inv_cref_rs {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {rs₁ : List MachineEvent} {b : HwBytes} (hwf : RecordsWF r) (hnb : CompSetupSecrecy.NoBrk r ms) (hrs₁_kind : ∀ e ∈ rs₁, eventKind e = .rng) (hrs₁_inits : ∀ c, .rng c ∈ rs₁ → c ∈ (rngAt 36).inits) (hmp : Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms ((.recv bundle0 :: call0Rng) ++ (.pt (ptAt 35) :: (rs₁ ++ [.send (sendAt 37)])))) (hb : b = ptAt 38 ∨ b = ptAt 78) : RunRandSafe g b (runTraceMoves r ms) ∧ NoSKS (runTraceMoves r ms) ∧ Pre38PrefixInv r S g ms b ∧ (∀ v ∈ runVis r ms, v.kind ≠ .leak) ∧ (∀ u : DY.Bytes, (runTraceMoves r ms).BaseAttackerKnows u → PtAvoidFull compI0 r S g ms b u) ∧ (∀ u ∈ prefixTerms r (runTraceMoves r ms) (runVis r ms), PtAvoidFull compI0 r S g ms b u) := by
  have hNe : r.alice ≠ r.bob := hwf.1; obtain ⟨hb6, _, hb32⟩ := ptAt38_or_ptAt78_len hb; have hc : Compat compI0 r S g := hmp.1; have hmr : ModelRun r ms := hmp.2.1
  obtain ⟨pre, a, idS, hb_h, shown, mid, cl, e, c', post, ikA, tr₁, tr₂, o, stA, htr₁, ho, hstA, htr₂, hms, hid, hvis₀, hm₁, hm₀, hpre, hmid, hpost⟩ := pia_x0_decomp_rs hNe hnb hmp call0Rng_length call0Rng_kind hrs₁_kind bundle0_byte4_ne_one sendAt37_head_ne_whisper; clear hmp
  have hns : ∀ m ∈ ms, m.isSetup = false := hmr.2.1; have hanc : MovesAnchored ms (setupTrace r) := hmr.2.2.1.2.1
  have hvA : List.Forall₂ (EventMatchesEntry compI0 r S g) (.recv bundle0 :: call0Rng)
      (aliceVis tr₁ (CompPrefixInvAlice.iniAliceStartTr tr₁ a r.bob o) hb_h) := by rw [← hm₀]; exact hvis₀
  have henc := encrypt_next_split38_eq_gen (cl := cl) (some (e, c')) hm₀ hmid htr₂
  have htr : runTraceMoves r ms = (runMoves post ((Move.encrypt a (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c'))).next tr₂)).1 := by subst htr₁ htr₂ hms; rw [xpl_runTrace_eq]; simp only [runMoves_append_fst, runMoves]
  have hrs : RunRandSafe g b (runTraceMoves r ms) := by
    rw [hms] at hanc hns; obtain ⟨hanc01, hanc1⟩ := movesAnchored_append' _ _ _ hanc; obtain ⟨hancP, hanc0⟩ := movesAnchored_append' _ _ _ hanc01
    have hancPost : MovesAnchored post ((Move.encrypt a (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c'))).next tr₂) := by
      have h := hanc1.2; rw [runMoves_append_fst, ← htr₁] at h
      have h2 : (runMoves (Move.aliceStart a r.bob idS 6 hb_h shown :: mid) tr₁).1 = tr₂ := by rw [htr₂]; rfl
      rw [h2] at h; exact h
    have hancMid : MovesAnchored mid ((Move.aliceStart a r.bob idS 6 hb_h shown).next tr₁) := by rw [htr₁]; exact hanc0.2
    have hnsPre : ∀ m ∈ pre, m.isSetup = false := fun m hm => hns m (by simp [hm])
    have hnsMid : ∀ m ∈ mid, m.isSetup = false := fun m hm => hns m (by simp [hm])
    have hnsPost : ∀ m ∈ post, m.isSetup = false := fun m hm => hns m (by simp [hm])
    have hek_safe : ∀ ev ∈ call0Rng.take 1, AesSafe b (eventBytes ev) := by
      intro ev hev; refine aesSafe_of_len hb6 ?_ (call0Rng_take_1_ne_16 ev hev)
      rw [eventBytes_eq_census443]; exact call0Rng_take_1_gt_6 ev hev
    have hdhs_safe : ∀ ev ∈ call0Rng.drop 33, AesSafe b (eventBytes ev) := by
      intro ev hev; refine aesSafe_of_len hb6 ?_ (call0Rng_drop_33_ne_16 ev hev)
      rw [eventBytes_eq_census443]; exact call0Rng_drop_33_gt_6 ev hev
    have hpt_safe : AesSafe b (ptAt 35) := by rw [ptAt35_eq_compAesPt1]; exact aesSafe_compAesPt1 hb
    have hc_safe : ∀ c, .rng c ∈ rs₁ → AesSafe b c := fun c hc => mem_rng36_inits_ne_and_perm_ne hb (hrs₁_inits c hc)
    have hA := aliceDraws_aesSafe hb6 hvA hek_safe hdhs_safe
    have hE := encDraws_aesSafe_rs hrs₁_kind hm₁ hpt_safe hc_safe
    intro j n hj hn; rw [htr] at hj; have hj1 := randAt_of_runMoves post _ hpost hancPost hnsPost hj
    rcases randAt_or_mem_next hj1 with hj2 | hmem
    · rw [htr₂] at hj2; have hj3 := randAt_of_runMoves mid _ hmid hancMid hnsMid hj2
      rcases randAt_or_mem_next hj3 with hj4 | hmem
      · rw [htr₁] at hj4; exact aesSafe_setup hc hwf hb6 (randAt_of_runMoves pre _ hpre hancP hnsPre hj4) hn
      · rw [hm₀] at hmem; exact aesSafe_of_mem_newRandoms hA hmem hn
    · rw [henc, ← hstA] at hmem; exact aesSafe_of_mem_newRandoms hE hmem hn
  have hsks : NoSKS (runTraceMoves r ms) := by
    have h₁ : NoSKS tr₁ := by rw [htr₁]; exact noSKS_of_movesFrom_invisibleNoEffect (noSKS_setupTrace r) hpre
    have h₂ : NoSKS tr₂ := by rw [htr₂]; refine noSKS_of_movesFrom_invisibleNoEffect ?_ hmid; rw [hm₀]; exact noSKS_iniAliceStartTr h₁ _ _ _
    rw [htr]; refine noSKS_of_movesFrom_invisibleNoEffect ?_ hpost; rw [henc]; exact noSKS_encNextTr h₂ _ _ _ _ _
  obtain ⟨hpt_pin, hcl_cases⟩ := encVis_rs_cases hrs₁_kind hm₁
  have hcpin : cl = 0 ∨ gamma compI0 S g (randTerm (tr₂.length + 1) cl) ∈ (rngAt 36).inits := by
    rcases hcl_cases with ⟨hcl0, _⟩ | ⟨_, c, hrs₁_eq, hpin⟩
    · exact Or.inl hcl0
    · refine Or.inr ?_; rw [(List.cons.inj hpin).1]; exact hrs₁_inits c (by rw [hrs₁_eq]; simp)
  have hrs_ek : ∀ ev ∈ call0Rng.take 1, b.length < (Census443Defs.eventBytes ev).length :=
    fun ev hev => Nat.lt_of_le_of_lt hb6 (call0Rng_take_1_gt_6 ev hev)
  have hrs_dhs : ∀ ev ∈ call0Rng.drop 33, b.length < (Census443Defs.eventBytes ev).length :=
    fun ev hev => Nat.lt_of_le_of_lt hb6 (call0Rng_drop_33_gt_6 ev hev)
  have hst : ∀ ls ∈ storedStates r (runTraceMoves r ms), PtAvoidFull compI0 r S g ms b (Comparse.serialize ls) := by
    intro ls hls; subst htr₁ htr₂ hms ho hstA
    rcases storedStates_split38_cases_gen hpre hmid hpost hm₀ hls with h | h <;> rw [h]
    · exact ptAvoidFull_iniAliceStartState_of_aliceVis hc hwf hb32 hid hvA hrs_ek hrs_dhs
    · exact ptAvoidFull_encSt_of_aliceVis hc hwf hb32 hid hvA hrs_ek hrs_dhs (ptAvoidFull_randTerm_of_mem_rng36_inits hb hcpin)
  have hnoleak : ∀ v ∈ runVis r ms, v.kind ≠ .leak := by subst htr₁ htr₂ hms; exact vis_kind_ne_leak_split38_gen hNe hpre hmid hpost
  have hbase := hbase_of_runFacts_no_leak hmr hc hwf hb hst hsks hnoleak hnb hrs
  have hinv : Pre38PrefixInv r S g ms b := by
    refine ⟨PtPrefixInv35.storedSecrets_inv_of_no_setup hwf hmr.2.1 hmr.2.2.1.1, ?_, ?_, ?_⟩
    · intro ls hls; subst htr₁ htr₂ hms ho hstA
      rcases storedStates_split38_cases_gen hpre hmid hpost hm₀ hls with h | h
      · exact ⟨_, a, ikA, hb_h, hid, hvA, .inl h⟩
      · exact ⟨_, a, ikA, hb_h, hid, hvA, .inr ⟨_, cl, hcpin, h⟩⟩
    · intro v hv hk u hu; subst htr₁ htr₂ hms ho hstA
      rcases send_terms_split38_mem_wrap_gen hNe hpre hmid hpost hm₀ hv hk hu with hr | he
      · exact .inl (ptAvoidFull_of_attackerKnows hbase (attackerKnows_of_mem_received (tr₂_le_runTrace_split38 r pre mid post _ _) hr))
      · exact .inr ⟨_, _, a, ikA, hb_h, cl, hid, hvA, hpt_pin, hcpin, he⟩
    · intro v hv hk u hu; subst htr₁ htr₂ hms; exact ⟨_, 32, pt_terms_split38_mem_gen hNe hpre hmid hpost hm₀ hv hk hu⟩
  exact ⟨hrs, hsks, hinv, hnoleak, hbase, ptAvoidFull_prefixTerms_of_pre38PrefixInv_cref hc hwf hb hinv⟩
theorem self_mem_inits {α : Type} : ∀ l : List α, l ∈ l.inits
  | [] => List.mem_singleton_self []
  | _ :: l => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨l, self_mem_inits l, rfl⟩)
theorem take38_inv_cref {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (hwf : RecordsWF r) (hnb : CompSetupSecrecy.NoBrk r ms) (hmp : Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms (trace.take 38)) (hb : b = ptAt 38 ∨ b = ptAt 78) : RunRandSafe g b (runTraceMoves r ms) ∧ NoSKS (runTraceMoves r ms) ∧ Pre38PrefixInv r S g ms b ∧ (∀ v ∈ runVis r ms, v.kind ≠ .leak) ∧ (∀ u : DY.Bytes, (runTraceMoves r ms).BaseAttackerKnows u → PtAvoidFull compI0 r S g ms b u) ∧ (∀ u ∈ prefixTerms r (runTraceMoves r ms) (runVis r ms), PtAvoidFull compI0 r S g ms b u) := by
  rw [trace_take_38_eq] at hmp
  exact take38_inv_cref_rs (rs₁ := [.rng (rngAt 36)]) hwf hnb
    (fun e he => by simp at he; subst he; rfl)
    (fun c hc => by simp at hc; subst hc; exact self_mem_inits _) hmp hb
theorem pre38PrefixInv_ws {r : Records} {S : Sem} {who₀ : List Participant} {g : Ghost} {ms : List Move} {b : HwBytes} (hwf : RecordsWF r) (hnb : CompSetupSecrecy.NoBrk r ms) (hmp : MatchedPrefix compI0 r S who₀ g ms (trace.take 38)) (hb : b = ptAt 38 ∨ b = ptAt 78) : Pre38PrefixInv r S g ms b := (take38_inv_cref hwf hnb (Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp) hb).2.2.1
theorem ptDeadAt38 : PtDeadAt 38 := ptDeadAt38_of (fun _ _ _ _ hfits hexp hnb => pre38PrefixInv_ws hfits.1.1 hnb hexp.1 (.inl rfl))
end Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv38

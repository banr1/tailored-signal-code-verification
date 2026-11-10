/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvSwap
public import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.HwEvents
open DY.Libsignal (HwBytes)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
cref_open
@[simp] private theorem length_append_entry {T : Type} [ExecTraceTypes.Has T]
    (tr : ExecTrace) (x : T) : (tr.append x).length = tr.length + 1 := length_append_entry_eq tr x
export Symbolic.BugInjection.Proofs.Common443.CompPrefixInvSwap ( at?_append_eq_of_eq NoBobDone noBobDone_nil bobDoneBaseKeys_eq_nil_of_noBobDone noBobDone_append_other NoBobDone.preserves_storeLocalState_pq NoBobDone.preserves_storeLocalState_tr NoBobDone.preserves_logEvent_pq NoBobDone.preserves_logEvent_tr NoBobDone.preserves_logEvent_c NoBobDone.preserves_setupAct noBobDone_setupTrace)
def encPreSaltTr (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl : Nat) : ExecTrace :=
  let coins := randTerm (tr₂.length + 1) cl; let (_, key, _) := DY.Spqr.spqrSend stA.spqr coins;
  (((tr₂.append (RndE 32)).append (RndE cl)).append (NetE key))
def encSalt (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : DY.Bytes := ((encPreSaltTr tr₂ stA cl).getMessageSentAt pq).getD (DY.Spqr.spqrSend stA.spqr (randTerm (tr₂.length + 1) cl)).2.1
def encWire (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : DY.Bytes :=
  let m := randTerm tr₂.length 32; let coins := randTerm (tr₂.length + 1) cl; let (_, _, pqMsg) := DY.Spqr.spqrSend stA.spqr coins; let (_, seed) := DY.Libsignal.TripleRatchet.kdfCk stA.cks; let keys := DY.Libsignal.TripleRatchet.trMsgKeys (encSalt tr₂ stA cl pq) seed;
  DY.Libsignal.TripleRatchet.trHonestWireMsg (DY.DiffieHellman.dhPk stA.dhs) stA.ns stA.pn (DY.SymEnc.symEnc keys.cipherKey keys.iv m) pqMsg
def encMac (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : DY.Bytes :=
  let (_, seed) := DY.Libsignal.TripleRatchet.kdfCk stA.cks; let keys := DY.Libsignal.TripleRatchet.trMsgKeys (encSalt tr₂ stA cl pq) seed;
  DY.Libsignal.TripleRatchet.computeMac keys.macKey stA.myIk stA.peerIk (encWire tr₂ stA cl pq)
def encOut (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : DY.Bytes := Concat.concat (encWire tr₂ stA cl pq) (encMac tr₂ stA cl pq)
def encSt (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl : Nat) : DY.Libsignal.TripleRatchet.TRState :=
  { stA with
    cks := (DY.Libsignal.TripleRatchet.kdfCk stA.cks).1, ns := stA.ns + 1, spqr := (DY.Spqr.spqrSend stA.spqr (randTerm (tr₂.length + 1) cl)).1 }
def encNextTr (tr₂ : ExecTrace) (me : Participant) (sIdx : Nat) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : ExecTrace :=
  let m := randTerm tr₂.length 32; let (_, seed) := DY.Libsignal.TripleRatchet.kdfCk stA.cks; let pqSalt := encSalt tr₂ stA cl pq;
  (((((encPreSaltTr tr₂ stA cl).append (TREvE (.Sent me stA.peer (DY.DiffieHellman.dhPk stA.dhs) stA.ns m))).append (TREvE (.MessageKey (stA.sinfo me) .sender seed pqSalt stA.ns stA.rIdx sIdx))).append (TRStE me (encSt tr₂ stA cl))).append (NetE (encOut tr₂ stA cl pq)))
theorem encPreSaltTr_getMessageSentAt_self (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl : Nat) : (encPreSaltTr tr₂ stA cl).getMessageSentAt (tr₂.length + 2) = some (DY.Spqr.spqrSend stA.spqr (randTerm (tr₂.length + 1) cl)).2.1 := by rw [getMessageSentAt_eq_at?]; unfold encPreSaltTr; dsimp only; rw [at?_append_eq_of_eq (T := DY.Network.ExecEntryT) _ (NetE _) (i := tr₂.length + 2) (by simp)]; rfl
@[simp] theorem encSalt_self (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl : Nat) : encSalt tr₂ stA cl (tr₂.length + 2) =
      (DY.Spqr.spqrSend stA.spqr (randTerm (tr₂.length + 1) cl)).2.1 := by
  unfold encSalt; rw [encPreSaltTr_getMessageSentAt_self]; rfl
theorem netMsgAt_encOut_encNextTr (tr₂ : ExecTrace) (me : Participant) (sIdx : Nat) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : NetMsgAt (encOut tr₂ stA cl pq) (tr₂.length + 6) (encNextTr tr₂ me sIdx stA cl pq) := by unfold NetMsgAt encNextTr encPreSaltTr; dsimp only; rw [at?_append_eq_of_eq (T := NetEntry) _ (NetE (encOut tr₂ stA cl pq)) (i := tr₂.length + 6) (by simp)]; rfl
theorem lastSent_encNextTr (tr₂ : ExecTrace) (me : Participant) (sIdx : Nat) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : lastSent tr₂ (encNextTr tr₂ me sIdx stA cl pq) = some (encOut tr₂ stA cl pq) := by
  unfold lastSent; have hlen : (encNextTr tr₂ me sIdx stA cl pq).length = tr₂.length + 7 := by unfold encNextTr encPreSaltTr; simp only [length_append_entry, Nat.add_assoc]
  have hlt : tr₂.length < (encNextTr tr₂ me sIdx stA cl pq).length := by omega
  have hsub : (encNextTr tr₂ me sIdx stA cl pq).length - 1 = tr₂.length + 6 := by omega
  simp only [hlt, ↓reduceIte, hsub]; rw [getMessageSentAt_eq_at?]; have hnet := netMsgAt_encOut_encNextTr tr₂ me sIdx stA cl pq; unfold NetMsgAt at hnet; rw [hnet]
theorem runMoves_le : ∀ (δ : List Move) (tr : ExecTrace), tr ≤ (runMoves δ tr).1
  | [], tr => Trace.le_refl tr
  | m :: δ, tr => Trace.le_trans _ _ _ (m.le_next tr) (runMoves_le δ (m.next tr))
theorem netMsgAt_runMoves (δ : List Move) {tr : ExecTrace} {msg : DY.Bytes} {idx : Nat} (h : NetMsgAt msg idx tr) : NetMsgAt msg idx (runMoves δ tr).1 := NetMsgAt.mono (runMoves_le δ tr) h
theorem at?_trSt_of_noSessionEffect {tr : ExecTrace} {m : Move} (heff : NoSessionEffect tr m) (j : Nat) : ((m.next tr).at? j : Option TRStEntry) = (tr.at? j : Option TRStEntry) := by
  have hle : tr ≤ m.next tr := m.le_next tr
  by_cases hj : j < tr.length
  · exact XplSteps.xat?_le_eq hle hj
  · have htr_none : (tr.at? j : Option TRStEntry) = none := Symbolic.Swarm.CREF.at?_ge_length tr (by omega)
    rw [htr_none]
    by_cases hj' : j < (m.next tr).length
    · exact (heff j (XplSteps.xpl_mem_newIndices (by omega) hj')).1
    · exact (XplSteps.xnone_of_ge (by omega)).1
theorem at?_trSt_of_movesFrom_noSessionEffect {tr : ExecTrace} {δ : List Move} (hδ : MovesFrom NoSessionEffect tr δ) (j : Nat) : (((runMoves δ tr).1).at? j : Option TRStEntry) = (tr.at? j : Option TRStEntry) := by
  induction δ generalizing tr with
  | nil => rfl
  | cons m δ ih => simp only [runMoves]; rw [ih hδ.2, at?_trSt_of_noSessionEffect hδ.1 j]
theorem at?_trSt_of_movesFrom_invisibleNoEffect {tr : ExecTrace} {δ : List Move} (hδ : MovesFrom InvisibleNoEffect tr δ) (j : Nat) : (((runMoves δ tr).1).at? j : Option TRStEntry) = (tr.at? j : Option TRStEntry) :=
  at?_trSt_of_movesFrom_noSessionEffect (movesFrom_mono (fun _ _ h => h.2) tr δ hδ) j
theorem encrypt_state_of_lastSent_ne_none {tr₂ : ExecTrace} {me : Participant} {sIdx cl pq : Nat} {wrap : Option (Nat × Nat)} (hls : lastSent tr₂ ((Move.encrypt me sIdx cl pq wrap).next tr₂) ≠ none) : ∃ st : DY.Libsignal.TripleRatchet.TRState, (tr₂.at? sIdx : Option TRStEntry) = some (TRStE me st) ∧ st.ns ≠ DY.Libsignal.TripleRatchet.u32Max := by
  rcases hget : ((PersistentLocalState.getLocalState me sIdx :
      Traceful DY.Libsignal.TripleRatchet.TRState).run tr₂).1 with _ | st
  · exfalso; apply hls
    have hnext : (Move.encrypt me sIdx cl pq wrap).next tr₂ = tr₂ := by
      unfold Move.next Move.act; rw [XplSteps.xrun_bind_unit]
      unfold DY.Libsignal.TripleRatchet.messageEncrypt; rw [run_bind_snd, hget, getLocalState_tr_snd]
    rw [hnext]; unfold lastSent; simp
  · rw [getLocalState_tr_fst] at hget
    rcases hat : (tr₂.at? sIdx : Option TRStEntry) with _ | ⟨⟨p, st'⟩⟩ <;> rw [hat] at hget
    · cases hget
    · dsimp only at hget; split_ifs at hget with hp
      injection hget with hst_eq; subst p hst_eq
      refine ⟨st', rfl, fun hns_eq => hls ?_⟩
      have hnext : (Move.encrypt me sIdx cl pq wrap).next tr₂ = tr₂ := by
        unfold Move.next Move.act; rw [XplSteps.xrun_bind_unit]
        unfold DY.Libsignal.TripleRatchet.messageEncrypt; rw [run_bind_snd, getLocalState_tr_fst, getLocalState_tr_snd, hat]; simp only [↓reduceIte, _root_.guard, hns_eq, ne_eq, not_true_eq_false, run_bind_snd, traceful_run_failure_fst, traceful_run_failure_snd]
      rw [hnext]; unfold lastSent; simp
theorem invert_send2_move_opt {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {tr : ExecTrace} {m : Move} {pt w : HwBytes} (hm : List.Forall₂ (EventMatchesEntry i r S g) [.pt pt, .send w] (m.vis tr)) : ∃ me sIdx cl pq wrap, m = .encrypt me sIdx cl pq wrap ∧ lastSent tr (m.next tr) ≠ none ∧ (wrap = none → w.head? = some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag) ∧ List.Forall₂ (EventMatchesEntry i r S g) [.pt pt, .send w] (encVis tr (m.next tr) wrap true) := by
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
theorem ownSaltsFrom_append : ∀ (ms₁ ms₂ : List Move) (tr : ExecTrace), ownSaltsFrom tr (ms₁ ++ ms₂) = (ownSaltsFrom tr ms₁ && ownSaltsFrom (runMoves ms₁ tr).1 ms₂)
  | [], _, _ => by simp [ownSaltsFrom, runMoves]
  | m :: ms₁, ms₂, tr => by
    simp only [List.cons_append, ownSaltsFrom, runMoves_cons_fst, ownSaltsFrom_append ms₁ ms₂ (m.next tr), Bool.and_assoc]
theorem pq_eq_of_ownSaltsFrom_split {tr₀ : ExecTrace} {ms ms₁ post : List Move} {me : Participant} {sIdx cl pq : Nat} {wrap : Option (Nat × Nat)} (hown : ownSaltsFrom tr₀ ms = true) (hms : ms = ms₁ ++ Move.encrypt me sIdx cl pq wrap :: post) : pq = (runMoves ms₁ tr₀).1.length + 2 := by rw [hms, ownSaltsFrom_append] at hown; simp only [ownSaltsFrom, Bool.and_eq_true, beq_iff_eq] at hown; exact hown.2.1
theorem encrypt_next_eq_encNextTr {tr₂ : ExecTrace} {me : Participant} {sIdx cl pq : Nat} {stA : DY.Libsignal.TripleRatchet.TRState} {wrap : Option (Nat × Nat)} (hst : (tr₂.at? sIdx : Option TRStEntry) = some (TRStE me stA)) (hns : stA.ns ≠ DY.Libsignal.TripleRatchet.u32Max) {pqSalt : DY.Bytes} (hpq : (encPreSaltTr tr₂ stA cl).getMessageSentAt pq = some pqSalt) : (Move.encrypt me sIdx cl pq wrap).next tr₂ = encNextTr tr₂ me sIdx stA cl pq := by
  have hsalt : encSalt tr₂ stA cl pq = pqSalt := by unfold encSalt; rw [hpq]; rfl
  have hpq_at : ((encPreSaltTr tr₂ stA cl).at? pq : Option NetEntry) = some (NetE pqSalt) := by
    rw [getMessageSentAt_eq_at?] at hpq
    rcases h : ((encPreSaltTr tr₂ stA cl).at? pq : Option NetEntry) with _ | ⟨⟨msg⟩⟩ <;> rw [h] at hpq
    · cases hpq
    · injection hpq with hmsg; subst hmsg; rfl
  unfold Move.next Move.act; rw [XplSteps.xrun_bind_unit]
  unfold DY.Libsignal.TripleRatchet.messageEncrypt; rw [run_bind_snd, getLocalState_tr_fst, getLocalState_tr_snd, hst]; simp only [↓reduceIte]; unfold _root_.guard; rw [ite_eq_left_iff.mpr fun h => absurd hns h]; rw [run_pure_bind_snd, run_genRand_bind_snd, run_genRand_bind_snd, length_append_entry, run_sendMessage_bind_snd]
  have hpre_eq : (((tr₂.append (RndE 32)).append (RndE cl)).append (NetE (DY.Spqr.spqrSend stA.spqr (mkRand (tr₂.length + 1) cl)).2.1)) = encPreSaltTr tr₂ stA cl := rfl
  rw [hpre_eq, run_bind_snd, receiveMessage_fst, receiveMessage_snd, hpq_at]; dsimp only
  rw [← hpre_eq, ← hsalt]
  have hcont := messageEncrypt_cont_run_snd_eq tr₂ me sIdx stA cl (encSalt tr₂ stA cl pq)
  exact hcont
theorem encrypt_next_eq_encNextTr_of_ownSalt {tr₂ : ExecTrace} {me : Participant} {sIdx cl pq : Nat} {stA : DY.Libsignal.TripleRatchet.TRState} {wrap : Option (Nat × Nat)} (hst : (tr₂.at? sIdx : Option TRStEntry) = some (TRStE me stA)) (hns : stA.ns ≠ DY.Libsignal.TripleRatchet.u32Max) (hpq : pq = tr₂.length + 2) : (Move.encrypt me sIdx cl pq wrap).next tr₂ = encNextTr tr₂ me sIdx stA cl pq := by subst hpq; exact encrypt_next_eq_encNextTr hst hns (encPreSaltTr_getMessageSentAt_self tr₂ stA cl)
theorem encrypt_lastSent_eq_some_encOut {tr₂ : ExecTrace} {me : Participant} {sIdx cl pq : Nat} {stA : DY.Libsignal.TripleRatchet.TRState} {wrap : Option (Nat × Nat)} (hst : (tr₂.at? sIdx : Option TRStEntry) = some (TRStE me stA)) (hns : stA.ns ≠ DY.Libsignal.TripleRatchet.u32Max) (hpq : pq = tr₂.length + 2) : lastSent tr₂ ((Move.encrypt me sIdx cl pq wrap).next tr₂) = some (encOut tr₂ stA cl pq) := by rw [encrypt_next_eq_encNextTr_of_ownSalt hst hns hpq, lastSent_encNextTr]
theorem NoBobDone.preserves_genRand (n : Nat) : Preserves NoBobDone (DY.Random.genRand n) := fun tr h => (TR.Runs.genRand tr n).2.symm ▸ noBobDone_append_other h (RndE n) rfl
theorem NoBobDone.preserves_sendMessage (msg : DY.Bytes) : Preserves NoBobDone (DY.Network.sendMessage msg) :=
  fun tr h => (TR.Runs.sendMessage tr msg).2.symm ▸ noBobDone_append_other h (NetE msg) rfl
export Symbolic.BugInjection.Proofs.Common443.CompPrefixInvSwap ( NoBobDone.preserves_aliceStart noBobDone_of_noSessionEffect)
theorem noBobDone_of_movesFrom_noSessionEffect {tr : ExecTrace} {δ : List Move} (htr : NoBobDone tr) (hδ : MovesFrom NoSessionEffect tr δ) : NoBobDone (runMoves δ tr).1 := by
  induction δ generalizing tr with
  | nil => exact htr
  | cons m δ ih => exact ih (noBobDone_of_noSessionEffect htr hδ.1) hδ.2
theorem noBobDone_of_movesFrom_invisibleNoEffect {tr : ExecTrace} {δ : List Move} (htr : NoBobDone tr) (hδ : MovesFrom InvisibleNoEffect tr δ) : NoBobDone (runMoves δ tr).1 :=
  noBobDone_of_movesFrom_noSessionEffect htr (movesFrom_mono (fun _ _ h => h.2) tr δ hδ)
theorem noBobDone_encNextTr {tr₂ : ExecTrace} (htr₂ : NoBobDone tr₂) (me : Participant) (sIdx : Nat) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : NoBobDone (encNextTr tr₂ me sIdx stA cl pq) := by unfold encNextTr encPreSaltTr; dsimp only; exact noBobDone_append_other (noBobDone_append_other (noBobDone_append_other (noBobDone_append_other (noBobDone_append_other (noBobDone_append_other (noBobDone_append_other htr₂ (RndE 32) rfl) (RndE cl) rfl) (NetE _) rfl) (TREvE _) rfl) (TREvE _) rfl) (TRStE _ _) rfl) (NetE _) rfl
theorem pia_enc_inv {r : Records} {ms pre mid post : List Move} {a b : Participant} {idS regB : Nat} {hb : PQXDH.BundleHandles} {shown : Nat} {me : Participant} {sIdx cl pq : Nat} {wrap : Option (Nat × Nat)} {ek ct : DY.Bytes} {stA : DY.Libsignal.TripleRatchet.TRState} (hms : ms = pre ++ Move.aliceStart a b idS regB hb shown :: mid ++ Move.encrypt me sIdx cl pq wrap :: post) (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre) (hmid : MovesFrom InvisibleNoEffect ((Move.aliceStart a b idS regB hb shown).next (runMoves pre (setupTrace r)).1) mid) (hpost : MovesFrom InvisibleNoEffect ((Move.encrypt me sIdx cl pq wrap).next (runMoves mid ((Move.aliceStart a b idS regB hb shown).next (runMoves pre (setupTrace r)).1)).1) post) (hown : ownSaltsFrom (setupTrace r) ms = true) (hek₁ : NetMsgAt ek ((runMoves pre (setupTrace r)).1.length + 3) ((Move.aliceStart a b idS regB hb shown).next (runMoves pre (setupTrace r)).1)) (hct₁ : NetMsgAt ct ((runMoves pre (setupTrace r)).1.length + 4) ((Move.aliceStart a b idS regB hb shown).next (runMoves pre (setupTrace r)).1)) (hst₁ : ∀ j : Nat, (((Move.aliceStart a b idS regB hb shown).next (runMoves pre (setupTrace r)).1).at? j : Option TRStEntry) = if j = (runMoves pre (setupTrace r)).1.length + 8 then some (TRStE a stA) else none) (hls : lastSent (runMoves mid ((Move.aliceStart a b idS regB hb shown).next (runMoves pre (setupTrace r)).1)).1 ((Move.encrypt me sIdx cl pq wrap).next (runMoves mid ((Move.aliceStart a b idS regB hb shown).next (runMoves pre (setupTrace r)).1)).1) ≠ none) : let tr₁ := (runMoves pre (setupTrace r)).1;
    let m₀ := Move.aliceStart a b idS regB hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let m₁ := Move.encrypt me sIdx cl pq wrap;
    (∀ j : Nat, (tr₂.at? j : Option TRStEntry) =
      if j = tr₁.length + 8 then some (TRStE a stA) else none) ∧
    me = a ∧ sIdx = tr₁.length + 8 ∧ pq = tr₂.length + 2 ∧ stA.ns ≠ DY.Libsignal.TripleRatchet.u32Max ∧
    m₁.next tr₂ = encNextTr tr₂ a (tr₁.length + 8) stA cl (tr₂.length + 2) ∧
    lastSent tr₂ (m₁.next tr₂) = some (encOut tr₂ stA cl pq) ∧
    NetMsgAt ek (tr₁.length + 3) tr₂ ∧ NetMsgAt ct (tr₁.length + 4) tr₂ ∧ NetMsgAt ek (tr₁.length + 3) (runTraceMoves r ms) ∧ NetMsgAt ct (tr₁.length + 4) (runTraceMoves r ms) ∧ NetMsgAt (encOut tr₂ stA cl pq) (tr₂.length + 6) (runTraceMoves r ms) ∧ ek.AttackerKnows (runTraceMoves r ms) ∧ ct.AttackerKnows (runTraceMoves r ms) ∧ (encOut tr₂ stA cl pq).AttackerKnows (runTraceMoves r ms) ∧
    bobDoneBaseKeys (runTraceMoves r ms) = [] := by
  let tr₁ := (runMoves pre (setupTrace r)).1; let m₀ := Move.aliceStart a b idS regB hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let m₁ := Move.encrypt me sIdx cl pq wrap;
  have hE1 : ∀ j : Nat, (tr₂.at? j : Option TRStEntry) =
      if j = tr₁.length + 8 then some (TRStE a stA) else none :=
    fun j => by rw [at?_trSt_of_movesFrom_invisibleNoEffect hmid j, hst₁ j]
  obtain ⟨st, hat, hns⟩ := encrypt_state_of_lastSent_ne_none hls
  rw [hE1 sIdx] at hat; split_ifs at hat with hsIdx; cases hat
  have htr₂_split : (runMoves (pre ++ m₀ :: mid) (setupTrace r)).1 = tr₂ := by rw [runMoves_append_fst, runMoves_cons_fst]
  have hpq : pq = tr₂.length + 2 := (by have hpq' := pq_eq_of_ownSaltsFrom_split hown (ms₁ := pre ++ m₀ :: mid) (post := post) hms; rwa [htr₂_split] at hpq')
  have hst₂ : (tr₂.at? sIdx : Option TRStEntry) = some (TRStE a stA) := by rw [hE1 sIdx]; simp [hsIdx]
  have hnext : m₁.next tr₂ = encNextTr tr₂ a (tr₁.length + 8) stA cl (tr₂.length + 2) := (by rw [encrypt_next_eq_encNextTr_of_ownSalt (cl := cl) (wrap := wrap) hst₂ hns hpq, hsIdx, hpq])
  have hlastSent : lastSent tr₂ (m₁.next tr₂) = some (encOut tr₂ stA cl pq) := encrypt_lastSent_eq_some_encOut hst₂ hns hpq
  have hrun_eq : runTraceMoves r ms = (runMoves post (m₁.next tr₂)).1 := by rw [hms, xpl_runTrace_eq, runMoves_append_fst, htr₂_split, runMoves_cons_fst]
  have hek₂ : NetMsgAt ek (tr₁.length + 3) tr₂ := netMsgAt_runMoves mid hek₁; have hct₂ : NetMsgAt ct (tr₁.length + 4) tr₂ := netMsgAt_runMoves mid hct₁; have hle_run : tr₂ ≤ runTraceMoves r ms := (by rw [hrun_eq]; exact Trace.le_trans _ _ _ (m₁.le_next tr₂) (runMoves_le post (m₁.next tr₂))); have hek_run : NetMsgAt ek (tr₁.length + 3) (runTraceMoves r ms) := NetMsgAt.mono hle_run hek₂; have hct_run : NetMsgAt ct (tr₁.length + 4) (runTraceMoves r ms) := NetMsgAt.mono hle_run hct₂; have henc_m₁ : NetMsgAt (encOut tr₂ stA cl pq) (tr₂.length + 6) (m₁.next tr₂) := (by rw [encrypt_next_eq_encNextTr_of_ownSalt (cl := cl) (wrap := wrap) hst₂ hns hpq]; exact netMsgAt_encOut_encNextTr tr₂ a sIdx stA cl pq)
  have henc_run : NetMsgAt (encOut tr₂ stA cl pq) (tr₂.length + 6) (runTraceMoves r ms) := by rw [hrun_eq]; exact netMsgAt_runMoves post henc_m₁
  have hnb_m₀ : NoBobDone (m₀.next tr₁) := by
    unfold m₀ Move.next Move.act; rw [XplSteps.xrun_bind_unit]
    exact NoBobDone.preserves_aliceStart a b idS regB hb tr₁ (noBobDone_of_movesFrom_invisibleNoEffect (noBobDone_setupTrace r) hpre)
  have hnb_m₁ : NoBobDone (m₁.next tr₂) := (by rw [encrypt_next_eq_encNextTr_of_ownSalt (cl := cl) (wrap := wrap) hst₂ hns hpq]; exact noBobDone_encNextTr (noBobDone_of_movesFrom_invisibleNoEffect hnb_m₀ hmid) a sIdx stA cl pq)
  have hnb_run : NoBobDone (runTraceMoves r ms) := by rw [hrun_eq]; exact noBobDone_of_movesFrom_invisibleNoEffect hnb_m₁ hpost
  exact ⟨hE1, rfl, hsIdx, hpq, hns, hnext, hlastSent, hek₂, hct₂, hek_run, hct_run, henc_run, hek_run.attackerKnows, hct_run.attackerKnows, henc_run.attackerKnows, bobDoneBaseKeys_eq_nil_of_noBobDone hnb_run⟩
end Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc

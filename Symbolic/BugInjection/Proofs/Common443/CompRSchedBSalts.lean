/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.Statement
public import Symbolic.BugInjection.Proofs.Common.DefsCompI0
public import Symbolic.BugInjection.Proofs.Common443.Census443Defs
public import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.CompRSchedBSalts
open ByteSpecs
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.Census443Defs
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
theorem view_initState_sendState_pack (st c : DY.Bytes) : (({ st := st, coins := c } : DY.Spqr.SendState.SubF DY.Bytes).pack).view? DY.Spqr.InitState.SubF = none := view_pack_none (F₁ := DY.Spqr.SendState.SubF) (F₂ := DY.Spqr.InitState.SubF) ({ st := st, coins := c } : DY.Spqr.SendState.SubF DY.Bytes) (by decide)
theorem gamma_lit (i : ExternInterpretation) (S : Sem) (g : Ghost) (b : ByteArray) : gamma i S g (({ lit := b } : DY.Literal.Literal.SubF DY.Bytes).pack) = ofByteArray b := by unfold gamma gamma'; rw [DY.Bytes.rec_eq gLit0 (gAll i S g)]; rfl
section O2
open DY.Libsignal.TripleRatchet (TRState spqrA2B)
open DY.Spqr (spqrSend spqrInit spqrChainKey spqrIdx zeroKey)
@[simp] private theorem length_append_entry {T : Type} [ExecTraceTypes.Has T] (tr : ExecTrace) (x : T) : (tr.append x).length = tr.length + 1 := length_append_entry_eq tr x
private theorem at?_append_eq_of_eq {T S : Type} [ExecTraceTypes.Has T] [ExecTraceTypes.Has S] (tr : ExecTrace) (x : S) {i : Nat} (hi : i = tr.length) : ((tr.append x).at? i : Option T) = TraceEntryHas.proj (TraceEntryHas.inj x : ExecTrace.Entry) := by
  subst hi; exact Symbolic.Swarm.CREF.at?_append_length tr x
private theorem xat?_le_some {E : Type} [ExecTraceTypes.Has E] {tr tr' : ExecTrace} (hle : tr ≤ tr') {i : Nat} {x : E} (h : (tr.at? i : Option E) = some x) : (tr'.at? i : Option E) = some x := by
  have hat := DY.Trace.at?_le (EntryT := E) tr tr' i hle; rwa [h] at hat
theorem encPreSaltTr_getMessageSentAt_self (tr₂ : ExecTrace) (stA : TRState) (cl : Nat) : (encPreSaltTr tr₂ stA cl).getMessageSentAt (tr₂.length + 2) = some (spqrSend stA.spqr (randTerm (tr₂.length + 1) cl)).2.1 := by unfold encPreSaltTr; rw [getMessageSentAt_eq_at?, at?_append_eq_of_eq (T := DY.Network.ExecEntryT) _ (NetE _) (i := tr₂.length + 2) (by simp)]; rfl
@[simp] theorem encSalt_self (tr₂ : ExecTrace) (stA : TRState) (cl : Nat) : encSalt tr₂ stA cl (tr₂.length + 2) =
      (spqrSend stA.spqr (randTerm (tr₂.length + 1) cl)).2.1 := by
  unfold encSalt; rw [encPreSaltTr_getMessageSentAt_self]; rfl
theorem spqrSend_spqrInit_key (a p coins : DY.Bytes) : (spqrSend (spqrInit a p) coins).2.1 = spqrChainKey a p (spqrIdx 1) := spqrSend_spqrInit_key_eq a p coins
theorem encSalt_iniAliceStartState_eq_spqrChainKey (tr₁ tr₂ : ExecTrace) (b : Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (cl : Nat) : encSalt tr₂ (iniAliceStartState tr₁ b o) cl (tr₂.length + 2) = spqrChainKey o.keys.pqr spqrA2B (spqrIdx 1) := by rw [encSalt_self]; exact spqrSend_spqrInit_key o.keys.pqr spqrA2B (randTerm (tr₂.length + 1) cl)
theorem encNextTr_getMessageSentAt_salt (tr₂ : ExecTrace) (me : Participant) (sIdx : Nat) (stA : TRState) (cl pq : Nat) : (encNextTr tr₂ me sIdx stA cl pq).getMessageSentAt (tr₂.length + 2) = some (spqrSend stA.spqr (randTerm (tr₂.length + 1) cl)).2.1 := by
  have hle : encPreSaltTr tr₂ stA cl ≤ encNextTr tr₂ me sIdx stA cl pq := (by unfold encNextTr; dsimp only; exact Trace.le_trans _ _ _ (Trace.le_trans _ _ _ (Trace.le_trans _ _ _ (Trace.append_le _ _) (Trace.append_le _ _)) (Trace.append_le _ _)) (Trace.append_le _ _))
  have h0 : ((encPreSaltTr tr₂ stA cl).at? (tr₂.length + 2) : Option NetEntry) =
      some (NetE (spqrSend stA.spqr (randTerm (tr₂.length + 1) cl)).2.1) := by
    unfold encPreSaltTr; dsimp only; rw [at?_append_eq_of_eq (T := NetEntry) _ (NetE _) (i := tr₂.length + 2) (by simp)]; rfl
  have h1 := xat?_le_some hle h0; rw [getMessageSentAt_eq_at?, h1]
theorem honestKeysFrom_encrypt_cons {tr : ExecTrace} {ms : List Move} {me : Participant} {sIdx cl pq : Nat} {wr : Option (Nat × Nat)} {stA : TRState} (henc : (Move.encrypt me sIdx cl pq wr).next tr = encNextTr tr me sIdx stA cl pq) : honestKeysFrom tr (Move.encrypt me sIdx cl pq wr :: ms) = (spqrSend stA.spqr (randTerm (tr.length + 1) cl)).2.1 :: honestKeysFrom (encNextTr tr me sIdx stA cl pq) ms := by simp only [honestKeysFrom]; rw [henc, encNextTr_getMessageSentAt_salt]; rfl
theorem honestKeysFrom_append : ∀ (ms₁ ms₂ : List Move) (tr : ExecTrace), honestKeysFrom tr (ms₁ ++ ms₂) = honestKeysFrom tr ms₁ ++ honestKeysFrom (runMoves ms₁ tr).1 ms₂
  | [], ms₂, tr => by simp [honestKeysFrom, runMoves]
  | m :: ms₁, ms₂, tr => by simp only [List.cons_append, honestKeysFrom, runMoves, honestKeysFrom_append ms₁ ms₂ (m.next tr), List.append_assoc]
theorem honestKeysFrom_noEncrypt : ∀ {ms : List Move} {tr : ExecTrace}, (∀ m ∈ ms, ∀ me sIdx cl pq wr, m ≠ Move.encrypt me sIdx cl pq wr) → honestKeysFrom tr ms = []
  | [], _, _ => rfl
  | m :: ms, tr, h => by
    cases m with
    | encrypt me sIdx cl pq wr => exact absurd rfl (h _ (List.mem_cons_self ..) me sIdx cl pq wr)
    | _ => simp only [honestKeysFrom, List.nil_append]; exact honestKeysFrom_noEncrypt (fun m hm => h m (List.mem_cons_of_mem _ hm))
private theorem getMessageSentAt_of_ge_length (tr : ExecTrace) {i : Nat} (hi : tr.length ≤ i) : tr.getMessageSentAt i = none := by rw [getMessageSentAt_eq_at?, Symbolic.Swarm.CREF.at?_ge_length tr hi]
private theorem xrun_bind_snd {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) : ((x >>= f).run tr).2.val = match (x.run tr).1 with | some a => ((f a).run (x.run tr).2.val).2.val | none => (x.run tr).2.val := traceful_run_bind_snd x f tr
private theorem xrun_le {α : Type} (x : Traceful α) (tr : ExecTrace) : tr ≤ (x.run tr).2.val := (x.run tr).2.property
private theorem xbind_fix {α β : Type} {x : Traceful α} {f : α → Traceful β} {tr : ExecTrace} (P : ExecTrace → Prop) (hx : (x.run tr).2.val = tr) (h0 : P tr) (hf : ∀ a, P ((f a).run tr).2.val) : P ((x >>= f).run tr).2.val := by rw [xrun_bind_snd]; split <;> [rw [hx]; rw [hx]] <;> [exact hf _; exact h0]
private theorem xbind_mono {α β : Type} {x : Traceful α} {f : α → Traceful β} {tr : ExecTrace} (P : ExecTrace → Prop) (hP : ∀ t t', t ≤ t' → P t → P t') (hx : P (x.run tr).2.val) : P ((x >>= f).run tr).2.val := by rw [xrun_bind_snd]; split <;> [exact hP _ _ (xrun_le _ _) hx; exact hx]
private def XFix {α : Type} (x : Traceful α) : Prop := ∀ tr, (x.run tr).2.val = tr
private theorem xfix_bind {α β : Type} {x : Traceful α} {f : α → Traceful β} (hx : XFix x) (hf : ∀ a, XFix (f a)) : XFix (x >>= f) := by intro tr; rw [xrun_bind_snd]; split <;> [rw [hx]; skip] <;> [exact hf _ _; exact hx tr]
private theorem xfix_pure {α : Type} (a : α) : XFix (pure a : Traceful α) := fun tr => by rw [Traceful.run_pure]
private theorem xfix_guard (p : Prop) [Decidable p] : XFix (_root_.guard p : Traceful Unit) := fun tr => by unfold _root_.guard; split <;> [exact xfix_pure () tr; exact traceful_run_failure_snd tr]
private theorem xfix_getLocalState {StateT : Type} [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT StateT)] (me : Participant) (i : Nat) : XFix (PersistentLocalState.getLocalState me i : Traceful StateT) := getLocalState_snd_eq me i
private theorem xrun_bind_unit {α : Type} (x : Traceful α) (tr : ExecTrace) : ((x >>= fun _ => (pure () : Traceful Unit)).run tr).2.val = (x.run tr).2.val := by rw [xrun_bind_snd]; split <;> [exact xfix_pure () _; rfl]
private def XRandAt (tr t : ExecTrace) : Prop := ∃ e : DY.Random.ExecEntryT, (t.at? tr.length : Option DY.Random.ExecEntryT) = some e
private theorem xrandAt_mono (tr : ExecTrace) : ∀ t t', t ≤ t' → XRandAt tr t → XRandAt tr t' := fun _ _ hle ⟨e, he⟩ => ⟨e, xat?_le_some hle he⟩
private theorem xrandAt_genRand (n : Nat) (tr : ExecTrace) : XRandAt tr ((DY.Random.genRand n : Traceful DY.Bytes).run tr).2.val := ⟨⟨n⟩, by rw [genRand_snd_eq]; exact Trace.at?_append tr (⟨n⟩ : DY.Random.ExecEntryT)⟩
private theorem xpl_messageEncrypt_shape (me : Participant) (stateIdx coinsLen pqIdx : Nat) (tr : ExecTrace) : ((DY.Libsignal.TripleRatchet.messageEncrypt me stateIdx coinsLen pqIdx).run tr).2.val = tr ∨ XRandAt tr ((DY.Libsignal.TripleRatchet.messageEncrypt me stateIdx coinsLen pqIdx).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  refine xbind_fix (fun t => t = tr ∨ XRandAt tr t) (xfix_getLocalState _ _ tr) (Or.inl rfl) fun st => ?_
  refine xbind_fix (fun t => t = tr ∨ XRandAt tr t) (xfix_guard _ tr) (Or.inl rfl) fun _ => ?_
  exact Or.inr (xbind_mono (XRandAt tr) (xrandAt_mono tr) (xrandAt_genRand 32 tr))
private theorem xpl_encrypt_next (me : Participant) (stateIdx coinsLen pqIdx : Nat) (w : Option (Nat × Nat)) (tr : ExecTrace) : (Move.encrypt me stateIdx coinsLen pqIdx w).next tr = tr ∨ XRandAt tr ((Move.encrypt me stateIdx coinsLen pqIdx w).next tr) := by unfold Move.next Move.act; rw [xrun_bind_unit]; exact xpl_messageEncrypt_shape me stateIdx coinsLen pqIdx tr
private theorem xlt_of_at?_some {E : Type} [ExecTraceTypes.Has E] {t : ExecTrace} {i : Nat} {e : E} (h : (t.at? i : Option E) = some e) : i < t.length := by
  have h1 := DY.Trace.at?_eq_some_implies_length_le (EntryT := E) t i; rwa [h] at h1
private theorem encrypt_next_eq_of_vis_nil {tr : ExecTrace} {me : Participant} {sIdx cl pq : Nat} {wr : Option (Nat × Nat)} (hvis : (Move.encrypt me sIdx cl pq wr).vis tr = []) : (Move.encrypt me sIdx cl pq wr).next tr = tr := by
  rcases xpl_encrypt_next me sIdx cl pq wr tr with h | ⟨e, he⟩; · exact h
  · exfalso; have hlt : tr.length < ((Move.encrypt me sIdx cl pq wr).next tr).length := xlt_of_at?_some he; have hmem_idx : tr.length ∈ newIndices tr ((Move.encrypt me sIdx cl pq wr).next tr) := (by unfold newIndices; rw [List.mem_range']; exact ⟨0, by omega, by omega⟩); have hmem_rnd : (randTerm tr.length e.length, e.length) ∈ newRandoms tr ((Move.encrypt me sIdx cl pq wr).next tr) := (by unfold newRandoms; rw [List.mem_filterMap]; exact ⟨tr.length, hmem_idx, by rw [he]; rfl⟩)
    cases hnr : newRandoms tr ((Move.encrypt me sIdx cl pq wr).next tr) with
    | nil => rw [hnr] at hmem_rnd; nomatch hmem_rnd
    | cons p rest =>
      unfold Move.vis encVis at hvis; dsimp only at hvis; rw [hnr] at hvis; rcases p with ⟨m0, n0⟩; simp [encDraws] at hvis
theorem honestKeysFrom_movesFrom_invisibleNoEffect : ∀ {ms : List Move} {tr : ExecTrace}, MovesFrom InvisibleNoEffect tr ms → honestKeysFrom tr ms = []
  | [], _, _ => rfl
  | m :: ms, tr, ⟨hm, hms⟩ => by
    cases m with
    | encrypt me sIdx cl pq wr =>
      have hnext := encrypt_next_eq_of_vis_nil hm.1; rw [honestKeysFrom, honestKeysFrom_movesFrom_invisibleNoEffect hms, hnext, getMessageSentAt_of_ge_length tr (i := tr.length + 2) (by omega)]; rfl
    | _ => simp only [honestKeysFrom, List.nil_append]; exact honestKeysFrom_movesFrom_invisibleNoEffect hms
def SaltFree (tr : ExecTrace) (seg : List Move) : Prop := MovesFrom InvisibleNoEffect tr seg ∨ (∀ m ∈ seg, ∀ me sIdx cl pq wr, m ≠ Move.encrypt me sIdx cl pq wr)
theorem honestKeysFrom_saltFree {tr : ExecTrace} {seg : List Move} (h : SaltFree tr seg) : honestKeysFrom tr seg = [] := h.elim honestKeysFrom_movesFrom_invisibleNoEffect honestKeysFrom_noEncrypt
theorem spqrSend_after_send_key (st c c' : DY.Bytes) : (spqrSend (spqrSend st c).1 c').2.1 = ({ st := (spqrSend st c).1, coins := c' } : DY.Spqr.SendKey.SubF DY.Bytes).pack := spqrSend_after_send_key_eq st c c'
theorem encSalt_encSt_eq_sendKeyPack (tr₂ tr₃ : ExecTrace) (stA₁ : TRState) (cl₁ cl₂ : Nat) : encSalt tr₃ (encSt tr₂ stA₁ cl₁) cl₂ (tr₃.length + 2) = ({ st := (spqrSend stA₁.spqr (randTerm (tr₂.length + 1) cl₁)).1, coins := randTerm (tr₃.length + 1) cl₂ } : DY.Spqr.SendKey.SubF DY.Bytes).pack := by rw [encSalt_self]; exact spqrSend_after_send_key stA₁.spqr (randTerm (tr₂.length + 1) cl₁) (randTerm (tr₃.length + 1) cl₂)
theorem honestSalts_schedB40_eq {r : Records} {s₀ s₁ s₂ s₃ : List Move} {A₁ E₁ E₂ : Move} {tr₁ tr₂ tr₃ : ExecTrace} {o₁ : DY.Libsignal.PQXDH.AliceHandshakeOut} {b me₁ me₂ : Participant} {i₁ i₂ cl₁ cl₂ pq₁ pq₂ : Nat} (hE₁ : ∃ wr, E₁ = Move.encrypt me₁ i₁ cl₁ pq₁ wr) (hE₂ : ∃ wr, E₂ = Move.encrypt me₂ i₂ cl₂ pq₂ wr) (hA₁ : ∀ me sIdx cl pq wr, A₁ ≠ Move.encrypt me sIdx cl pq wr) (htr₁ : tr₁ = (runMoves s₀ (setupTrace r)).1) (htr₂ : tr₂ = (runMoves s₁ (A₁.next tr₁)).1) (htr₃ : tr₃ = (runMoves s₂ (E₁.next tr₂)).1) (hs₀ : SaltFree (setupTrace r) s₀) (hs₁ : SaltFree (A₁.next tr₁) s₁) (hs₂ : SaltFree (E₁.next tr₂) s₂) (hs₃ : SaltFree (E₂.next tr₃) s₃) (henc₁ : E₁.next tr₂ = encNextTr tr₂ me₁ i₁ (iniAliceStartState tr₁ b o₁) cl₁ pq₁) (henc₂ : E₂.next tr₃ = encNextTr tr₃ me₂ i₂ (encSt tr₂ (iniAliceStartState tr₁ b o₁) cl₁) cl₂ pq₂) : honestSalts r (s₀ ++ A₁ :: s₁ ++ E₁ :: s₂ ++ E₂ :: s₃) = [zeroKey, spqrChainKey o₁.keys.pqr spqrA2B (spqrIdx 1), ({ st := (spqrSend (spqrInit o₁.keys.pqr spqrA2B) (randTerm (tr₂.length + 1) cl₁)).1, coins := randTerm (tr₃.length + 1) cl₂ } : DY.Spqr.SendKey.SubF DY.Bytes).pack] := by obtain ⟨wr₁, rfl⟩ := hE₁; obtain ⟨wr₂, rfl⟩ := hE₂; have hA₁_keys : honestKeysFrom tr₁ [A₁] = [] := honestKeysFrom_noEncrypt (fun m hm => by simp at hm; subst hm; exact hA₁); unfold honestSalts; congr 1; rw [List.append_assoc, List.append_assoc, honestKeysFrom_append s₀, honestKeysFrom_saltFree hs₀, List.nil_append, ← htr₁, show A₁ :: s₁ ++ (Move.encrypt me₁ i₁ cl₁ pq₁ wr₁ :: s₂ ++ Move.encrypt me₂ i₂ cl₂ pq₂ wr₂ :: s₃) = [A₁] ++ (s₁ ++ (Move.encrypt me₁ i₁ cl₁ pq₁ wr₁ :: s₂ ++ Move.encrypt me₂ i₂ cl₂ pq₂ wr₂ :: s₃)) from rfl, honestKeysFrom_append [A₁], hA₁_keys, List.nil_append]; dsimp only [runMoves]; rw [honestKeysFrom_append s₁, honestKeysFrom_saltFree hs₁, List.nil_append, ← htr₂, List.cons_append, honestKeysFrom_encrypt_cons henc₁, ← henc₁, honestKeysFrom_append s₂, honestKeysFrom_saltFree hs₂, List.nil_append, ← htr₃, honestKeysFrom_encrypt_cons henc₂, ← henc₂, honestKeysFrom_saltFree hs₃]; change [(spqrSend (spqrInit o₁.keys.pqr spqrA2B) (randTerm (tr₂.length + 1) cl₁)).2.1, (spqrSend (spqrSend (spqrInit o₁.keys.pqr spqrA2B) (randTerm (tr₂.length + 1) cl₁)).1 (randTerm (tr₃.length + 1) cl₂)).2.1] = _; rw [spqrSend_spqrInit_key, spqrSend_after_send_key]
theorem honestSalts_schedB40_mem {r : Records} {s₀ s₁ s₂ s₃ : List Move} {A₁ E₁ E₂ : Move} {tr₁ tr₂ tr₃ : ExecTrace} {o₁ : DY.Libsignal.PQXDH.AliceHandshakeOut} {b me₁ me₂ : Participant} {i₁ i₂ cl₁ cl₂ pq₁ pq₂ : Nat} (hE₁ : ∃ wr, E₁ = Move.encrypt me₁ i₁ cl₁ pq₁ wr) (hE₂ : ∃ wr, E₂ = Move.encrypt me₂ i₂ cl₂ pq₂ wr) (hA₁ : ∀ me sIdx cl pq wr, A₁ ≠ Move.encrypt me sIdx cl pq wr) (htr₁ : tr₁ = (runMoves s₀ (setupTrace r)).1) (htr₂ : tr₂ = (runMoves s₁ (A₁.next tr₁)).1) (htr₃ : tr₃ = (runMoves s₂ (E₁.next tr₂)).1) (hs₀ : SaltFree (setupTrace r) s₀) (hs₁ : SaltFree (A₁.next tr₁) s₁) (hs₂ : SaltFree (E₁.next tr₂) s₂) (hs₃ : SaltFree (E₂.next tr₃) s₃) (henc₁ : E₁.next tr₂ = encNextTr tr₂ me₁ i₁ (iniAliceStartState tr₁ b o₁) cl₁ pq₁) (henc₂ : E₂.next tr₃ = encNextTr tr₃ me₂ i₂ (encSt tr₂ (iniAliceStartState tr₁ b o₁) cl₁) cl₂ pq₂) {s : DY.Bytes} (hs : s ∈ honestSalts r (s₀ ++ A₁ :: s₁ ++ E₁ :: s₂ ++ E₂ :: s₃)) : s = zeroKey ∨ s = spqrChainKey o₁.keys.pqr spqrA2B (spqrIdx 1) ∨ s = (spqrSend (encSt tr₂ (iniAliceStartState tr₁ b o₁) cl₁).spqr (randTerm (tr₃.length + 1) cl₂)).2.1 := by rw [honestSalts_schedB40_eq hE₁ hE₂ hA₁ htr₁ htr₂ htr₃ hs₀ hs₁ hs₂ hs₃ henc₁ henc₂] at hs; have h2 : ({ st := (spqrSend (spqrInit o₁.keys.pqr spqrA2B) (randTerm (tr₂.length + 1) cl₁)).1, coins := randTerm (tr₃.length + 1) cl₂ } : DY.Spqr.SendKey.SubF DY.Bytes).pack = (spqrSend (encSt tr₂ (iniAliceStartState tr₁ b o₁) cl₁).spqr (randTerm (tr₃.length + 1) cl₂)).2.1 := (spqrSend_after_send_key (spqrInit o₁.keys.pqr spqrA2B) (randTerm (tr₂.length + 1) cl₁) (randTerm (tr₃.length + 1) cl₂)).symm; rw [h2] at hs; simpa using hs
end O2
end Symbolic.BugInjection.Proofs.Common443.CompRSchedBSalts

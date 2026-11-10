/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.Statement
public import Symbolic.BugInjection.Proofs.Common.CompFitsPin
public import Symbolic.BugInjection.Proofs.Fixtures.Cheval26WeakStateIdx1
public import Symbolic.BugInjection.Proofs.Common443.Census443Defs
public import Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire
public import Symbolic.BugInjection.Proofs.Common443.CompRTag
public import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1DecompSwap
open CryptoProofLib.Refinement (ExternInterpretation) open DY.Libsignal (HwBytes) open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Refinement (paddedVarint encodeField PbValue encodeWith canonicalVariation WireFields FieldItem knownValue? sha256CompressFunction)
open ByteSpecs DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire Symbolic.BugInjection.Proofs.Common443.CompRTag
attribute [local instance 2000] DY.Libsignal.Composed.instHasExecTrace
  DY.Libsignal.Composed.instHasExecBytes DY.Libsignal.Composed.HasExecTrace.toCExecBytes
  DY.Libsignal.Composed.HasExecBytes.toTRExecBytes DY.Libsignal.Composed.HasExecBytes.toPQXDHExecBytes
  DY.Libsignal.Composed.toTripleRatchet DY.Libsignal.Composed.toPQXDHSpqr
  DY.Libsignal.Composed.instBytesFunctor_symbolic DY.Libsignal.Composed.instExecTraceTypes_symbolic
@[simp] theorem encrypt_act_eq_wrap (me : Participant) (s cl pq : Nat) (w₁ w₂ : Option (Nat × Nat)) : (Move.encrypt me s cl pq w₁).act = (Move.encrypt me s cl pq w₂).act := rfl
@[simp] theorem encrypt_next_eq_wrap (tr : ExecTrace) (me : Participant) (s cl pq : Nat) (w₁ w₂ : Option (Nat × Nat)) : (Move.encrypt me s cl pq w₁).next tr = (Move.encrypt me s cl pq w₂).next tr := rfl
@[simp] theorem encrypt_isSetup_wrap (me : Participant) (s cl pq : Nat) (w : Option (Nat × Nat)) : (Move.encrypt me s cl pq w).isSetup = false := rfl
@[simp] theorem encrypt_anchored_wrap (tr : ExecTrace) (me : Participant) (s cl pq : Nat) (w : Option (Nat × Nat)) : (Move.encrypt me s cl pq w).LogsSessionCompletion tr = True := rfl
@[simp] theorem encrypt_party?_wrap (me : Participant) (s cl pq : Nat) (w : Option (Nat × Nat)) : (Move.encrypt me s cl pq w).party? = some me := rfl
@[simp] theorem encrypt_stateLoad?_wrap (me : Participant) (s cl pq : Nat) (w : Option (Nat × Nat)) : (Move.encrypt me s cl pq w).stateLoad? = some (me, s, true) := rfl
@[simp] theorem encrypt_prekeyPath?_wrap (me : Participant) (s cl pq : Nat) (w : Option (Nat × Nat)) : (Move.encrypt me s cl pq w).prekeyPath? = none := rfl
@[simp] theorem encrypt_peerOk_wrap (r : Records) (me : Participant) (s cl pq : Nat) (w : Option (Nat × Nat)) : (Move.encrypt me s cl pq w).MatchesSetupPeer r = True := rfl
theorem runMoves_fst_set_encrypt :
    ∀ (ms : List Move) (tr : ExecTrace) (k : Nat) (me : Participant) (s cl pq : Nat) (w₁ w₂ : Option (Nat × Nat)), ms[k]? = some (.encrypt me s cl pq w₁) → (runMoves (ms.set k (.encrypt me s cl pq w₂)) tr).1 = (runMoves ms tr).1
  | [], _, _, _, _, _, _, _, _, hk => by simp at hk
  | _ :: _, _, 0, _, _, _, _, _, _, hk => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hk; subst hk; rfl
  | m :: ms, tr, k + 1, me, s, cl, pq, w₁, w₂, hk => by
    simp only [List.getElem?_cons_succ] at hk; simp only [List.set_cons_succ, runMoves]
    exact runMoves_fst_set_encrypt ms (m.next tr) k me s cl pq w₁ w₂ hk
theorem runTrace_set_wrap {r : Records} {ms : List Move} {k : Nat} {me : Participant} {s cl pq : Nat} {w₁ w₂ : Option (Nat × Nat)} (hk : ms[k]? = some (.encrypt me s cl pq w₁)) : runTraceMoves r (ms.set k (.encrypt me s cl pq w₂)) = runTraceMoves r ms := runMoves_fst_set_encrypt ms (setupTrace r) k me s cl pq w₁ w₂ hk
theorem list_take_set_of_le {α : Type} :
    ∀ (xs : List α) (k j : Nat) (v : α), j ≤ k → (xs.set k v).take j = xs.take j
  | [], _, _, _, _ | _ :: _, _, 0, _, _ => by simp
  | _ :: _, 0, _ + 1, _, hj => by omega
  | _ :: xs, k + 1, j + 1, v, hj => by
    simp only [List.set_cons_succ, List.take_succ_cons, List.cons.injEq, true_and]
    exact list_take_set_of_le xs k j v (by omega)
theorem list_take_set_of_gt {α : Type} :
    ∀ (xs : List α) (k j : Nat) (v : α), k < j → (xs.set k v).take j = (xs.take j).set k v
  | [], _, _, _, _ | _ :: _, 0, _ + 1, _, _ => by simp
  | _ :: _, _, 0, _, hj => by omega
  | _ :: xs, k + 1, j + 1, v, hj => by
    simp only [List.set_cons_succ, List.take_succ_cons, List.cons.injEq, true_and]
    exact list_take_set_of_gt xs k j v (by omega)
theorem runTrace_take_set_wrap {r : Records} {ms : List Move} {k : Nat} {me : Participant} {s cl pq : Nat} {w₁ w₂ : Option (Nat × Nat)} (hk : ms[k]? = some (.encrypt me s cl pq w₁)) (j : Nat) : runTraceMoves r ((ms.set k (.encrypt me s cl pq w₂)).take j) = runTraceMoves r (ms.take j) := by
  by_cases hjk : j ≤ k
  · rw [list_take_set_of_le ms k j _ hjk]
  · have hlt : k < j := by omega
    rw [list_take_set_of_gt ms k j _ hlt]
    exact runTrace_set_wrap (w₁ := w₁) (by rw [List.getElem?_take_of_lt hlt]; exact hk)
theorem runMoves_append :
    ∀ (ms₁ ms₂ : List Move) (tr : ExecTrace), runMoves (ms₁ ++ ms₂) tr =
        let (tr₁, vs₁) := runMoves ms₁ tr; let (tr₂, vs₂) := runMoves ms₂ tr₁; (tr₂, vs₁ ++ vs₂)
  | [], _, _ => by simp [runMoves]
  | m :: ms₁, ms₂, tr => by
    simp only [List.cons_append, runMoves, runMoves_append ms₁ ms₂ (m.next tr), List.append_assoc]
theorem encSend_map_kind (tr tr' : ExecTrace) (w₁ w₂ : Option (Nat × Nat)) : (encSend tr tr' w₁).map VisEntry.kind = (encSend tr tr' w₂).map VisEntry.kind := by unfold encSend; cases lastSent tr tr' <;> cases w₁ <;> cases w₂ <;> rfl
theorem encrypt_vis_map_kind (tr : ExecTrace) (me : Participant) (s cl pq : Nat) (w₁ w₂ : Option (Nat × Nat)) : ((Move.encrypt me s cl pq w₁).vis tr).map VisEntry.kind = ((Move.encrypt me s cl pq w₂).vis tr).map VisEntry.kind := by
  simp only [Move.vis, encrypt_next_eq_wrap tr me s cl pq w₁ w₂, encVis, ↓reduceIte,
    List.map_append, encSend_map_kind tr ((Move.encrypt me s cl pq w₂).next tr) w₁ w₂]
theorem runMoves_snd_map_kind_set_encrypt :
    ∀ (ms : List Move) (tr : ExecTrace) (k : Nat) (me : Participant) (s cl pq : Nat) (w₁ w₂ : Option (Nat × Nat)), ms[k]? = some (.encrypt me s cl pq w₁) → ((runMoves (ms.set k (.encrypt me s cl pq w₂)) tr).2).map VisEntry.kind = ((runMoves ms tr).2).map VisEntry.kind
  | [], _, _, _, _, _, _, _, _, hk => by simp at hk
  | _ :: _, tr, 0, me, s, cl, pq, w₁, w₂, hk => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hk; subst hk
    simp only [List.set_cons_zero, runMoves, encrypt_next_eq_wrap tr me s cl pq w₂ w₁, List.map_append, encrypt_vis_map_kind tr me s cl pq w₂ w₁]
  | m :: ms, tr, k + 1, me, s, cl, pq, w₁, w₂, hk => by
    simp only [List.getElem?_cons_succ] at hk; simp only [List.set_cons_succ, runMoves, List.map_append]
    rw [runMoves_snd_map_kind_set_encrypt ms (m.next tr) k me s cl pq w₁ w₂ hk]
theorem runVis_map_kind_set_wrap {r : Records} {ms : List Move} {k : Nat} {me : Participant} {s cl pq : Nat} {w₁ w₂ : Option (Nat × Nat)} (hk : ms[k]? = some (.encrypt me s cl pq w₁)) : (runVis r (ms.set k (.encrypt me s cl pq w₂))).map VisEntry.kind = (runVis r ms).map VisEntry.kind := by
  unfold runVis; simp only [runMoves, List.map_append]
  rw [runMoves_snd_map_kind_set_encrypt ms (r.setupMove.next Trace.nil) k me s cl pq w₁ w₂ hk]
theorem runVis_take_map_kind_set_wrap {r : Records} {ms : List Move} {k : Nat} {me : Participant} {s cl pq : Nat} {w₁ w₂ : Option (Nat × Nat)} (hk : ms[k]? = some (.encrypt me s cl pq w₁)) (j : Nat) : (runVis r ((ms.set k (.encrypt me s cl pq w₂)).take j)).map VisEntry.kind = (runVis r (ms.take j)).map VisEntry.kind := by
  by_cases hjk : j ≤ k
  · rw [list_take_set_of_le ms k j _ hjk]
  · have hlt : k < j := by omega
    rw [list_take_set_of_gt ms k j _ hlt]
    exact runVis_map_kind_set_wrap (w₁ := w₁) (by rw [List.getElem?_take_of_lt hlt]; exact hk)
theorem callCount_eq_of_map_kind_eq {vs₁ vs₂ : List VisEntry} (h : vs₁.map VisEntry.kind = vs₂.map VisEntry.kind) : callCount vs₁ = callCount vs₂ := by
  have h1 : ∀ vs : List VisEntry,
      callCount vs = ((vs.map VisEntry.kind).filter fun k => k == .recv || k == .pt).length := by
    intro vs; unfold callCount; rw [List.filter_map, List.length_map]; rfl
  rw [h1 vs₁, h1 vs₂, h]
theorem callCount_runVis_take_set_wrap {r : Records} {ms : List Move} {k : Nat} {me : Participant} {s cl pq : Nat} {w₁ w₂ : Option (Nat × Nat)} (hk : ms[k]? = some (.encrypt me s cl pq w₁)) (j : Nat) : callCount (runVis r ((ms.set k (.encrypt me s cl pq w₂)).take j)) = callCount (runVis r (ms.take j)) := callCount_eq_of_map_kind_eq (runVis_take_map_kind_set_wrap hk j)
theorem list_eq_take_append_cons_drop {α : Type} :
    ∀ (xs : List α) (k : Nat) (x : α), xs[k]? = some x → xs = xs.take k ++ x :: xs.drop (k + 1)
  | [], _, _, hk => by simp at hk
  | _ :: _, 0, _, hk => by simp only [List.getElem?_cons_zero, Option.some.injEq] at hk; subst hk; rfl
  | _ :: xs, k + 1, x, hk => by
    simp only [List.getElem?_cons_succ] at hk
    simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append, List.cons.injEq, true_and]; exact list_eq_take_append_cons_drop xs k x hk
theorem list_set_eq_take_append_cons_drop {α : Type} :
    ∀ (xs : List α) (k : Nat) (x y : α), xs[k]? = some x → xs.set k y = xs.take k ++ y :: xs.drop (k + 1)
  | [], _, _, _, hk => by simp at hk
  | _ :: _, 0, _, _, _ => rfl
  | _ :: xs, k + 1, x, y, hk => by
    simp only [List.getElem?_cons_succ] at hk
    simp only [List.set_cons_succ, List.take_succ_cons, List.drop_succ_cons, List.cons_append, List.cons.injEq, true_and]; exact list_set_eq_take_append_cons_drop xs k x y hk
theorem runVis_set_wrap {r : Records} {ms : List Move} {k : Nat}
    {me : Participant} {s cl pq : Nat} {w₁ w₂ : Option (Nat × Nat)}
    (hk : ms[k]? = some (.encrypt me s cl pq w₁)) :
    let m := Move.encrypt me s cl pq w₁; let m' := Move.encrypt me s cl pq w₂
    let tr_k := runTraceMoves r (ms.take k)
    runVis r (ms.set k m') = runVis r (ms.take k) ++ m'.vis tr_k ++ (runMoves (ms.drop (k + 1)) (m.next tr_k)).2 ∧
    runVis r ms = runVis r (ms.take k) ++ m.vis tr_k ++ (runMoves (ms.drop (k + 1)) (m.next tr_k)).2 := by
  dsimp only; have hms := list_eq_take_append_cons_drop ms k (.encrypt me s cl pq w₁) hk; have hms' := list_set_eq_take_append_cons_drop ms k (.encrypt me s cl pq w₁) (.encrypt me s cl pq w₂) hk
  refine ⟨?_, ?_⟩
  · conv_lhs => rw [hms']
    unfold runVis; simp only [runMoves, runMoves_append, runTraceMoves, List.append_assoc]; rfl
  · conv_lhs => rw [hms]
    unfold runVis; simp only [runMoves, runMoves_append, runTraceMoves, List.append_assoc]
def VisEntryRel (i : ExternInterpretation) (S : Sem) (g : Ghost) (v₁ v₂ : VisEntry) : Prop := v₁ = v₂ ∨ (v₁.kind = .send ∧ v₂.kind = .send ∧ v₁.layout = .preKeySend ∧ v₂.layout = .preKeySend ∧ v₁.anchor = none ∧ v₂.anchor = none ∧ v₁.terms.map (gamma i S g) = v₂.terms.map (gamma i S g))
theorem VisEntryRel.refl (i : ExternInterpretation) (S : Sem) (g : Ghost) (v : VisEntry) : VisEntryRel i S g v v := Or.inl rfl
theorem VisEntryRel.eq_of_recv {i : ExternInterpretation} {S : Sem} {g : Ghost}
    {v₁ v₂ : VisEntry} (h : VisEntryRel i S g v₁ v₂) (hk : v₂.kind = .recv) : v₁ = v₂ :=
  h.elim id fun ⟨_, hk2, _⟩ => by rw [hk] at hk2; cases hk2
theorem forall₂_append {α β : Type} {R : α → β → Prop} {xs₁ ys₁ : List α} {xs₂ ys₂ : List β} (h1 : List.Forall₂ R xs₁ xs₂) (h2 : List.Forall₂ R ys₁ ys₂) : List.Forall₂ R (xs₁ ++ ys₁) (xs₂ ++ ys₂) := by induction h1 with | nil => exact h2 | cons hr _ ih => exact .cons hr ih
theorem forall₂_visEntryRel_refl (i : ExternInterpretation) (S : Sem) (g : Ghost) :
    ∀ (vs : List VisEntry), List.Forall₂ (VisEntryRel i S g) vs vs
  | [] => .nil | v :: vs => .cons (VisEntryRel.refl i S g v) (forall₂_visEntryRel_refl i S g vs)
theorem sendMatches_of_map_gamma_eq {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {b : HwBytes} {ts₁ ts₂ : List DY.Bytes} (hγ : ts₁.map (gamma i S g) = ts₂.map (gamma i S g)) (h : SendMatchesMoves i r S g b ts₁) : SendMatchesMoves i r S g b ts₂ := by
  obtain ⟨ids, h⟩ := h
  rcases ts₁ with _ | ⟨ek₁, _ | ⟨ct₁, _ | ⟨msg₁, _ | _⟩⟩⟩ <;> try exact False.elim h
  rcases ts₂ with _ | ⟨ek₂, _ | ⟨ct₂, _ | ⟨msg₂, _ | _⟩⟩⟩
  · have hlen := congrArg List.length hγ; simp at hlen
  · have hlen := congrArg List.length hγ; simp at hlen
  · have hlen := congrArg List.length hγ; simp at hlen
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at hγ
    obtain ⟨hek, hct, hmsg, -⟩ := hγ
    rcases h with ⟨preKeyId, spkId, kpkId, hids, hb⟩
    exact ⟨ids, preKeyId, spkId, kpkId, hids, by rw [← hek, ← hct, ← hmsg]; exact hb⟩
  · have hlen := congrArg List.length hγ; simp at hlen
theorem eventMatchesEntry_of_visEntryRel {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ev : MachineEvent} {v₁ v₂ : VisEntry} (hrel : VisEntryRel i S g v₁ v₂) (hm : EventMatchesEntry i r S g ev v₁) : EventMatchesEntry i r S g ev v₂ := by
  rcases hrel with rfl | ⟨hk1, hk2, hl1, hl2, _, _, hγ⟩
  · exact hm
  · unfold EventMatchesEntry at hm ⊢; rw [hk1, hl1] at hm; rw [hk2, hl2]
    exact ⟨hm.1, sendMatches_of_map_gamma_eq hγ hm.2⟩
theorem forall₂_eventMatchesEntry_of_visEntryRel {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {τ : List MachineEvent} {vs₁ vs₂ : List VisEntry} (hm : List.Forall₂ (EventMatchesEntry i r S g) τ vs₁) (hr : List.Forall₂ (VisEntryRel i S g) vs₁ vs₂) : List.Forall₂ (EventMatchesEntry i r S g) τ vs₂ := by
  induction hm generalizing vs₂ with
  | nil => cases hr; exact .nil
  | cons h1 _ ih => cases hr with | cons hr1 hrs => exact .cons (eventMatchesEntry_of_visEntryRel hr1 h1) (ih hrs)
theorem forall₂_visEntryRel_encSend {i : ExternInterpretation} {S : Sem} {g : Ghost} {tr tr' : ExecTrace} {e c e' c' : Nat} (hγ : (received tr [e, c]).map (gamma i S g) = (received tr [e', c']).map (gamma i S g)) : List.Forall₂ (VisEntryRel i S g) (encSend tr tr' (some (e, c))) (encSend tr tr' (some (e', c'))) := by
  unfold encSend; rcases lastSent tr tr' with _ | w
  · exact .nil
  · refine .cons (Or.inr ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩) .nil
    simp only [List.map_append, hγ]
theorem forall₂_visEntryRel_encrypt_vis {i : ExternInterpretation} {S : Sem} {g : Ghost} {tr : ExecTrace} {me : Participant} {s cl pq e c e' c' : Nat} (hγ : (received tr [e, c]).map (gamma i S g) = (received tr [e', c']).map (gamma i S g)) : List.Forall₂ (VisEntryRel i S g) ((Move.encrypt me s cl pq (some (e, c))).vis tr) ((Move.encrypt me s cl pq (some (e', c'))).vis tr) := by simp only [Move.vis, encrypt_next_eq_wrap tr me s cl pq (some (e, c)) (some (e', c')), encVis, ↓reduceIte]; exact forall₂_append (forall₂_append (forall₂_visEntryRel_refl i S g _) (forall₂_visEntryRel_encSend hγ)) (forall₂_visEntryRel_refl i S g _)
theorem forall₂_visEntryRel_runVis_set_wrap {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {k me s cl pq e c e' c'} (hk : ms[k]? = some (.encrypt me s cl pq (some (e, c)))) (hγ : (received (runTraceMoves r (ms.take k)) [e, c]).map (gamma i S g) = (received (runTraceMoves r (ms.take k)) [e', c']).map (gamma i S g)) : List.Forall₂ (VisEntryRel i S g) (runVis r ms) (runVis r (ms.set k (.encrypt me s cl pq (some (e', c'))))) := by obtain ⟨hvis', hvis⟩ := runVis_set_wrap (r := r) (w₂ := some (e', c')) hk; rw [hvis, hvis']; exact forall₂_append (forall₂_append (forall₂_visEntryRel_refl i S g _) (forall₂_visEntryRel_encrypt_vis hγ)) (forall₂_visEntryRel_refl i S g _)
theorem movesAnchored_set_encrypt :
    ∀ (ms : List Move) (tr : ExecTrace) (k : Nat) (me : Participant) (s cl pq : Nat) (w₁ w₂ : Option (Nat × Nat)), ms[k]? = some (.encrypt me s cl pq w₁) → MovesAnchored ms tr → MovesAnchored (ms.set k (.encrypt me s cl pq w₂)) tr
  | [], _, _, _, _, _, _, _, _, hk, _ => by simp at hk
  | _ :: _, _, 0, _, _, _, _, _, _, hk, ⟨_, hrest⟩ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hk; subst hk; exact ⟨trivial, hrest⟩
  | m :: ms, tr, k + 1, me, s, cl, pq, w₁, w₂, hk, ⟨hm, hrest⟩ => by
    simp only [List.getElem?_cons_succ] at hk
    exact ⟨hm, movesAnchored_set_encrypt ms (m.next tr) k me s cl pq w₁ w₂ hk hrest⟩
theorem compromisesCurrentFrom_set_encrypt :
    ∀ (ms : List Move) (tr : ExecTrace) (k : Nat) (me : Participant) (s cl pq : Nat) (w₁ w₂ : Option (Nat × Nat)), ms[k]? = some (.encrypt me s cl pq w₁) → compromisesCurrentFrom tr (ms.set k (.encrypt me s cl pq w₂)) = compromisesCurrentFrom tr ms
  | [], _, _, _, _, _, _, _, _, hk => by simp at hk
  | _ :: _, _, 0, _, _, _, _, _, _, hk => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hk; subst hk; rfl
  | m :: ms, tr, k + 1, me, s, cl, pq, w₁, w₂, hk => by
    simp only [List.getElem?_cons_succ] at hk; simp only [List.set_cons_succ, compromisesCurrentFrom]
    rw [compromisesCurrentFrom_set_encrypt ms (m.next tr) k me s cl pq w₁ w₂ hk]
theorem ownSaltsFrom_set_encrypt :
    ∀ (ms : List Move) (tr : ExecTrace) (k : Nat) (me : Participant) (s cl pq : Nat) (w₁ w₂ : Option (Nat × Nat)), ms[k]? = some (.encrypt me s cl pq w₁) → ownSaltsFrom tr (ms.set k (.encrypt me s cl pq w₂)) = ownSaltsFrom tr ms
  | [], _, _, _, _, _, _, _, _, hk => by simp at hk
  | _ :: _, _, 0, _, _, _, _, _, _, hk => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hk; subst hk; rfl
  | m :: ms, tr, k + 1, me, s, cl, pq, w₁, w₂, hk => by
    simp only [List.getElem?_cons_succ] at hk; simp only [List.set_cons_succ, ownSaltsFrom]
    rw [ownSaltsFrom_set_encrypt ms (m.next tr) k me s cl pq w₁ w₂ hk]
theorem getElem?_set_encrypt_props {ms : List Move} {k idx : Nat} {me : Participant} {s cl pq : Nat} {w₁ w₂ : Option (Nat × Nat)} {m' : Move} (hk : ms[k]? = some (.encrypt me s cl pq w₁)) (hidx : (ms.set k (.encrypt me s cl pq w₂))[idx]? = some m') : ∃ m, ms[idx]? = some m ∧ m'.party? = m.party? ∧ m'.stateLoad? = m.stateLoad? ∧ m'.prekeyPath? = m.prekeyPath? ∧ m'.act = m.act ∧ m'.next = m.next ∧ (∀ ds, m' = .reject ds → m = .reject ds) := by
  by_cases hki : k = idx
  · subst hki
    have hlt : k < ms.length := (List.getElem?_eq_some_iff.1 hk).1
    rw [List.getElem?_set_self hlt, Option.some.injEq] at hidx; subst hidx
    exact ⟨.encrypt me s cl pq w₁, hk, rfl, rfl, rfl, rfl, rfl, fun _ h => nomatch h⟩
  · rw [List.getElem?_set_ne hki] at hidx
    exact ⟨m', hidx, rfl, rfl, rfl, rfl, rfl, fun _ h => h⟩
theorem modelRun_set_wrap {r : Records} {ms : List Move} {k : Nat} {me : Participant} {s cl pq : Nat} {w₁ w₂ : Option (Nat × Nat)} (hk : ms[k]? = some (.encrypt me s cl pq w₁)) (hmr : ModelRun r ms) : ModelRun r (ms.set k (.encrypt me s cl pq w₂)) := by
  obtain ⟨hrnd, hsetup, ⟨hreach, hanc, hreach_take⟩, hcomp, hsalt, hpeer, hstate⟩ := hmr
  refine ⟨hrnd, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro m hm; exact (List.mem_or_eq_of_mem_set hm).elim (hsetup m) fun h => h ▸ rfl
  · rw [runTrace_set_wrap hk]; exact hreach
  · exact movesAnchored_set_encrypt ms (setupTrace r) k me s cl pq w₁ w₂ hk hanc
  · intro j; rw [runTrace_take_set_wrap hk j]; exact hreach_take j
  · rw [compromisesCurrentFrom_set_encrypt ms (setupTrace r) k me s cl pq w₁ w₂ hk]; exact hcomp
  · rw [ownSaltsFrom_set_encrypt ms (setupTrace r) k me s cl pq w₁ w₂ hk]; exact hsalt
  · intro m' hm'; exact (List.mem_or_eq_of_mem_set hm').elim (hpeer m') fun h => h ▸ trivial
  · intro idx₁ idx₂ mi' mj' p stIdx b hlt hmi' hmj' hload₁ hrun hload₂
    obtain ⟨mi, hmi, _, hst₁, _, hact₁, -⟩ := getElem?_set_encrypt_props hk hmi'
    obtain ⟨mj, hmj, _, hst₂, -⟩ := getElem?_set_encrypt_props hk hmj'
    rw [hact₁, runTrace_take_set_wrap hk idx₁] at hrun; exact hstate idx₁ idx₂ mi mj p stIdx b hlt hmi hmj (hst₁ ▸ hload₁) hrun (hst₂ ▸ hload₂)
private theorem mem_zip_of_visEntryRel_recv {i : ExternInterpretation} {S : Sem} {g : Ghost} {vs₁ vs₂ : List VisEntry} (hrel : List.Forall₂ (VisEntryRel i S g) vs₁ vs₂) : ∀ {τ : List MachineEvent} {ev : MachineEvent × VisEntry}, ev ∈ τ.zip vs₂ → ev.2.kind = .recv → ev ∈ τ.zip vs₁ := by
  induction hrel with
  | nil => intro τ ev hmem _; cases τ <;> cases hmem
  | cons hr _ ih =>
    intro τ ev hmem hkind; cases τ with
    | nil => cases hmem
    | cons e τ' =>
      simp only [List.zip_cons_cons, List.mem_cons] at hmem ⊢
      rcases hmem with rfl | hmem
      · left; rw [VisEntryRel.eq_of_recv hr hkind]
      · right; exact ih hmem hkind
theorem recvRepresentations_eq_of_runTrace_eq {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms₁ ms₂ : List Move} (htr : runTraceMoves r ms₁ = runTraceMoves r ms₂) : recvRepresentations i r S g ms₁ = recvRepresentations i r S g ms₂ := by funext b; unfold recvRepresentations; rw [htr]
theorem preKeyRepresentations_eq_of_runTrace_eq {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms₁ ms₂ : List Move} (htr : runTraceMoves r ms₁ = runTraceMoves r ms₂) : preKeyRepresentations i r S g ms₁ = preKeyRepresentations i r S g ms₂ := by funext b; unfold preKeyRepresentations; rw [htr]
theorem matchedPrefix_set_wrap {i : ExternInterpretation} {r : Records} {S : Sem} {who : List Participant} {g : Ghost} {ms : List Move} {τ₁ : List MachineEvent} {k : Nat} {me : Participant} {s cl pq e c e' c' : Nat} (hk : ms[k]? = some (.encrypt me s cl pq (some (e, c)))) (hγ : (received (runTraceMoves r (ms.take k)) [e, c]).map (gamma i S g) = (received (runTraceMoves r (ms.take k)) [e', c']).map (gamma i S g)) (hmp : MatchedPrefix i r S who g ms τ₁) : MatchedPrefix i r S who g (ms.set k (.encrypt me s cl pq (some (e', c')))) τ₁ := by
  obtain ⟨hcompat, hmr, hrole, hpath, hread, hvis⟩ := hmp
  refine ⟨hcompat, modelRun_set_wrap hk hmr, ?_, ?_, ?_, ?_⟩
  · intro idx m' p hm' hp
    obtain ⟨m, hm, hparty, -⟩ := getElem?_set_encrypt_props hk hm'
    rw [callCount_runVis_take_set_wrap hk idx]; exact hrole idx m p hm (hparty ▸ hp)
  · intro idx m' promote b p hm' hpp hcs hp
    obtain ⟨m, hm, _, _, hpre, -⟩ := getElem?_set_encrypt_props hk hm'
    rw [callCount_runVis_take_set_wrap hk idx] at hcs; rw [runTrace_take_set_wrap hk idx]; exact hpath idx m promote b p hm (hpre ▸ hpp) hcs hp
  · intro ev hev hkind
    have hev_old := mem_zip_of_visEntryRel_recv (forall₂_visEntryRel_runVis_set_wrap hk hγ) hev hkind; have htr := runTrace_set_wrap (r := r) (w₂ := some (e', c')) hk; rw [recvRepresentations_eq_of_runTrace_eq htr, preKeyRepresentations_eq_of_runTrace_eq htr]; exact hread ev hev_old hkind
  · exact forall₂_eventMatchesEntry_of_visEntryRel hvis (forall₂_visEntryRel_runVis_set_wrap hk hγ)
theorem outcomeFaithful_set_wrap {r : Records} {ok : Nat → Bool} {ms : List Move} {k : Nat} {me : Participant} {s cl pq : Nat} {w₁ w₂ : Option (Nat × Nat)} (hk : ms[k]? = some (.encrypt me s cl pq w₁)) (hout : OutcomeFaithful r ok ms) : OutcomeFaithful r ok (ms.set k (.encrypt me s cl pq w₂)) := by
  intro idx m' hm'
  obtain ⟨m, hm, _, _, _, _, hnext, hrej⟩ := getElem?_set_encrypt_props hk hm'; dsimp only
  rw [callCount_runVis_take_set_wrap hk idx, runTrace_take_set_wrap hk idx, hnext]; have ho := hout idx m hm
  exact ⟨fun ds hds => ho.1 ds (hrej ds hds), ho.2⟩
theorem explains_set_wrap {i : ExternInterpretation} {r : Records} {S : Sem} {who : List Participant} {ok : Nat → Bool} {g : Ghost} {ms : List Move} {τ₁ : List MachineEvent} {k : Nat} {me : Participant} {s cl pq e c e' c' : Nat} (hk : ms[k]? = some (.encrypt me s cl pq (some (e, c)))) (hγ : (received (runTraceMoves r (ms.take k)) [e, c]).map (gamma i S g) = (received (runTraceMoves r (ms.take k)) [e', c']).map (gamma i S g)) (hex : ExplainsMoves i r S who ok g ms τ₁) : ExplainsMoves i r S who ok g (ms.set k (.encrypt me s cl pq (some (e', c')))) τ₁ := ⟨matchedPrefix_set_wrap hk hγ hex.1, outcomeFaithful_set_wrap hk hex.2⟩
def NetMsgAt (x : DY.Bytes) (i : Nat) (tr : ExecTrace) : Prop := (tr.at? i : Option NetEntry) = some (NetE x)
theorem getMessageSentAt_of_netMsgAt {tr : ExecTrace} {i : Nat} {x : DY.Bytes} (h : NetMsgAt x i tr) : tr.getMessageSentAt i = some x := by unfold NetMsgAt at h; rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.getMessageSentAt_eq_at?, h]
theorem received_pair_of_netMsgAt {tr : ExecTrace} {a b : DY.Bytes} {i j : Nat} (ha : NetMsgAt a i tr) (hb : NetMsgAt b j tr) : received tr [i, j] = [a, b] := by simp only [received, List.filterMap_cons, List.filterMap_nil, getMessageSentAt_of_netMsgAt ha, getMessageSentAt_of_netMsgAt hb]
theorem explains_swap_step {i : ExternInterpretation} {r : Records} {S : Sem}
    {who : List Participant} {ok : Nat → Bool} {g : Ghost} {ms : List Move}
    {τ₁ : List MachineEvent} {k : Nat} {me : Participant} {s cl pq e c e' c' : Nat} {ek ct : DY.Bytes}
    (hk : ms[k]? = some (.encrypt me s cl pq (some (e, c))))
    (hek : NetMsgAt ek e' (runTraceMoves r (ms.take k))) (hct : NetMsgAt ct c' (runTraceMoves r (ms.take k)))
    (hγ : (received (runTraceMoves r (ms.take k)) [e, c]).map (gamma i S g) = [gamma i S g ek, gamma i S g ct])
    (hex : ExplainsMoves i r S who ok g ms τ₁) :
    let ms' := ms.set k (.encrypt me s cl pq (some (e', c')))
    ExplainsMoves i r S who ok g ms' τ₁ ∧ runTraceMoves r ms' = runTraceMoves r ms ∧
    preKeyRepresentations i r S g ms' = preKeyRepresentations i r S g ms := by
  dsimp only
  have hγ' : (received (runTraceMoves r (ms.take k)) [e, c]).map (gamma i S g) = (received (runTraceMoves r (ms.take k)) [e', c']).map (gamma i S g) := by rw [hγ, received_pair_of_netMsgAt hek hct]; rfl
  have htr := runTrace_set_wrap (r := r) (w₂ := some (e', c')) hk; exact ⟨explains_set_wrap hk hγ' hex, htr, preKeyRepresentations_eq_of_runTrace_eq htr⟩
theorem runTrace_append (r : Records) (ms₁ ms₂ : List Move) : runTraceMoves r (ms₁ ++ ms₂) = (runMoves ms₂ (runTraceMoves r ms₁)).1 := by unfold runTraceMoves; simp only [runMoves, runMoves_append]
theorem explains_swap_append {i : ExternInterpretation} {r : Records} {S : Sem}
    {who : List Participant} {ok : Nat → Bool} {g : Ghost}
    {τ₁ : List MachineEvent} {pre post : List Move}
    {me : Participant} {s cl pq e c e' c' : Nat} {ek ct : DY.Bytes}
    (hek : NetMsgAt ek e' (runTraceMoves r pre)) (hct : NetMsgAt ct c' (runTraceMoves r pre))
    (hγ : (received (runTraceMoves r pre) [e, c]).map (gamma i S g) = [gamma i S g ek, gamma i S g ct])
    (hex : ExplainsMoves i r S who ok g (pre ++ .encrypt me s cl pq (some (e, c)) :: post) τ₁) :
    let ms := pre ++ .encrypt me s cl pq (some (e, c)) :: post
    let ms' := pre ++ .encrypt me s cl pq (some (e', c')) :: post
    ExplainsMoves i r S who ok g ms' τ₁ ∧ runTraceMoves r ms' = runTraceMoves r ms ∧
    preKeyRepresentations i r S g ms' = preKeyRepresentations i r S g ms := by
  dsimp only
  have hk : (pre ++ Move.encrypt me s cl pq (some (e, c)) :: post)[pre.length]? = some (.encrypt me s cl pq (some (e, c))) := by
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl
  have htake : (pre ++ Move.encrypt me s cl pq (some (e, c)) :: post).take pre.length = pre := List.take_left
  have hset : (pre ++ Move.encrypt me s cl pq (some (e, c)) :: post).set pre.length (.encrypt me s cl pq (some (e', c'))) = pre ++ Move.encrypt me s cl pq (some (e', c')) :: post := by rw [List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self]; rfl
  rw [← hset]
  exact explains_swap_step hk (by rw [htake]; exact hek) (by rw [htake]; exact hct) (by rw [htake]; exact hγ) hex
theorem matchedPrefix_swap_step {i : ExternInterpretation} {r : Records} {S : Sem}
    {who : List Participant} {g : Ghost} {ms : List Move}
    {τ₁ : List MachineEvent} {k : Nat} {me : Participant} {s cl pq e c e' c' : Nat} {ek ct : DY.Bytes}
    (hk : ms[k]? = some (.encrypt me s cl pq (some (e, c))))
    (hek : NetMsgAt ek e' (runTraceMoves r (ms.take k))) (hct : NetMsgAt ct c' (runTraceMoves r (ms.take k)))
    (hγ : (received (runTraceMoves r (ms.take k)) [e, c]).map (gamma i S g) = [gamma i S g ek, gamma i S g ct])
    (hmp : MatchedPrefix i r S who g ms τ₁) :
    let ms' := ms.set k (.encrypt me s cl pq (some (e', c')))
    MatchedPrefix i r S who g ms' τ₁ ∧ runTraceMoves r ms' = runTraceMoves r ms ∧
    preKeyRepresentations i r S g ms' = preKeyRepresentations i r S g ms := by
  dsimp only
  have hγ' : (received (runTraceMoves r (ms.take k)) [e, c]).map (gamma i S g) = (received (runTraceMoves r (ms.take k)) [e', c']).map (gamma i S g) := by rw [hγ, received_pair_of_netMsgAt hek hct]; rfl
  have htr := runTrace_set_wrap (r := r) (w₂ := some (e', c')) hk; exact ⟨matchedPrefix_set_wrap hk hγ' hmp, htr, preKeyRepresentations_eq_of_runTrace_eq htr⟩

theorem matchedPrefix_swap_append {i : ExternInterpretation} {r : Records} {S : Sem}
    {who : List Participant} {g : Ghost}
    {τ₁ : List MachineEvent} {pre post : List Move}
    {me : Participant} {s cl pq e c e' c' : Nat} {ek ct : DY.Bytes}
    (hek : NetMsgAt ek e' (runTraceMoves r pre)) (hct : NetMsgAt ct c' (runTraceMoves r pre))
    (hγ : (received (runTraceMoves r pre) [e, c]).map (gamma i S g) = [gamma i S g ek, gamma i S g ct])
    (hmp : MatchedPrefix i r S who g (pre ++ .encrypt me s cl pq (some (e, c)) :: post) τ₁) :
    let ms := pre ++ .encrypt me s cl pq (some (e, c)) :: post
    let ms' := pre ++ .encrypt me s cl pq (some (e', c')) :: post
    MatchedPrefix i r S who g ms' τ₁ ∧ runTraceMoves r ms' = runTraceMoves r ms ∧
    preKeyRepresentations i r S g ms' = preKeyRepresentations i r S g ms := by
  dsimp only
  have hk : (pre ++ Move.encrypt me s cl pq (some (e, c)) :: post)[pre.length]? = some (.encrypt me s cl pq (some (e, c))) := by
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl
  have htake : (pre ++ Move.encrypt me s cl pq (some (e, c)) :: post).take pre.length = pre := List.take_left
  have hset : (pre ++ Move.encrypt me s cl pq (some (e, c)) :: post).set pre.length (.encrypt me s cl pq (some (e', c'))) = pre ++ Move.encrypt me s cl pq (some (e', c')) :: post := by rw [List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self]; rfl
  rw [← hset]
  exact matchedPrefix_swap_step hk (by rw [htake]; exact hek) (by rw [htake]; exact hct) (by rw [htake]; exact hγ) hmp

end Symbolic.BugInjection.Proofs.Common443.WsIdx1DecompSwap

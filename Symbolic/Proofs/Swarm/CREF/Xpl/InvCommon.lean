/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Xpl.Faithful
import Mathlib.Data.List.Forall2
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.Xpl.StepsMix

/-!
# Shared Call-Block Inversion Lemmas

Proves participant-attribution and visible-entry classification helpers together with `xpl_oneMove`,
which decomposes any call block with a single `recv`/`pt` head and no subsequent `recv`/`pt`/`leak`
events into a single visible move surrounded by `InvisibleNoEffect` moves.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF

cref_open

open CryptoProofLib.Refinement (ExternInterpretation)

/-- A visible move inside a faithful block acts for `p` or has no actor. -/
theorem actorIn_of_vis_ne_nil {p : Participant} {tr : ExecTrace} {pre post : List Move} {m : Move}
    (hf : DeltaFaithful p tr (pre ++ m :: post)) (hv : m.vis (runMoves pre tr).1 ≠ []) :
    ActorIn p m := by
  have hmem : moveActor m ∈ visActorsFrom (pre ++ m :: post) tr := by
    rw [visActorsFrom_append]
    refine List.mem_append_right _ ?_
    simp only [visActorsFrom]
    refine List.mem_append_left _ (List.mem_replicate.2 ⟨?_, rfl⟩)
    intro h0
    exact hv (List.eq_nil_of_length_eq_zero h0)
  rcases hf _ hmem with h | h | h
  · exact Or.inl h
  · exact absurd h (by simp)
  · exact Or.inr h

theorem vis_ne_nil_of_forall₂ {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {blk : List MachineEvent} {l : List VisEntry}
    (h : List.Forall₂ (EventMatchesEntry interpretation r S g) blk l) (hne : blk ≠ []) : l ≠ [] := by
  rintro rfl
  cases h
  exact hne rfl

/-! ## Entry Kinds per Move -/

theorem xpl_kind_of_matches {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {e : MachineEvent} {v : VisEntry}
    (h : EventMatchesEntry interpretation r S g e v) : v.kind = eventKind e := h.1.symm

theorem xpl_forall₂_mem_left {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ a ∈ l₁, ∃ b ∈ l₂, R a b
  | [], _, _, a, ha => by simp at ha
  | _ :: _, _ :: _, .cons hab h, a, ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, List.mem_cons_self .., hab⟩
    · obtain ⟨b, hb, hr⟩ := xpl_forall₂_mem_left h a ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

theorem xpl_forall₂_cons_left {α β : Type} {R : α → β → Prop} {a : α} {l : List α} :
    ∀ {u : List β}, List.Forall₂ R (a :: l) u → ∃ b u', R a b ∧ List.Forall₂ R l u' ∧ u = b :: u'
  | _ :: _, .cons h hl => ⟨_, _, h, hl, rfl⟩

theorem xpl_aliceVis_kind {tr tr' : ExecTrace} {h : PQXDH.BundleHandles} {v : VisEntry}
    (hv : v ∈ aliceVis tr tr' h) : v.kind = .recv ∨ v.kind = .rng := by
  simp only [aliceVis, List.mem_cons] at hv
  rcases hv with rfl | hv
  · exact Or.inl rfl
  · exact Or.inr (aliceDraws_kind _ _ hv)

theorem xpl_bobVis_kind {tr tr' : ExecTrace} {mh : PQXDH.PreKeyMsgHandles}
    {opk : Option DY.Bytes} {v : VisEntry} (hv : v ∈ bobVis tr tr' mh opk) :
    v.kind = .recv ∨ v.kind = .rng ∨ v.kind = .accept := by
  simp only [bobVis, List.cons_append, List.mem_cons, List.mem_append, List.mem_map] at hv
  rcases hv with rfl | ⟨_, _, rfl⟩ | hv
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · cases hp : receivedPlaintext tr tr' with
    | none => simp [hp] at hv
    | some m =>
      simp only [hp, Option.map_some, Option.toList_some, List.mem_singleton] at hv
      subst hv
      exact Or.inr (Or.inr rfl)

theorem xpl_decVis_kind {tr tr' : ExecTrace} {si i : Nat} {w : Bool} {v : VisEntry}
    (hv : v ∈ decVis tr tr' si i w) : v.kind = .recv ∨ v.kind = .rng ∨ v.kind = .accept := by
  simp only [decVis, List.mem_append, List.mem_map] at hv
  rcases hv with (hv | ⟨_, _, rfl⟩) | hv
  · cases hm : tr.getMessageSentAt i with
    | none => simp [hm] at hv
    | some b =>
      simp only [hm, Option.map_some, Option.toList_some, List.mem_singleton] at hv
      subst hv
      exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · cases hp : receivedPlaintext tr tr' with
    | none => simp [hp] at hv
    | some m =>
      simp only [hp, Option.map_some, Option.toList_some, List.mem_singleton] at hv
      subst hv
      exact Or.inr (Or.inr rfl)

theorem xpl_encVis_kind {tr tr' : ExecTrace} {wrap : Option (Nat × Nat)} {ws : Bool}
    {v : VisEntry} (hv : v ∈ encVis tr tr' wrap ws) :
    v.kind = .pt ∨ v.kind = .rng ∨ (ws = true ∧ v.kind = .send) := by
  simp only [encVis, List.mem_append] at hv
  rcases hv with hv | hv
  · rcases encDraws_kind _ hv with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
  · cases ws
    · simp at hv
    · simp only [ite_true] at hv
      unfold encSend at hv
      split at hv
      · split at hv <;> (simp only [List.mem_singleton] at hv; subst hv; exact Or.inr (Or.inr ⟨rfl, rfl⟩))
      · simp at hv

/-- Every visible entry of `m.vis tr` is either a `leak` exposure, an encrypt-family entry (`pt`,
`rng`, or `send` for `Move.encrypt`), or a receive-family entry (`recv`, `rng`, or `accept`). -/
theorem xpl_vis_kind (m : Move) (tr : ExecTrace) {v : VisEntry} (hv : v ∈ m.vis tr) :
    v.kind = .leak ∨
      (SendKind m ∧ (v.kind = .pt ∨ v.kind = .rng ∨
        (v.kind = .send ∧ ∃ me s c q w, m = .encrypt me s c q w))) ∨
      (¬ SendKind m ∧ (v.kind = .recv ∨ v.kind = .rng ∨ v.kind = .accept)) := by
  rw [xpl_vis_eq] at hv
  rcases List.mem_append.1 hv with hv | hv
  · right
    cases m <;> dsimp only [xpl_ownVis] at hv
    case aliceStart => exact Or.inr ⟨id, (xpl_aliceVis_kind (List.mem_of_mem_take hv)).elim
      Or.inl (fun h => Or.inr (Or.inl h))⟩
    case bobStart => exact Or.inr ⟨id, xpl_bobVis_kind (List.mem_of_mem_take hv)⟩
    case encrypt =>
      refine Or.inl ⟨trivial, ?_⟩
      rcases xpl_encVis_kind hv with h | h | ⟨_, h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨h, _, _, _, _, _, rfl⟩)
    case encryptAbort =>
      refine Or.inl ⟨trivial, ?_⟩
      rcases xpl_encVis_kind hv with h | h | ⟨h, _⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · cases h
    case encryptFail =>
      refine Or.inl ⟨trivial, ?_⟩
      rcases xpl_encVis_kind hv with h | h | ⟨h, _⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · cases h
    case decrypt => exact Or.inr ⟨id, xpl_decVis_kind hv⟩
    case decryptSkipped => exact Or.inr ⟨id, xpl_decVis_kind hv⟩
    case reject =>
      refine Or.inr ⟨id, ?_⟩
      simp only [List.mem_cons, List.mem_map] at hv
      rcases hv with rfl | ⟨_, _, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    all_goals simp at hv
  · exact Or.inl (xpl_exposures_kind hv)

theorem xpl_forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ b ∈ l₂, ∃ a ∈ l₁, R a b
  | _, [], _, b, hb => by simp at hb
  | _ :: _, _ :: _, .cons hab h, b, hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨_, List.mem_cons_self .., hab⟩
    · obtain ⟨a, ha, hr⟩ := xpl_forall₂_mem_right h b hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩

theorem xpl_forall₂_length {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → l₁.length = l₂.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, .cons _ h => by simp [xpl_forall₂_length h]

/-- Moves that can emit a `recv` visible entry. -/
def RecvHeadKind : Move → Prop
  | .aliceStart .. | .bobStart .. | .decrypt .. | .decryptSkipped .. | .reject _ => True
  | _ => False

theorem xpl_recvHeadKind (m : Move) (tr : ExecTrace) {v : VisEntry} (hv : v ∈ m.vis tr)
    (hk : v.kind = .recv) : RecvHeadKind m := by
  rcases xpl_vis_kind m tr hv with h | ⟨_, h⟩ | ⟨hns, _⟩
  · rw [hk] at h; cases h
  · rw [hk] at h; rcases h with h | h | ⟨h, _⟩ <;> cases h
  · rw [xpl_vis_eq] at hv
    rcases List.mem_append.1 hv with hv | hv
    · cases m <;> simp only [RecvHeadKind] <;>
        first | exact (hns trivial).elim | (dsimp only [xpl_ownVis] at hv; simp at hv)
    · have := xpl_exposures_kind hv
      rw [hk] at this; cases this

/-- Only `bobStart`, `decrypt`, and `decryptSkipped` emit an `accept` entry. -/
theorem xpl_accept_by {p : Participant} (m : Move) (tr : ExecTrace) {v : VisEntry}
    (hv : v ∈ m.vis tr) (hk : v.kind = .accept) (hact : ActorIn p m) :
    BobStartBy p m ∨ DecryptBy p m := by
  rcases xpl_vis_kind m tr hv with h | ⟨_, h⟩ | ⟨_, _⟩
  · rw [hk] at h; cases h
  · rw [hk] at h; rcases h with h | h | ⟨h, _⟩ <;> cases h
  · rw [xpl_vis_eq] at hv
    rcases List.mem_append.1 hv with hv | hv
    · cases m <;> dsimp only [xpl_ownVis] at hv
      case aliceStart =>
        rcases xpl_aliceVis_kind (List.mem_of_mem_take hv) with h | h <;> rw [hk] at h <;> cases h
      case reject =>
        simp only [List.mem_cons, List.mem_map] at hv
        rcases hv with rfl | ⟨_, _, rfl⟩ <;> cases hk
      case bobStart =>
        left
        rcases hact with h | h <;> simp only [moveActor, Option.some.injEq, reduceCtorEq] at h
        exact h
      case decrypt =>
        right
        rcases hact with h | h <;> simp only [moveActor, Option.some.injEq, reduceCtorEq] at h
        exact h
      case decryptSkipped =>
        right
        rcases hact with h | h <;> simp only [moveActor, Option.some.injEq, reduceCtorEq] at h
        exact h
      case encrypt => rcases xpl_encVis_kind hv with h | h | ⟨_, h⟩ <;> rw [hk] at h <;> cases h
      case encryptAbort => rcases xpl_encVis_kind hv with h | h | ⟨_, h⟩ <;> rw [hk] at h <;> cases h
      case encryptFail => rcases xpl_encVis_kind hv with h | h | ⟨_, h⟩ <;> rw [hk] at h <;> cases h
      all_goals simp at hv
    · have := xpl_exposures_kind hv
      rw [hk] at this; cases this

theorem xpl_head_entry {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {blk : List MachineEvent} {l : List VisEntry} {e : MachineEvent}
    (hm : List.Forall₂ (EventMatchesEntry interpretation r S g) blk l) (he : blk.head? = some e) :
    ∃ v ∈ l, v.kind = eventKind e ∧ l.head? = some v := by
  cases blk with
  | nil => simp at he
  | cons e' t =>
    simp only [List.head?_cons, Option.some.injEq] at he
    subst he
    obtain ⟨v, l', hv, _, rfl⟩ := xpl_forall₂_cons_left hm
    exact ⟨v, List.mem_cons_self .., xpl_kind_of_matches hv, rfl⟩

/-! ## Single Visible Move per Block -/

theorem xpl_runTrace_eq (r : ProtocolSetup) :
    ∀ ms : List Move, runTraceMoves r ms = (runMoves ms (setupTrace r)).1 := by
  intro ms
  simp only [runTraceMoves, setupMove_next_nil, runMoves_cons_fst]

theorem xpl_movesAnchored_append_right :
    ∀ (ms₁ ms₂ : List Move) (tr : ExecTrace),
      MovesAnchored (ms₁ ++ ms₂) tr → MovesAnchored ms₂ (runMoves ms₁ tr).1
  | [], _, _, h => by simpa [runMoves] using h
  | m :: ms₁, ms₂, tr, h => by
    rw [runMoves_cons_fst]
    exact xpl_movesAnchored_append_right ms₁ ms₂ (m.next tr) h.2

theorem xpl_movesFrom_of :
    ∀ (δ : List Move) (tr : ExecTrace), (∀ m ∈ δ, m.isSetup = false) → MovesAnchored δ tr →
      MovesFrom (fun tr m => m.isSetup = false ∧ m.LogsSessionCompletion tr) tr δ
  | [], _, _, _ => trivial
  | m :: δ, tr, hs, ⟨ha, hδ⟩ =>
    ⟨⟨hs m (List.mem_cons_self ..), ha⟩,
      xpl_movesFrom_of δ (m.next tr) (fun m' hm' => hs m' (List.mem_cons_of_mem _ hm')) hδ⟩

/-- The first entry of a run of non-setup anchored moves is a `recv`, `pt` or `leak`. -/
theorem xpl_runMoves_head_kind :
    ∀ (δ : List Move) (tr : ExecTrace),
      MovesFrom (fun tr m => m.isSetup = false ∧ m.LogsSessionCompletion tr) tr δ →
      ∀ v ∈ (runMoves δ tr).2.head?, v.kind = .recv ∨ v.kind = .pt ∨ v.kind = .leak
  | [], _, _, v, hv => by simp [runMoves] at hv
  | m :: δ, tr, ⟨⟨hs, ha⟩, hδ⟩, v, hv => by
    rw [runMoves_cons_snd] at hv
    cases hvm : m.vis tr with
    | nil =>
      rw [hvm, List.nil_append] at hv
      exact xpl_runMoves_head_kind δ (m.next tr) hδ v hv
    | cons w l =>
      rw [hvm, List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hv
      subst hv
      exact xpl_vis_head_kind hs ha w (by rw [hvm]; rfl)

/-- A run of non-setup anchored moves emitting no visible entries consists of `InvisibleNoEffect`
moves. -/
theorem xpl_movesFrom_invisible :
    ∀ (δ : List Move) (tr : ExecTrace),
      MovesFrom (fun tr m => m.isSetup = false ∧ m.LogsSessionCompletion tr) tr δ →
      (runMoves δ tr).2 = [] → MovesFrom InvisibleNoEffect tr δ
  | [], _, _, _ => trivial
  | m :: δ, tr, ⟨⟨hs, ha⟩, hδ⟩, hnil => by
    rw [runMoves_cons_snd] at hnil
    have hv : m.vis tr = [] := (List.append_eq_nil_iff.1 hnil).1
    have hr : (runMoves δ (m.next tr)).2 = [] := (List.append_eq_nil_iff.1 hnil).2
    exact ⟨⟨hv, noSessionEffect_of_vis_nil hs ha hv⟩,
      xpl_movesFrom_invisible δ (m.next tr) hδ hr⟩

theorem xpl_oneMove_aux {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} :
    ∀ (δ : List Move) (tr : ExecTrace) (blk : List MachineEvent),
      MovesFrom (fun tr m => m.isSetup = false ∧ m.LogsSessionCompletion tr) tr δ →
      List.Forall₂ (EventMatchesEntry interpretation r S g) blk (runMoves δ tr).2 →
      blk ≠ [] →
      (∀ e ∈ blk.tail, eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak) →
      OneMove (fun tr m => m.isSetup = false ∧ m.LogsSessionCompletion tr ∧
        List.Forall₂ (EventMatchesEntry interpretation r S g) blk (m.vis tr)) tr δ
  | [], _, blk, _, hm, hne, _ => by
    simp only [runMoves] at hm
    cases hm
    exact absurd rfl hne
  | m :: δ, tr, blk, ⟨⟨hs, ha⟩, hδ⟩, hm, hne, htail => by
    rw [runMoves_cons_snd] at hm
    by_cases hv0 : m.vis tr = []
    · rw [hv0, List.nil_append] at hm
      obtain ⟨pre, mm, post, hδeq, hpre, hQ, hpost⟩ :=
        xpl_oneMove_aux δ (m.next tr) blk hδ hm hne htail
      refine ⟨m :: pre, mm, post, by rw [hδeq]; rfl, ⟨⟨hv0, noSessionEffect_of_vis_nil hs ha hv0⟩,
        hpre⟩, ?_, ?_⟩
      · simpa only [runMoves_cons_fst] using hQ
      · simpa only [runMoves_cons_fst] using hpost
    · have hlen : (m.vis tr).length ≤ blk.length := by
        rw [xpl_forall₂_length hm, List.length_append]; omega
      have hsplit : blk = blk.take (m.vis tr).length ++ blk.drop (m.vis tr).length :=
        (List.take_append_drop _ _).symm
      rw [hsplit] at hm
      obtain ⟨hm₁, hm₂⟩ := xpl_forall₂_append_split (by simp; omega) hm
      have hdrop : blk.drop (m.vis tr).length = [] := by
        cases hb₂ : blk.drop (m.vis tr).length with
        | nil => rfl
        | cons e rest =>
          exfalso
          rw [hb₂] at hm₂
          obtain ⟨u, u', hu, _, hueq⟩ := xpl_forall₂_cons_left hm₂
          have hk := xpl_runMoves_head_kind δ (m.next tr) hδ u (by rw [hueq]; rfl)
          rw [xpl_kind_of_matches hu] at hk
          have hmem : e ∈ blk.tail := by
            have h1 : (blk.take (m.vis tr).length).length = (m.vis tr).length := by
              simp; omega
            rw [hsplit, hb₂]
            cases ht : blk.take (m.vis tr).length with
            | nil =>
              rw [ht] at h1
              exact absurd (List.eq_nil_of_length_eq_zero h1.symm) hv0
            | cons x xs => simp
          obtain ⟨h1, h2, h3⟩ := htail e hmem
          rcases hk with hk | hk | hk
          · exact h1 hk
          · exact h2 hk
          · exact h3 hk
      have hblk : blk = blk.take (m.vis tr).length := by
        conv_lhs => rw [hsplit, hdrop, List.append_nil]
      rw [← hblk] at hm₁
      rw [hdrop] at hm₂
      refine ⟨[], m, δ, rfl, trivial, ⟨hs, ha, hm₁⟩, ?_⟩
      have hnil : (runMoves δ (m.next tr)).2 = [] := List.forall₂_nil_left_iff.1 hm₂
      exact xpl_movesFrom_invisible δ (m.next tr) hδ hnil

/-- If `blk` is nonempty, starts with a `recv` or `pt` event, and has no `recv`, `pt`, or `leak`
events in its tail, then `δ` decomposes into one visible move matching `blk` surrounded by
`InvisibleNoEffect` moves. -/
theorem xpl_oneMove {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost}
    {ms₀ δ : List Move} {acc blk : List MachineEvent}
    (hB : XplBlock interpretation r S who g ms₀ δ acc blk)
    (_hhead : ∀ e ∈ blk.head?, eventKind e = .recv ∨ eventKind e = .pt)
    (hne : blk ≠ [])
    (htail : ∀ e ∈ blk.tail, eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak) :
    OneMove (fun tr m => m.isSetup = false ∧ m.LogsSessionCompletion tr ∧
      List.Forall₂ (EventMatchesEntry interpretation r S g) blk (m.vis tr)) (runTraceMoves r ms₀) δ := by
  obtain ⟨_, hs, ⟨_, hanc, _⟩, -⟩ := hB.run
  have hanc' := xpl_movesAnchored_append_right ms₀ δ (setupTrace r) hanc
  rw [← xpl_runTrace_eq] at hanc'
  exact xpl_oneMove_aux δ (runTraceMoves r ms₀) blk
    (xpl_movesFrom_of δ _ (fun m hm => hs m (List.mem_append_right _ hm)) hanc') hB.matched hne htail

end Symbolic.Swarm.CREF

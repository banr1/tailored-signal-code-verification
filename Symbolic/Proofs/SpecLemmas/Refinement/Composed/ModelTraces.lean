/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Mathlib.Tactic.Push

/-!
# Model Trace and Run Lemmas

Monotonicity and list-append lemmas for `runMoves` and `runTraceMoves`, attacker-knowledge bounds
for visible trace entries (`runVis_known`) and setup messages (`setupSent_known`), and prefix and
snoc closure for `ModelRun`.
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Refinement

open DY DY.Comparse

/-! ## Algebra of model runs -/

@[simp] theorem runMoves_nil (tr : ExecTrace) : runMoves [] tr = (tr, []) := rfl

theorem runMoves_cons_fst (m : Move) (ms : List Move) (tr : ExecTrace) :
    (runMoves (m :: ms) tr).1 = (runMoves ms (m.next tr)).1 := rfl

theorem runMoves_cons_snd (m : Move) (ms : List Move) (tr : ExecTrace) :
    (runMoves (m :: ms) tr).2 = m.vis tr ++ (runMoves ms (m.next tr)).2 := rfl

theorem Move.le_next (m : Move) (tr : ExecTrace) : tr ≤ m.next tr := (m.act.run tr).2.property

theorem runMoves_le : ∀ (L : List Move) (tr : ExecTrace), tr ≤ (runMoves L tr).1
  | [], tr => Trace.le_refl tr
  | m :: L, tr => Trace.le_trans _ _ _ (m.le_next tr) (runMoves_le L (m.next tr))

theorem setupTrace_le_runTrace (r : ProtocolSetup) (ms : List Move) : setupTrace r ≤ runTraceMoves r ms :=
  runMoves_le ms (setupTrace r)

private theorem runMoves_append_fst : ∀ (ms₁ ms₂ : List Move) (tr : ExecTrace),
    (runMoves (ms₁ ++ ms₂) tr).1 = (runMoves ms₂ (runMoves ms₁ tr).1).1
  | [], _, _ => rfl
  | m :: ms₁, ms₂, tr => runMoves_append_fst ms₁ ms₂ (m.next tr)

theorem runTrace_take_le (r : ProtocolSetup) (ms : List Move) (i : Nat) :
    runTraceMoves r (ms.take i) ≤ runTraceMoves r ms := by
  conv_rhs => rw [← List.take_append_drop i ms]
  show (runMoves (ms.take i) (setupTrace r)).1 ≤
    (runMoves (ms.take i ++ ms.drop i) (setupTrace r)).1
  rw [runMoves_append_fst]
  exact runMoves_le (ms.drop i) _

/-! ## Observed terms are attacker-known -/

/-- Every term of a `send`, `recv`, or `leak` entry is attacker-known on `tr`. -/
def VisKnown (tr : ExecTrace) (v : VisEntry) : Prop :=
  (v.kind = .send ∨ v.kind = .recv ∨ v.kind = .leak) → ∀ t ∈ v.terms, t.AttackerKnows tr

theorem VisKnown.mono {tr₁ tr₂ : ExecTrace} {v : VisEntry} (hle : tr₁ ≤ tr₂)
    (h : VisKnown tr₁ v) : VisKnown tr₂ v :=
  fun hk t ht => Bytes.AttackerKnows_le _ _ _ hle (h hk t ht)

theorem visKnown_of_kind {tr : ExecTrace} {v : VisEntry}
    (h : v.kind = .rng ∨ v.kind = .pt ∨ v.kind = .accept) : VisKnown tr v := by
  intro hk
  rcases h with h | h | h <;> rw [h] at hk <;> simp at hk

theorem getMessageSentAt_attackerKnows {tr : ExecTrace} {i : Nat} {b : DY.Bytes}
    (h : tr.getMessageSentAt i = some b) : b.AttackerKnows tr :=
  Trace.MessageSentAt_implies_AttackerKnows tr b i
    ((Trace.MessageSentAt_eq_getMessageSentAt b i tr).mpr h)

theorem received_known {tr tr' : ExecTrace} (hle : tr ≤ tr') {hs : List Nat} {t : DY.Bytes}
    (ht : t ∈ received tr hs) : t.AttackerKnows tr' := by
  obtain ⟨_, _, hi⟩ := List.mem_filterMap.mp ht
  exact Bytes.AttackerKnows_le _ _ _ hle (getMessageSentAt_attackerKnows hi)

theorem exposures_known {tr tr' : ExecTrace} {v : VisEntry} (hv : v ∈ exposures tr tr') :
    VisKnown tr' v := by
  rcases List.mem_append.mp hv with hv | hv
  · obtain ⟨_, _, hj⟩ := List.mem_filterMap.mp hv
    unfold pqExposureAt at hj
    intro _ t ht
    split at hj <;> (try cases hj) <;>
      exact getMessageSentAt_attackerKnows (Option.mem_toList.mp ht)
  · obtain ⟨_, _, hj⟩ := List.mem_filterMap.mp hv
    unfold trExposureAt at hj
    intro _ t ht
    split at hj <;> (try cases hj) <;>
      exact getMessageSentAt_attackerKnows (Option.mem_toList.mp ht)

theorem aliceDraws_kind (done : Option Nat) :
    ∀ (L : List DY.Bytes) {v : VisEntry}, v ∈ aliceDraws done L → v.kind = .rng
  | [], _, hv => by simp [aliceDraws] at hv
  | [_], _, hv => by simp [aliceDraws, rngEntry] at hv; subst hv; rfl
  | _ :: _ :: _, _, hv => by
    simp only [aliceDraws, List.cons_append, List.mem_cons, List.mem_append] at hv
    rcases hv with rfl | hv | hv
    · rfl
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv
      rfl
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv
      rfl

theorem encDraws_kind : ∀ (L : List (DY.Bytes × Nat)) {v : VisEntry}, v ∈ encDraws L →
    v.kind = .rng ∨ v.kind = .pt
  | [], _, hv => by simp [encDraws] at hv
  | _ :: _, _, hv => by
    simp only [encDraws, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact Or.inr rfl
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv
      exact Or.inl rfl

theorem lastSent_known {tr tr' : ExecTrace} {w : DY.Bytes} (h : lastSent tr tr' = some w) :
    w.AttackerKnows tr' := by
  unfold lastSent at h
  split at h
  · exact getMessageSentAt_attackerKnows h
  · cases h

theorem encVis_known {tr tr' : ExecTrace} (hle : tr ≤ tr') {wrap : Option (Nat × Nat)}
    {withSend : Bool} {v : VisEntry} (hv : v ∈ encVis tr tr' wrap withSend) : VisKnown tr' v := by
  unfold encVis at hv
  rcases List.mem_append.mp hv with hv | hv
  · exact visKnown_of_kind ((encDraws_kind _ hv).elim Or.inl (Or.inr ∘ Or.inl))
  · cases withSend with
    | false => simp at hv
    | true =>
      simp only [↓reduceIte] at hv
      unfold encSend at hv
      split at hv
      · rename_i w hw
        split at hv
        · rcases List.mem_singleton.mp hv with rfl
          intro _ t ht
          rcases List.mem_singleton.mp ht with rfl
          exact lastSent_known hw
        · rcases List.mem_singleton.mp hv with rfl
          intro _ t ht
          rcases List.mem_append.mp ht with ht | ht
          · exact received_known hle ht
          · rcases List.mem_singleton.mp ht with rfl
            exact lastSent_known hw
      · cases hv

theorem decVis_known {tr tr' : ExecTrace} (hle : tr ≤ tr') {stateIdx msgIdx : Nat} {wrapped : Bool}
    {v : VisEntry} (hv : v ∈ decVis tr tr' stateIdx msgIdx wrapped) : VisKnown tr' v := by
  unfold decVis at hv
  rcases List.mem_append.mp hv with hv | hv
  · rcases List.mem_append.mp hv with hv | hv
    · rcases hm : tr.getMessageSentAt msgIdx with _ | b
      · rw [hm] at hv; cases hv
      · rw [hm] at hv
        rcases List.mem_singleton.mp hv with rfl
        intro _ t ht
        rcases List.mem_singleton.mp ht with rfl
        exact Bytes.AttackerKnows_le _ _ _ hle (getMessageSentAt_attackerKnows hm)
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv
      exact visKnown_of_kind (Or.inl rfl)
  · rcases hp : receivedPlaintext tr tr' with _ | _
    · rw [hp] at hv; cases hv
    · rw [hp] at hv
      rcases List.mem_singleton.mp hv with rfl
      exact visKnown_of_kind (Or.inr (Or.inr rfl))

theorem aliceVis_known {tr tr' : ExecTrace} (hle : tr ≤ tr') {h : PQXDH.BundleHandles}
    {v : VisEntry} (hv : v ∈ aliceVis tr tr' h) : VisKnown tr' v := by
  unfold aliceVis at hv
  rcases List.mem_cons.mp hv with rfl | hv
  · exact fun _ t ht => received_known hle ht
  · exact visKnown_of_kind (Or.inl (aliceDraws_kind _ _ hv))

theorem bobVis_known {tr tr' : ExecTrace} (hle : tr ≤ tr') {mh : PQXDH.PreKeyMsgHandles}
    {opk : Option DY.Bytes} (hopk : ∀ t ∈ opk.toList, t.AttackerKnows tr') {v : VisEntry}
    (hv : v ∈ bobVis tr tr' mh opk) : VisKnown tr' v := by
  unfold bobVis at hv
  rcases List.mem_cons.mp hv with rfl | hv
  · intro _ t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact received_known hle ht
    · exact hopk t ht
  · rcases List.mem_append.mp hv with hv | hv
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv
      exact visKnown_of_kind (Or.inl rfl)
    · rcases hp : receivedPlaintext tr tr' with _ | _
      · rw [hp] at hv; cases hv
      · rw [hp] at hv
        rcases List.mem_singleton.mp hv with rfl
        exact visKnown_of_kind (Or.inr (Or.inr rfl))

theorem move_known (m : Move) {tr : ExecTrace} (hs : OpkNetOK tr) {v : VisEntry}
    (hv : v ∈ m.vis tr) : VisKnown (m.next tr) v := by
  have hle := m.le_next tr
  unfold Move.vis at hv
  rcases List.mem_append.mp hv with hv | hv
  · cases m with
    | aliceStart _ _ _ _ _ _ => exact aliceVis_known hle (List.mem_of_mem_take hv)
    | bobStart _ _ _ _ _ _ _ _ =>
      exact bobVis_known hle (fun t ht => Bytes.AttackerKnows_le _ _ _ hle (bobOpkPk_known hs ht))
        (List.mem_of_mem_take hv)
    | encrypt _ _ _ _ _ => exact encVis_known hle hv
    | encryptAbort _ _ => exact encVis_known hle hv
    | encryptFail _ _ _ => exact encVis_known hle hv
    | decrypt _ _ _ _ _ _ => exact decVis_known hle hv
    | decryptSkipped _ _ _ _ _ _ _ => exact decVis_known hle hv
    | reject _ =>
      rcases List.mem_cons.mp hv with rfl | hv
      · exact fun _ _ ht => by cases ht
      · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv
        exact visKnown_of_kind (Or.inl rfl)
    | setup => exact absurd hv List.not_mem_nil
    | compromiseIK => exact absurd hv List.not_mem_nil
    | compromiseSPK => exact absurd hv List.not_mem_nil
    | compromisePQSPK => exact absurd hv List.not_mem_nil
    | compromiseOPK => exact absurd hv List.not_mem_nil
    | exposeKey => exact absurd hv List.not_mem_nil
    | exposeSpqr => exact absurd hv List.not_mem_nil
    | exposeSkipped => exact absurd hv List.not_mem_nil
    | attackerSend => exact absurd hv List.not_mem_nil
    | brkDH =>
      exact absurd hv List.not_mem_nil
    | brkKEM =>
      exact absurd hv List.not_mem_nil
  · exact exposures_known hv

theorem runMoves_known : ∀ (L : List Move) {tr : ExecTrace}, OpkNetOK tr → ∀ {v : VisEntry},
    v ∈ (runMoves L tr).2 → VisKnown (runMoves L tr).1 v
  | [], _, _, _, hv => by cases hv
  | m :: L, tr, hs, _, hv => by
    rw [runMoves_cons_snd] at hv
    rw [runMoves_cons_fst]
    rcases List.mem_append.mp hv with hm | hL
    · exact (move_known m hs hm).mono (runMoves_le L (m.next tr))
    · exact runMoves_known L (hs.next m) hL

/-- Every term of a visible `send`, `recv`, or `leak` entry of `runVis r ms` is attacker-known on
`runTraceMoves r ms`. -/
theorem runVis_known {r : ProtocolSetup} {ms : List Move} {v : VisEntry} (hv : v ∈ runVis r ms) :
    VisKnown (runTraceMoves r ms) v :=
  runMoves_known _ opkNetOK_nil hv

theorem newSent_known {tr tr' : ExecTrace} {t : DY.Bytes}
    (ht : t ∈ (newIndices tr tr').filterMap fun i => tr'.getMessageSentAt i) :
    t.AttackerKnows tr' := by
  obtain ⟨_, _, hi⟩ := List.mem_filterMap.mp ht
  exact getMessageSentAt_attackerKnows hi

/-- Every public setup message in `setupSent r` is attacker-known on `runTraceMoves r ms`. -/
theorem setupSent_known {r : ProtocolSetup} {ms : List Move} {t : DY.Bytes} (ht : t ∈ setupSent r) :
    t.AttackerKnows (runTraceMoves r ms) :=
  Bytes.AttackerKnows_le _ _ _ (setupTrace_le_runTrace r ms) (newSent_known ht)

/-! ## Prefix reachability and `ModelRun` closure -/

theorem runTrace_take_reach_append {r : ProtocolSetup} {ms δ : List Move}
    (hall : ∀ k, (runTraceMoves r (ms.take k)).Reachable reachability)
    (hδ : ∀ j, (runTraceMoves r (ms ++ δ.take j)).Reachable reachability) :
    ∀ k, (runTraceMoves r ((ms ++ δ).take k)).Reachable reachability := by
  intro k
  rw [List.take_append]
  by_cases hk : k ≤ ms.length
  · rw [Nat.sub_eq_zero_of_le hk, List.take_zero, List.append_nil]
    exact hall k
  · have he : ms.take k = ms := List.take_of_length_le (by omega)
    rw [he]
    exact hδ _

theorem runTrace_take_reach_snoc {r : ProtocolSetup} {ms : List Move} {m : Move}
    (hall : ∀ k, (runTraceMoves r (ms.take k)).Reachable reachability)
    (hlast : (runTraceMoves r (ms ++ [m])).Reachable reachability) :
    ∀ k, (runTraceMoves r ((ms ++ [m]).take k)).Reachable reachability := by
  refine runTrace_take_reach_append hall fun j => ?_
  cases j with
  | zero =>
    have h := hall ms.length
    rw [List.take_length] at h
    simpa using h
  | succ _ => simpa using hlast

theorem runTrace_take_reach_prefix {r : ProtocolSetup} {ms₀ δ : List Move}
    (hall : ∀ k, (runTraceMoves r ((ms₀ ++ δ).take k)).Reachable reachability) :
    ∀ k, (runTraceMoves r (ms₀.take k)).Reachable reachability := by
  intro k
  by_cases hk : k ≤ ms₀.length
  · have h := hall k
    rwa [List.take_append_of_le_length hk] at h
  · have he : ms₀.take k = ms₀ := List.take_of_length_le (by omega)
    have h := hall ms₀.length
    rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length] at h
    rw [he]; exact h

theorem movesAnchored_append : ∀ (ms₁ ms₂ : List Move) (tr : ExecTrace),
    MovesAnchored (ms₁ ++ ms₂) tr ↔
      MovesAnchored ms₁ tr ∧ MovesAnchored ms₂ (runMoves ms₁ tr).1
  | [], _, _ => by simp [MovesAnchored]
  | m :: ms₁, ms₂, tr => by
    simp only [List.cons_append, MovesAnchored, runMoves_cons_fst,
      movesAnchored_append ms₁ ms₂ (m.next tr), and_assoc]

theorem compromisesCurrentFrom_append : ∀ (ms₁ ms₂ : List Move) (tr : ExecTrace),
    compromisesCurrentFrom tr (ms₁ ++ ms₂) =
      (compromisesCurrentFrom tr ms₁ && compromisesCurrentFrom (runMoves ms₁ tr).1 ms₂)
  | [], _, _ => by simp [compromisesCurrentFrom]
  | m :: ms₁, ms₂, tr => by
    simp only [List.cons_append, compromisesCurrentFrom, runMoves_cons_fst,
      compromisesCurrentFrom_append ms₁ ms₂ (m.next tr), Bool.and_assoc]

theorem ownSaltsFrom_append : ∀ (ms₁ ms₂ : List Move) (tr : ExecTrace),
    ownSaltsFrom tr (ms₁ ++ ms₂) =
      (ownSaltsFrom tr ms₁ && ownSaltsFrom (runMoves ms₁ tr).1 ms₂)
  | [], _, _ => by simp [ownSaltsFrom]
  | m :: ms₁, ms₂, tr => by
    simp only [List.cons_append, ownSaltsFrom, runMoves_cons_fst,
      ownSaltsFrom_append ms₁ ms₂ (m.next tr), Bool.and_assoc]

theorem peerFaithful_append {r : ProtocolSetup} {ms₁ ms₂ : List Move} :
    PeerFaithful r (ms₁ ++ ms₂) ↔ PeerFaithful r ms₁ ∧ PeerFaithful r ms₂ :=
  List.forall_mem_append

theorem peerFaithful_prefix {r : ProtocolSetup} {ms₁ ms₂ : List Move}
    (h : PeerFaithful r (ms₁ ++ ms₂)) : PeerFaithful r ms₁ :=
  (peerFaithful_append.mp h).1

theorem peerFaithful_snoc {r : ProtocolSetup} {ms : List Move} {m : Move}
    (h : PeerFaithful r ms) (hm : m.MatchesSetupPeer r) : PeerFaithful r (ms ++ [m]) :=
  peerFaithful_append.mpr ⟨h, fun _ hx => by rcases List.mem_singleton.mp hx with rfl; exact hm⟩

/-- `ModelRun` is closed under taking prefixes of the move list. -/
theorem modelRun_prefix {r : ProtocolSetup} {ms₀ δ : List Move}
    (h : ModelRun r (ms₀ ++ δ)) : ModelRun r ms₀ := by
  obtain ⟨hsetup, hns, ⟨_, hanc, hall⟩, hcomp, hown, hpeer, hstate⟩ := h
  have hr₀ : (runTraceMoves r ms₀).Reachable reachability := by
    have hk := hall ms₀.length
    rwa [List.take_append_of_le_length (Nat.le_refl _), List.take_length] at hk
  have hcomp₀ : compromisesCurrentFrom (setupTrace r) ms₀ = true := by
    rw [compromisesCurrentFrom_append, Bool.and_eq_true] at hcomp
    exact hcomp.1
  have hown₀ : ownSaltsFrom (setupTrace r) ms₀ = true := by
    rw [ownSaltsFrom_append, Bool.and_eq_true] at hown
    exact hown.1
  have hst₀ : StateFaithful r ms₀ := by
    intro i j mi mj p k b hij hi hj hl hs hl'
    have hj' : j < ms₀.length := (List.getElem?_eq_some_iff.mp hj).1
    have hi' : i < ms₀.length := Nat.lt_trans hij hj'
    refine hstate i j mi mj p k b hij ?_ ?_ hl ?_ hl'
    · rw [List.getElem?_append_left hi']; exact hi
    · rw [List.getElem?_append_left hj']; exact hj
    · rw [List.take_append_of_le_length (Nat.le_of_lt hi')]; exact hs
  exact ⟨hsetup, fun m hm => hns m (List.mem_append_left _ hm),
    ⟨hr₀, ((movesAnchored_append ms₀ δ _).mp hanc).1, runTrace_take_reach_prefix hall⟩,
    hcomp₀, hown₀, peerFaithful_prefix hpeer, hst₀⟩

/-- Extends `ModelRun r ms` by a single move `m`. -/
theorem modelRun_snoc_of_old {r : ProtocolSetup} {ms : List Move} {m : Move} (hrun : ModelRun r ms)
    (h : (setupRandoms r).length = (if r.withOpk then 7 else 6) ∧
      (∀ m' ∈ ms ++ [m], m'.isSetup = false) ∧
      ((runTraceMoves r (ms ++ [m])).Reachable reachability ∧
        MovesAnchored (ms ++ [m]) (setupTrace r)) ∧
      compromisesCurrentFrom (setupTrace r) (ms ++ [m]) = true ∧
      ownSaltsFrom (setupTrace r) (ms ++ [m]) = true)
    (hpeer : m.MatchesSetupPeer r) (hstate : StateFaithful r (ms ++ [m])) :
    ModelRun r (ms ++ [m]) :=
  ⟨h.1, h.2.1, ⟨h.2.2.1.1, h.2.2.1.2, runTrace_take_reach_snoc hrun.2.2.1.2.2 h.2.2.1.1⟩,
    h.2.2.2.1, h.2.2.2.2, peerFaithful_snoc hrun.2.2.2.2.2.1 hpeer, hstate⟩

end DY.Libsignal.Composed.Refinement

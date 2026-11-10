/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem1Reductions
public import Computational.Proofs.CryptoGames.SM.GameProofDefs

/-!
# Helper invariants and projections for Lemma 17

**Checked by Lean.** Defines the well-formed game-state invariant `WFState` and projections
`toAuth` and `toMirror` used in `SM/Theorem1/Lemma17.lean`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames.SM.Thm1L17

open CryptoGames.SM.Thm1

set_option linter.unusedSectionVars false

variable {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]

/-! ### Epoch and leak helpers -/

theorem sendsIn_add_one (P : Party) (t : ℕ) :
    P.sendsIn (t + 1) = !(P.sendsIn t) := by
  cases P <;> {
    unfold Party.sendsIn
    rw [Bool.eq_iff_iff]
    simp only [Bool.not_eq_true', beq_iff_eq, beq_eq_false_iff_ne, ne_eq]
    omega
  }

theorem sendsIn_of_sendsIn_add_one_eq_false {P : Party} {t : ℕ}
    (h : P.sendsIn (t + 1) = false) : P.sendsIn t = true := by
  rw [sendsIn_add_one, Bool.not_eq_false'] at h
  exact h

theorem sendsIn_eq_false_of_sendsIn_add_one {P : Party} {t : ℕ}
    (h : P.sendsIn (t + 1) = true) : P.sendsIn t = false := by
  rw [sendsIn_add_one, Bool.not_eq_true'] at h
  exact h

theorem senderOf_eq_of_sendsIn {P : Party} {t : ℕ} (h : P.sendsIn t = true) :
    Party.senderOf t = P := by
  cases P <;> simp [Party.sendsIn, Party.senderOf] at h ⊢ <;> omega

theorem receiverOf_eq_other_of_sendsIn {P : Party} {t : ℕ} (h : P.sendsIn t = true) :
    Party.receiverOf t = P.other := by
  unfold Party.receiverOf
  rw [senderOf_eq_of_sendsIn h]

@[simp] theorem healedBy_none (Δ t : ℕ) : healedBy none Δ t = true := rfl

@[simp] theorem healedBy_some (l Δ t : ℕ) :
    healedBy (some l) Δ t = decide (l + Δ ≤ t) := rfl

@[simp] theorem ltOpt_none (t : ℕ) : ltOpt none t = true := rfl

@[simp] theorem ltOpt_some (l t : ℕ) : ltOpt (some l) t = decide (l < t) := rfl

@[simp] theorem maxOpt_none (t : ℕ) : maxOpt none t = t := rfl

@[simp] theorem maxOpt_some (l t : ℕ) : maxOpt (some l) t = max l t := rfl

theorem le_maxOpt_right (tL : Option ℕ) (t : ℕ) : t ≤ maxOpt tL t := by
  cases tL <;> simp

theorem le_maxOpt_left (l t : ℕ) : l ≤ maxOpt (some l) t := by
  simp

theorem not_healedBy_lt_of_healedBy {tL : Option ℕ} {Δ t₁ t₂ : ℕ}
    (h1 : healedBy tL Δ t₁ = false) (h2 : healedBy tL Δ t₂ = true) : t₁ < t₂ := by
  cases tL with
  | none => simp at h1
  | some l =>
    simp only [healedBy_some, decide_eq_false_iff_not, decide_eq_true_eq] at h1 h2
    omega

theorem not_healedBy_leak {tL : Option ℕ} {Δ t l₀ : ℕ}
    (h : healedBy tL Δ t = false) :
    healedBy (some (maxOpt tL l₀)) Δ t = false := by
  cases tL with
  | none => simp at h
  | some l =>
    simp only [healedBy_some, decide_eq_false_iff_not, maxOpt_some] at h ⊢
    omega

theorem mem_targetsL_of_validGuess {Δ t : ℕ} {tL : Option ℕ} (_hΔ : 0 < Δ)
    (hv : lastLeakGuessAdmissible Δ tL t = true) : tL ∈ admissibleLastLeakGuesses Δ t := by
  unfold lastLeakGuessAdmissible at hv
  unfold admissibleLastLeakGuesses
  cases tL with
  | none => simp
  | some l =>
    simp only [healedBy_some, decide_eq_true_eq] at hv
    simp only [Finset.mem_insert, reduceCtorEq, Finset.mem_image, Finset.mem_range,
      Option.some.injEq, exists_eq_right, false_or]
    omega

theorem max?_cons_of_forall_le {a : ℕ} {xs : List ℕ} (h : ∀ b ∈ xs, b ≤ a) :
    (a :: xs).max? = some a := by
  rw [List.max?_eq_some_iff]
  refine ⟨List.mem_cons_self, fun b hb => ?_⟩
  rcases List.mem_cons.mp hb with rfl | hb
  · exact le_rfl
  · exact h b hb

theorem leaks_all_canon (t : ℕ) (s : GameState St Msg C) :
    s.leaks.all (fun l => !(ltOpt (canon t s) l && decide (l < t))) = true := by
  rw [List.all_eq_true]
  intro l hl
  by_cases hlt : l < t
  · have hmem : l ∈ s.leaks.filter (· < t) := by
      rw [List.mem_filter]
      exact ⟨hl, decide_eq_true hlt⟩
    have hne : s.leaks.filter (· < t) ≠ [] := List.ne_nil_of_mem hmem
    cases hmax : (s.leaks.filter (· < t)).max? with
    | none => exact absurd (List.max?_eq_none_iff.mp hmax) hne
    | some m =>
      have hle : l ≤ m := (List.max?_eq_some_iff.mp hmax).2 l hmem
      unfold canon
      rw [hmax]
      have hdec : decide (m < l) = false := decide_eq_false (by omega)
      simp [ltOpt_some, hdec]
  · simp [hlt]

theorem canon_eq_tL_of_healedBy {Δ t : ℕ} {s : GameState St Msg C}
    (hΔ : 0 < Δ) (htL : s.tL = s.leaks.max?) (hh : healedBy s.tL Δ t = true) :
    canon t s = s.tL := by
  unfold canon
  rw [htL]
  have hfilt : s.leaks.filter (· < t) = s.leaks := by
    rw [List.filter_eq_self]
    intro l hl
    have hne : s.leaks ≠ [] := List.ne_nil_of_mem hl
    cases hmax : s.leaks.max? with
    | none => exact absurd (List.max?_eq_none_iff.mp hmax) hne
    | some m =>
      rw [htL, hmax] at hh
      simp only [healedBy_some, decide_eq_true_eq] at hh
      have hle : l ≤ m := (List.max?_eq_some_iff.mp hmax).2 l hl
      simp only [decide_eq_true_eq]
      omega
  rw [hfilt]

theorem canon_leak_of_le {t l₀ : ℕ} {s : GameState St Msg C} (hl : t ≤ l₀) :
    canon t (s.leak l₀) = canon t s := by
  unfold canon GameState.leak
  have hle : t ≤ maxOpt s.tL l₀ := hl.trans (le_maxOpt_right s.tL l₀)
  have hdec : (decide (maxOpt s.tL l₀ < t)) = false := by
    simp only [decide_eq_false_iff_not]; omega
  simp [hdec]

/-! ### Game-state invariant `WFState` -/

/-- Well-formedness invariant on `GameState` maintained across SM oracle steps. -/
structure WFState (Δ : ℕ) (s : GameState St Msg C) : Prop where
  tL_eq : s.tL = s.leaks.max?
  epoch_bound : ∀ P : Party,
    s.epoch P ≤ if P.sendsIn (s.epoch P) then s.epoch P.other + 1 else s.epoch P.other
  corrs_le_leaks : ∀ pe ∈ s.corrs, ∃ l ∈ s.leaks, pe.2 ≤ l
  comp_not_healed : ∀ pos ∈ s.comp, healedBy s.tL Δ pos.epoch = false
  chall_in_trans : ∀ pos ∈ s.chall, ∃ r ∈ s.trans, r.pos = pos ∧ r.pos ∉ s.comp
  trans_sender : ∀ r ∈ s.trans, r.pos.sender.sendsIn r.pos.epoch = true
  trans_epoch_idx : ∀ r ∈ s.trans,
    r.pos.epoch < s.epoch r.pos.sender ∨
      (r.pos.epoch = s.epoch r.pos.sender ∧ r.pos.idx ≤ s.idx r.pos.sender)
  trans_uncomp : ∀ r ∈ s.trans, r.pos ∉ s.comp →
    lastLeakGuessAdmissible Δ (canon r.pos.epoch s) r.pos.epoch = true ∧
    ∀ pe ∈ s.corrs, pe.1 = Party.receiverOf r.pos.epoch →
      ltOpt (canon r.pos.epoch s) pe.2 = false

theorem WFState.trans_epoch_le {Δ : ℕ} {s : GameState St Msg C}
    (hwf : WFState Δ s) (r : Record Msg C) (hr : r ∈ s.trans) :
    r.pos.epoch ≤ s.epoch r.pos.sender := by
  rcases hwf.trans_epoch_idx r hr with h | ⟨h, _⟩ <;> omega

theorem WFState.epoch_le_other_add_one {Δ : ℕ} {s : GameState St Msg C}
    (hwf : WFState Δ s) (P : Party) : s.epoch P ≤ s.epoch P.other + 1 := by
  have h := hwf.epoch_bound P
  split at h <;> omega

theorem WFState.epoch_le_any_add_one {Δ : ℕ} {s : GameState St Msg C}
    (hwf : WFState Δ s) (P Q : Party) : s.epoch P ≤ s.epoch Q + 1 := by
  have h := hwf.epoch_le_other_add_one P
  cases P <;> cases Q <;> simp at h ⊢ <;> omega

theorem WFState.epoch_le_max {Δ : ℕ} {s : GameState St Msg C}
    (_hwf : WFState Δ s) (P : Party) : s.epoch P ≤ max (s.epoch .A) (s.epoch .B) := by
  cases P <;> simp

theorem WFState.tL_leak_eq {Δ : ℕ} {s : GameState St Msg C}
    (hwf : WFState Δ s) (l₀ : ℕ) : (s.leak l₀).tL = (s.leak l₀).leaks.max? := by
  unfold GameState.leak
  dsimp only
  symm
  apply max?_cons_of_forall_le
  intro b hb
  have hne : s.leaks ≠ [] := List.ne_nil_of_mem hb
  cases hmax : s.leaks.max? with
  | none => exact absurd (List.max?_eq_none_iff.mp hmax) hne
  | some m =>
    have hle : b ≤ m := (List.max?_eq_some_iff.mp hmax).2 b hb
    rw [hwf.tL_eq, hmax]
    exact hle.trans (le_maxOpt_left m l₀)

theorem wfState_init (sm : SMScheme Key St Msg Coins C) (Δ : ℕ) (k : Key) (b : Bool) :
    WFState Δ (initState sm k b) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P; cases P <;> simp [initState]
  · intro pe hpe; simp [initState] at hpe
  · intro pos hpos; simp [initState] at hpos
  · intro pos hpos; simp [initState] at hpos
  · intro r hr; simp [initState] at hr
  · intro r hr; simp [initState] at hr
  · intro r hr; simp [initState] at hr

theorem wfState_leak_of_trans_le {Δ l₀ : ℕ} {s : GameState St Msg C}
    (hwf : WFState Δ s) (hl₀ : ∀ r ∈ s.trans, r.pos.epoch ≤ l₀) :
    WFState Δ (s.leak l₀) := by
  refine ⟨hwf.tL_leak_eq l₀, hwf.epoch_bound, ?_, ?_, hwf.chall_in_trans,
    hwf.trans_sender, hwf.trans_epoch_idx, ?_⟩
  · intro pe hpe
    rcases hwf.corrs_le_leaks pe hpe with ⟨l, hl, hle⟩
    exact ⟨l, List.mem_cons_of_mem _ hl, hle⟩
  · intro pos hpos
    exact not_healedBy_leak (hwf.comp_not_healed pos hpos)
  · intro r hr huncomp
    have hcanon : canon r.pos.epoch (s.leak l₀) = canon r.pos.epoch s :=
      canon_leak_of_le (hl₀ r hr)
    rw [hcanon]
    exact hwf.trans_uncomp r hr huncomp

theorem epMgmt_wf {Δ qep : ℕ} {s s₁ : GameState St Msg C} {P : Party} {bad : Bool}
    (hwf : WFState Δ s) (hep : s.epMgmt Δ qep P bad = some s₁) :
    WFState Δ s₁ ∧ P.sendsIn (s₁.epoch P) = true := by
  unfold GameState.epMgmt at hep
  by_cases hsends : P.sendsIn (s.epoch P + 1) = true
  · simp only [hsends, ↓reduceIte] at hep
    by_cases hq : qep < s.epoch P + 1
    · simp [hq] at hep
    · simp only [hq, ↓reduceIte, Option.some.injEq] at hep
      let s₀ := if (bad && !(s.safeCh Δ P)) = true then s.leak (s.epoch P + 1) else s
      change { s₀ with epoch := Function.update s₀.epoch P (s₀.epoch P + 1),
                       idx := Function.update s₀.idx P 0 } = s₁ at hep
      subst hep
      have hs₀_wf : WFState Δ s₀ := by
        dsimp only [s₀]
        split
        · apply wfState_leak_of_trans_le hwf
          intro r hr
          exact (hwf.trans_epoch_le r hr).trans (hwf.epoch_le_any_add_one r.pos.sender P)
        · exact hwf
      have hs₀_ep : s₀.epoch = s.epoch := by
        dsimp only [s₀]; split <;> rfl
      have hs₀_idx : s₀.idx = s.idx := by
        dsimp only [s₀]; split <;> rfl
      have hsends0 : P.sendsIn (s.epoch P) = false :=
        sendsIn_eq_false_of_sendsIn_add_one hsends
      have hboundP : s.epoch P ≤ s.epoch P.other := by
        have hb := hwf.epoch_bound P
        rw [hsends0] at hb
        simpa using hb
      refine ⟨⟨hs₀_wf.tL_eq, ?_, hs₀_wf.corrs_le_leaks, hs₀_wf.comp_not_healed,
        hs₀_wf.chall_in_trans, hs₀_wf.trans_sender, ?_, ?_⟩, ?_⟩
      · intro Q
        dsimp only
        rw [hs₀_ep]
        by_cases hQP : Q = P
        · subst hQP
          simp [Function.update_self, Function.update_of_ne (Party.other_ne Q), hsends, hboundP]
        · have hne : Q.other = P := by cases Q <;> cases P <;> trivial
          have hbQ := hwf.epoch_bound Q
          rw [hne] at hbQ
          simp only [Function.update_of_ne hQP, hne, Function.update_self]
          split at hbQ <;> split <;> omega
      · intro r hr
        have hle := hs₀_wf.trans_epoch_le r hr
        have hidx := hs₀_wf.trans_epoch_idx r hr
        dsimp only
        rw [hs₀_ep] at hle ⊢
        rw [hs₀_ep, hs₀_idx] at hidx
        rw [hs₀_idx]
        by_cases hP : r.pos.sender = P
        · left
          rw [hP] at hle ⊢
          rw [Function.update_self]
          omega
        · rw [Function.update_of_ne hP, Function.update_of_ne hP]
          exact hidx
      · intro r hr huncomp
        exact hs₀_wf.trans_uncomp r hr huncomp
      · dsimp only
        rw [hs₀_ep, Function.update_self]
        exact hsends
  · have hsendsF : P.sendsIn (s.epoch P + 1) = false := Bool.eq_false_iff.mpr hsends
    simp only [hsendsF, Bool.false_eq_true, ↓reduceIte] at hep
    by_cases hq : qep < s.epoch P
    · simp [hq] at hep
    · simp only [hq, ↓reduceIte, Option.some.injEq] at hep
      subst hep
      exact ⟨hwf, sendsIn_of_sendsIn_add_one_eq_false hsendsF⟩

theorem record_wf {Δ : ℕ} {s : GameState St Msg C} {P : Party} {st' : St}
    {r : Record Msg C} {isChall : Bool} (hΔ : 0 < Δ) (hwf : WFState Δ s)
    (hr_sender : r.pos.sender = P) (hr_epoch : r.pos.epoch = s.epoch P)
    (hr_idx : r.pos.idx = s.idx P + 1)
    (hsends : P.sendsIn (s.epoch P) = true)
    (hchall_safe : isChall = true → s.safeCh Δ P = true) :
    WFState Δ (s.record Δ P st' r isChall) := by
  have hr_ne : ∀ r₀ ∈ s.trans, r₀.pos ≠ r.pos := by
    intro r₀ hr₀ heq
    have h1 := hwf.trans_epoch_idx r₀ hr₀
    have hs0 : r₀.pos.sender = P := by rw [heq, hr_sender]
    have he0 : r₀.pos.epoch = s.epoch P := by rw [heq, hr_epoch]
    have hi0 : r₀.pos.idx = s.idx P + 1 := by rw [heq, hr_idx]
    rw [hs0, he0, hi0] at h1
    rcases h1 with h1 | ⟨_, h1⟩ <;> omega
  refine ⟨hwf.tL_eq, hwf.epoch_bound, hwf.corrs_le_leaks, ?_, ?_, ?_, ?_, ?_⟩
  · intro pos hpos
    unfold GameState.record at hpos
    dsimp only at hpos ⊢
    split at hpos
    · exact hwf.comp_not_healed pos hpos
    · rename_i hns
      rcases List.mem_cons.mp hpos with rfl | hpos
      · rw [hr_epoch]
        exact Bool.eq_false_iff.mpr hns
      · exact hwf.comp_not_healed pos hpos
  · intro pos hpos
    unfold GameState.record at hpos ⊢
    dsimp only at hpos ⊢
    have hcase : pos = r.pos ∧ isChall = true ∨ pos ∈ s.chall := by
      split at hpos
      · rename_i hch
        rcases List.mem_cons.mp hpos with rfl | hpos
        · exact Or.inl ⟨rfl, hch⟩
        · exact Or.inr hpos
      · exact Or.inr hpos
    rcases hcase with ⟨rfl, hch⟩ | hpos
    · have hsafe : s.safeCh Δ P = true := hchall_safe hch
      refine ⟨r, List.mem_cons_self, rfl, ?_⟩
      simp only [hsafe, ↓reduceIte]
      intro hmem
      have hnh := hwf.comp_not_healed r.pos hmem
      unfold GameState.safeCh at hsafe
      rw [← hr_epoch, hnh] at hsafe
      cases hsafe
    · rcases hwf.chall_in_trans pos hpos with ⟨r₀, hr₀, rfl, huncomp₀⟩
      refine ⟨r₀, List.mem_cons_of_mem _ hr₀, rfl, ?_⟩
      split
      · exact huncomp₀
      · intro hmem
        rcases List.mem_cons.mp hmem with heq | hmem
        · exact hr_ne r₀ hr₀ heq
        · exact huncomp₀ hmem
  · intro r' hr'
    unfold GameState.record at hr'
    dsimp only at hr'
    rcases List.mem_cons.mp hr' with rfl | hr'
    · rw [hr_sender, hr_epoch]
      exact hsends
    · exact hwf.trans_sender r' hr'
  · intro r' hr'
    unfold GameState.record at hr' ⊢
    dsimp only at hr' ⊢
    rcases List.mem_cons.mp hr' with rfl | hr'
    · right
      rw [hr_sender, hr_epoch, hr_idx, Function.update_self]
      exact ⟨rfl, le_rfl⟩
    · have h1 := hwf.trans_epoch_idx r' hr'
      by_cases hP : r'.pos.sender = P
      · rw [hP] at h1 ⊢
        rw [Function.update_self]
        rcases h1 with h1 | ⟨h1, h2⟩
        · exact Or.inl h1
        · exact Or.inr ⟨h1, by omega⟩
      · rw [Function.update_of_ne hP]
        exact h1
  · intro r' hr' huncomp
    have hcanon : canon r'.pos.epoch (s.record Δ P st' r isChall) = canon r'.pos.epoch s := rfl
    rw [hcanon]
    unfold GameState.record at hr' huncomp
    dsimp only at hr' huncomp
    rcases List.mem_cons.mp hr' with rfl | hr'
    · have hsafe : s.safeCh Δ P = true := by
        by_contra hns
        have hnsF : s.safeCh Δ P = false := Bool.eq_false_iff.mpr hns
        rw [hnsF] at huncomp
        exact huncomp List.mem_cons_self
      unfold GameState.safeCh at hsafe
      rw [← hr_epoch] at hsafe
      have hc_eq : canon r'.pos.epoch s = s.tL :=
        canon_eq_tL_of_healedBy hΔ hwf.tL_eq hsafe
      rw [hc_eq]
      refine ⟨hsafe, fun pe hpe _ => ?_⟩
      rcases hwf.corrs_le_leaks pe hpe with ⟨l, hl, hle⟩
      have hne : s.leaks ≠ [] := List.ne_nil_of_mem hl
      cases hmax : s.leaks.max? with
      | none => exact absurd (List.max?_eq_none_iff.mp hmax) hne
      | some m =>
        have hlm : l ≤ m := (List.max?_eq_some_iff.mp hmax).2 l hl
        rw [hwf.tL_eq, hmax]
        simp only [ltOpt_some, decide_eq_false_iff_not]
        omega
    · apply hwf.trans_uncomp r' hr'
      intro hmem
      apply huncomp
      split
      · exact hmem
      · exact List.mem_cons_of_mem _ hmem

theorem accept_wf {Δ : ℕ} {s : GameState St Msg C} {P : Party} {st' : St} {pos : Pos}
    (hwf : WFState Δ s) (hpos : pos.epoch ≤ max (s.epoch P) (s.epoch P.other)) :
    WFState Δ (s.accept P st' pos) := by
  refine ⟨hwf.tL_eq, ?_, hwf.corrs_le_leaks, ?_, ?_, ?_, ?_, ?_⟩
  · intro Q
    unfold GameState.accept GameState.delete
    dsimp only
    by_cases hQP : Q = P
    · subst hQP
      simp only [Function.update_self, Function.update_of_ne (Party.other_ne Q)]
      by_cases hle : pos.epoch ≤ s.epoch Q
      · have hmax : max (s.epoch Q) pos.epoch = s.epoch Q := Nat.max_eq_left hle
        rw [hmax]
        exact hwf.epoch_bound Q
      · have hle' : pos.epoch ≤ s.epoch Q.other := by omega
        have hmax : max (s.epoch Q) pos.epoch = pos.epoch := Nat.max_eq_right (by omega)
        rw [hmax]
        split <;> omega
    · have hne : Q.other = P := by cases Q <;> cases P <;> trivial
      have hbQ := hwf.epoch_bound Q
      rw [hne] at hbQ
      simp only [Function.update_of_ne hQP, hne, Function.update_self]
      split at hbQ <;> split <;> omega
  · intro pos' hpos'
    unfold GameState.accept GameState.delete at hpos' ⊢
    dsimp only at hpos' ⊢
    rw [List.mem_filter] at hpos'
    exact hwf.comp_not_healed pos' hpos'.1
  · intro pos' hpos'
    unfold GameState.accept GameState.delete at hpos' ⊢
    dsimp only at hpos' ⊢
    rw [List.mem_filter] at hpos'
    rcases hwf.chall_in_trans pos' hpos'.1 with ⟨r, hr, rfl, huncomp⟩
    refine ⟨r, ?_, rfl, ?_⟩
    · rw [List.mem_filter]
      exact ⟨hr, hpos'.2⟩
    · intro hmem
      rw [List.mem_filter] at hmem
      exact huncomp hmem.1
  · intro r hr
    unfold GameState.accept GameState.delete at hr
    dsimp only at hr
    rw [List.mem_filter] at hr
    exact hwf.trans_sender r hr.1
  · intro r hr
    unfold GameState.accept GameState.delete at hr ⊢
    dsimp only at hr ⊢
    rw [List.mem_filter] at hr
    have h1 := hwf.trans_epoch_idx r hr.1
    by_cases hP : r.pos.sender = P
    · rw [hP] at h1 ⊢
      rw [Function.update_self]
      rcases h1 with h1 | ⟨h1, h2⟩
      · exact Or.inl (by omega)
      · by_cases hle : pos.epoch ≤ s.epoch P
        · right
          exact ⟨by omega, h2⟩
        · left
          omega
    · rw [Function.update_of_ne hP]
      exact h1
  · intro r hr huncomp
    have hcanon : canon r.pos.epoch (s.accept P st' pos) = canon r.pos.epoch s := rfl
    rw [hcanon]
    unfold GameState.accept GameState.delete at hr huncomp
    dsimp only at hr huncomp
    rw [List.mem_filter] at hr
    apply hwf.trans_uncomp r hr.1
    intro hmem
    apply huncomp
    rw [List.mem_filter]
    exact ⟨hmem, hr.2⟩

theorem afterCorr_wf {Δ : ℕ} {s : GameState St Msg C} {P : Party}
    (hΔ : 0 < Δ) (hwf : WFState Δ s) (hallow : s.corrAllowed P = true) :
    WFState Δ (s.afterCorr P) := by
  unfold GameState.afterCorr
  let s₁ : GameState St Msg C :=
    { s with comp := (s.trans.filter (fun r : Record Msg C => r.pos.sender == P.other)).map
                       (fun r : Record Msg C => r.pos) ++ s.comp }
  let l₀ := max (s.epoch .A) (s.epoch .B)
  have htrans_le : ∀ r ∈ s.trans, r.pos.epoch ≤ l₀ := by
    intro r hr
    exact (hwf.trans_epoch_le r hr).trans (hwf.epoch_le_max r.pos.sender)
  have htL : (s₁.leak l₀).tL = (s₁.leak l₀).leaks.max? := hwf.tL_leak_eq l₀
  refine ⟨htL, hwf.epoch_bound, ?_, ?_, ?_, hwf.trans_sender, hwf.trans_epoch_idx, ?_⟩
  · intro pe hpe
    rcases List.mem_cons.mp hpe with rfl | hpe
    · refine ⟨maxOpt s.tL l₀, List.mem_cons_self, ?_⟩
      exact (hwf.epoch_le_max P).trans (le_maxOpt_right s.tL l₀)
    · rcases hwf.corrs_le_leaks pe hpe with ⟨l, hl, hle⟩
      exact ⟨l, List.mem_cons_of_mem _ hl, hle⟩
  · intro pos hpos
    dsimp only [s₁, GameState.leak] at hpos ⊢
    rcases List.mem_append.mp hpos with hpos | hpos
    · rcases List.mem_map.mp hpos with ⟨r, hr, rfl⟩
      rw [List.mem_filter] at hr
      have hle : r.pos.epoch ≤ maxOpt s.tL l₀ :=
        (htrans_le r hr.1).trans (le_maxOpt_right s.tL l₀)
      dsimp only [l₀] at hle
      simp only [healedBy_some, decide_eq_false_iff_not]
      omega
    · exact not_healedBy_leak (hwf.comp_not_healed pos hpos)
  · intro pos hpos
    dsimp only [s₁, GameState.leak] at hpos ⊢
    rcases hwf.chall_in_trans pos hpos with ⟨r, hr, rfl, huncomp⟩
    unfold GameState.corrAllowed at hallow
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false] at hallow
    have hne_other : r.pos.sender ≠ P.other := by
      intro heq
      have h1 := hallow.1 r.pos hpos
      exact h1 (beq_iff_eq.mpr heq)
    refine ⟨r, hr, rfl, ?_⟩
    intro hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · rcases List.mem_map.mp hmem with ⟨r', hr', heq⟩
      rw [List.mem_filter, beq_iff_eq] at hr'
      apply hne_other
      rw [← heq, hr'.2]
    · exact huncomp hmem
  · intro r hr huncomp
    have hcanon : canon r.pos.epoch { s₁.leak l₀ with corrs := (P, s.epoch P) :: s.corrs } =
        canon r.pos.epoch s := canon_leak_of_le (htrans_le r hr)
    rw [hcanon]
    have huncomp0 : r.pos ∉ s.comp := by
      intro hmem
      apply huncomp
      exact List.mem_append_right _ hmem
    have hne_other : r.pos.sender ≠ P.other := by
      intro heq
      apply huncomp
      apply List.mem_append_left
      rw [List.mem_map]
      refine ⟨r, ?_, rfl⟩
      rw [List.mem_filter]
      exact ⟨hr, beq_iff_eq.mpr heq⟩
    have htc := hwf.trans_uncomp r hr huncomp0
    refine ⟨htc.1, fun pe hpe hrec => ?_⟩
    rcases List.mem_cons.mp hpe with rfl | hpe
    · have hrec_eq : Party.receiverOf r.pos.epoch = r.pos.sender.other :=
        receiverOf_eq_other_of_sendsIn (hwf.trans_sender r hr)
      rw [hrec_eq] at hrec
      dsimp only at hrec
      exfalso
      apply hne_other
      rw [hrec, Party.other_other]
    · exact htc.2 pe hpe hrec

theorem pos_epoch_le_of_trivial {Δ : ℕ} {s : GameState St Msg C} {P : Party} {pos : Pos}
    (hwf : WFState Δ s) (hsafe : s.safeInj Δ = true) (htriv : s.trivial Δ pos = true) :
    pos.epoch ≤ max (s.epoch P) (s.epoch P.other) := by
  unfold GameState.trivial at htriv
  have hnh : healedBy s.tL Δ pos.epoch = false := by
    rcases Bool.or_eq_true_iff.mp htriv with hcomp | hnot
    · rw [List.contains_iff_mem] at hcomp
      exact hwf.comp_not_healed pos hcomp
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hnot
      exact hnot.2
  unfold GameState.safeInj at hsafe
  have hlt : pos.epoch < min (s.epoch .A) (s.epoch .B) :=
    not_healedBy_lt_of_healedBy hnh hsafe
  cases P <;> simp at hlt ⊢ <;> omega

theorem corrAllowed_eq_of_chall_in_trans {s sa : GameState St Msg C} (P : Party)
    (hchall : ∀ pos ∈ s.chall, ∃ r ∈ s.trans, r.pos = pos ∧ r.pos ∉ s.comp)
    (htrans : sa.trans = s.trans) (hcomp : sa.comp = s.comp)
    (hsa_chall : sa.chall = []) :
    sa.corrAllowed P = s.corrAllowed P := by
  unfold GameState.corrAllowed
  rw [htrans, hcomp, hsa_chall]
  simp only [List.any_nil, Bool.not_false, Bool.true_and]
  by_cases hany : (s.trans.any fun r => (r.pos.sender == P.other) && !s.comp.contains r.pos) = true
  · rw [hany]
    simp
  · have hanyF : (s.trans.any fun r => (r.pos.sender == P.other) && !s.comp.contains r.pos) = false :=
      Bool.eq_false_iff.mpr hany
    have hchF : (s.chall.any fun pos => pos.sender == P.other) = false := by
      rw [List.any_eq_false]
      intro pos hpos
      rcases hchall pos hpos with ⟨r, hr, rfl, huncomp⟩
      rw [List.any_eq_false] at hanyF
      have hrF := hanyF r hr
      have hncomp_b : (!s.comp.contains r.pos) = true := by
        simp [huncomp]
      rw [hncomp_b, Bool.and_true] at hrF
      exact hrF
    rw [hanyF, hchF]
    rfl

theorem authOK_of_nontrivial_inject {Δ : ℕ} {s : GameState St Msg C}
    {P : Party} {t' i' : ℕ} (hΔ : 0 < Δ) (hwf : WFState Δ s)
    (htriv : s.trivial Δ ⟨P.other, t', i'⟩ = false) :
    authLosingConditionsAvoided Δ (canon t' s) t' s = true ∧ canon t' s ∈ admissibleLastLeakGuesses Δ t' := by
  let pos : Pos := ⟨P.other, t', i'⟩
  unfold GameState.trivial at htriv
  simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, Bool.not_eq_false'] at htriv
  rcases htriv with ⟨hncomp_b, htriv2⟩
  have hncomp : pos ∉ s.comp := by
    simpa [List.contains_iff_mem] using hncomp_b
  have hmain : lastLeakGuessAdmissible Δ (canon t' s) t' = true ∧
      ∀ pe ∈ s.corrs, pe.1 = Party.receiverOf t' → ltOpt (canon t' s) pe.2 = false := by
    rcases htriv2 with htrans | hhealed
    · rw [List.any_eq_true] at htrans
      rcases htrans with ⟨r, hr, hrpos⟩
      rw [beq_iff_eq] at hrpos
      have hepoch : r.pos.epoch = t' := by rw [hrpos]
      have huncomp : r.pos ∉ s.comp := by rw [hrpos]; exact hncomp
      have htc := hwf.trans_uncomp r hr huncomp
      rw [hepoch] at htc
      exact htc
    · change healedBy s.tL Δ t' = true at hhealed
      have hc_eq : canon t' s = s.tL := canon_eq_tL_of_healedBy hΔ hwf.tL_eq hhealed
      rw [hc_eq]
      refine ⟨hhealed, fun pe hpe _ => ?_⟩
      rcases hwf.corrs_le_leaks pe hpe with ⟨l, hl, hle⟩
      have hne : s.leaks ≠ [] := List.ne_nil_of_mem hl
      cases hmax : s.leaks.max? with
      | none => exact absurd (List.max?_eq_none_iff.mp hmax) hne
      | some m =>
        have hlm : l ≤ m := (List.max?_eq_some_iff.mp hmax).2 l hl
        rw [hwf.tL_eq, hmax]
        simp only [ltOpt_some, decide_eq_false_iff_not]
        omega
  have hok : authLosingConditionsAvoided Δ (canon t' s) t' s = true := by
    unfold authLosingConditionsAvoided
    rw [hmain.1, beq_self_eq_true, leaks_all_canon]
    simp only [Bool.true_and, List.all_eq_true]
    intro pe hpe
    by_cases h1 : pe.1 = Party.receiverOf t'
    · rw [hmain.2 pe hpe h1]
      simp
    · have h1b : (pe.1 == Party.receiverOf t') = false := beq_eq_false_iff_ne.mpr h1
      simp [h1b]
  exact ⟨hok, mem_targetsL_of_validGuess hΔ hmain.1⟩

/-! ### State projections -/

/-- Project a game state to the corresponding `Config.auth` game state (`chall = []`, `b = false`). -/
def toAuth (s : GameState St Msg C) : GameState St Msg C :=
  { s with chall := [], b := false }

@[simp] theorem toMirror_initState (sm : SMScheme Key St Msg Coins C) (k : Key) (b : Bool) :
    toMirror (initState sm k b) = ({ st := fun _ => (), b } : GameState Unit Msg C) := rfl

@[simp] theorem toAuth_initState (sm : SMScheme Key St Msg Coins C) (k : Key) (b : Bool) :
    toAuth (initState sm k b) = initState sm k false := rfl

@[simp] theorem toMirror_safeCh (s : GameState St Msg C) (Δ : ℕ) (P : Party) :
    (toMirror s).safeCh Δ P = s.safeCh Δ P := rfl

@[simp] theorem toAuth_safeCh (s : GameState St Msg C) (Δ : ℕ) (P : Party) :
    (toAuth s).safeCh Δ P = s.safeCh Δ P := rfl

@[simp] theorem toAuth_safeInj (s : GameState St Msg C) (Δ : ℕ) :
    (toAuth s).safeInj Δ = s.safeInj Δ := rfl

@[simp] theorem toMirror_inTransit (s : GameState St Msg C) (Q : Party) (c : C) :
    (toMirror s).inTransit Q c = s.inTransit Q c := rfl

@[simp] theorem toAuth_inTransit (s : GameState St Msg C) (Q : Party) (c : C) :
    (toAuth s).inTransit Q c = s.inTransit Q c := rfl

@[simp] theorem toAuth_trivial (s : GameState St Msg C) (Δ : ℕ) (pos : Pos) :
    (toAuth s).trivial Δ pos = s.trivial Δ pos := rfl

@[simp] theorem toMirror_leak (s : GameState St Msg C) (l : ℕ) :
    (toMirror s).leak l = toMirror (s.leak l) := rfl

@[simp] theorem toAuth_leak (s : GameState St Msg C) (l : ℕ) :
    (toAuth s).leak l = toAuth (s.leak l) := rfl

theorem toMirror_epMgmt (s : GameState St Msg C) (Δ qep : ℕ) (P : Party) (bad : Bool) :
    (toMirror s).epMgmt Δ qep P bad = (s.epMgmt Δ qep P bad).map toMirror := by
  unfold GameState.epMgmt toMirror GameState.safeCh GameState.leak
  dsimp only
  split <;> split <;> try rfl
  dsimp only [Option.map]
  congr 1
  split <;> rfl

theorem toAuth_epMgmt (s : GameState St Msg C) (Δ qep : ℕ) (P : Party) (bad : Bool) :
    (toAuth s).epMgmt Δ qep P bad = (s.epMgmt Δ qep P bad).map toAuth := by
  unfold GameState.epMgmt toAuth GameState.safeCh GameState.leak
  dsimp only
  split <;> split <;> try rfl
  dsimp only [Option.map]
  congr 1
  split <;> rfl

@[simp] theorem toMirror_record (s : GameState St Msg C) (Δ : ℕ) (P : Party) (st' : St)
    (r : Record Msg C) (isChall : Bool) :
    (toMirror s).record Δ P () r isChall = toMirror (s.record Δ P st' r isChall) := by
  unfold GameState.record toMirror
  simp only [GameState.safeCh]
  congr 1

@[simp] theorem toAuth_record (s : GameState St Msg C) (Δ : ℕ) (P : Party) (st' : St)
    (r : Record Msg C) (isChall : Bool) :
    (toAuth s).record Δ P st' r false = toAuth (s.record Δ P st' r isChall) := rfl

@[simp] theorem toMirror_accept (s : GameState St Msg C) (P : Party) (st' : St) (pos : Pos) :
    (toMirror s).accept P () pos = toMirror (s.accept P st' pos) := rfl

@[simp] theorem toAuth_accept (s : GameState St Msg C) (P : Party) (st' : St) (pos : Pos) :
    (toAuth s).accept P st' pos = toAuth (s.accept P st' pos) := rfl

@[simp] theorem toMirror_afterCorr (s : GameState St Msg C) (P : Party) :
    (toMirror s).afterCorr P = toMirror (s.afterCorr P) := rfl

@[simp] theorem toAuth_afterCorr (s : GameState St Msg C) (P : Party) :
    (toAuth s).afterCorr P = toAuth (s.afterCorr P) := rfl

@[simp] theorem canon_toAuth (t : ℕ) (s : GameState St Msg C) :
    canon t (toAuth s) = canon t s := rfl

@[simp] theorem authOK_toAuth (Δ : ℕ) (tLStar : Option ℕ) (tStar : ℕ) (s : GameState St Msg C) :
    authLosingConditionsAvoided Δ tLStar tStar (toAuth s) = authLosingConditionsAvoided Δ tLStar tStar s := rfl

@[simp] theorem authOK_with_win (Δ : ℕ) (tLStar : Option ℕ) (tStar : ℕ)
    (s : GameState St Msg C) (w : Bool) :
    authLosingConditionsAvoided Δ tLStar tStar { s with win := w } = authLosingConditionsAvoided Δ tLStar tStar s := rfl

end CryptoGames.SM.Thm1L17

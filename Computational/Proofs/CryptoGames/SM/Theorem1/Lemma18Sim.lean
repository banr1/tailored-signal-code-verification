/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem1.Queries
import VCVio.CryptoFoundations.SecExp.Measure

/-!
# Simulation relation for Lemma 18

**Checked by Lean.** Defines the hybrid configuration `cfgHyb`, the state relation `SimRel`
between the SM game and `privRed`, and proves step-by-step and `simulateQ` equivalence.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.SM.Thm1.L18

variable {Key St Msg Coins C : Type}

section SimRel

variable (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)

def challMsgI (i : ℕ) (mbar : Msg) : ℕ → Option Msg :=
  fun t => if t < i then some mbar else none

def cfgHyb (i : ℕ) (mbar : Msg) (b_priv : Bool) : Config Msg :=
  if b_priv then Config.h3 i mbar else Config.h3 (i + 1) mbar

lemma cfgHyb_deliverWin (i : ℕ) (mbar : Msg) (b_priv : Bool) :
    (cfgHyb i mbar b_priv).deliverWin = false := by
  cases b_priv <;> rfl

lemma cfgHyb_injectFull (i : ℕ) (mbar : Msg) (b_priv : Bool) (t : ℕ) :
    (cfgHyb i mbar b_priv).injectFull t = false := by
  cases b_priv <;> rfl

lemma cfgHyb_challOK (i : ℕ) (mbar : Msg) (b_priv : Bool) (t : ℕ) :
    (cfgHyb i mbar b_priv).challAllowedIn t = true := by
  cases b_priv <;> rfl

lemma cfgHyb_challMsg_eq (i : ℕ) (mbar : Msg) (b_priv : Bool) {t : ℕ} (hm : t = i) (mb : Msg) :
    ((cfgHyb i mbar b_priv).challMsg t).getD mb = (if b_priv then mb else mbar) := by
  subst hm
  cases b_priv <;> simp [cfgHyb, Config.h3]

lemma cfgHyb_challMsg_ne (i : ℕ) (mbar : Msg) (b_priv : Bool) {t : ℕ} (hne : t ≠ i) (mb : Msg) :
    ((cfgHyb i mbar b_priv).challMsg t).getD mb = (challMsgI i mbar t).getD mb := by
  have hiff : (t ≤ i) ↔ (t < i) := by omega
  cases b_priv <;> simp [cfgHyb, Config.h3, challMsgI, hiff]

def posBound (h : GameState St Msg C) (pos : Pos) : Prop :=
  pos.epoch < h.epoch pos.sender ∨
    (pos.epoch = h.epoch pos.sender ∧ pos.idx ≤ h.idx pos.sender)

lemma posBound_mono {h h' : GameState St Msg C} {pos : Pos} (hp : posBound h pos)
    (he : h.epoch pos.sender < h'.epoch pos.sender ∨
      (h.epoch pos.sender = h'.epoch pos.sender ∧ h.idx pos.sender ≤ h'.idx pos.sender)) :
    posBound h' pos := by
  unfold posBound at hp ⊢
  omega

lemma not_posBound_next (h : GameState St Msg C) (P : Party) :
    ¬ posBound h ⟨P, h.epoch P, h.idx P + 1⟩ := by
  unfold posBound
  dsimp only
  omega

structure SimRel (i : ℕ) (b_priv : Bool)
    (s : GameState St Msg C) (m : Mirror Msg C) (h : GameState St Msg C) : Prop where
  win_s : s.win = false
  win_m : m.win = false
  win_h : h.win = false
  b_s : s.b = b_priv
  b_m : m.b = h.b
  st_eq : s.st = h.st
  ep_s : s.epoch = h.epoch
  ep_m : m.epoch = h.epoch
  idx_s : s.idx = h.idx
  idx_m : m.idx = h.idx
  tL_s : s.tL = h.tL
  tL_m : m.tL = h.tL
  trans_s : s.trans = h.trans
  trans_m : m.trans.map (fun r => (r.pos, r.ct)) = h.trans.map (fun r => (r.pos, r.ct))
  chall_m : m.chall = h.chall
  chall_sub : ∀ pos ∈ s.chall, pos ∈ h.chall
  chall_trans : ∀ pos ∈ h.chall, ∃ r ∈ h.trans, r.pos = pos ∧ pos ∉ h.comp
  comp_s : s.comp = h.comp
  comp_m : m.comp = h.comp
  maxAcc_s : s.maxAcc = h.maxAcc
  maxAcc_m : m.maxAcc = h.maxAcc
  leaks_s : s.leaks = h.leaks
  leaks_m : m.leaks = h.leaks
  corrs_s : s.corrs = h.corrs
  corrs_m : m.corrs = h.corrs
  bound_trans : ∀ r ∈ h.trans, posBound h r.pos
  bound_comp : ∀ pos ∈ h.comp, posBound h pos

lemma SimRel.init (i : ℕ) (k : Key) (b_priv b_sim : Bool) :
    SimRel i b_priv (initState sm k b_priv)
      ({ st := fun _ => (), b := b_sim } : Mirror Msg C)
      (initState sm k b_sim) where
  win_s := rfl
  win_m := rfl
  win_h := rfl
  b_s := rfl
  b_m := rfl
  st_eq := rfl
  ep_s := rfl
  ep_m := rfl
  idx_s := rfl
  idx_m := rfl
  tL_s := rfl
  tL_m := rfl
  trans_s := rfl
  trans_m := rfl
  chall_m := rfl
  chall_sub := by rintro _ ⟨⟩
  chall_trans := by rintro _ ⟨⟩
  comp_s := rfl
  comp_m := rfl
  maxAcc_s := rfl
  maxAcc_m := rfl
  leaks_s := rfl
  leaks_m := rfl
  corrs_s := rfl
  corrs_m := rfl
  bound_trans := by rintro _ ⟨⟩
  bound_comp := by rintro _ ⟨⟩

lemma SimRel.safeCh_s {i : ℕ} {b_priv : Bool} {s : GameState St Msg C} {m : Mirror Msg C}
    {h : GameState St Msg C} (hr : SimRel i b_priv s m h) (P : Party) :
    s.safeCh Δ P = h.safeCh Δ P := by
  simp [GameState.safeCh, hr.tL_s, hr.ep_s]

lemma SimRel.safeCh_m {i : ℕ} {b_priv : Bool} {s : GameState St Msg C} {m : Mirror Msg C}
    {h : GameState St Msg C} (hr : SimRel i b_priv s m h) (P : Party) :
    m.safeCh Δ P = h.safeCh Δ P := by
  simp [GameState.safeCh, hr.tL_m, hr.ep_m]

lemma SimRel.safeInj_s {i : ℕ} {b_priv : Bool} {s : GameState St Msg C} {m : Mirror Msg C}
    {h : GameState St Msg C} (hr : SimRel i b_priv s m h) :
    s.safeInj Δ = h.safeInj Δ := by
  simp [GameState.safeInj, hr.tL_s, hr.ep_s]

lemma SimRel.inTransit_s [DecidableEq C] {i : ℕ} {b_priv : Bool} {s : GameState St Msg C}
    {m : Mirror Msg C} {h : GameState St Msg C} (hr : SimRel i b_priv s m h) (Q : Party) (c : C) :
    s.inTransit Q c = h.inTransit Q c := by
  simp [GameState.inTransit, hr.trans_s]

lemma find_pos_of_map_eq [DecidableEq C] {l₁ l₂ : List (Record Msg C)}
    (hm : l₁.map (fun r => (r.pos, r.ct)) = l₂.map (fun r => (r.pos, r.ct)))
    (Q : Party) (c : C) :
    (l₁.find? (fun r => r.pos.sender == Q && decide (r.ct = c))).map Record.pos =
      (l₂.find? (fun r => r.pos.sender == Q && decide (r.ct = c))).map Record.pos := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons _ _ => cases hm
  | cons r₁ l₁ ih =>
    cases l₂ with
    | nil => cases hm
    | cons r₂ l₂ =>
      simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at hm
      rcases hm with ⟨⟨hpos, hct⟩, htl⟩
      simp only [List.find?_cons, hpos, hct]
      cases (r₂.pos.sender == Q && decide (r₂.ct = c))
      · exact ih htl
      · simp [hpos]

lemma SimRel.inTransit_m_pos [DecidableEq C] {i : ℕ} {b_priv : Bool} {s : GameState St Msg C}
    {m : Mirror Msg C} {h : GameState St Msg C} (hr : SimRel i b_priv s m h) (Q : Party) (c : C) :
    (m.inTransit Q c).map Record.pos = (h.inTransit Q c).map Record.pos :=
  find_pos_of_map_eq hr.trans_m Q c

lemma SimRel.trivial_s {i : ℕ} {b_priv : Bool} {s : GameState St Msg C} {m : Mirror Msg C}
    {h : GameState St Msg C} (hr : SimRel i b_priv s m h) (pos : Pos) :
    s.trivial Δ pos = h.trivial Δ pos := by
  simp [GameState.trivial, hr.comp_s, hr.trans_s, hr.tL_s]

lemma SimRel.canon_s {i : ℕ} {b_priv : Bool} {s : GameState St Msg C} {m : Mirror Msg C}
    {h : GameState St Msg C} (hr : SimRel i b_priv s m h) (tStar : ℕ) :
    canon tStar s = canon tStar h := by
  simp [canon, hr.leaks_s]

lemma SimRel.corrAllowed_s {i : ℕ} {b_priv : Bool} {s : GameState St Msg C} {m : Mirror Msg C}
    {h : GameState St Msg C} (hr : SimRel i b_priv s m h) (P : Party) :
    s.corrAllowed P = h.corrAllowed P := by
  unfold GameState.corrAllowed
  rw [hr.trans_s, hr.comp_s]
  cases htr : h.trans.any (fun r => r.pos.sender == P.other && !(h.comp.contains r.pos)) with
  | true => simp
  | false =>
    have hch_h : h.chall.any (fun pos => pos.sender == P.other) = false := by
      rw [List.any_eq_false]
      intro pos hpos hsend
      rcases hr.chall_trans pos hpos with ⟨r, hr_mem, hr_pos, hr_ncomp⟩
      have hnot := List.any_eq_false.mp htr r hr_mem
      simp [hr_pos, hsend, hr_ncomp] at hnot
    have hch_s : s.chall.any (fun pos => pos.sender == P.other) = false := by
      rw [List.any_eq_false] at hch_h ⊢
      intro pos hpos
      exact hch_h pos (hr.chall_sub pos hpos)
    rw [hch_s, hch_h]

lemma SimRel.epMgmt_none {i : ℕ} {b_priv : Bool} {s : GameState St Msg C} {m : Mirror Msg C}
    {h : GameState St Msg C} (hr : SimRel i b_priv s m h) (P : Party) (bad : Bool)
    (hnone : h.epMgmt Δ qep P bad = none) :
    s.epMgmt Δ qep P bad = none ∧ m.epMgmt Δ qep P bad = none := by
  unfold GameState.epMgmt GameState.safeCh at hnone ⊢
  rw [hr.ep_s, hr.ep_m, hr.tL_s, hr.tL_m]
  split_ifs at hnone ⊢ <;> trivial

lemma SimRel.epMgmt_some {i : ℕ} {b_priv : Bool} {s : GameState St Msg C} {m : Mirror Msg C}
    {h h₁ : GameState St Msg C} (hr : SimRel i b_priv s m h) (P : Party) (bad : Bool)
    (hsome : h.epMgmt Δ qep P bad = some h₁) :
    ∃ s₁ m₁, s.epMgmt Δ qep P bad = some s₁ ∧ m.epMgmt Δ qep P bad = some m₁ ∧
      SimRel i b_priv s₁ m₁ h₁ := by
  have hmono : ∀ Q, h.epoch Q < Function.update h.epoch P (h.epoch P + 1) Q ∨
      (h.epoch Q = Function.update h.epoch P (h.epoch P + 1) Q ∧
        h.idx Q ≤ Function.update h.idx P 0 Q) := by
    intro Q
    by_cases hQ : Q = P
    · subst hQ; left; simp
    · right; simp [hQ]
  unfold GameState.epMgmt GameState.safeCh at hsome ⊢
  rw [hr.ep_s, hr.ep_m, hr.tL_s, hr.tL_m]
  by_cases h1 : P.sendsIn (h.epoch P + 1) = true
  · by_cases h2 : qep < h.epoch P + 1
    · simp [h1, h2] at hsome
    · simp only [h1, h2, ↓reduceIte] at hsome ⊢
      cases hsome
      refine ⟨_, _, rfl, rfl, ?_⟩
      by_cases hbad : (bad && !healedBy h.tL Δ (h.epoch P)) = true
      · simp only [hbad, ↓reduceIte, GameState.leak]
        exact {
          win_s := hr.win_s, win_m := hr.win_m, win_h := hr.win_h
          b_s := hr.b_s, b_m := hr.b_m, st_eq := hr.st_eq
          ep_s := by rw [hr.ep_s], ep_m := by rw [hr.ep_m]
          idx_s := by rw [hr.idx_s], idx_m := by rw [hr.idx_m]
          tL_s := by simp [hr.tL_s], tL_m := by simp [hr.tL_m]
          trans_s := hr.trans_s, trans_m := hr.trans_m
          chall_m := hr.chall_m, chall_sub := hr.chall_sub, chall_trans := hr.chall_trans
          comp_s := hr.comp_s, comp_m := hr.comp_m
          maxAcc_s := hr.maxAcc_s, maxAcc_m := hr.maxAcc_m
          leaks_s := by simp [hr.leaks_s, hr.tL_s], leaks_m := by simp [hr.leaks_m, hr.tL_m]
          corrs_s := hr.corrs_s, corrs_m := hr.corrs_m
          bound_trans := fun r hr_mem => posBound_mono (hr.bound_trans r hr_mem) (hmono r.pos.sender)
          bound_comp := fun pos hp_mem => posBound_mono (hr.bound_comp pos hp_mem) (hmono pos.sender)
        }
      · simp only [hbad, Bool.false_eq_true, ↓reduceIte]
        exact {
          win_s := hr.win_s, win_m := hr.win_m, win_h := hr.win_h
          b_s := hr.b_s, b_m := hr.b_m, st_eq := hr.st_eq
          ep_s := by rw [hr.ep_s], ep_m := by rw [hr.ep_m]
          idx_s := by rw [hr.idx_s], idx_m := by rw [hr.idx_m]
          tL_s := hr.tL_s, tL_m := hr.tL_m
          trans_s := hr.trans_s, trans_m := hr.trans_m
          chall_m := hr.chall_m, chall_sub := hr.chall_sub, chall_trans := hr.chall_trans
          comp_s := hr.comp_s, comp_m := hr.comp_m
          maxAcc_s := hr.maxAcc_s, maxAcc_m := hr.maxAcc_m
          leaks_s := hr.leaks_s, leaks_m := hr.leaks_m
          corrs_s := hr.corrs_s, corrs_m := hr.corrs_m
          bound_trans := fun r hr_mem => posBound_mono (hr.bound_trans r hr_mem) (hmono r.pos.sender)
          bound_comp := fun pos hp_mem => posBound_mono (hr.bound_comp pos hp_mem) (hmono pos.sender)
        }
  · by_cases h2 : qep < h.epoch P
    · simp [h1, h2] at hsome
    · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hsome ⊢
      subst hsome
      exact ⟨s, m, rfl, rfl, hr⟩

lemma SimRel.record_transmit {i : ℕ} {b_priv : Bool} {s₁ : GameState St Msg C} {m₁ : Mirror Msg C}
    {h₁ : GameState St Msg C} (hr : SimRel i b_priv s₁ m₁ h₁) (P : Party) (st' : St)
    (msg : Msg) (ct : C) :
    let pos : Pos := ⟨P, h₁.epoch P, h₁.idx P + 1⟩
    SimRel i b_priv
      (s₁.record Δ P st' ⟨pos, msg, ct⟩ false)
      (m₁.record Δ P () ⟨pos, msg, ct⟩ false)
      (h₁.record Δ P st' ⟨pos, msg, ct⟩ false) := by
  intro pos
  have hsafe_s := hr.safeCh_s Δ P
  have hsafe_m := hr.safeCh_m Δ P
  have hmono : ∀ Q, h₁.epoch Q < h₁.epoch Q ∨
      (h₁.epoch Q = h₁.epoch Q ∧ h₁.idx Q ≤ Function.update h₁.idx P (h₁.idx P + 1) Q) := by
    intro Q
    right
    refine ⟨rfl, ?_⟩
    by_cases hQ : Q = P
    · subst hQ; simp
    · simp [hQ]
  have hpos_new : posBound (h₁.record Δ P st' ⟨pos, msg, ct⟩ false) pos := by
    right
    simp [pos, GameState.record]
  refine {
    win_s := hr.win_s, win_m := hr.win_m, win_h := hr.win_h
    b_s := hr.b_s, b_m := hr.b_m
    st_eq := by simp [GameState.record, hr.st_eq]
    ep_s := hr.ep_s, ep_m := hr.ep_m
    idx_s := by simp [GameState.record, hr.idx_s]
    idx_m := by simp [GameState.record, hr.idx_m]
    tL_s := hr.tL_s, tL_m := hr.tL_m
    trans_s := by simp [GameState.record, hr.trans_s]
    trans_m := by simp [GameState.record, hr.trans_m]
    chall_m := by simp [GameState.record, hr.chall_m]
    chall_sub := by simpa [GameState.record] using hr.chall_sub
    chall_trans := ?_
    comp_s := by simp [GameState.record, hr.comp_s, hsafe_s]
    comp_m := by simp [GameState.record, hr.comp_m, hsafe_m]
    maxAcc_s := hr.maxAcc_s, maxAcc_m := hr.maxAcc_m
    leaks_s := hr.leaks_s, leaks_m := hr.leaks_m
    corrs_s := hr.corrs_s, corrs_m := hr.corrs_m
    bound_trans := ?_
    bound_comp := ?_
  }
  · intro pos₀ hpos₀
    simp only [GameState.record, Bool.false_eq_true, ↓reduceIte] at hpos₀ ⊢
    rcases hr.chall_trans pos₀ hpos₀ with ⟨r, hr_mem, hr_pos, hr_ncomp⟩
    refine ⟨r, List.mem_cons_of_mem _ hr_mem, hr_pos, ?_⟩
    split_ifs
    · exact hr_ncomp
    · simp only [List.mem_cons, not_or]
      refine ⟨?_, hr_ncomp⟩
      intro heq
      have hb := hr.bound_trans r hr_mem
      rw [hr_pos, heq] at hb
      exact not_posBound_next h₁ P hb
  · intro r hr_mem
    simp only [GameState.record, List.mem_cons] at hr_mem
    rcases hr_mem with rfl | hr_old
    · exact hpos_new
    · exact posBound_mono (hr.bound_trans r hr_old) (hmono r.pos.sender)
  · intro pos₀ hpos₀
    simp only [GameState.record] at hpos₀
    split_ifs at hpos₀
    · exact posBound_mono (hr.bound_comp pos₀ hpos₀) (hmono pos₀.sender)
    · simp only [List.mem_cons] at hpos₀
      rcases hpos₀ with rfl | hpos_old
      · exact hpos_new
      · exact posBound_mono (hr.bound_comp pos₀ hpos_old) (hmono pos₀.sender)

lemma SimRel.record_chall {i : ℕ} {b_priv : Bool} {s₁ : GameState St Msg C} {m₁ : Mirror Msg C}
    {h₁ : GameState St Msg C} (hr : SimRel i b_priv s₁ m₁ h₁) (P : Party)
    (hsafe : h₁.safeCh Δ P = true) (st' : St) (msg_s msg_m : Msg) (ct : C) (isChall_s : Bool) :
    let pos : Pos := ⟨P, h₁.epoch P, h₁.idx P + 1⟩
    SimRel i b_priv
      (s₁.record Δ P st' ⟨pos, msg_s, ct⟩ isChall_s)
      (m₁.record Δ P () ⟨pos, msg_m, ct⟩ true)
      (h₁.record Δ P st' ⟨pos, msg_s, ct⟩ true) := by
  intro pos
  have hsafe_s : s₁.safeCh Δ P = true := (hr.safeCh_s Δ P).trans hsafe
  have hsafe_m : m₁.safeCh Δ P = true := (hr.safeCh_m Δ P).trans hsafe
  have hmono : ∀ Q, h₁.epoch Q < h₁.epoch Q ∨
      (h₁.epoch Q = h₁.epoch Q ∧ h₁.idx Q ≤ Function.update h₁.idx P (h₁.idx P + 1) Q) := by
    intro Q
    right
    refine ⟨rfl, ?_⟩
    by_cases hQ : Q = P
    · subst hQ; simp
    · simp [hQ]
  have hpos_new : posBound (h₁.record Δ P st' ⟨pos, msg_s, ct⟩ true) pos := by
    right
    simp [pos, GameState.record]
  have hpos_ncomp : pos ∉ h₁.comp := by
    intro hmem
    exact not_posBound_next h₁ P (hr.bound_comp pos hmem)
  refine {
    win_s := hr.win_s, win_m := hr.win_m, win_h := hr.win_h
    b_s := hr.b_s, b_m := hr.b_m
    st_eq := by simp [GameState.record, hr.st_eq]
    ep_s := hr.ep_s, ep_m := hr.ep_m
    idx_s := by simp [GameState.record, hr.idx_s]
    idx_m := by simp [GameState.record, hr.idx_m]
    tL_s := hr.tL_s, tL_m := hr.tL_m
    trans_s := by simp [GameState.record, hr.trans_s]
    trans_m := by simp [GameState.record, hr.trans_m]
    chall_m := by simp [GameState.record, hr.chall_m]
    chall_sub := ?_
    chall_trans := ?_
    comp_s := by simp [GameState.record, hr.comp_s, hsafe_s, hsafe]
    comp_m := by simp [GameState.record, hr.comp_m, hsafe_m, hsafe]
    maxAcc_s := hr.maxAcc_s, maxAcc_m := hr.maxAcc_m
    leaks_s := hr.leaks_s, leaks_m := hr.leaks_m
    corrs_s := hr.corrs_s, corrs_m := hr.corrs_m
    bound_trans := ?_
    bound_comp := ?_
  }
  · intro pos₀ hpos₀
    simp only [GameState.record, ↓reduceIte, List.mem_cons] at hpos₀ ⊢
    cases isChall_s
    · simp only [Bool.false_eq_true, ↓reduceIte] at hpos₀
      exact Or.inr (hr.chall_sub pos₀ hpos₀)
    · simp only [↓reduceIte, List.mem_cons] at hpos₀
      exact hpos₀.imp id (hr.chall_sub pos₀)
  · intro pos₀ hpos₀
    simp only [GameState.record, hsafe, ↓reduceIte, List.mem_cons] at hpos₀ ⊢
    rcases hpos₀ with rfl | hpos_old
    · exact ⟨⟨pos, msg_s, ct⟩, Or.inl rfl, rfl, hpos_ncomp⟩
    · rcases hr.chall_trans pos₀ hpos_old with ⟨r, hr_mem, hr_pos, hr_ncomp⟩
      exact ⟨r, Or.inr hr_mem, hr_pos, hr_ncomp⟩
  · intro r hr_mem
    simp only [GameState.record, List.mem_cons] at hr_mem
    rcases hr_mem with rfl | hr_old
    · exact hpos_new
    · exact posBound_mono (hr.bound_trans r hr_old) (hmono r.pos.sender)
  · intro pos₀ hpos₀
    simp only [GameState.record, hsafe, ↓reduceIte] at hpos₀
    exact posBound_mono (hr.bound_comp pos₀ hpos₀) (hmono pos₀.sender)

lemma filter_map_pos_ct_eq {l₁ l₂ : List (Record Msg C)}
    (hm : l₁.map (fun r => (r.pos, r.ct)) = l₂.map (fun r => (r.pos, r.ct))) (pos : Pos) :
    (l₁.filter (fun r => r.pos != pos)).map (fun r => (r.pos, r.ct)) =
      (l₂.filter (fun r => r.pos != pos)).map (fun r => (r.pos, r.ct)) := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons _ _ => cases hm
  | cons r₁ l₁ ih =>
    cases l₂ with
    | nil => cases hm
    | cons r₂ l₂ =>
      simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at hm
      rcases hm with ⟨⟨hpos, hct⟩, htl⟩
      simp only [List.filter_cons, hpos]
      split_ifs
      · simp [hpos, hct, ih htl]
      · exact ih htl

lemma SimRel.accept {i : ℕ} {b_priv : Bool} {s : GameState St Msg C} {m : Mirror Msg C}
    {h : GameState St Msg C} (hr : SimRel i b_priv s m h) (P : Party) (st' : St) (pos : Pos) :
    SimRel i b_priv (s.accept P st' pos) (m.accept P () pos) (h.accept P st' pos) := by
  have hmono : ∀ Q, h.epoch Q < (h.accept P st' pos).epoch Q ∨
      (h.epoch Q = (h.accept P st' pos).epoch Q ∧ h.idx Q ≤ (h.accept P st' pos).idx Q) := by
    intro Q
    simp only [GameState.accept, GameState.delete]
    by_cases hQ : Q = P
    · subst hQ
      simp only [Function.update_self]
      omega
    · right
      simp [hQ]
  refine {
    win_s := hr.win_s, win_m := hr.win_m, win_h := hr.win_h
    b_s := hr.b_s, b_m := hr.b_m
    st_eq := by simp [GameState.accept, GameState.delete, hr.st_eq]
    ep_s := by simp [GameState.accept, GameState.delete, hr.ep_s]
    ep_m := by simp [GameState.accept, GameState.delete, hr.ep_m]
    idx_s := by simp [GameState.accept, GameState.delete, hr.idx_s]
    idx_m := by simp [GameState.accept, GameState.delete, hr.idx_m]
    tL_s := hr.tL_s, tL_m := hr.tL_m
    trans_s := by simp [GameState.accept, GameState.delete, hr.trans_s]
    trans_m := filter_map_pos_ct_eq hr.trans_m pos
    chall_m := by simp [GameState.accept, GameState.delete, hr.chall_m]
    chall_sub := by
      intro pos₀ hpos₀
      simp only [GameState.accept, GameState.delete, List.mem_filter] at hpos₀ ⊢
      exact ⟨hr.chall_sub pos₀ hpos₀.1, hpos₀.2⟩
    chall_trans := by
      intro pos₀ hpos₀
      simp only [GameState.accept, GameState.delete, List.mem_filter] at hpos₀ ⊢
      rcases hr.chall_trans pos₀ hpos₀.1 with ⟨r, hr_mem, hr_pos, hr_ncomp⟩
      refine ⟨r, ⟨hr_mem, ?_⟩, hr_pos, ?_⟩
      · simpa [hr_pos] using hpos₀.2
      · intro hmem
        exact hr_ncomp hmem.1
    comp_s := by simp [GameState.accept, GameState.delete, hr.comp_s]
    comp_m := by simp [GameState.accept, GameState.delete, hr.comp_m]
    maxAcc_s := by
      ext Q t
      simp [GameState.accept, GameState.delete, hr.maxAcc_s]
    maxAcc_m := by
      ext Q t
      simp [GameState.accept, GameState.delete, hr.maxAcc_m]
    leaks_s := hr.leaks_s, leaks_m := hr.leaks_m
    corrs_s := hr.corrs_s, corrs_m := hr.corrs_m
    bound_trans := by
      intro r hr_mem
      simp only [GameState.accept, GameState.delete, List.mem_filter] at hr_mem
      exact posBound_mono (hr.bound_trans r hr_mem.1) (hmono r.pos.sender)
    bound_comp := by
      intro pos₀ hpos₀
      simp only [GameState.accept, GameState.delete, List.mem_filter] at hpos₀
      exact posBound_mono (hr.bound_comp pos₀ hpos₀.1) (hmono pos₀.sender)
  }

lemma filter_sender_map_pos_eq {l₁ : List (Record Msg C)} {l₂ : List (Record Msg C)}
    (hm : l₁.map (fun r => (r.pos, r.ct)) = l₂.map (fun r => (r.pos, r.ct))) (Q : Party) :
    (l₁.filter (fun r => r.pos.sender == Q)).map (fun r => r.pos) =
      (l₂.filter (fun r => r.pos.sender == Q)).map (fun r => r.pos) := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons _ _ => cases hm
  | cons r₁ l₁ ih =>
    cases l₂ with
    | nil => cases hm
    | cons r₂ l₂ =>
      simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at hm
      rcases hm with ⟨⟨hpos, _⟩, htl⟩
      simp only [List.filter_cons, hpos]
      split_ifs
      · simp [hpos, ih htl]
      · exact ih htl

lemma SimRel.afterCorr {i : ℕ} {b_priv : Bool} {s : GameState St Msg C} {m : Mirror Msg C}
    {h : GameState St Msg C} (hr : SimRel i b_priv s m h) (P : Party)
    (hcorr : h.corrAllowed P = true) :
    SimRel i b_priv (s.afterCorr P) (m.afterCorr P) (h.afterCorr P) := by
  have hno_chall : ∀ pos ∈ h.chall, (pos.sender == P.other) = false := by
    unfold GameState.corrAllowed at hcorr
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false] at hcorr
    intro pos hpos
    exact Bool.eq_false_iff.mpr (hcorr.1 pos hpos)
  refine {
    win_s := hr.win_s, win_m := hr.win_m, win_h := hr.win_h
    b_s := hr.b_s, b_m := hr.b_m
    st_eq := hr.st_eq
    ep_s := hr.ep_s, ep_m := hr.ep_m
    idx_s := hr.idx_s, idx_m := hr.idx_m
    tL_s := by simp [GameState.afterCorr, GameState.leak, hr.ep_s, hr.tL_s]
    tL_m := by simp [GameState.afterCorr, GameState.leak, hr.ep_m, hr.tL_m]
    trans_s := hr.trans_s, trans_m := hr.trans_m
    chall_m := hr.chall_m, chall_sub := hr.chall_sub
    chall_trans := by
      intro pos₀ hpos₀
      simp only [GameState.afterCorr, GameState.leak] at hpos₀ ⊢
      rcases hr.chall_trans pos₀ hpos₀ with ⟨r, hr_mem, hr_pos, hr_ncomp⟩
      refine ⟨r, hr_mem, hr_pos, ?_⟩
      simp only [List.mem_append, List.mem_map, List.mem_filter, not_or]
      refine ⟨?_, hr_ncomp⟩
      rintro ⟨r', ⟨_, hsend⟩, hr'_pos⟩
      rw [hr'_pos, hno_chall pos₀ hpos₀] at hsend
      cases hsend
    comp_s := by simp [GameState.afterCorr, GameState.leak, hr.trans_s, hr.comp_s]
    comp_m := by
      simp only [GameState.afterCorr, GameState.leak, hr.comp_m]
      rw [filter_sender_map_pos_eq hr.trans_m P.other]
    maxAcc_s := hr.maxAcc_s, maxAcc_m := hr.maxAcc_m
    leaks_s := by simp [GameState.afterCorr, GameState.leak, hr.leaks_s, hr.ep_s, hr.tL_s]
    leaks_m := by simp [GameState.afterCorr, GameState.leak, hr.leaks_m, hr.ep_m, hr.tL_m]
    corrs_s := by simp [GameState.afterCorr, GameState.leak, hr.corrs_s, hr.ep_s]
    corrs_m := by simp [GameState.afterCorr, GameState.leak, hr.corrs_m, hr.ep_m]
    bound_trans := hr.bound_trans
    bound_comp := by
      intro pos₀ hpos₀
      simp only [GameState.afterCorr, GameState.leak, List.mem_append, List.mem_map,
        List.mem_filter] at hpos₀
      rcases hpos₀ with ⟨r, ⟨hr_mem, _⟩, rfl⟩ | hpos_old
      · exact hr.bound_trans r hr_mem
      · exact hr.bound_comp pos₀ hpos_old
  }

/-! ### Relational equivalence for `privRed` -/

lemma samIfNec_bind [SampleableType Coins] (r : Option Coins) {α : Type}
    (f : Coins × Bool → ProbComp α) :
    ((samIfNec r : ProbComp (Coins × Bool)) >>= f) =
      ((samIfNec r : ProbComp (Coins × Bool)) >>= fun cb => f (cb.1, r.isSome)) := by
  cases r <;> simp [samIfNec]

lemma evalDist_samIfNec_const [SampleableType Coins] (r : Option Coins) {α : Type}
    [MeasurableSpace α] (mx : ProbComp α) :
    𝒟[(samIfNec r : ProbComp (Coins × Bool)) >>= fun _ => mx] = 𝒟[mx] := by
  cases r <;> simp [samIfNec]

lemma deliver_msg_eq {i : ℕ} {b_priv : Bool} {s : GameState St Msg C} {m : Mirror Msg C}
    {h : GameState St Msg C} (hr : SimRel i b_priv s m h) (pos : Pos) (m' : Msg) :
    (if m.chall.contains pos then none else if s.chall.contains pos then none else some m') =
      (if h.chall.contains pos then none else some m') := by
  rw [hr.chall_m]
  simp only [List.contains_iff_mem]
  by_cases hh : pos ∈ h.chall
  · simp [hh]
  · have hs : pos ∉ s.chall := fun hs_mem => hh (hr.chall_sub pos hs_mem)
    simp [hh, hs]

lemma monadLift_self {m : Type → Type} {α : Type} (x : m α) :
    (monadLift x : m α) = x := rfl

variable [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]

lemma simStep_privRed (i : ℕ) (mbar : Msg) (b_priv : Bool)
    (t : (unifSpec + spec St Msg Coins C).Domain)
    (s : GameState St Msg C) (m : Mirror Msg C) (h : GameState St Msg C)
    (hr : SimRel i b_priv s m h)
    (k₁ : (unifSpec + spec St Msg Coins C).Range t → Mirror Msg C → GameState St Msg C → ProbComp Bool)
    (k₂ : (unifSpec + spec St Msg Coins C).Range t → GameState St Msg C → ProbComp Bool)
    (hk : ∀ u s' m' h', SimRel i b_priv s' m' h' → 𝒟[k₁ u m' s'] = 𝒟[k₂ u h']) :
    𝒟[((simulateQ (runImpl sm Δ qep (Config.priv i))
        ((simImpl (St := St) (Coins := Coins) Δ qep (challMsgI i mbar) (some (i, mbar)) t).run m)).run s) >>=
        fun p => k₁ p.1.1 p.1.2 p.2] =
      𝒟[((runImpl sm Δ qep (cfgHyb i mbar b_priv) t).run h) >>= fun p => k₂ p.1 p.2] := by
  rcases t with n | ((((⟨P, msg, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
  ·
    change 𝒟[((simulateQ (runImpl sm Δ qep (Config.priv i))
        ((simCoins (St := St) (Msg := Msg) (Coins := Coins) (C := C) n).run m)).run s) >>= _] =
      𝒟[((StateT.lift (query (spec := unifSpec) n) : StateT _ ProbComp _).run h) >>= _]
    unfold simCoins
    simp only [stateT_lift_run, query_eq_liftM, simulateQ_bind, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, id_map, simulateQ_pure, StateT.run_bind,
      StateT.run_pure, pure_bind, bind_assoc]
    change 𝒟[((StateT.lift (query (spec := unifSpec) n) : StateT _ ProbComp _).run s) >>= _] = _
    simp only [stateT_lift_run, bind_assoc, pure_bind]
    exact evalDist_bind_congr _ _ _ fun u => hk u s m h hr
  ·
    change 𝒟[((simulateQ (runImpl sm Δ qep (Config.priv i))
        ((simTransmit (St := St) Δ qep (P, msg, r)).run m)).run s) >>= _] =
      𝒟[((transmitImpl sm Δ qep (P, msg, r)).run h) >>= _]
    unfold simTransmit transmitQuery
    simp only [StateT.run_bind, StateT.run_get, pure_bind, stateT_lift_run, bind_assoc,
      query_eq_liftM, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map]
    change 𝒟[((transmitImpl sm Δ qep (P, msg, r)).run s) >>=
      fun p => ((simulateQ (runImpl sm Δ qep (Config.priv i)) _).run p.2) >>= _] = _
    unfold transmitImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hr.win_s, hr.win_h,
      Bool.false_eq_true, ↓reduceIte, StateT.run_monadLift, monadLift_self, bind_assoc]
    conv_lhs => rw [samIfNec_bind r]
    conv_rhs => rw [samIfNec_bind r]
    dsimp only
    refine evalDist_bind_congr _ _ _ fun cb => ?_
    cases hep_h : h.epMgmt Δ qep P r.isSome with
    | none =>
      rcases hr.epMgmt_none Δ qep P r.isSome hep_h with ⟨hep_s, hep_m⟩
      rw [hep_s, hep_m]
      simp only [StateT.run_pure, simulateQ_pure, pure_bind]
      exact hk none s m h hr
    | some h₁ =>
      rcases hr.epMgmt_some Δ qep P r.isSome hep_h with ⟨s₁, m_ep, hep_s, hep_m, hr₁⟩
      rw [hep_s, hep_m]
      simp only [hr₁.st_eq, hr₁.ep_s, hr₁.idx_s, hr₁.ep_m, hr₁.idx_m,
        StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure, pure_bind]
      exact hk _ _ _ _ (hr₁.record_transmit Δ P _ msg _)
  ·
    change 𝒟[((simulateQ (runImpl sm Δ qep (Config.priv i))
        ((simChall (St := St) Δ qep (challMsgI i mbar) (some (i, mbar)) (P, m₀, m₁, r)).run m)).run s) >>= _] =
      𝒟[((challImpl sm Δ qep (cfgHyb i mbar b_priv) (P, m₀, m₁, r)).run h) >>= _]
    unfold simChall challImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hr.win_h, Bool.false_eq_true,
      ↓reduceIte, StateT.run_monadLift, monadLift_self, bind_assoc]
    rw [samIfNec_bind r]
    dsimp only
    cases hep_h : h.epMgmt Δ qep P r.isSome with
    | none =>
      rcases hr.epMgmt_none Δ qep P r.isSome hep_h with ⟨_, hep_m⟩
      simp only [hep_m, StateT.run_pure, simulateQ_pure, pure_bind]
      rw [evalDist_samIfNec_const]
      exact hk none s m h hr
    | some h₁ =>
      rcases hr.epMgmt_some Δ qep P r.isSome hep_h with ⟨s₁, m_ep, hep_s, hep_m, hr₁⟩
      simp only [hep_m, hr₁.safeCh_m, cfgHyb_challOK, Bool.not_true, Bool.or_false]
      cases hsafe : h₁.safeCh Δ P with
      | false =>
        simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, simulateQ_pure, pure_bind]
        rw [evalDist_samIfNec_const]
        exact hk none s m h hr
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
          stateT_lift_run, bind_assoc, pure_bind, hr.b_m, hr₁.ep_m, StateT.run_set,
          StateT.run_pure]
        unfold simSend
        dsimp only
        by_cases hti : h₁.epoch P = i
        ·
          have hchallOK_priv : (Config.priv i : Config Msg).challAllowedIn i = true := by
            simp [Config.priv]
          have hchallMsg_priv : (Config.priv i : Config Msg).challMsg i = none := rfl
          have hsafe_s : s₁.safeCh Δ P = true := (hr₁.safeCh_s Δ P).trans hsafe
          simp only [hti, ↓reduceIte, challQuery, query_eq_liftM, simulateQ_bind, simulateQ_query,
            OracleQuery.input_query, OracleQuery.cont_query, id_map, StateT.run_bind, bind_assoc]
          change 𝒟[((challImpl sm Δ qep (Config.priv i)
              (P, mbar, if h.b then m₁ else m₀, r)).run s) >>= _] = _
          unfold challImpl
          simp only [StateT.run_bind, StateT.run_get, pure_bind, hr.win_s, Bool.false_eq_true,
            ↓reduceIte, StateT.run_monadLift, monadLift_self, bind_assoc]
          rw [samIfNec_bind r]
          dsimp only
          simp only [hep_s, hsafe_s, hr₁.ep_s, hti, hchallOK_priv, Bool.not_true, Bool.or_self,
            Bool.false_eq_true, ↓reduceIte, hchallMsg_priv, Option.getD_none,
            hr.b_s, hr₁.st_eq, hr₁.idx_s, StateT.run_bind, StateT.run_set,
            StateT.run_pure, simulateQ_pure, pure_bind]
          refine evalDist_bind_congr _ _ _ fun cb => ?_
          rw [cfgHyb_challMsg_eq i mbar b_priv rfl (if h.b then m₁ else m₀)]
          have hr' := hr₁.record_chall Δ P hsafe
            (sm.send (h₁.st P) (if b_priv then if h.b then m₁ else m₀ else mbar) cb.1).1
            (if b_priv then if h.b then m₁ else m₀ else mbar)
            (if h.b then m₁ else m₀)
            (sm.send (h₁.st P) (if b_priv then if h.b then m₁ else m₀ else mbar) cb.1).2
            true
          rw [hti] at hr'
          rw [hr₁.idx_m]
          exact hk _ _ _ _ hr'
        ·
          simp only [hti, ↓reduceIte, transmitQuery, query_eq_liftM, simulateQ_bind,
            simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
            StateT.run_bind, bind_assoc]
          change 𝒟[((transmitImpl sm Δ qep
              (P, (challMsgI i mbar (h₁.epoch P)).getD (if h.b then m₁ else m₀), r)).run s) >>= _] = _
          unfold transmitImpl
          simp only [StateT.run_bind, StateT.run_get, pure_bind, hr.win_s, Bool.false_eq_true,
            ↓reduceIte, StateT.run_monadLift, monadLift_self, bind_assoc]
          rw [samIfNec_bind r]
          dsimp only
          simp only [hep_s, hr₁.st_eq, hr₁.ep_s, hr₁.idx_s, StateT.run_bind, StateT.run_set,
            StateT.run_pure, simulateQ_pure, pure_bind]
          refine evalDist_bind_congr _ _ _ fun cb => ?_
          rw [cfgHyb_challMsg_ne i mbar b_priv hti (if h.b then m₁ else m₀), hr₁.idx_m]
          exact hk _ _ _ _ (hr₁.record_chall Δ P hsafe _ _ _ _ false)
  ·
    change 𝒟[((simulateQ (runImpl sm Δ qep (Config.priv i))
        ((simDeliver (St := St) (Coins := Coins) (P, c)).run m)).run s) >>= _] =
      𝒟[((deliverImpl sm (cfgHyb i mbar b_priv) (P, c)).run h) >>= _]
    unfold simDeliver deliverQuery
    simp only [StateT.run_bind, StateT.run_get, pure_bind, stateT_lift_run, bind_assoc,
      query_eq_liftM, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map]
    change 𝒟[((deliverImpl sm (Config.priv i) (P, c)).run s) >>= _] = _
    unfold deliverImpl
    have hdw_priv : (Config.priv i : Config Msg).deliverWin = false := rfl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hr.win_s, hr.win_h,
      Bool.false_eq_true, ↓reduceIte, hr.inTransit_s, hdw_priv, cfgHyb_deliverWin, Bool.false_and]
    cases htr_h : h.inTransit P.other c with
    | none =>
      simp only [StateT.run_pure, simulateQ_pure, pure_bind]
      exact hk none s m h hr
    | some r =>
      have htr_m : ∃ rm, m.inTransit P.other c = some rm ∧ rm.pos = r.pos := by
        have hpos := hr.inTransit_m_pos P.other c
        rw [htr_h] at hpos
        cases hm_tr : m.inTransit P.other c with
        | none => simp [hm_tr] at hpos
        | some rm =>
          simp only [hm_tr, Option.map_some, Option.some.injEq] at hpos
          exact ⟨rm, rfl, hpos⟩
      rcases htr_m with ⟨rm, htr_m, hrm_pos⟩
      simp only [hr.st_eq]
      cases sm.receive (h.st P) c with
      | none =>
        simp only [StateT.run_pure, simulateQ_pure, pure_bind]
        exact hk (some .rejected) s m h hr
      | some res =>
        rcases res with ⟨st', t', i', m'⟩
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, htr_m, hrm_pos,
          simulateQ_pure, deliver_msg_eq hr r.pos m']
        exact hk _ _ _ _ (hr.accept P st' r.pos)
  ·
    change 𝒟[((simulateQ (runImpl sm Δ qep (Config.priv i))
        ((simInject (St := St) (Coins := Coins) (P, c)).run m)).run s) >>= _] =
      𝒟[((injectImpl sm Δ qep (cfgHyb i mbar b_priv) (P, c)).run h) >>= _]
    unfold simInject injectQuery
    simp only [StateT.run_bind, StateT.run_get, pure_bind, stateT_lift_run, bind_assoc,
      query_eq_liftM, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map]
    change 𝒟[((injectImpl sm Δ qep (Config.priv i) (P, c)).run s) >>= _] = _
    unfold injectImpl
    have hij_priv : ∀ t', (Config.priv i : Config Msg).injectFull t' = false := fun _ => rfl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hr.win_s, hr.win_h, Bool.false_or,
      hr.inTransit_s, hr.safeInj_s, hr.st_eq]
    by_cases hreq : ((h.inTransit P.other c).isSome || !h.safeInj Δ) = true
    · simp only [hreq, ↓reduceIte, StateT.run_pure, simulateQ_pure, pure_bind]
      exact hk none s m h hr
    · simp only [hreq, Bool.false_eq_true, ↓reduceIte]
      cases sm.receive (h.st P) c with
      | none =>
        simp only [StateT.run_pure, simulateQ_pure, pure_bind]
        exact hk (some .rejected) s m h hr
      | some res =>
        rcases res with ⟨st', t', i', m'⟩
        dsimp only
        by_cases hqep : qep + 1 < t'
        · simp only [hqep, ↓reduceIte, StateT.run_pure, simulateQ_pure, pure_bind]
          exact hk (some .rejected) s m h hr
        · simp only [hqep, ↓reduceIte, hr.trivial_s, hij_priv, cfgHyb_injectFull,
            Bool.false_eq_true]
          by_cases htriv : h.trivial Δ ⟨P.other, t', i'⟩ = true
          · simp only [htriv, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
              simulateQ_pure, pure_bind]
            exact hk _ _ _ _ (hr.accept P st' ⟨P.other, t', i'⟩)
          · simp only [htriv, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure,
              pure_bind]
            exact hk (some .rejected) s m h hr
  ·
    change 𝒟[((simulateQ (runImpl sm Δ qep (Config.priv i))
        ((simCorr (St := St) (Msg := Msg) (Coins := Coins) (C := C) P).run m)).run s) >>= _] =
      𝒟[((corrImpl (St := St) (Msg := Msg) (C := C) P).run h) >>= _]
    unfold simCorr corrQuery
    simp only [StateT.run_bind, StateT.run_get, pure_bind, stateT_lift_run, bind_assoc,
      query_eq_liftM, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map]
    change 𝒟[((corrImpl (St := St) (Msg := Msg) (C := C) P).run s) >>= _] = _
    unfold corrImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hr.win_s, hr.win_h, Bool.false_or,
      hr.corrAllowed_s]
    cases hcorr : h.corrAllowed P with
    | false =>
      simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, Option.isSome_none,
        Bool.false_eq_true, simulateQ_pure, pure_bind]
      exact hk none s m h hr
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
        StateT.run_pure, Option.isSome_some, simulateQ_pure, pure_bind, hr.st_eq]
      exact hk _ _ _ _ (hr.afterCorr P hcorr)

lemma simulateQ_privRed (i : ℕ) (mbar : Msg) (b_priv : Bool)
    {α : Type} (oa : AdversaryComp St Msg Coins C α)
    (s : GameState St Msg C) (m : Mirror Msg C) (h : GameState St Msg C)
    (hr : SimRel i b_priv s m h)
    (k₁ : α → Mirror Msg C → GameState St Msg C → ProbComp Bool)
    (k₂ : α → GameState St Msg C → ProbComp Bool)
    (hk : ∀ a s' m' h', SimRel i b_priv s' m' h' → 𝒟[k₁ a m' s'] = 𝒟[k₂ a h']) :
    𝒟[((simulateQ (runImpl sm Δ qep (Config.priv i))
        ((simulateQ (simImpl (St := St) (Coins := Coins) Δ qep (challMsgI i mbar) (some (i, mbar))) oa).run m)).run s) >>=
        fun p => k₁ p.1.1 p.1.2 p.2] =
      𝒟[((simulateQ (runImpl sm Δ qep (cfgHyb i mbar b_priv)) oa).run h) >>=
        fun p => k₂ p.1 p.2] := by
  induction oa using OracleComp.inductionOn generalizing s m h with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact hk a s m h hr
  | query_bind t mx ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, bind_assoc]
    exact simStep_privRed sm Δ qep i mbar b_priv t s m h hr
      (fun u m' s' =>
        ((simulateQ (runImpl sm Δ qep (Config.priv i))
          ((simulateQ (simImpl Δ qep (challMsgI i mbar) (some (i, mbar))) (mx u)).run m')).run s') >>=
          fun p => k₁ p.1.1 p.1.2 p.2)
      (fun u h' =>
        ((simulateQ (runImpl sm Δ qep (cfgHyb i mbar b_priv)) (mx u)).run h') >>=
          fun p => k₂ p.1 p.2)
      (fun u s' m' h' hr' => ih u s' m' h' hr')

lemma simulateQ_liftM_unif (cfg : Config Msg) {α : Type} (mx : ProbComp α)
    (s : GameState St Msg C) :
    (simulateQ (runImpl sm Δ qep cfg) (liftM mx : Comp St Msg Coins C α)).run s =
      (mx >>= fun a => pure (a, s)) := by
  change (simulateQ (runImpl sm Δ qep cfg) (liftComp mx (unifSpec + spec St Msg Coins C))).run s = _
  induction mx using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t mx ih =>
    simp only [liftComp_bind, liftComp_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query, simulateQ_bind, StateT.run_bind, bind_assoc]
    change (StateT.lift (query (spec := unifSpec) t) : StateT _ ProbComp _).run s >>= _ = _
    simp only [stateT_lift_run, bind_assoc, pure_bind]
    exact bind_congr fun u => ih u

variable [SampleableType Key]

/-- Hybrid branch computation returning `b == b' || h.win` when `canon i h == tL` is admissible,
and a uniform coin otherwise. -/
def hybBranch (tL : Option ℕ) (i : ℕ) (cfg : Config Msg) (A : Adversary St Msg Coins C) :
    ProbComp Bool := do
  let b ← $ᵗ Bool
  let (b', h) ← run sm Δ qep cfg b A
  if lastLeakGuessAdmissible Δ tL i && canon i h == tL then return (b == b' || h.win)
  else $ᵗ Bool

lemma evalDist_privRed_run (tL : Option ℕ) (i : ℕ) (mbar : Msg) (b_priv : Bool)
    (A : Adversary St Msg Coins C) :
    𝒟[do
        let (out, s) ← run sm Δ qep (Config.priv i) b_priv (privRed Δ qep i mbar A)
        if lastLeakGuessAdmissible Δ tL i && canon i s == tL then return (b_priv == out)
        else $ᵗ Bool] =
      𝒟[do
        let z ← hybBranch sm Δ qep tL i (cfgHyb i mbar b_priv) A
        return (b_priv == z)] := by
  unfold hybBranch run privRed simRun
  simp only [StateT.run'_eq, map_eq_bind_pure_comp, Function.comp_def, simulateQ_bind,
    simulateQ_pure, StateT.run_bind, StateT.run_pure, pure_bind, bind_assoc,
    simulateQ_liftM_unif]
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ Key : ProbComp Key) ($ᵗ Bool : ProbComp Bool)]
  refine evalDist_bind_congr ($ᵗ Bool : ProbComp Bool) _ _ fun b_sim => ?_
  refine evalDist_bind_congr ($ᵗ Key : ProbComp Key) _ _ fun k => ?_
  refine simulateQ_privRed sm Δ qep i mbar b_priv A
    (initState sm k b_priv)
    ({ st := fun _ => (), b := b_sim } : Mirror Msg C)
    (initState sm k b_sim)
    (SimRel.init sm i k b_priv b_sim)
    (fun b' _ s' =>
      if (lastLeakGuessAdmissible Δ tL i && canon i s' == tL) = true then pure (b_priv == (b_sim == b'))
      else $ᵗ Bool)
    (fun b' h' =>
      (if (lastLeakGuessAdmissible Δ tL i && canon i h' == tL) = true then pure (b_sim == b' || h'.win)
       else $ᵗ Bool) >>= fun z => pure (b_priv == z))
    (fun b' s' m' h' hr' => ?_)
  rw [hr'.canon_s i, hr'.win_h, Bool.or_false]
  by_cases hcond : (lastLeakGuessAdmissible Δ tL i && canon i h' == tL) = true
  · simp [hcond]
  · simp only [hcond, Bool.false_eq_true, ↓reduceIte]
    cases b_priv
    · simpa using (ProbComp.evalDist_bind_not_uniformBool (pure : Bool → ProbComp Bool)).symm
    · simp

theorem privAdvantage_privRed_eq (tL : Option ℕ) (i : ℕ) (mbar : Msg)
    (A : Adversary St Msg Coins C) :
    privAdvantage sm Δ qep tL i (privRed Δ qep i mbar A) =
      𝒟[hybBranch sm Δ qep tL i (Config.h3 i mbar) A].boolDist
        𝒟[hybBranch sm Δ qep tL i (Config.h3 (i + 1) mbar) A] := by
  rw [← evalDist_boolBias_bind_uniformBool
    (hybBranch sm Δ qep tL i (Config.h3 i mbar) A)
    (hybBranch sm Δ qep tL i (Config.h3 (i + 1) mbar) A)]
  unfold privAdvantage privGame
  congr 1
  refine evalDist_bind_congr ($ᵗ Bool) _ _ fun b_priv => ?_
  rw [evalDist_privRed_run sm Δ qep tL i mbar b_priv A]
  cases b_priv <;> rfl

end SimRel

end CryptoGames.SM.Thm1.L18

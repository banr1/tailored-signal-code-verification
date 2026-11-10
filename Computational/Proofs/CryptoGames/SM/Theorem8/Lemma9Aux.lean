/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Reductions
import VCVio.OracleComp.EvalDist.Measure

/-!
# Auxiliary invariants and lemmas for Lemma 9

**Checked by Lean.**

Defines the doomed-run predicate `DoomedAuth` and the synchronization invariant `Sync9` between the
real authenticity game, the `redCKA` engine state, and the CKA game state.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.SM.Construction.AuthL9

theorem evalDist_true_eq_zero_of_support {α : Type} (x : ProbComp α) (f : α → Bool)
    (h : ∀ a ∈ support x, f a = false) :
    𝒟[x >>= fun a => pure (f a)] {true} = 0 := by
  have heq : 𝒟[x >>= fun a => pure (f a)] = 𝒟[(pure false : ProbComp Bool)] := by
    rw [evalDist_bind_congr_of_support x _ (fun _ => pure false)]
    · exact OracleComp.evalDist_bind_const x (pure false)
    · intro a ha
      rw [h a ha]
  rw [heq]
  simp

theorem evalDist_bind_eq_pure_false {α : Type} (x : ProbComp α) (f : α → ProbComp Bool)
    (h : ∀ a ∈ support x, 𝒟[f a] = 𝒟[(pure false : ProbComp Bool)]) :
    𝒟[x >>= f] = 𝒟[(pure false : ProbComp Bool)] := by
  rw [evalDist_bind_congr_of_support x f (fun _ => pure false) h]
  exact OracleComp.evalDist_bind_const x (pure false)

/-! ## Doomed authenticity states -/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section Doomed

variable {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]

def Doomed1 (tL : Option ℕ) (tStar : ℕ) (s : GameState St Msg C) : Prop :=
  s.leaks.any (fun l => ltOpt tL l && decide (l < tStar)) = true

def Doomed2 (tStar : ℕ) (s : GameState St Msg C) : Prop :=
  s.win = false ∧ (∃ m, s.tL = some m ∧ tStar ≤ m) ∧
    ∀ r ∈ s.trans, r.pos.epoch = tStar → r.pos ∈ s.comp

def Doomed3 (tL : Option ℕ) (tStar : ℕ) (s : GameState St Msg C) : Prop :=
  s.corrs.any (fun pe => pe.1 == Party.receiverOf tStar && ltOpt tL pe.2) = true

def Doomed4 (tL : Option ℕ) (s : GameState St Msg C) : Prop :=
  ∃ l, tL = some l ∧ l ∉ s.leaks ∧
    l ≤ min (s.epoch .A) (s.epoch .B) ∧ l < max (s.epoch .A) (s.epoch .B)

/-- States in `Config.auth tStar` from which the authenticity winning condition can never hold. -/
def DoomedAuth (tL : Option ℕ) (tStar : ℕ) (s : GameState St Msg C) : Prop :=
  Doomed1 tL tStar s ∨ Doomed2 tStar s ∨ Doomed3 tL tStar s ∨ Doomed4 tL s

theorem list_max?_mem {l : List ℕ} : ∀ {m : ℕ}, l.max? = some m → m ∈ l := by
  induction l with
  | nil => intro m h; simp at h
  | cons a as ih =>
    intro m h
    simp only [List.max?_cons] at h
    cases hm : as.max? with
    | none =>
      rw [hm] at h
      simp only [Option.elim, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self
    | some k =>
      rw [hm] at h
      simp only [Option.elim, Option.some.injEq] at h
      rcases max_choice a k with hmax | hmax
      · rw [← h, hmax]; exact List.mem_cons_self
      · rw [← h, hmax]; exact List.mem_cons_of_mem a (ih hm)

theorem doomedAuth_not_win (Δ : ℕ) (tL : Option ℕ) (tStar : ℕ) (s : GameState St Msg C)
    (hd : DoomedAuth tL tStar s) : (s.win && authLosingConditionsAvoided Δ tL tStar s) = false := by
  rcases hd with h1 | h2 | h3 | ⟨l, rfl, hnl, _⟩
  · unfold Doomed1 at h1
    rw [List.any_eq_true] at h1
    rcases h1 with ⟨l, hl, hlt⟩
    have hall : s.leaks.all (fun l => !(ltOpt tL l && decide (l < tStar))) = false := by
      rw [List.all_eq_false]
      exact ⟨l, hl, by simp [hlt]⟩
    simp only [authLosingConditionsAvoided, hall, Bool.and_false, Bool.false_and]
  · simp [h2.1]
  · unfold Doomed3 at h3
    rw [List.any_eq_true] at h3
    rcases h3 with ⟨pe, hpe, hlt⟩
    have hall : s.corrs.all (fun pe => !(pe.1 == Party.receiverOf tStar && ltOpt tL pe.2)) = false := by
      rw [List.all_eq_false]
      exact ⟨pe, hpe, by simp [hlt]⟩
    simp only [authLosingConditionsAvoided, hall, Bool.and_false]
  · have hcan : (canon tStar s == some l) = false := by
      rw [beq_eq_false_iff_ne]
      intro hc
      have hm := list_max?_mem hc
      rw [List.mem_filter] at hm
      exact hnl hm.1
    simp only [authLosingConditionsAvoided, hcan, Bool.and_false, Bool.false_and]

theorem le_maxOpt_right (tL : Option ℕ) (l : ℕ) : l ≤ maxOpt tL l := by
  cases tL <;> simp [maxOpt]

theorem le_maxOpt_left {tL : Option ℕ} {m : ℕ} (h : tL = some m) (l : ℕ) :
    m ≤ maxOpt tL l := by
  subst h; simp [maxOpt]

theorem update_epoch_ge (ep : Party → ℕ) (P Q : Party) (v : ℕ) (hv : ep P ≤ v) :
    ep Q ≤ Function.update ep P v Q := by
  by_cases h : Q = P
  · subst h; simp [hv]
  · simp [h]

theorem doomed1_of_leaks_sub {tL : Option ℕ} {tStar : ℕ} {s s' : GameState St Msg C}
    (h1 : Doomed1 tL tStar s) (hsub : ∀ x ∈ s.leaks, x ∈ s'.leaks) :
    Doomed1 tL tStar s' := by
  unfold Doomed1 at h1 ⊢
  rw [List.any_eq_true] at h1 ⊢
  rcases h1 with ⟨l, hl, hlt⟩
  exact ⟨l, hsub l hl, hlt⟩

theorem doomed3_of_corrs_sub {tL : Option ℕ} {tStar : ℕ} {s s' : GameState St Msg C}
    (h3 : Doomed3 tL tStar s) (hsub : ∀ x ∈ s.corrs, x ∈ s'.corrs) :
    Doomed3 tL tStar s' := by
  unfold Doomed3 at h3 ⊢
  rw [List.any_eq_true] at h3 ⊢
  rcases h3 with ⟨pe, hpe, hlt⟩
  exact ⟨pe, hsub pe hpe, hlt⟩

theorem doomedAuth_epMgmt {Δ qep : ℕ} {tL : Option ℕ} {tStar : ℕ}
    {s s₁ : GameState St Msg C} {P : Party} {bad : Bool}
    (hd : DoomedAuth tL tStar s) (hep : s.epMgmt Δ qep P bad = some s₁) :
    DoomedAuth tL tStar s₁ := by
  unfold GameState.epMgmt at hep
  split_ifs at hep with hs hq1 hb hq2
  · injection hep with hep; subst hep
    have hA := update_epoch_ge s.epoch P .A (s.epoch P + 1) (by omega)
    have hB := update_epoch_ge s.epoch P .B (s.epoch P + 1) (by omega)
    rcases hd with h1 | ⟨hw, ⟨m, hm, htm⟩, htr⟩ | h3 | ⟨l, rfl, hnl, hmin, hmax⟩
    · exact Or.inl (doomed1_of_leaks_sub h1 fun x hx => by
        simp [GameState.leak, List.mem_cons, hx])
    · refine Or.inr (Or.inl ⟨hw, ⟨maxOpt s.tL (s.epoch P + 1), rfl, ?_⟩, htr⟩)
      exact le_trans htm (le_maxOpt_left hm _)
    · exact Or.inr (Or.inr (Or.inl h3))
    · refine Or.inr (Or.inr (Or.inr ⟨l, rfl, ?_, by dsimp only [GameState.leak]; omega,
        by dsimp only [GameState.leak]; omega⟩))
      simp only [GameState.leak, List.mem_cons, not_or]
      refine ⟨?_, hnl⟩
      have hP : l ≤ s.epoch P := by cases P <;> omega
      have := le_maxOpt_right s.tL (s.epoch P + 1)
      omega
  · injection hep with hep; subst hep
    have hA := update_epoch_ge s.epoch P .A (s.epoch P + 1) (by omega)
    have hB := update_epoch_ge s.epoch P .B (s.epoch P + 1) (by omega)
    rcases hd with h1 | h2 | h3 | ⟨l, rfl, hnl, hmin, hmax⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr ⟨l, rfl, hnl, by dsimp only; omega, by dsimp only; omega⟩))
  · injection hep with hep; subst hep; exact hd

theorem doomedAuth_record {Δ : ℕ} (hΔ : 0 < Δ) {tL : Option ℕ} {tStar : ℕ}
    {s : GameState St Msg C} (P : Party) (st' : St) (r : Record Msg C) (isChall : Bool)
    (hr : r.pos.epoch = s.epoch P)
    (hd : DoomedAuth tL tStar s) :
    DoomedAuth tL tStar (s.record Δ P st' r isChall) := by
  rcases hd with h1 | ⟨hw, ⟨m, hm, htm⟩, htr⟩ | h3 | ⟨l, rfl, hnl, hmin, hmax⟩
  · exact Or.inl h1
  · refine Or.inr (Or.inl ⟨hw, ⟨m, hm, htm⟩, ?_⟩)
    intro r' hr' heq
    simp only [GameState.record, List.mem_cons] at hr' ⊢
    rcases hr' with rfl | hr'
    · have hsafe : s.safeCh Δ P = false := by
        simp only [GameState.safeCh, healedBy, hm, ← hr, heq, decide_eq_false_iff_not]
        omega
      simp [hsafe]
    · have hmem := htr r' hr' heq
      split_ifs <;> simp [hmem]
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr ⟨l, rfl, hnl, hmin, hmax⟩))

theorem doomedAuth_accept {tL : Option ℕ} {tStar : ℕ}
    {s : GameState St Msg C} (P : Party) (st' : St) (pos : Pos)
    (hd : DoomedAuth tL tStar s) :
    DoomedAuth tL tStar (s.accept P st' pos) := by
  have hA := update_epoch_ge s.epoch P .A (max (s.epoch P) pos.epoch) (Nat.le_max_left _ _)
  have hB := update_epoch_ge s.epoch P .B (max (s.epoch P) pos.epoch) (Nat.le_max_left _ _)
  rcases hd with h1 | ⟨hw, ⟨m, hm, htm⟩, htr⟩ | h3 | ⟨l, rfl, hnl, hmin, hmax⟩
  · exact Or.inl h1
  · refine Or.inr (Or.inl ⟨hw, ⟨m, hm, htm⟩, ?_⟩)
    intro r hr heq
    simp only [GameState.accept, GameState.delete, List.mem_filter] at hr ⊢
    exact ⟨htr r hr.1 heq, hr.2⟩
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr ⟨l, rfl, hnl, by dsimp only [GameState.accept, GameState.delete]; omega,
      by dsimp only [GameState.accept, GameState.delete]; omega⟩))

theorem doomedAuth_afterCorr {tL : Option ℕ} {tStar : ℕ}
    {s : GameState St Msg C} (P : Party)
    (hd : DoomedAuth tL tStar s) :
    DoomedAuth tL tStar (s.afterCorr P) := by
  rcases hd with h1 | ⟨hw, ⟨m, hm, htm⟩, htr⟩ | h3 | ⟨l, rfl, hnl, hmin, hmax⟩
  · exact Or.inl (doomed1_of_leaks_sub h1 fun x hx => by
      simp [GameState.afterCorr, GameState.leak, List.mem_cons, hx])
  · refine Or.inr (Or.inl ⟨hw, ⟨maxOpt s.tL (max (s.epoch .A) (s.epoch .B)), rfl, ?_⟩, ?_⟩)
    · exact le_trans htm (le_maxOpt_left hm _)
    · intro r hr heq
      simp only [GameState.afterCorr, GameState.leak, List.mem_append] at hr ⊢
      exact Or.inr (htr r hr heq)
  · exact Or.inr (Or.inr (Or.inl (doomed3_of_corrs_sub h3 fun x hx => by
      simp [GameState.afterCorr, List.mem_cons, hx])))
  · refine Or.inr (Or.inr (Or.inr ⟨l, rfl, ?_, hmin, hmax⟩))
    simp only [GameState.afterCorr, GameState.leak, List.mem_cons, not_or]
    refine ⟨?_, hnl⟩
    have := le_maxOpt_right s.tL (max (s.epoch .A) (s.epoch .B))
    omega

theorem doomed2_trivial_tStar {Δ tStar : ℕ} (hΔ : 0 < Δ) {s : GameState St Msg C}
    (h2 : Doomed2 tStar s) (pos : Pos) (hpos : pos.epoch = tStar) :
    s.trivial Δ pos = true := by
  rcases h2 with ⟨_, ⟨m, hm, htm⟩, htr⟩
  unfold GameState.trivial
  by_cases hany : s.trans.any (fun r => r.pos == pos) = true
  · rw [List.any_eq_true] at hany
    rcases hany with ⟨r, hr, hreq⟩
    rw [beq_iff_eq] at hreq
    subst hreq
    have hc : r.pos ∈ s.comp := htr r hr hpos
    simp [List.contains_iff_exists_mem_beq, hc]
  · have hnh : healedBy s.tL Δ pos.epoch = false := by
      simp only [healedBy, hm, hpos, decide_eq_false_iff_not]
      omega
    simp [hany, hnh]

theorem mem_support_liftProb {α : Type} {p : ProbComp α} {s s' : GameState St Msg C} {a : α}
    (h : (a, s') ∈ support ((liftM p : StateT (GameState St Msg C) ProbComp α).run s)) :
    a ∈ support p ∧ s' = s := by
  simp only [StateT.run_monadLift, monadLift_self, MonadAttach.mem_support_bind,
    support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h
  rcases h with ⟨a', ha', rfl, rfl⟩
  exact ⟨ha', rfl⟩

theorem doomedAuth_oracleImpl (sm : SMScheme Key St Msg Coins C) {Δ qep : ℕ} (hΔ : 0 < Δ)
    (tL : Option ℕ) (tStar : ℕ)
    (t : (unifSpec + spec St Msg Coins C).Domain)
    {s s' : GameState St Msg C} {u : (unifSpec + spec St Msg Coins C).Range t}
    (hd : DoomedAuth tL tStar s)
    (hmem : (u, s') ∈ support
      ((((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (GameState St Msg C) ProbComp) +
        oracleImpl sm Δ qep (Config.auth tStar)) t).run s)) :
    DoomedAuth tL tStar s' := by
  rcases t with n | ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
  · dsimp only [QueryImpl.add_apply, QueryImpl.liftTarget, QueryImpl.ofLift] at hmem
    rw [(mem_support_liftProb hmem).2]
    exact hd
  · dsimp only [QueryImpl.add_apply, oracleImpl, transmitImpl] at hmem
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hw : s.win = true
    · simp only [hw, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.ext_iff] at hmem
      rw [hmem.2]; exact hd
    · simp only [hw, Bool.false_eq_true, ↓reduceIte] at hmem
      rw [StateT.run_bind, MonadAttach.mem_support_bind] at hmem
      rcases hmem with ⟨⟨⟨coins, bad⟩, s₀⟩, h₀, hmem⟩
      have hs₀ := (mem_support_liftProb h₀).2
      rw [hs₀] at hmem
      dsimp only at hmem
      cases hep : s.epMgmt Δ qep P bad with
      | none =>
        rw [hep] at hmem
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
        rw [hmem.2]; exact hd
      | some s₁ =>
        rw [hep] at hmem
        simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
          support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
        rw [hmem.2]
        exact doomedAuth_record hΔ P _ _ false rfl (doomedAuth_epMgmt hd hep)
  · dsimp only [QueryImpl.add_apply, oracleImpl, challImpl, Config.auth] at hmem
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hw : s.win = true
    · simp only [hw, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.ext_iff] at hmem
      rw [hmem.2]; exact hd
    · simp only [hw, Bool.false_eq_true, ↓reduceIte] at hmem
      rw [StateT.run_bind, MonadAttach.mem_support_bind] at hmem
      rcases hmem with ⟨⟨⟨coins, bad⟩, s₀⟩, h₀, hmem⟩
      have hs₀ := (mem_support_liftProb h₀).2
      rw [hs₀] at hmem
      dsimp only at hmem
      cases hep : s.epMgmt Δ qep P bad <;>
        simp only [hep, Bool.not_false, Bool.or_true, ↓reduceIte, StateT.run_pure,
          support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem <;>
        (rw [hmem.2]; exact hd)
  · dsimp only [QueryImpl.add_apply, oracleImpl, deliverImpl, Config.auth] at hmem
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hw : s.win = true
    · simp only [hw, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.ext_iff] at hmem
      rw [hmem.2]; exact hd
    · simp only [hw, Bool.false_eq_true, ↓reduceIte] at hmem
      cases hin : s.inTransit P.other c with
      | none =>
        rw [hin] at hmem
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
        rw [hmem.2]; exact hd
      | some r =>
        rw [hin] at hmem
        cases hrcv : sm.receive (s.st P) c with
        | none =>
          rw [hrcv] at hmem
          simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
            support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
          rw [hmem.2]; exact hd
        | some res =>
          rcases res with ⟨st', t', i', m'⟩
          rw [hrcv] at hmem
          simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
            StateT.run_set, pure_bind, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.ext_iff] at hmem
          rw [hmem.2]
          exact doomedAuth_accept P st' r.pos hd
  · dsimp only [QueryImpl.add_apply, oracleImpl, injectImpl] at hmem
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    split_ifs at hmem with hcond
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
      rw [hmem.2]; exact hd
    · cases hrcv : sm.receive (s.st P) c with
      | none =>
        rw [hrcv] at hmem
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
        rw [hmem.2]; exact hd
      | some res =>
        rcases res with ⟨st', t', i', m'⟩
        rw [hrcv] at hmem
        dsimp only at hmem
        split_ifs at hmem with hqep htriv hfull
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
          rw [hmem.2]; exact hd
        · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
            support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
          rw [hmem.2]
          exact doomedAuth_accept P st' ⟨P.other, t', i'⟩ hd
        · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
            support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
          rw [hmem.2]
          simp only [Config.auth, beq_iff_eq] at hfull
          rcases hd with h1 | h2 | h3 | h4
          · exact Or.inl h1
          · exfalso; exact htriv (doomed2_trivial_tStar hΔ h2 ⟨P.other, t', i'⟩ hfull)
          · exact Or.inr (Or.inr (Or.inl h3))
          · exact Or.inr (Or.inr (Or.inr h4))
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
          rw [hmem.2]; exact hd
  · dsimp only [QueryImpl.add_apply, oracleImpl, corrImpl] at hmem
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    split_ifs at hmem with hcond
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
      rw [hmem.2]; exact hd
    · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
        support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
      rw [hmem.2]
      exact doomedAuth_afterCorr P hd

theorem doomedAuth_simulateQ (sm : SMScheme Key St Msg Coins C) {Δ qep : ℕ} (hΔ : 0 < Δ)
    (tL : Option ℕ) (tStar : ℕ) {α : Type} (oa : AdversaryComp St Msg Coins C α) :
    ∀ {s s' : GameState St Msg C} {a : α},
      DoomedAuth tL tStar s →
      (a, s') ∈ support ((simulateQ
        ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (GameState St Msg C) ProbComp) +
          oracleImpl sm Δ qep (Config.auth tStar)) oa).run s) →
      DoomedAuth tL tStar s' := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s s' a' hd hmem
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.ext_iff] at hmem
    rw [hmem.2]; exact hd
  | query_bind t k ih =>
    intro s s' a' hd hmem
    rw [simulateQ_query_bind, StateT.run_bind, MonadAttach.mem_support_bind] at hmem
    rcases hmem with ⟨⟨u, s₁⟩, h₁, h₂⟩
    exact ih u (doomedAuth_oracleImpl sm hΔ tL tStar t hd h₁) h₂

end Doomed

/-! ## Engine abort preservation -/

section Abort

open Engine

variable {Γ T Sig SS RS M E CCoins : Type} {Γv Sv SSv RSv HS : Type} {ι : Type}
  {tspec : OracleSpec.{0, 0} ι} {S : Type}
  [DecidableEq M] [DecidableEq T] [DecidableEq E] [Inhabited E]

theorem abort_simulateQ
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy)
    (tImpl : QueryImpl tspec (StateT S ProbComp))
    {α : Type} (oa : AdversaryComp (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α) :
    ∀ {es es' : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS} {sc sc' : S} {a : α},
      es.abort = true →
      ((a, es'), sc') ∈ support ((simulateQ
        ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT S ProbComp) + tImpl)
        ((simulateQ (implE hk Δ qep maxSkip cfg π) oa).run es)).run sc) →
      es'.abort = true := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro es es' sc sc' a' hab hmem
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.ext_iff] at hmem
    rw [hmem.1.2]; exact hab
  | query_bind t k ih =>
    intro es es' sc sc' a' hab hmem
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, MonadAttach.mem_support_bind] at hmem
    rcases hmem with ⟨⟨⟨u, es₁⟩, sc₁⟩, h₁, h₂⟩
    rcases t with n | ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
    · dsimp only [implE, coinsE, HAdd.hAdd, Add.add, QueryImpl.add] at h₁
      simp only [StateT.run_lift, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, QueryImpl.add_apply, QueryImpl.liftTarget,
        QueryImpl.ofLift, simulateQ_pure, StateT.run_bind, StateT.run_monadLift, monadLift_self,
        StateT.run_pure, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff,
        Prod.ext_iff] at h₁
      rcases h₁ with ⟨_, _, ⟨_, rfl⟩, rfl⟩
      exact ih u hab h₂
    all_goals
      dsimp only [implE, transmitE, challE, deliverE, injectE, corrE,
        HAdd.hAdd, Add.add, QueryImpl.add] at h₁
      simp only [hab, Bool.true_or, ↓reduceIte,
        StateT.run_bind, StateT.run_get, pure_bind, StateT.run_pure,
        simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₁
      rw [← h₁.1.2] at hab
      exact ih u hab h₂

theorem evalDist_runR_eq_pure_false_of_abort
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy)
    (tImpl : QueryImpl tspec (StateT S ProbComp))
    {α : Type} (oa : AdversaryComp (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) (sc : S)
    (hab : es.abort = true) :
    𝒟[((simulateQ
      ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT S ProbComp) + tImpl)
      ((simulateQ (implE hk Δ qep maxSkip cfg π) oa).run es)).run sc) >>=
        fun res => pure (authOut Δ π res.1.2)] =
      𝒟[(pure false : ProbComp Bool)] := by
  apply evalDist_bind_eq_pure_false
  rintro ⟨⟨a, es'⟩, sc'⟩ hmem
  have hab' : es'.abort = true :=
    abort_simulateQ hk Δ qep maxSkip cfg π tImpl oa hab hmem
  simp [authOut, hab']

end Abort

/-! ## State projection and `Sync9` -/

section Sync9

open Engine

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

def realVP (γc : Γ) (vp : PartyState (Option Γ) T Sig SS RS) : PartyState Γ T Sig SS RS :=
  { id := vp.id
    root := vp.root
    vS := vp.vS
    vR := vp.vR
    γ := vp.γ.getD γc
    curCkaMsg := vp.curCkaMsg
    tcur := vp.tcur }

def realGS (sc : CKA.GameState Γ T)
    (g : GameState (PartyState (Option Γ) T Sig SS RS) M (Header T × E)) :
    GameState (PartyState Γ T Sig SS RS) M (Header T × E) :=
  { st := fun P => realVP (sc.st P) (g.st P)
    epoch := g.epoch
    idx := g.idx
    tL := g.tL
    trans := g.trans
    chall := g.chall
    comp := g.comp
    maxAcc := g.maxAcc
    b := g.b
    win := g.win
    leaks := g.leaks
    corrs := g.corrs }

theorem evalDist_runL_eq_pure_false_of_doomed
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (tStar : ℕ)
    {α : Type} (oa : AdversaryComp (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (s : GameState (PartyState Γ T Sig SS RS) M (Header T × E))
    (hdoom : DoomedAuth tL tStar s) :
    𝒟[((simulateQ
      ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (GameState (PartyState Γ T Sig SS RS) M (Header T × E)) ProbComp) +
        oracleImpl (scheme cka prng fs lam) (2 + Δcka) qep (Config.auth tStar))
      oa).run s) >>= fun res => pure (res.2.win && authLosingConditionsAvoided (2 + Δcka) tL tStar res.2)] =
      𝒟[(pure false : ProbComp Bool)] := by
  apply evalDist_bind_eq_pure_false
  rintro ⟨a, s'⟩ hmem
  have hΔ : 0 < 2 + Δcka := by omega
  have hdoom' : DoomedAuth tL tStar s' :=
    doomedAuth_simulateQ (scheme cka prng fs lam) hΔ tL tStar oa hdoom hmem
  rw [doomedAuth_not_win (2 + Δcka) tL tStar s' hdoom']

theorem sendsIn_other (P : Party) (t : ℕ) : P.other.sendsIn t = !(P.sendsIn t) := by
  rw [Bool.eq_iff_iff]
  cases P <;> simp [Party.other, Party.sendsIn]

theorem sendsIn_succ (P : Party) (t : ℕ) : P.sendsIn (t + 1) = !(P.sendsIn t) := by
  rw [Bool.eq_iff_iff]
  cases P <;> simp [Party.sendsIn] <;> omega

theorem eq_senderOf_of_sendsIn {P : Party} {t : ℕ} (h : P.sendsIn t = true) :
    P = Party.senderOf t := by
  cases P <;> unfold Party.senderOf <;> simp [Party.sendsIn] at h ⊢ <;> omega

theorem eq_receiverOf_of_sendsIn_false {P : Party} {t : ℕ} (h : P.sendsIn t = false) :
    P = Party.receiverOf t := by
  unfold Party.receiverOf
  have h' : P.other.sendsIn t = true := by rw [sendsIn_other, h]; rfl
  rw [← eq_senderOf_of_sendsIn h', Party.other_other]

def isLocal (tL : Option ℕ) (Δcka t : ℕ) : Bool :=
  match tL with
  | none => true
  | some l => decide (l + 2 + Δcka ≤ t)

/-- Synchronization invariant between the `authGame` state `s`, the `redCKA` engine state `es`, and
the CKA game state `sc`. -/
structure Sync9 (cka : CKAScheme KC Γ CCoins T I) (Δcka : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (s : GameState (PartyState Γ T Sig SS RS) M (Header T × E))
    (es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I))
    (sc : CKA.GameState Γ T) : Prop where
  valid : lastLeakGuessAdmissible (2 + Δcka) tL tStar = true
  s_eq : s = realGS sc es.g
  no_abort : es.abort = false
  b_eq : es.g.b = false
  sc_b : sc.b = false
  st_id : ∀ P, (es.g.st P).id = P
  st_tcur : ∀ P, (es.g.st P).tcur = es.g.epoch P
  γ_eq : ∀ P, (es.g.st P).γ = if isLocal tL Δcka (es.g.epoch P) then some (s.st P).γ else none
  sc_epoch : ∀ l, tL = some l → ∀ P, sc.epoch P = min (es.g.epoch P) (l + 2 + Δcka)
  tL_none : es.g.tL = none → es.g.leaks = []
  tL_some : ∀ m, es.g.tL = some m → m ∈ es.g.leaks ∧ ∀ l ∈ es.g.leaks, l ≤ m
  leaks_ub : ∀ l ∈ es.g.leaks, l ≤ max (es.g.epoch .A) (es.g.epoch .B)
  comp_unhealed : ∀ pos ∈ es.g.comp, healedBy es.g.tL (2 + Δcka) pos.epoch = false
  epoch_le : ∀ P, es.g.epoch P ≤ es.g.epoch P.other + 1
  epoch_step_sends : ∀ P, es.g.epoch P = es.g.epoch P.other + 1 →
    P.sendsIn (es.g.epoch P) = true
  trans_inv : ∀ r ∈ es.g.trans,
    r.ct.1.1 = r.pos.epoch ∧
    r.pos.sender.sendsIn r.pos.epoch = true ∧
    r.pos.epoch ≤ es.g.epoch r.pos.sender ∧
    (r.pos.epoch = es.g.epoch r.pos.sender → r.ct.1.2 = (es.g.st r.pos.sender).curCkaMsg)
  cache_gt : ∀ t', max (es.g.epoch .A) (es.g.epoch .B) < t' → es.h.cache t' = none
  cka_eq : ∀ P, es.g.epoch P = es.g.epoch P.other → P.sendsIn (es.g.epoch P + 1) = true →
    ∀ rs, cka.AgreesFrom (s.st P).γ (s.st P.other).γ rs
  cka_step : ∀ P, es.g.epoch P + 1 = es.g.epoch P.other →
    ∃ T_t I_t,
      es.h.cache (es.g.epoch P.other) = some (T_t, I_t) ∧
      (es.g.st P.other).curCkaMsg = some T_t ∧
      (∀ l, tL = some l → es.g.epoch P.other ≤ l + 2 + Δcka → sc.lastMsg = some T_t) ∧
      (cka.receive (s.st P).γ T_t).2 = I_t ∧
      ∀ rs, cka.AgreesFrom (cka.receive (s.st P).γ T_t).1 (s.st P.other).γ rs

namespace Sync9

variable {cka : CKAScheme KC Γ CCoins T I} {Δcka : ℕ} {tL : Option ℕ} {tStar : ℕ}
  {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
  {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
  {sc : CKA.GameState Γ T}

theorem epoch_eq_of_sendsIn_succ (hs : Sync9 cka Δcka tL tStar s es sc) {P : Party}
    (hsend : P.sendsIn (es.g.epoch P + 1) = true) :
    es.g.epoch P = es.g.epoch P.other := by
  have hle1 := hs.epoch_le P
  have hle2 := hs.epoch_le P.other
  rw [Party.other_other] at hle2
  by_cases h1 : es.g.epoch P = es.g.epoch P.other + 1
  · have hs1 := hs.epoch_step_sends P h1
    rw [sendsIn_succ, hs1] at hsend
    contradiction
  · by_cases h2 : es.g.epoch P.other = es.g.epoch P + 1
    · have hs2 := hs.epoch_step_sends P.other (by rw [Party.other_other]; exact h2)
      rw [h2, sendsIn_other, hsend] at hs2
      contradiction
    · omega

theorem epoch_eq_of_deliver_step (hs : Sync9 cka Δcka tL tStar s es sc) {P : Party}
    {r : Record M (Header T × E)} (hmem : r ∈ es.g.trans) (hsnd : r.pos.sender = P.other)
    (ht : r.ct.1.1 = es.g.epoch P + 1) :
    es.g.epoch P + 1 = es.g.epoch P.other := by
  have htr := hs.trans_inv r hmem
  have hle := hs.epoch_le P.other
  rw [Party.other_other] at hle
  have h1 : r.pos.epoch = es.g.epoch P + 1 := by omega
  have h2 : r.pos.epoch ≤ es.g.epoch P.other := by rw [← hsnd]; exact htr.2.2.1
  omega

theorem trivial_false_of_safeInj (hs : Sync9 cka Δcka tL tStar s es sc)
    (hsafe : es.g.safeInj (2 + Δcka) = true) {P : Party} {pos : Pos}
    (ht : es.g.epoch P < pos.epoch) :
    es.g.trivial (2 + Δcka) pos = false := by
  unfold GameState.safeInj at hsafe
  unfold GameState.trivial
  rw [Bool.or_eq_false_iff]
  have hmin : min (es.g.epoch .A) (es.g.epoch .B) ≤ es.g.epoch P := by
    cases P <;> simp
  have hheal : healedBy es.g.tL (2 + Δcka) pos.epoch = true := by
    cases htL : es.g.tL with
    | none => rfl
    | some m =>
      simp only [htL, healedBy, decide_eq_true_eq] at hsafe ⊢
      omega
  refine ⟨?_, by simp [hheal]⟩
  rw [List.contains_eq_mem, decide_eq_false_iff_not]
  intro hmem
  have hun := hs.comp_unhealed pos hmem
  rw [hheal] at hun
  contradiction

theorem doomed4_or_local_of_safeInj_tStar (hs : Sync9 cka Δcka tL tStar s es sc)
    (hsafe : es.g.safeInj (2 + Δcka) = true) {P : Party}
    (ht : es.g.epoch P + 1 = tStar) :
    isLocal tL Δcka (es.g.epoch P) = true ∨ Doomed4 tL s := by
  cases htL : tL with
  | none =>
    left; rfl
  | some l =>
    have hvg := hs.valid
    simp only [lastLeakGuessAdmissible, htL, healedBy, Bool.and_eq_true, decide_eq_true_eq] at hvg
    by_cases hmem : l ∈ es.g.leaks
    · left
      simp only [isLocal, decide_eq_true_eq]
      cases hstL : es.g.tL with
      | none =>
        rw [hs.tL_none hstL] at hmem
        nomatch hmem
      | some m =>
        have hle := (hs.tL_some m hstL).2 l hmem
        unfold GameState.safeInj at hsafe
        simp only [hstL, healedBy, decide_eq_true_eq] at hsafe
        have hmin : min (es.g.epoch .A) (es.g.epoch .B) ≤ es.g.epoch P := by
          cases P <;> simp
        omega
    · right
      rw [hs.s_eq]
      refine ⟨l, rfl, hmem, ?_, ?_⟩
      · have hle1 := hs.epoch_le P
        cases P <;> simp [realGS, Party.other] at hle1 ⊢ <;> omega
      · cases P <;> simp [realGS] <;> omega

theorem epMgmt_tL_inv (hs : Sync9 cka Δcka tL tStar s es sc) {qep : ℕ} {P : Party} {bad : Bool}
    {s₁ : GameState (PartyState (Option Γ) T Sig SS RS) M (Header T × E)}
    (hep : es.g.epMgmt (2 + Δcka) qep P bad = some s₁) :
    s₁.win = es.g.win ∧ s₁.trans = es.g.trans ∧ s₁.comp = es.g.comp ∧
    (s₁.tL = none → s₁.leaks = []) ∧
    (∀ m, s₁.tL = some m → m ∈ s₁.leaks ∧ ∀ l ∈ s₁.leaks, l ≤ m) := by
  by_cases h1 : P.sendsIn (es.g.epoch P + 1) = true
  · have h2 : ¬qep < es.g.epoch P + 1 := by intro h; simp [GameState.epMgmt, h1, h] at hep
    by_cases h3 : (bad && !(es.g.safeCh (2 + Δcka) P)) = true
    · simp only [GameState.epMgmt, h1, h2, h3, ↓reduceIte, Option.some.injEq] at hep
      subst hep
      refine ⟨rfl, rfl, rfl, by simp [GameState.leak], ?_⟩
      intro m hm
      simp only [GameState.leak, Option.some.injEq] at hm
      subst hm
      refine ⟨by simp [GameState.leak], ?_⟩
      intro l hl
      simp only [GameState.leak, List.mem_cons] at hl
      rcases hl with rfl | hl
      · exact le_rfl
      · cases hstL : es.g.tL with
        | none =>
          rw [hs.tL_none hstL] at hl
          nomatch hl
        | some m₀ =>
          have hle := (hs.tL_some m₀ hstL).2 l hl
          simp [maxOpt]
          omega
    · simp only [Bool.not_eq_true] at h3
      simp [GameState.epMgmt, h1, h2, h3] at hep
      subst hep
      exact ⟨rfl, rfl, rfl, hs.tL_none, hs.tL_some⟩
  · simp only [Bool.not_eq_true] at h1
    have h2 : ¬qep < es.g.epoch P := by intro h; simp [GameState.epMgmt, h1, h] at hep
    simp [GameState.epMgmt, h1, h2] at hep
    subst hep
    exact ⟨rfl, rfl, rfl, hs.tL_none, hs.tL_some⟩

theorem doomed_of_leakDoom_epMgmt (hs : Sync9 cka Δcka tL tStar s es sc)
    (hwin : es.g.win = false) {qep : ℕ} {P : Party} {bad : Bool}
    {s₁ : GameState (PartyState (Option Γ) T Sig SS RS) M (Header T × E)}
    (hep : es.g.epMgmt (2 + Δcka) qep P bad = some s₁)
    (hld : (Policy.mk true tL tStar).leakDoom es.g s₁ = true)
    (st' : PartyState Γ T Sig SS RS) (m : M) (c : Header T × E) (isChall : Bool) :
    DoomedAuth tL tStar
      ((realGS sc s₁).record (2 + Δcka) P st' ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, c⟩ isChall) := by
  obtain ⟨hwin1, htr1, hcomp1, htL1, htL2⟩ := hs.epMgmt_tL_inv hep
  rw [hwin] at hwin1
  unfold Policy.leakDoom at hld
  rw [Bool.or_eq_true] at hld
  rcases hld with h1 | h2
  · left
    simpa [Doomed1, GameState.record, realGS] using h1
  · right; left
    simp only [Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq] at h2
    rcases h2 with ⟨⟨l, hl, htle⟩, hlt⟩
    cases hstL : s₁.tL with
    | none =>
      rw [htL1 hstL] at hl
      nomatch hl
    | some m' =>
      have hm' : tStar ≤ m' := le_trans htle ((htL2 m' hstL).2 l hl)
      refine ⟨by simp [GameState.record, realGS, hwin1], ⟨m', by simp [GameState.record, realGS, hstL], hm'⟩, ?_⟩
      intro r' hr' hrt
      simp only [GameState.record, List.mem_cons] at hr'
      rcases hr' with rfl | hr'
      · dsimp only at hrt
        have hsafe : (realGS sc s₁).safeCh (2 + Δcka) P = false := by
          simp only [GameState.safeCh, realGS, hstL, hrt, healedBy, decide_eq_false_iff_not]
          omega
        simp [GameState.record, hsafe]
      · exfalso
        simp only [realGS, htr1] at hr'
        have hinv := hs.trans_inv r' hr'
        have hsnd : r'.pos.sender = Party.senderOf tStar := by
          apply eq_senderOf_of_sendsIn
          rw [← hrt]; exact hinv.2.1
        have hle := hinv.2.2.1
        rw [hrt, hsnd] at hle
        omega

theorem doomed_of_corr_doom (hs : Sync9 cka Δcka tL tStar s es sc)
    (hwin : es.g.win = false) {P : Party}
    (hd : ((Policy.mk true tL tStar).leakDoom es.g (es.g.afterCorr P) ||
      (Policy.mk true tL tStar).corrDoom es.g P) = true) :
    DoomedAuth tL tStar (s.afterCorr P) := by
  rw [Bool.or_eq_true] at hd
  rcases hd with hld | hcd
  · unfold Policy.leakDoom at hld
    rw [Bool.or_eq_true] at hld
    rcases hld with h1 | h2
    · left
      rw [hs.s_eq]
      simpa [Doomed1, GameState.afterCorr, GameState.leak, realGS] using h1
    · right; left
      simp only [Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq] at h2
      rcases h2 with ⟨⟨l, hl, htle⟩, hlt⟩
      rw [hs.s_eq]
      let m' := maxOpt es.g.tL (max (es.g.epoch .A) (es.g.epoch .B))
      have hm' : tStar ≤ m' := by
        simp only [GameState.afterCorr, GameState.leak, List.mem_cons] at hl
        rcases hl with rfl | hl
        · exact htle
        · cases hstL : es.g.tL with
          | none =>
            rw [hs.tL_none hstL] at hl
            nomatch hl
          | some m₀ =>
            have hle := (hs.tL_some m₀ hstL).2 l hl
            simp only [m', maxOpt, hstL]
            omega
      refine ⟨by simp [GameState.afterCorr, GameState.leak, realGS, hwin],
        ⟨m', by simp [GameState.afterCorr, GameState.leak, realGS, m'], hm'⟩, ?_⟩
      intro r' hr' hrt
      simp only [GameState.afterCorr, GameState.leak, realGS] at hr'
      exfalso
      have hinv := hs.trans_inv r' hr'
      have hsnd : r'.pos.sender = Party.senderOf tStar := by
        apply eq_senderOf_of_sendsIn
        rw [← hrt]; exact hinv.2.1
      have hle := hinv.2.2.1
      rw [hrt, hsnd] at hle
      omega
  · right; right; left
    rw [hs.s_eq]
    unfold Doomed3
    simp only [GameState.afterCorr, GameState.leak, realGS, List.any_cons, Bool.or_eq_true]
    left
    simpa [Policy.corrDoom] using hcd

theorem allowCorr_of_corr (hs : Sync9 cka Δcka tL tStar s es sc) {l : ℕ}
    (htL : tL = some l) {P : Party} (hloc : es.g.epoch P < l + 2 + Δcka)
    (hld : (Policy.mk true tL tStar).leakDoom es.g (es.g.afterCorr P) = false)
    (hcd : (Policy.mk true tL tStar).corrDoom es.g P = false) :
    sc.allowCorr (l + 2) = true := by
  unfold CKA.GameState.allowCorr
  rw [decide_eq_true_eq]
  have hscA := hs.sc_epoch l htL .A
  have hscB := hs.sc_epoch l htL .B
  suffices hmax : max (es.g.epoch .A) (es.g.epoch .B) ≤ l by omega
  by_contra hgt
  have hm'_eq : maxOpt es.g.tL (max (es.g.epoch .A) (es.g.epoch .B)) =
      max (es.g.epoch .A) (es.g.epoch .B) := by
    cases hstL : es.g.tL with
    | none => simp [maxOpt]
    | some m₀ =>
      have hm₀ := hs.leaks_ub m₀ (hs.tL_some m₀ hstL).1
      simp [maxOpt]
      omega
  have hld1 : ¬(l < max (es.g.epoch .A) (es.g.epoch .B) ∧
      max (es.g.epoch .A) (es.g.epoch .B) < tStar) := by
    intro ⟨h1, h2⟩
    unfold Policy.leakDoom at hld
    simp only [Bool.or_eq_false_iff, List.any_eq_false] at hld
    have h3 := hld.1 (maxOpt es.g.tL (max (es.g.epoch .A) (es.g.epoch .B)))
      (by simp [GameState.afterCorr, GameState.leak])
    rw [hm'_eq] at h3
    simp [htL, ltOpt, h1, h2] at h3
  have hvg := hs.valid
  simp only [lastLeakGuessAdmissible, htL, healedBy, Bool.and_eq_true, decide_eq_true_eq] at hvg
  have hle_other := hs.epoch_le P.other
  rw [Party.other_other] at hle_other
  have hmax_le : max (es.g.epoch .A) (es.g.epoch .B) ≤ es.g.epoch P + 1 := by
    cases P <;> simp [Party.other] at hle_other ⊢ <;> omega
  have htStar_eq : es.g.epoch P + 1 = tStar ∧ es.g.epoch P.other = tStar ∧ l < es.g.epoch P := by
    cases P <;> simp [Party.other] at hle_other hmax_le hgt hld1 ⊢ <;> omega
  have hsnd_other : P.other.sendsIn tStar = true := by
    rw [← htStar_eq.2.1]
    apply hs.epoch_step_sends P.other
    rw [Party.other_other, htStar_eq.1, htStar_eq.2.1]
  have hrcv : P = Party.receiverOf tStar := by
    apply eq_receiverOf_of_sendsIn_false
    have h := sendsIn_other P.other tStar
    rw [Party.other_other, hsnd_other] at h
    exact h
  unfold Policy.corrDoom at hcd
  rw [← hrcv] at hcd
  simp [htL, ltOpt, htStar_eq.2.2] at hcd

theorem doomed4_of_sendBad_gt (hs : Sync9 cka Δcka tL tStar s es sc) {l qep : ℕ}
    (htL : tL = some l) {P : Party} (hloc : es.g.epoch P < l + 2 + Δcka)
    (hsend : P.sendsIn (es.g.epoch P + 1) = true)
    {s₁ : GameState (PartyState (Option Γ) T Sig SS RS) M (Header T × E)}
    (hep : es.g.epMgmt (2 + Δcka) qep P true = some s₁)
    (hld : (Policy.mk true tL tStar).leakDoom es.g s₁ = false)
    (hgt : l < es.g.epoch P + 1)
    (st' : PartyState Γ T Sig SS RS) (m : M) (c : Header T × E) (isChall : Bool) :
    DoomedAuth tL tStar
      ((realGS sc s₁).record (2 + Δcka) P st' ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, c⟩ isChall) := by
  have heq := hs.epoch_eq_of_sendsIn_succ hsend
  have hvg := hs.valid
  simp only [lastLeakGuessAdmissible, htL, healedBy, Bool.and_eq_true, decide_eq_true_eq] at hvg
  have hq : ¬qep < es.g.epoch P + 1 := by
    intro hq
    simp [GameState.epMgmt, hsend, hq] at hep
  have hsafe : es.g.safeCh (2 + Δcka) P = true := by
    by_contra hnsafe
    simp only [Bool.not_eq_true] at hnsafe
    simp only [GameState.epMgmt, hsend, hq, hnsafe, Bool.not_false, Bool.and_self, ↓reduceIte,
      Option.some.injEq] at hep
    subst hep
    have hm'_ge : es.g.epoch P + 1 ≤ maxOpt es.g.tL (es.g.epoch P + 1) := by
      cases es.g.tL <;> simp [maxOpt]
    unfold Policy.leakDoom at hld
    rw [Bool.or_eq_false_iff] at hld
    by_cases hlt : maxOpt es.g.tL (es.g.epoch P + 1) < tStar
    · have h1 := hld.1
      rw [List.any_eq_false] at h1
      have h1' := h1 (maxOpt es.g.tL (es.g.epoch P + 1)) (by simp [GameState.leak])
      have hlm : l < maxOpt es.g.tL (es.g.epoch P + 1) := by omega
      simp [htL, ltOpt, hlm, hlt] at h1'
    · have h2 := hld.2
      have h3 : es.g.epoch (Party.senderOf tStar) < tStar := by
        have h4 : es.g.epoch (Party.senderOf tStar) = es.g.epoch P := by
          cases P <;> cases Party.senderOf tStar <;> simp [Party.other] at heq ⊢ <;> omega
        omega
      simp only [h3, decide_true, Bool.and_true, List.any_eq_false] at h2
      have h2' := h2 (maxOpt es.g.tL (es.g.epoch P + 1)) (by simp [GameState.leak])
      rw [decide_eq_true_eq] at h2'
      omega
  have hnl : l ∉ es.g.leaks := by
    intro hmem
    cases hstL : es.g.tL with
    | none =>
      rw [hs.tL_none hstL] at hmem
      nomatch hmem
    | some m₀ =>
      have hle := (hs.tL_some m₀ hstL).2 l hmem
      unfold GameState.safeCh at hsafe
      simp only [hstL, healedBy, decide_eq_true_eq] at hsafe
      omega
  simp only [GameState.epMgmt, hsend, hq, hsafe, Bool.not_true, Bool.and_false, ↓reduceIte,
    Option.some.injEq] at hep
  subst hep
  right; right; right
  refine ⟨l, htL, hnl, ?_, ?_⟩
  · cases P <;> simp [GameState.record, realGS, Party.other] at heq ⊢ <;> omega
  · cases P <;> simp [GameState.record, realGS, Party.other] at heq ⊢ <;> omega

theorem sync9_corr (hs : Sync9 cka Δcka tL tStar s es sc) (P : Party) :
    Sync9 cka Δcka tL tStar (s.afterCorr P) { es with g := es.g.afterCorr P } sc := by
  refine
    { valid := hs.valid
      s_eq := by rw [hs.s_eq]; rfl
      no_abort := hs.no_abort
      b_eq := hs.b_eq
      sc_b := hs.sc_b
      st_id := hs.st_id
      st_tcur := hs.st_tcur
      γ_eq := hs.γ_eq
      sc_epoch := hs.sc_epoch
      tL_none := by simp [GameState.afterCorr, GameState.leak]
      tL_some := ?_
      leaks_ub := ?_
      comp_unhealed := ?_
      epoch_le := hs.epoch_le
      epoch_step_sends := hs.epoch_step_sends
      trans_inv := hs.trans_inv
      cache_gt := hs.cache_gt
      cka_eq := hs.cka_eq
      cka_step := hs.cka_step }
  · intro m hm
    simp only [GameState.afterCorr, GameState.leak, Option.some.injEq] at hm
    subst hm
    refine ⟨by simp [GameState.afterCorr, GameState.leak], ?_⟩
    intro l hl
    simp only [GameState.afterCorr, GameState.leak, List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact le_rfl
    · cases hstL : es.g.tL with
      | none =>
        rw [hs.tL_none hstL] at hl
        nomatch hl
      | some m₀ =>
        have hle := (hs.tL_some m₀ hstL).2 l hl
        simp [maxOpt]
        omega
  · intro l hl
    simp only [GameState.afterCorr, GameState.leak, List.mem_cons] at hl ⊢
    rcases hl with rfl | hl
    · cases hstL : es.g.tL with
      | none => simp [maxOpt]
      | some m₀ =>
        have hm₀ := hs.leaks_ub m₀ (hs.tL_some m₀ hstL).1
        simp [maxOpt]
        omega
    · exact hs.leaks_ub l hl
  · intro pos hpos
    simp only [GameState.afterCorr, GameState.leak, List.mem_append, List.mem_map,
      List.mem_filter] at hpos
    rcases hpos with ⟨r, ⟨hr, _⟩, rfl⟩ | hpos
    · have hinv := hs.trans_inv r hr
      have hmax : es.g.epoch r.pos.sender ≤ max (es.g.epoch .A) (es.g.epoch .B) := by
        cases r.pos.sender <;> simp
      cases hstL : es.g.tL <;>
        simp only [GameState.afterCorr, GameState.leak, hstL, maxOpt, healedBy,
          decide_eq_false_iff_not] <;> omega
    · have hun := hs.comp_unhealed pos hpos
      cases hstL : es.g.tL with
      | none => simp [hstL, healedBy] at hun
      | some m₀ =>
        simp only [hstL, healedBy, decide_eq_false_iff_not] at hun
        simp only [GameState.afterCorr, GameState.leak, hstL, maxOpt, healedBy,
          decide_eq_false_iff_not]
        omega

theorem sync9_send_same (hs : Sync9 cka Δcka tL tStar s es sc) {P : Party}
    (hnsend : P.sendsIn (es.g.epoch P + 1) = false) (vS' : Option SS) (m : M) (e : E)
    (isChall : Bool) :
    let h : Header T := (es.g.epoch P, (es.g.st P).curCkaMsg)
    let st_v' := { es.g.st P with vS := vS' }
    let st_r' := { s.st P with vS := vS' }
    let rec_P : Record M (Header T × E) := ⟨⟨P, es.g.epoch P, es.g.idx P + 1⟩, m, (h, e)⟩
    Sync9 cka Δcka tL tStar
      (s.record (2 + Δcka) P st_r' rec_P isChall)
      { es with g := es.g.record (2 + Δcka) P st_v' rec_P isChall }
      sc := by
  intro h st_v' st_r' rec_P
  have hsendP : P.sendsIn (es.g.epoch P) = true := by
    have h1 := sendsIn_succ P (es.g.epoch P)
    rw [hnsend] at h1
    cases hP : P.sendsIn (es.g.epoch P) <;> simp [hP] at h1 ⊢
  refine
    { valid := hs.valid
      s_eq := by
        rw [hs.s_eq]
        simp only [GameState.record, realGS]
        congr 1
        funext Q
        by_cases hQP : Q = P
        · subst hQP; simp [Function.update, realVP, realGS, st_v', st_r', hs.s_eq]
        · simp [Function.update, hQP]
      no_abort := hs.no_abort
      b_eq := hs.b_eq
      sc_b := hs.sc_b
      st_id := fun Q => by
        by_cases hQP : Q = P
        · subst hQP; simp [GameState.record, Function.update, st_v', hs.st_id]
        · simp [GameState.record, Function.update, hQP, hs.st_id]
      st_tcur := fun Q => by
        by_cases hQP : Q = P
        · subst hQP; simp [GameState.record, Function.update, st_v', hs.st_tcur]
        · simp [GameState.record, Function.update, hQP, hs.st_tcur]
      γ_eq := fun Q => by
        by_cases hQP : Q = P
        · subst hQP; simp [GameState.record, Function.update, st_v', st_r', hs.γ_eq]
        · simp [GameState.record, Function.update, hQP, hs.γ_eq]
      sc_epoch := hs.sc_epoch
      tL_none := hs.tL_none
      tL_some := hs.tL_some
      leaks_ub := hs.leaks_ub
      comp_unhealed := ?_
      epoch_le := hs.epoch_le
      epoch_step_sends := hs.epoch_step_sends
      trans_inv := ?_
      cache_gt := hs.cache_gt
      cka_eq := fun Q h1 h2 rs => by
        have hγQ : ((s.record (2 + Δcka) P st_r' rec_P isChall).st Q).γ = (s.st Q).γ := by
          by_cases hQP : Q = P
          · subst hQP; simp [GameState.record, Function.update, st_r']
          · simp [GameState.record, Function.update, hQP]
        have hγQo : ((s.record (2 + Δcka) P st_r' rec_P isChall).st Q.other).γ =
            (s.st Q.other).γ := by
          by_cases hQP : Q.other = P
          · rw [hQP]; simp [GameState.record, Function.update, st_r']
          · simp [GameState.record, Function.update, hQP]
        rw [hγQ, hγQo]
        exact hs.cka_eq Q h1 h2 rs
      cka_step := fun Q h1 => by
        obtain ⟨T_t, I_t, hc, hT, hl, hI, hagr⟩ := hs.cka_step Q h1
        have hT' : ((es.g.record (2 + Δcka) P st_v' rec_P isChall).st Q.other).curCkaMsg =
            (es.g.st Q.other).curCkaMsg := by
          by_cases hQP : Q.other = P
          · rw [hQP]; simp [GameState.record, Function.update, st_v']
          · simp [GameState.record, Function.update, hQP]
        have hγQ : ((s.record (2 + Δcka) P st_r' rec_P isChall).st Q).γ = (s.st Q).γ := by
          by_cases hQP : Q = P
          · subst hQP; simp [GameState.record, Function.update, st_r']
          · simp [GameState.record, Function.update, hQP]
        have hγQo : ((s.record (2 + Δcka) P st_r' rec_P isChall).st Q.other).γ =
            (s.st Q.other).γ := by
          by_cases hQP : Q.other = P
          · rw [hQP]; simp [GameState.record, Function.update, st_r']
          · simp [GameState.record, Function.update, hQP]
        rw [hT', hγQ, hγQo]
        exact ⟨T_t, I_t, hc, hT, hl, hI, hagr⟩ }
  · intro pos hpos
    simp only [GameState.record] at hpos ⊢
    split_ifs at hpos with hsafe
    · exact hs.comp_unhealed pos hpos
    · simp only [List.mem_cons] at hpos
      rcases hpos with rfl | hpos
      · simpa [GameState.safeCh] using hsafe
      · exact hs.comp_unhealed pos hpos
  · intro r hr
    simp only [GameState.record, List.mem_cons] at hr
    rcases hr with rfl | hr
    · refine ⟨rfl, hsendP, le_rfl, fun _ => ?_⟩
      simp [GameState.record, Function.update, st_v', rec_P, h]
    · obtain ⟨h1, h2, h3, h4⟩ := hs.trans_inv r hr
      refine ⟨h1, h2, h3, fun heq => ?_⟩
      rw [h4 heq]
      by_cases hP : r.pos.sender = P
      · rw [hP]; simp [GameState.record, Function.update, st_v']
      · simp [GameState.record, Function.update, hP]

theorem sync9_send_new (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (hs : Sync9 cka Δcka tL tStar s es sc) {qep : ℕ} {P : Party} {bad : Bool}
    (hsend : P.sendsIn (es.g.epoch P + 1) = true)
    {s₁ : GameState (PartyState (Option Γ) T Sig SS RS) M (Header T × E)}
    (hep : es.g.epMgmt (2 + Δcka) qep P bad = some s₁)
    (coins : CCoins) (m : M) (isChall : Bool) :
    let t := es.g.epoch P + 1
    let c_cka := cka.send (s.st P).γ coins
    let p := prng.up (es.g.st P).root c_cka.2.2
    let ss := fs.initSender p.2
    let h : Header T := (t, some c_cka.2.1)
    let out_fs := fs.send ss h m
    let γv' : Option Γ := if isLocal tL Δcka t then some c_cka.1 else none
    let st_v' : PartyState (Option Γ) T Sig SS RS :=
      { es.g.st P with tcur := t, γ := γv', curCkaMsg := some c_cka.2.1, root := p.1, vS := some out_fs.1 }
    let st_r' : PartyState Γ T Sig SS RS :=
      { s.st P with tcur := t, γ := c_cka.1, curCkaMsg := some c_cka.2.1, root := p.1, vS := some out_fs.1 }
    let rec_P : Record M (Header T × E) := ⟨⟨P, t, 1⟩, m, (h, out_fs.2)⟩
    let h' : CKAState T I := { cache := Function.update es.h.cache t (some (c_cka.2.1, c_cka.2.2)) }
    let sc' : CKA.GameState Γ T :=
      if isLocal tL Δcka (es.g.epoch P) then sc else sc.afterSend P c_cka.1 c_cka.2.1
    Sync9 cka Δcka tL tStar
      ((realGS sc s₁).record (2 + Δcka) P st_r' rec_P isChall)
      { es with g := s₁.record (2 + Δcka) P st_v' rec_P isChall, h := h' }
      sc' := by
  intro t c_cka p ss h out_fs γv' st_v' st_r' rec_P h' sc'
  have heq := hs.epoch_eq_of_sendsIn_succ hsend
  have hq : ¬qep < es.g.epoch P + 1 := by intro hq; simp [GameState.epMgmt, hsend, hq] at hep
  obtain ⟨hwin1, htr1, hcomp1, htL1, htL2⟩ := hs.epMgmt_tL_inv hep
  have hs₁_epoch : s₁.epoch = Function.update es.g.epoch P t := by
    by_cases h3 : (bad && !(es.g.safeCh (2 + Δcka) P)) = true
    · simp only [GameState.epMgmt, hsend, hq, h3, ↓reduceIte, Option.some.injEq] at hep
      subst hep; rfl
    · simp only [Bool.not_eq_true] at h3
      simp [GameState.epMgmt, hsend, hq, h3] at hep
      subst hep; rfl
  have hs₁_st : s₁.st = es.g.st := by
    by_cases h3 : (bad && !(es.g.safeCh (2 + Δcka) P)) = true
    · simp only [GameState.epMgmt, hsend, hq, h3, ↓reduceIte, Option.some.injEq] at hep
      subst hep; rfl
    · simp only [Bool.not_eq_true] at h3
      simp [GameState.epMgmt, hsend, hq, h3] at hep
      subst hep; rfl
  have hs₁_b : s₁.b = es.g.b := by
    by_cases h3 : (bad && !(es.g.safeCh (2 + Δcka) P)) = true
    · simp only [GameState.epMgmt, hsend, hq, h3, ↓reduceIte, Option.some.injEq] at hep
      subst hep; rfl
    · simp only [Bool.not_eq_true] at h3
      simp [GameState.epMgmt, hsend, hq, h3] at hep
      subst hep; rfl
  refine
    { valid := hs.valid
      s_eq := by
        simp only [GameState.record, realGS]
        congr 1
        funext Q
        by_cases hQP : Q = P
        · subst Q
          simp only [Function.update_self, realVP, st_v', st_r', hs.s_eq, realGS, γv', sc']
          by_cases hloc1 : isLocal tL Δcka t = true <;>
            by_cases hloc2 : isLocal tL Δcka (es.g.epoch P) = true
          · simp [hloc1, hloc2]
          · simp [hloc1, hloc2]
          · exfalso
            cases tL <;> simp [isLocal, t] at hloc1 hloc2; omega
          · simp [hloc1, hloc2, CKA.GameState.afterSend]
        · simp only [Function.update_of_ne hQP, hs₁_st, sc']
          split_ifs
          · rfl
          · simp [CKA.GameState.afterSend, Function.update_of_ne hQP, realVP]
      no_abort := hs.no_abort
      b_eq := by simp [GameState.record, hs₁_b, hs.b_eq]
      sc_b := by
        dsimp only [sc']
        split_ifs <;> simp [CKA.GameState.afterSend, hs.sc_b]
      st_id := fun Q => by
        by_cases hQP : Q = P
        · subst Q; simp [GameState.record, Function.update, st_v', hs.st_id]
        · simp [GameState.record, Function.update, hQP, hs₁_st, hs.st_id]
      st_tcur := fun Q => by
        by_cases hQP : Q = P
        · subst Q; simp [GameState.record, hs₁_epoch, Function.update, st_v', t]
        · simp [GameState.record, hs₁_epoch, Function.update, hQP, hs₁_st, hs.st_tcur]
      γ_eq := fun Q => by
        by_cases hQP : Q = P
        · subst Q; simp [GameState.record, hs₁_epoch, Function.update, st_v', st_r', γv', t]
        · simp [GameState.record, hs₁_epoch, Function.update, hQP, hs₁_st, hs.γ_eq, hs.s_eq, realGS]
      sc_epoch := fun l htL Q => by
        dsimp only [sc', GameState.record]
        rw [hs₁_epoch]
        by_cases hloc : isLocal tL Δcka (es.g.epoch P) = true
        · simp only [hloc, ↓reduceIte, hs.sc_epoch l htL Q]
          by_cases hQP : Q = P
          · subst Q
            simp only [isLocal, htL, decide_eq_true_eq] at hloc
            simp only [Function.update_self, t]
            omega
          · simp [Function.update_of_ne hQP]
        · simp [ hloc]
          simp only [isLocal, htL, decide_eq_true_eq] at hloc
          by_cases hQP : Q = P
          · subst Q
            simp only [CKA.GameState.afterSend, Function.update_self, hs.sc_epoch l htL P, t]
            omega
          · simp [CKA.GameState.afterSend, Function.update_of_ne hQP, hs.sc_epoch l htL Q]
      tL_none := htL1
      tL_some := htL2
      leaks_ub := ?_
      comp_unhealed := ?_
      epoch_le := fun Q => by
        simp only [GameState.record, hs₁_epoch]
        cases P <;> cases Q <;> simp [Function.update, Party.other, t] at heq ⊢ <;> omega
      epoch_step_sends := fun Q hstep => by
        simp only [GameState.record, hs₁_epoch] at hstep ⊢
        by_cases hQP : Q = P
        · subst Q; simpa [Function.update, t] using hsend
        · exfalso
          cases P <;> cases Q <;> simp [Function.update, Party.other, t] at hQP heq hstep <;> omega
      trans_inv := ?_
      cache_gt := fun t' ht' => by
        simp only [GameState.record, hs₁_epoch] at ht'
        have ht'_ne : t' ≠ t := by
          cases P <;> simp [Function.update, Party.other, t] at heq ht' <;> omega
        have ht'_gt : max (es.g.epoch .A) (es.g.epoch .B) < t' := by
          cases P <;> simp [Function.update, Party.other, t] at heq ht' ⊢ <;> omega
        simp [h', Function.update_of_ne ht'_ne, hs.cache_gt t' ht'_gt]
      cka_eq := fun Q h1 => by
        exfalso
        simp only [GameState.record, hs₁_epoch] at h1
        cases P <;> cases Q <;> simp [Function.update, Party.other, t] at heq h1 <;> omega
      cka_step := fun Q h1 => by
        simp only [GameState.record, hs₁_epoch] at h1 ⊢
        have hQP : Q = P.other := by
          cases P <;> cases Q <;> simp [Function.update, Party.other, t] at heq h1 ⊢ <;> omega
        subst Q
        simp only [Party.other_other, Function.update_self,
          Function.update_of_ne (Party.other_ne P)]
        refine ⟨c_cka.2.1, c_cka.2.2, by simp [h'], by simp [st_v'], ?_, ?_, ?_⟩
        · intro l htL htle
          have hloc : isLocal tL Δcka (es.g.epoch P) = false := by
            simp only [isLocal, htL, decide_eq_false_iff_not, t] at htle ⊢
            omega
          simp [sc', hloc, CKA.GameState.afterSend]
        · have h1' := (hs.cka_eq P heq hsend [coins]).1
          simpa [hs.s_eq, realGS, hs₁_st, c_cka] using h1'.symm
        · intro rs
          have h2' := (hs.cka_eq P heq hsend (coins :: rs)).2
          simpa [hs.s_eq, realGS, hs₁_st, st_r', c_cka] using h2' }
  · intro l hl
    simp only [GameState.record, hs₁_epoch] at hl ⊢
    have hmax1 : es.g.epoch P + 1 ≤
        max (Function.update es.g.epoch P t .A) (Function.update es.g.epoch P t .B) := by
      cases P <;> simp [Function.update, t]
    have hmax2 : max (es.g.epoch .A) (es.g.epoch .B) ≤
        max (Function.update es.g.epoch P t .A) (Function.update es.g.epoch P t .B) := by
      cases P <;> simp [Function.update, Party.other, t] at heq ⊢ <;> omega
    by_cases h3 : (bad && !(es.g.safeCh (2 + Δcka) P)) = true
    · simp only [GameState.epMgmt, hsend, hq, h3, ↓reduceIte, Option.some.injEq] at hep
      subst hep
      simp only [GameState.leak, List.mem_cons] at hl
      rcases hl with rfl | hl
      · cases hstL : es.g.tL with
        | none =>
          simp only [maxOpt]
          omega
        | some m₀ =>
          have hm₀ := hs.leaks_ub m₀ (hs.tL_some m₀ hstL).1
          simp only [maxOpt]
          omega
      · have hle := hs.leaks_ub l hl
        omega
    · simp only [Bool.not_eq_true] at h3
      simp [GameState.epMgmt, hsend, hq, h3] at hep
      subst hep
      have hle := hs.leaks_ub l hl
      omega
  · intro pos hpos
    simp only [GameState.record, hcomp1] at hpos ⊢
    split_ifs at hpos with hsafe
    · have hun := hs.comp_unhealed pos hpos
      by_cases h3 : (bad && !(es.g.safeCh (2 + Δcka) P)) = true
      · simp only [GameState.epMgmt, hsend, hq, h3, ↓reduceIte, Option.some.injEq] at hep
        subst hep
        cases hstL : es.g.tL with
        | none => simp [hstL, healedBy] at hun
        | some m₀ =>
          simp only [hstL, healedBy, decide_eq_false_iff_not] at hun
          simp only [GameState.leak, hstL, maxOpt, healedBy, decide_eq_false_iff_not]
          omega
      · simp only [Bool.not_eq_true] at h3
        simp [GameState.epMgmt, hsend, hq, h3] at hep
        subst hep; exact hun
    · simp only [List.mem_cons] at hpos
      rcases hpos with rfl | hpos
      · simpa [GameState.safeCh, realGS, hs₁_epoch, Function.update_self, rec_P] using hsafe
      · have hun := hs.comp_unhealed pos hpos
        by_cases h3 : (bad && !(es.g.safeCh (2 + Δcka) P)) = true
        · simp only [GameState.epMgmt, hsend, hq, h3, ↓reduceIte, Option.some.injEq] at hep
          subst hep
          cases hstL : es.g.tL with
          | none => simp [hstL, healedBy] at hun
          | some m₀ =>
            simp only [hstL, healedBy, decide_eq_false_iff_not] at hun
            simp only [GameState.leak, hstL, maxOpt, healedBy, decide_eq_false_iff_not]
            omega
        · simp only [Bool.not_eq_true] at h3
          simp [GameState.epMgmt, hsend, hq, h3] at hep
          subst hep; exact hun
  · intro r hr
    simp only [GameState.record, htr1, hs₁_epoch, List.mem_cons] at hr ⊢
    rcases hr with rfl | hr
    · refine ⟨rfl, hsend, by simp [Function.update, rec_P], fun _ => ?_⟩
      simp [Function.update, st_v', rec_P, h]
    · obtain ⟨h1, h2, h3, h4⟩ := hs.trans_inv r hr
      refine ⟨h1, h2, ?_, ?_⟩
      · by_cases hP : r.pos.sender = P
        · rw [hP] at h3 ⊢; simp [Function.update, t]; omega
        · simp [Function.update_of_ne hP, h3]
      · intro heq'
        by_cases hP : r.pos.sender = P
        · rw [hP, Function.update_self] at heq'
          rw [hP] at h3
          omega
        · rw [Function.update_of_ne hP] at heq' ⊢
          rw [hs₁_st]
          exact h4 heq'

theorem sync9_win (hs : Sync9 cka Δcka tL tStar s es sc) (w : Bool) :
    Sync9 cka Δcka tL tStar
      { s with win := w }
      { es with g := { es.g with win := w } }
      sc :=
  { valid := hs.valid
    s_eq := by rw [hs.s_eq]; rfl
    no_abort := hs.no_abort
    b_eq := hs.b_eq
    sc_b := hs.sc_b
    st_id := hs.st_id
    st_tcur := hs.st_tcur
    γ_eq := hs.γ_eq
    sc_epoch := hs.sc_epoch
    tL_none := hs.tL_none
    tL_some := hs.tL_some
    leaks_ub := hs.leaks_ub
    comp_unhealed := hs.comp_unhealed
    epoch_le := hs.epoch_le
    epoch_step_sends := hs.epoch_step_sends
    trans_inv := hs.trans_inv
    cache_gt := hs.cache_gt
    cka_eq := hs.cka_eq
    cka_step := hs.cka_step }

theorem sync9_accept_same (hs : Sync9 cka Δcka tL tStar s es sc) {P : Party}
    (vR' : ℕ → Option RS) {pos : Pos} (hpos_le : pos.epoch ≤ es.g.epoch P) :
    let st_v' := { es.g.st P with vR := vR' }
    let st_r' := { s.st P with vR := vR' }
    Sync9 cka Δcka tL tStar
      (s.accept P st_r' pos)
      { es with g := es.g.accept P st_v' pos }
      sc := by
  intro st_v' st_r'
  have hep_eq : Function.update es.g.epoch P (max (es.g.epoch P) pos.epoch) = es.g.epoch := by
    funext Q
    by_cases hQP : Q = P
    · subst Q; simp [Function.update, Nat.max_eq_left hpos_le]
    · simp [Function.update_of_ne hQP]
  refine
    { valid := hs.valid
      s_eq := by
        rw [hs.s_eq]
        simp only [GameState.accept, GameState.delete, realGS]
        congr 1
        funext Q
        by_cases hQP : Q = P
        · subst Q; simp [Function.update, realVP, realGS, st_v', st_r', hs.s_eq]
        · simp [Function.update_of_ne hQP]
      no_abort := hs.no_abort
      b_eq := hs.b_eq
      sc_b := hs.sc_b
      st_id := fun Q => by
        by_cases hQP : Q = P
        · subst Q; simp [GameState.accept, GameState.delete, Function.update, st_v', hs.st_id]
        · simp [GameState.accept, GameState.delete, Function.update_of_ne hQP, hs.st_id]
      st_tcur := fun Q => by
        simp only [GameState.accept, GameState.delete, hep_eq]
        by_cases hQP : Q = P
        · subst Q; simp [Function.update, st_v', hs.st_tcur]
        · simp [Function.update_of_ne hQP, hs.st_tcur]
      γ_eq := fun Q => by
        simp only [GameState.accept, GameState.delete, hep_eq]
        by_cases hQP : Q = P
        · subst Q; simp [Function.update, st_v', st_r', hs.γ_eq]
        · simp [Function.update_of_ne hQP, hs.γ_eq]
      sc_epoch := fun l htL Q => by
        simp only [GameState.accept, GameState.delete, hep_eq]
        exact hs.sc_epoch l htL Q
      tL_none := hs.tL_none
      tL_some := hs.tL_some
      leaks_ub := fun l hl => by
        simp only [GameState.accept, GameState.delete, hep_eq] at hl ⊢
        exact hs.leaks_ub l hl
      comp_unhealed := fun pos' hpos' => by
        simp only [GameState.accept, GameState.delete, List.mem_filter] at hpos' ⊢
        exact hs.comp_unhealed pos' hpos'.1
      epoch_le := fun Q => by
        simp only [GameState.accept, GameState.delete, hep_eq]
        exact hs.epoch_le Q
      epoch_step_sends := fun Q hstep => by
        simp only [GameState.accept, GameState.delete, hep_eq] at hstep ⊢
        exact hs.epoch_step_sends Q hstep
      trans_inv := fun r hr => by
        simp only [GameState.accept, GameState.delete, hep_eq, List.mem_filter] at hr ⊢
        obtain ⟨h1, h2, h3, h4⟩ := hs.trans_inv r hr.1
        refine ⟨h1, h2, h3, fun heq => ?_⟩
        rw [h4 heq]
        by_cases hQP : r.pos.sender = P
        · rw [hQP]; simp [Function.update, st_v']
        · simp [Function.update_of_ne hQP]
      cache_gt := fun t' ht' => by
        simp only [GameState.accept, GameState.delete, hep_eq] at ht'
        exact hs.cache_gt t' ht'
      cka_eq := fun Q h1 h2 rs => by
        simp only [GameState.accept, GameState.delete, hep_eq] at h1 h2
        have hγQ : ((s.accept P st_r' pos).st Q).γ = (s.st Q).γ := by
          by_cases hQP : Q = P
          · subst Q; simp [GameState.accept, GameState.delete, Function.update, st_r']
          · simp [GameState.accept, GameState.delete, Function.update_of_ne hQP]
        have hγQo : ((s.accept P st_r' pos).st Q.other).γ = (s.st Q.other).γ := by
          by_cases hQP : Q.other = P
          · rw [hQP]; simp [GameState.accept, GameState.delete, Function.update, st_r']
          · simp [GameState.accept, GameState.delete, Function.update_of_ne hQP]
        rw [hγQ, hγQo]
        exact hs.cka_eq Q h1 h2 rs
      cka_step := fun Q h1 => by
        have hγQ : ((s.accept P st_r' pos).st Q).γ = (s.st Q).γ := by
          by_cases hQP : Q = P
          · subst Q; simp [GameState.accept, GameState.delete, Function.update, st_r']
          · simp [GameState.accept, GameState.delete, Function.update_of_ne hQP]
        have hγQo : ((s.accept P st_r' pos).st Q.other).γ = (s.st Q.other).γ := by
          by_cases hQP : Q.other = P
          · rw [hQP]; simp [GameState.accept, GameState.delete, Function.update, st_r']
          · simp [GameState.accept, GameState.delete, Function.update_of_ne hQP]
        rw [hγQ, hγQo]
        simp only [GameState.accept, GameState.delete, hep_eq] at h1 ⊢
        obtain ⟨T_t, I_t, hc, hT, hl, hI, hagr⟩ := hs.cka_step Q h1
        have hT' : (Function.update es.g.st P st_v' Q.other).curCkaMsg = (es.g.st Q.other).curCkaMsg := by
          by_cases hQP : Q.other = P
          · rw [hQP]; simp [Function.update, st_v']
          · simp [Function.update_of_ne hQP]
        rw [hT']
        exact ⟨T_t, I_t, hc, hT, hl, hI, hagr⟩ }

theorem sync9_accept_new (hs : Sync9 cka Δcka tL tStar s es sc) {P : Party}
    (σ' : Sig) (vR' : ℕ → Option RS) {pos : Pos}
    (ht : pos.epoch = es.g.epoch P + 1)
    (heq_other : es.g.epoch P + 1 = es.g.epoch P.other)
    (hnsend : P.sendsIn pos.epoch = false)
    (T_t : T)
    (hagr_step : ∀ rs, cka.AgreesFrom (cka.receive (s.st P).γ T_t).1 (s.st P.other).γ rs) :
    let t := pos.epoch
    let γ_r' := (cka.receive (s.st P).γ T_t).1
    let γ_v' : Option Γ := if isLocal tL Δcka t then some γ_r' else none
    let st_v' : PartyState (Option Γ) T Sig SS RS :=
      { es.g.st P with tcur := t, γ := γ_v', root := σ', vR := vR' }
    let st_r' : PartyState Γ T Sig SS RS :=
      { s.st P with tcur := t, γ := γ_r', root := σ', vR := vR' }
    let sc' : CKA.GameState Γ T :=
      if isLocal tL Δcka (es.g.epoch P) then sc else sc.afterReceive P γ_r'
    Sync9 cka Δcka tL tStar
      (s.accept P st_r' pos)
      { es with g := es.g.accept P st_v' pos }
      sc' := by
  intro t γ_r' γ_v' st_v' st_r' sc'
  have hmax_t : max (es.g.epoch P) pos.epoch = t := by
    dsimp only [t]; omega
  have hep_const : ∀ Q, (es.g.accept P st_v' pos).epoch Q = t := by
    intro Q
    simp only [GameState.accept, GameState.delete, hmax_t]
    by_cases hQP : Q = P
    · subst Q; simp [Function.update]
    · have hQo : Q = P.other := by cases P <;> cases Q <;> first | contradiction | rfl
      subst Q; simp [Function.update_of_ne hQP, t, ← heq_other, ht]
  have hmax_eq : max ((es.g.accept P st_v' pos).epoch .A) ((es.g.accept P st_v' pos).epoch .B) =
      max (es.g.epoch .A) (es.g.epoch .B) := by
    rw [hep_const .A, hep_const .B]
    cases P <;> simp [Party.other, t] at ht heq_other ⊢ <;> omega
  refine
    { valid := hs.valid
      s_eq := by
        simp only [GameState.accept, GameState.delete, realGS, hs.s_eq]
        congr 1
        funext Q
        by_cases hQP : Q = P
        · subst Q
          simp only [Function.update_self, realVP, st_v', st_r', hs.s_eq, realGS, γ_v', sc']
          by_cases hloc1 : isLocal tL Δcka t = true <;>
            by_cases hloc2 : isLocal tL Δcka (es.g.epoch P) = true
          · simp [hloc1, hloc2]
          · simp [hloc1, hloc2]
          · exfalso
            cases tL <;> simp [isLocal, t, ht] at hloc1 hloc2; omega
          · simp [hloc1, hloc2, CKA.GameState.afterReceive]
        · simp only [Function.update_of_ne hQP, sc']
          split_ifs
          · rfl
          · simp [CKA.GameState.afterReceive, Function.update_of_ne hQP, realVP]
      no_abort := hs.no_abort
      b_eq := hs.b_eq
      sc_b := by
        dsimp only [sc']
        split_ifs <;> simp [CKA.GameState.afterReceive, hs.sc_b]
      st_id := fun Q => by
        by_cases hQP : Q = P
        · subst Q; simp [GameState.accept, GameState.delete, Function.update, st_v', hs.st_id]
        · simp [GameState.accept, GameState.delete, Function.update_of_ne hQP, hs.st_id]
      st_tcur := fun Q => by
        rw [hep_const Q]
        by_cases hQP : Q = P
        · subst Q; simp [GameState.accept, GameState.delete, Function.update, st_v']
        · have hQo : Q = P.other := by cases P <;> cases Q <;> first | contradiction | rfl
          subst Q
          simp [GameState.accept, GameState.delete, Function.update_of_ne hQP, hs.st_tcur, t,
            ← heq_other, ht]
      γ_eq := fun Q => by
        rw [hep_const Q]
        by_cases hQP : Q = P
        · subst Q
          simp [GameState.accept, GameState.delete, Function.update, st_v', st_r', γ_v']
        · have hQo : Q = P.other := by cases P <;> cases Q <;> first | contradiction | rfl
          subst Q
          have h_ep : es.g.epoch P.other = t := by dsimp only [t]; omega
          simp [GameState.accept, GameState.delete, Function.update_of_ne hQP, hs.γ_eq, h_ep]
      sc_epoch := fun l htL Q => by
        rw [hep_const Q]
        dsimp only [sc']
        by_cases hloc : isLocal tL Δcka (es.g.epoch P) = true
        · simp only [hloc, ↓reduceIte, hs.sc_epoch l htL Q]
          by_cases hQP : Q = P
          · subst Q
            simp only [isLocal, htL, decide_eq_true_eq] at hloc
            dsimp only [t]; omega
          · have hQo : Q = P.other := by cases P <;> cases Q <;> first | contradiction | rfl
            subst Q; dsimp only [t]; omega
        · simp [hloc]
          simp only [isLocal, htL, decide_eq_true_eq] at hloc
          by_cases hQP : Q = P
          · subst Q
            simp only [CKA.GameState.afterReceive, Function.update_self, hs.sc_epoch l htL P, t, ht]
            omega
          · have hQo : Q = P.other := by cases P <;> cases Q <;> first | contradiction | rfl
            subst Q
            simp only [CKA.GameState.afterReceive, Function.update_of_ne hQP,
              hs.sc_epoch l htL P.other, t, ht, heq_other]
      tL_none := hs.tL_none
      tL_some := hs.tL_some
      leaks_ub := fun l hl => by
        rw [hmax_eq]
        exact hs.leaks_ub l hl
      comp_unhealed := fun pos' hpos' => by
        simp only [GameState.accept, GameState.delete, List.mem_filter] at hpos' ⊢
        exact hs.comp_unhealed pos' hpos'.1
      epoch_le := fun Q => by
        rw [hep_const Q, hep_const Q.other]
        omega
      epoch_step_sends := fun Q hstep => by
        exfalso
        rw [hep_const Q, hep_const Q.other] at hstep
        omega
      trans_inv := fun r hr => by
        simp only [GameState.accept, GameState.delete, List.mem_filter] at hr
        obtain ⟨h1, h2, h3, h4⟩ := hs.trans_inv r hr.1
        rw [hep_const r.pos.sender]
        refine ⟨h1, h2, ?_, ?_⟩
        · by_cases hQP : r.pos.sender = P
          · rw [hQP] at h3; dsimp only [t]; omega
          · have hQo : r.pos.sender = P.other := by
              revert hQP; cases P <;> cases r.pos.sender <;> decide
            rw [hQo] at h3; dsimp only [t]; omega
        · intro heq'
          by_cases hQP : r.pos.sender = P
          · rw [hQP] at h3; dsimp only [t] at heq'; omega
          · have hQo : r.pos.sender = P.other := by
              revert hQP; cases P <;> cases r.pos.sender <;> decide
            simp only [GameState.accept, GameState.delete, Function.update_of_ne hQP]
            apply h4
            rw [hQo]; dsimp only [t] at heq'; omega
      cache_gt := fun t' ht' => by
        rw [hmax_eq] at ht'
        exact hs.cache_gt t' ht'
      cka_eq := fun Q h1 h2 rs => by
        rw [hep_const Q] at h2
        have hQP : Q = P := by
          have hsendP : P.sendsIn (t + 1) = true := by
            rw [sendsIn_succ, hnsend]; rfl
          have h1' := eq_senderOf_of_sendsIn h2
          have h2' := eq_senderOf_of_sendsIn hsendP
          exact h1'.trans h2'.symm
        subst Q
        simp only [GameState.accept, GameState.delete, Function.update_self,
          Function.update_of_ne (Party.other_ne P), st_r']
        exact hagr_step rs
      cka_step := fun Q h1 => by
        exfalso
        rw [hep_const Q, hep_const Q.other] at h1
        omega }

theorem sync9_init (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (hc : cka.Correct) (hvg : lastLeakGuessAdmissible (2 + Δcka) tL tStar = true)
    (kr : KR) (kc : KC) :
    let out := prng.up (prng.init kr) lam
    let γv : PartyState (Option Γ) T Sig SS RS × PartyState (Option Γ) T Sig SS RS :=
      mkParties
        (match tL with | none => some (cka.initA kc) | some _ => none)
        (match tL with | none => some (cka.initB kc) | some _ => none)
        out.1 (fs.initSender out.2) (fs.initReceiver out.2)
    let g₀ : Ctx (Option Γ) T Sig SS RS M E :=
      { st := fun P => match P with | .A => γv.1 | .B => γv.2, b := false }
    Sync9 cka Δcka tL tStar
      (initState (scheme cka prng fs lam) (kr, kc) false)
      { g := g₀, h := {} }
      (CKA.initState cka kc false) := by
  intro out γv g₀
  refine
    { valid := hvg
      s_eq := by
        simp only [initState, scheme, realGS, g₀]
        congr 1
        funext P
        cases P <;> cases tL <;> rfl
      no_abort := rfl
      b_eq := rfl
      sc_b := rfl
      st_id := fun P => by cases P <;> rfl
      st_tcur := fun P => by cases P <;> rfl
      γ_eq := fun P => by
        dsimp only [g₀, γv, mkParties, initState, scheme, initParty]
        cases P <;> cases tL <;> simp [isLocal]
      sc_epoch := fun l htL P => by cases P <;> rfl
      tL_none := fun _ => rfl
      tL_some := fun m hm => by nomatch hm
      leaks_ub := fun l hl => by nomatch hl
      comp_unhealed := fun pos hpos => by nomatch hpos
      epoch_le := fun P => by dsimp [g₀]; omega
      epoch_step_sends := fun P h => by nomatch h
      trans_inv := fun r hr => by nomatch hr
      cache_gt := fun t' _ => rfl
      cka_eq := fun P _ hsend rs => by
        have hP : P = .A := by
          cases P
          · rfl
          · nomatch hsend
        subst P
        exact hc kc rs
      cka_step := fun P h => by nomatch h }

end Sync9

end Sync9

end CryptoGames.SM.Construction.AuthL9

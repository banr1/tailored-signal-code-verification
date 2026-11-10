/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperShiftedFS
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma9
import ProofLib.SepLogic.WP.StateNorm

/-!
# Shifted-Paper Hop 1 at `Δ = 2 + 1`

Proves `lemma9_df_shifted_paper`: for `1 ≤ l` and any `NoBadCoinsDF` adversary `A`,
`forgeGuessedAdvantageShiftedPaper` at `Δ = 2 + 1` is bounded by the real-world CKA branch
`CKA.branch cka 1 (l + 1) false` of `redCKAAuthDFShiftedPaper`.
-/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory OracleComp OracleSpec

namespace CryptoGames.SM.Construction.DeliverForge

open CryptoGames.SM CryptoGames.SM.Engine CryptoGames.SM.Construction
open CryptoGames.SM.Construction.AuthL9 CryptoGames.SM.Construction.DeliverForge.AuthL9DF

section AuthL9ShiftedPaper

variable {KC Γ CCoins T I KR Sig K SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

def Doomed4ShiftedStrong {St Msg C : Type} (l tStar : ℕ) (s : GameState St Msg C) : Prop :=
  1 ≤ l ∧ l < tStar ∧ l - 1 ∉ s.leaks ∧
    l ≤ min (s.epoch .A) (s.epoch .B) ∧ l < max (s.epoch .A) (s.epoch .B)

def DoomedAuthShiftedK4Free {St Msg C : Type} (l tStar : ℕ) (s : GameState St Msg C) : Prop :=
  Doomed1 (some (l - 1)) tStar s ∨ Doomed2 tStar s ∨
    Doomed3 (some (l - 1)) tStar s ∨ Doomed4ShiftedStrong l tStar s

theorem doomed4Shifted_of_doomed4ShiftedStrong {St Msg C : Type} {l tStar : ℕ}
    {s : GameState St Msg C} (h : Doomed4ShiftedStrong l tStar s) : Doomed4Shifted l tStar s := by
  rcases h with ⟨h1, h2, h3, h4, h5⟩
  exact ⟨h1, h2, h3, by omega, by omega, fun _ => by omega⟩

theorem doomedAuthShifted_of_doomedAuthShiftedK4Free {St Msg C : Type} {l tStar : ℕ}
    {s : GameState St Msg C} (h : DoomedAuthShiftedK4Free l tStar s) :
    DoomedAuthShifted l tStar s :=
  h.imp_right (Or.imp_right (Or.imp_right doomed4Shifted_of_doomed4ShiftedStrong))

theorem doomedAuthShiftedK4Free_not_win {St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    (Δ l tStar : ℕ) (s : GameState St Msg C) (hd : DoomedAuthShiftedK4Free l tStar s) :
    (s.win && authLosingConditionsAvoided Δ (some (l - 1)) tStar s) = false :=
  doomedAuthShifted_not_win Δ l tStar s (doomedAuthShifted_of_doomedAuthShiftedK4Free hd)

theorem doomedAuthShiftedK4Free_epMgmt {St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    {qep l tStar : ℕ} {s s₁ : GameState St Msg C} {P : Party} {bad : Bool}
    (hd : DoomedAuthShiftedK4Free l tStar s) (hep : s.epMgmt (2 + 1) qep P bad = some s₁) :
    DoomedAuthShiftedK4Free l tStar s₁ := by
  unfold GameState.epMgmt at hep
  split_ifs at hep with hs hq1 hb hq2
  · injection hep with hep; subst hep
    have hA := update_epoch_ge s.epoch P .A (s.epoch P + 1) (by omega)
    have hB := update_epoch_ge s.epoch P .B (s.epoch P + 1) (by omega)
    rcases hd with h1 | ⟨hw, ⟨m, hm, htm⟩, htr⟩ | h3 | ⟨hl1, hlt, hnl, hmin, hmax⟩
    · exact Or.inl (doomed1_of_leaks_sub h1 fun x hx => by
        simp [GameState.leak, List.mem_cons, hx])
    · refine Or.inr (Or.inl ⟨hw, ⟨maxOpt s.tL (s.epoch P + 1), rfl, ?_⟩, htr⟩)
      exact le_trans htm (le_maxOpt_left hm _)
    · exact Or.inr (Or.inr (Or.inl h3))
    · refine Or.inr (Or.inr (Or.inr ⟨hl1, hlt, ?_, by dsimp only [GameState.leak]; omega,
        by dsimp only [GameState.leak]; omega⟩))
      simp only [GameState.leak, List.mem_cons, not_or]
      refine ⟨?_, hnl⟩
      have hP : l ≤ s.epoch P := by cases P <;> omega
      have := le_maxOpt_right s.tL (s.epoch P + 1)
      omega
  · injection hep with hep; subst hep
    have hA := update_epoch_ge s.epoch P .A (s.epoch P + 1) (by omega)
    have hB := update_epoch_ge s.epoch P .B (s.epoch P + 1) (by omega)
    rcases hd with h1 | h2 | h3 | ⟨hl1, hlt, hnl, hmin, hmax⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr ⟨hl1, hlt, hnl, by dsimp only; omega, by dsimp only; omega⟩))
  · injection hep with hep; subst hep; exact hd

theorem doomedAuthShiftedK4Free_record {St Msg C : Type} {l tStar : ℕ}
    {s : GameState St Msg C} (P : Party) (st' : St) (r : Record Msg C) (isChall : Bool)
    (hr : r.pos.epoch = s.epoch P) (hd : DoomedAuthShiftedK4Free l tStar s) :
    DoomedAuthShiftedK4Free l tStar (s.record (2 + 1) P st' r isChall) := by
  rcases hd with h1 | ⟨hw, ⟨m, hm, htm⟩, htr⟩ | h3 | ⟨hl1, hlt, hnl, hmin, hmax⟩
  · exact Or.inl h1
  · refine Or.inr (Or.inl ⟨hw, ⟨m, hm, htm⟩, ?_⟩)
    intro r' hr' heq
    simp only [GameState.record, List.mem_cons] at hr' ⊢
    rcases hr' with rfl | hr'
    · have hsafe : s.safeCh (2 + 1) P = false := by
        simp only [GameState.safeCh, healedBy, hm, ← hr, heq, decide_eq_false_iff_not]
        omega
      simp [hsafe]
    · have hmem := htr r' hr' heq
      split_ifs <;> simp [hmem]
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr ⟨hl1, hlt, hnl, hmin, hmax⟩))

theorem doomedAuthShiftedK4Free_accept {St Msg C : Type} {l tStar : ℕ}
    {s : GameState St Msg C} (P : Party) (st' : St) (pos : Pos)
    (hd : DoomedAuthShiftedK4Free l tStar s) :
    DoomedAuthShiftedK4Free l tStar (s.accept P st' pos) := by
  have hA := update_epoch_ge s.epoch P .A (max (s.epoch P) pos.epoch) (Nat.le_max_left _ _)
  have hB := update_epoch_ge s.epoch P .B (max (s.epoch P) pos.epoch) (Nat.le_max_left _ _)
  rcases hd with h1 | ⟨hw, ⟨m, hm, htm⟩, htr⟩ | h3 | ⟨hl1, hlt, hnl, hmin, hmax⟩
  · exact Or.inl h1
  · refine Or.inr (Or.inl ⟨hw, ⟨m, hm, htm⟩, ?_⟩)
    intro r hr heq
    simp only [GameState.accept, GameState.delete, List.mem_filter] at hr ⊢
    exact ⟨htr r hr.1 heq, hr.2⟩
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr ⟨hl1, hlt, hnl,
      by dsimp only [GameState.accept, GameState.delete]; omega,
      by dsimp only [GameState.accept, GameState.delete]; omega⟩))

theorem doomed4ShiftedStrong_afterCorrShifted {St Msg C : Type} {l tStar : ℕ}
    {s : GameState St Msg C} (P : Party) (hd : Doomed4ShiftedStrong l tStar s) :
    Doomed4ShiftedStrong l tStar (afterCorrShifted l s P) := by
  rcases hd with ⟨hl1, hlt, hnl, hmin, hmax⟩
  have hnot : ¬(max (s.epoch .A) (s.epoch .B) = l ∧ s.epoch P + 1 ≤ l) := by omega
  rw [afterCorrShifted_eq_afterCorr_of_not l s P hnot]
  refine ⟨hl1, hlt, ?_, hmin, hmax⟩
  intro hm
  simp only [GameState.afterCorr, GameState.leak, List.mem_cons] at hm
  rcases hm with heq | hm
  · have hge := AuthL9.le_maxOpt_right s.tL (max (s.epoch .A) (s.epoch .B))
    omega
  · exact hnl hm

theorem doomedAuthShiftedK4Free_afterCorrShifted {St Msg C : Type}
    [DecidableEq Msg] [DecidableEq C] {l tStar : ℕ}
    {s : GameState St Msg C} (P : Party) (hd : DoomedAuthShiftedK4Free l tStar s) :
    DoomedAuthShiftedK4Free l tStar (afterCorrShifted l s P) := by
  rcases hd with h1 | ⟨hw, ⟨m, hm, htm⟩, htr⟩ | h3 | h4
  · exact Or.inl (doomed1_of_leaks_sub h1 fun x hx => by
      simp [afterCorrShifted, GameState.leak, List.mem_cons, hx])
  · refine Or.inr (Or.inl ⟨hw, ⟨_, rfl, ?_⟩, ?_⟩)
    · exact le_trans htm (le_maxOpt_left hm _)
    · intro r hr heq
      simp only [afterCorrShifted, GameState.leak, List.mem_append] at hr ⊢
      exact Or.inr (htr r hr heq)
  · exact Or.inr (Or.inr (Or.inl (doomed3_of_corrs_sub h3 fun x hx => by
      simp [afterCorrShifted, List.mem_cons, hx])))
  · exact Or.inr (Or.inr (Or.inr (doomed4ShiftedStrong_afterCorrShifted P h4)))

theorem doomedAuthShiftedK4Free_oracleImplShiftedPaper {Key St Msg Coins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (l qep tStar : ℕ)
    (t : (unifSpec + spec St Msg Coins C).Domain)
    {s s' : GameState St Msg C} {u : (unifSpec + spec St Msg Coins C).Range t}
    (hd : DoomedAuthShiftedK4Free l tStar s)
    (hmem : (u, s') ∈ support
      ((((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (GameState St Msg C) ProbComp) +
        oracleImplShiftedPaper sm (2 + 1) l qep (Config.auth tStar)) t).run s)) :
    DoomedAuthShiftedK4Free l tStar s' := by
  rcases t with n | ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
  · dsimp only [QueryImpl.add_apply, QueryImpl.liftTarget, QueryImpl.ofLift] at hmem
    rw [(mem_support_liftProb hmem).2]
    exact hd
  · dsimp only [QueryImpl.add_apply, oracleImplShiftedPaper, transmitImpl] at hmem
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
      cases hep : s.epMgmt (2 + 1) qep P bad with
      | none =>
        rw [hep] at hmem
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
        rw [hmem.2]; exact hd
      | some s₁ =>
        rw [hep] at hmem
        simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
          support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
        rw [hmem.2]
        exact doomedAuthShiftedK4Free_record P _ _ false rfl (doomedAuthShiftedK4Free_epMgmt hd hep)
  · dsimp only [QueryImpl.add_apply, oracleImplShiftedPaper, challImpl, Config.auth] at hmem
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
      cases hep : s.epMgmt (2 + 1) qep P bad <;>
        simp only [hep, Bool.not_false, Bool.or_true, ↓reduceIte, StateT.run_pure,
          support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem <;>
        (rw [hmem.2]; exact hd)
  · dsimp only [QueryImpl.add_apply, oracleImplShiftedPaper, deliverImpl, Config.auth] at hmem
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
          exact doomedAuthShiftedK4Free_accept P st' r.pos hd
  · dsimp only [QueryImpl.add_apply, oracleImplShiftedPaper, injectImpl] at hmem
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
          exact doomedAuthShiftedK4Free_accept P st' ⟨P.other, t', i'⟩ hd
        · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
            support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
          rw [hmem.2]
          simp only [Config.auth, beq_iff_eq] at hfull
          rcases hd with h1 | h2 | h3 | h4
          · exact Or.inl h1
          · exfalso; exact htriv (doomed2_trivial_tStar (by omega) h2 ⟨P.other, t', i'⟩ hfull)
          · exact Or.inr (Or.inr (Or.inl h3))
          · exact Or.inr (Or.inr (Or.inr h4))
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
          rw [hmem.2]; exact hd
  · dsimp only [QueryImpl.add_apply, oracleImplShiftedPaper, corrImplShiftedPaper] at hmem
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    split_ifs at hmem with hcond
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
      rw [hmem.2]; exact hd
    · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
        support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
      rw [hmem.2]
      exact doomedAuthShiftedK4Free_afterCorrShifted P hd

omit [Inhabited E] in
theorem doomedAuthShiftedK4Free_deliverForgeBaseImpl {Key St Msg Coins : Type} [DecidableEq Msg]
    (sm : SMScheme Key St Msg Coins (Header T × E)) (qep l tStar : ℕ)
    (q : Party × (Header T × E) × (Header T × E))
    {s s' : GameState St Msg (Header T × E)} {u : Option (RecvResult Msg)}
    (hd : DoomedAuthShiftedK4Free l tStar s)
    (hmem : (u, s') ∈ support
      ((deliverForgeBaseImpl sm (2 + 1) qep sameHdrScheme (Config.auth tStar) q).run s)) :
    DoomedAuthShiftedK4Free l tStar s' := by
  rcases q with ⟨P, c, c'⟩
  dsimp only [deliverForgeBaseImpl] at hmem
  rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  split_ifs at hmem with hw
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
    rw [hmem.2]; exact hd
  · cases hin : s.inTransit P.other c with
    | none =>
      rw [hin] at hmem
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
      rw [hmem.2]; exact hd
    | some r =>
      rw [hin] at hmem
      dsimp only at hmem
      split_ifs at hmem with hguard
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
        rw [hmem.2]; exact hd
      · cases hrcv : sm.receive (s.st P) c' with
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
            exact doomedAuthShiftedK4Free_accept P st' ⟨P.other, t', i'⟩ hd
          · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
              support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
            rw [hmem.2]
            simp only [Config.auth, beq_iff_eq] at hfull
            rcases hd with h1 | h2 | h3 | h4
            · exact Or.inl h1
            · exfalso; exact htriv (doomed2_trivial_tStar (by omega) h2 ⟨P.other, t', i'⟩ hfull)
            · exact Or.inr (Or.inr (Or.inl h3))
            · exact Or.inr (Or.inr (Or.inr h4))
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
            rw [hmem.2]; exact hd

omit [Inhabited E] in
theorem doomedAuthShiftedK4Free_simulateQ_DF {Key St Msg Coins : Type}
    [DecidableEq Msg] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins (Header T × E)) (l qep tStar : ℕ)
    {α : Type} (oa : AdversaryCompDF St Msg Coins (Header T × E) α) :
    ∀ {s s' : GameState St Msg (Header T × E)} {a : α},
      DoomedAuthShiftedK4Free l tStar s →
      (a, s') ∈ support
        ((simulateQ
          (fullImplBaseDFShiftedPaper sm (2 + 1) l qep sameHdrScheme (Config.auth tStar))
          oa).run s) →
      DoomedAuthShiftedK4Free l tStar s' := by
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
    rcases t with n | (q | qdf)
    · exact ih u (doomedAuthShiftedK4Free_oracleImplShiftedPaper sm l qep tStar (.inl n) hd h₁) h₂
    · exact ih u (doomedAuthShiftedK4Free_oracleImplShiftedPaper sm l qep tStar (.inr q) hd h₁) h₂
    · exact ih u (doomedAuthShiftedK4Free_deliverForgeBaseImpl sm qep l tStar qdf hd h₁) h₂

local notation "ASpecDF" =>
  unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)

def runLDFShiftedPaper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (qep l tStar : ℕ) {α : Type}
    (oa : AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)) : ProbComp Bool :=
  ((simulateQ
    (fullImplBaseDFShiftedPaper (scheme cka prng fs lam) (2 + 1) l qep sameHdrScheme
      (Config.auth tStar))
    oa).run s) >>= fun res => pure (res.2.win && authLosingConditionsAvoided (2 + 1) (some (l - 1)) tStar res.2)

def runRDFShiftedPaper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (qep l tStar : ℕ) {α : Type}
    (oa : AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I))
    (sc : CKA.GameState Γ T) : ProbComp Bool :=
  ((simulateQ
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (CKA.GameState Γ T) ProbComp) +
      CKA.oracleImpl cka 1 (l + 1))
    ((simulateQ
      (implEDFShiftedPaper l (hooksCKAShifted cka prng fs l tStar)
        (2 + 1) qep fs.maxSkip (Config.auth tStar) ⟨true, some (l - 1), tStar⟩)
      oa).run es)).run sc) >>=
    fun res => pure (authOut (2 + 1) ⟨true, some (l - 1), tStar⟩ res.1.2)

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType I]
  [SampleableType K] in
theorem runLDFShiftedPaper_pure (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (qep l tStar : ℕ) {α : Type} (a : α)
    (s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)) :
    runLDFShiftedPaper cka prng fs lam qep l tStar (pure a) s =
      pure (s.win && authLosingConditionsAvoided (2 + 1) (some (l - 1)) tStar s) := by
  simp [runLDFShiftedPaper]

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem runRDFShiftedPaper_pure (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (qep l tStar : ℕ) {α : Type} (a : α)
    (es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I))
    (sc : CKA.GameState Γ T) :
    runRDFShiftedPaper cka prng fs qep l tStar (pure a) es sc =
      pure (authOut (2 + 1) ⟨true, some (l - 1), tStar⟩ es) := by
  simp [runRDFShiftedPaper]

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType I]
  [SampleableType K] in
theorem runLDFShiftedPaper_query_bind (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (qep l tStar : ℕ)
    {α : Type} (t : (ASpecDF).Domain)
    (k : (ASpecDF).Range t →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)) :
    runLDFShiftedPaper cka prng fs lam qep l tStar (query (spec := ASpecDF) t >>= k) s =
      (((fullImplBaseDFShiftedPaper (scheme cka prng fs lam) (2 + 1) l qep sameHdrScheme
        (Config.auth tStar)) t).run s >>=
        fun res => runLDFShiftedPaper cka prng fs lam qep l tStar (k res.1) res.2) := by
  simp [runLDFShiftedPaper, StateT.run_bind]

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem runRDFShiftedPaper_query_bind (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (qep l tStar : ℕ)
    {α : Type} (t : (ASpecDF).Domain)
    (k : (ASpecDF).Range t →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I))
    (sc : CKA.GameState Γ T) :
    runRDFShiftedPaper cka prng fs qep l tStar (query (spec := ASpecDF) t >>= k) es sc =
      (((simulateQ
        ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (CKA.GameState Γ T) ProbComp) +
          CKA.oracleImpl cka 1 (l + 1))
        ((implEDFShiftedPaper l (hooksCKAShifted cka prng fs l tStar)
          (2 + 1) qep fs.maxSkip (Config.auth tStar) ⟨true, some (l - 1), tStar⟩ t).run es)).run sc)
        >>= fun res => runRDFShiftedPaper cka prng fs qep l tStar (k res.1.1) res.1.2 res.2) := by
  simp [runRDFShiftedPaper, StateT.run_bind]

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType I]
  [SampleableType K] in
theorem evalDist_runLDFShiftedPaper_eq_pure_false_of_doomed
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (qep l tStar : ℕ)
    {α : Type} (oa : AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (s : GameState (PartyState Γ T Sig SS RS) M (Header T × E))
    (hdoom : DoomedAuthShiftedK4Free l tStar s) :
    𝒟[runLDFShiftedPaper cka prng fs lam qep l tStar oa s] =
      𝒟[(pure false : ProbComp Bool)] := by
  apply evalDist_bind_eq_pure_false
  rintro ⟨a, s'⟩ hmem
  have hdoom' : DoomedAuthShiftedK4Free l tStar s' :=
    doomedAuthShiftedK4Free_simulateQ_DF (scheme cka prng fs lam) l qep tStar oa hdoom hmem
  rw [doomedAuthShiftedK4Free_not_win (2 + 1) l tStar s' hdoom']

omit [SampleableType CCoins] in
theorem abort_simulateQ_DFShiftedPaper {Γv Sv SSv RSv HS : Type} {ι : Type}
    {tspec : OracleSpec.{0, 0} ι} {S : Type}
    (l : ℕ) (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy)
    (tImpl : QueryImpl tspec (StateT S ProbComp))
    {α : Type} (oa : AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α) :
    ∀ {es es' : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS} {sc sc' : S} {a : α},
      es.abort = true →
      ((a, es'), sc') ∈ support ((simulateQ
        ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT S ProbComp) + tImpl)
        ((simulateQ (implEDFShiftedPaper l hk Δ qep maxSkip cfg π) oa).run es)).run sc) →
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
    rcases t with n | (((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩)
    · dsimp only [implEDFShiftedPaper, coinsE, HAdd.hAdd, Add.add, QueryImpl.add] at h₁
      simp only [StateT.run_lift, simulateQ_bind, QueryImpl.liftTarget,
        simulateQ_pure, StateT.run_bind, StateT.run_pure, MonadAttach.mem_support_bind,
        support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₁
      rcases h₁ with ⟨_, _, ⟨_, rfl⟩, rfl⟩
      exact ih u hab h₂
    all_goals
      dsimp only [implEDFShiftedPaper, transmitE, challE, deliverE, injectE, corrEShiftedPaper,
        deliverForgeE, HAdd.hAdd, Add.add, QueryImpl.add] at h₁
      simp only [hab, Bool.true_or, ↓reduceIte,
        StateT.run_bind, StateT.run_get, pure_bind, StateT.run_pure,
        simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₁
      rw [← h₁.1.2] at hab
      exact ih u hab h₂

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem evalDist_runRDFShiftedPaper_eq_pure_false_of_abort
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (qep l tStar : ℕ)
    {α : Type} (oa : AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I))
    (sc : CKA.GameState Γ T)
    (hab : es.abort = true) :
    𝒟[runRDFShiftedPaper cka prng fs qep l tStar oa es sc] =
      𝒟[(pure false : ProbComp Bool)] := by
  apply evalDist_bind_eq_pure_false
  rintro ⟨⟨a, es'⟩, sc'⟩ hmem
  have hab' : es'.abort = true :=
    abort_simulateQ_DFShiftedPaper l
      (hooksCKAShifted cka prng fs l tStar)
      (2 + 1) qep fs.maxSkip (Config.auth tStar) ⟨true, some (l - 1), tStar⟩
      (CKA.oracleImpl cka 1 (l + 1)) oa hab hmem
  simp [authOut, hab']

theorem doomedShiftedK4Free_of_leakDoom_epMgmt {cka : CKAScheme KC Γ CCoins T I} {l tStar : ℕ}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9Shifted cka l tStar s es sc)
    (hwin : es.g.win = false) {qep : ℕ} {P : Party} {bad : Bool}
    {s₁ : GameState (PartyState (Option Γ) T Sig SS RS) M (Header T × E)}
    (hep : es.g.epMgmt (2 + 1) qep P bad = some s₁)
    (hld : (Policy.mk true (some (l - 1)) tStar).leakDoom es.g s₁ = true)
    (st' : PartyState Γ T Sig SS RS) (m : M) (c : Header T × E) (isChall : Bool) :
    DoomedAuthShiftedK4Free l tStar
      ((AuthL9.realGS sc s₁).record (2 + 1) P st'
        ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, c⟩ isChall) := by
  obtain ⟨hwin1, htr1, hcomp1, htL1, htL2⟩ := hs.baseSync.epMgmt_tL_inv hep
  rw [hwin] at hwin1
  unfold Policy.leakDoom at hld
  rw [Bool.or_eq_true] at hld
  rcases hld with h1 | h2
  · left
    simpa [AuthL9.Doomed1, GameState.record, AuthL9.realGS] using h1
  · right; left
    simp only [Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq] at h2
    rcases h2 with ⟨⟨x, hx, htle⟩, hlt⟩
    cases hstL : s₁.tL with
    | none =>
      rw [htL1 hstL] at hx
      nomatch hx
    | some m' =>
      have hm' : tStar ≤ m' := le_trans htle ((htL2 m' hstL).2 x hx)
      refine ⟨by simp [GameState.record, AuthL9.realGS, hwin1],
        ⟨m', by simp [GameState.record, AuthL9.realGS, hstL], hm'⟩, ?_⟩
      intro r' hr' hrt
      simp only [GameState.record, List.mem_cons] at hr'
      rcases hr' with rfl | hr'
      · dsimp only at hrt
        have hsafe : (AuthL9.realGS sc s₁).safeCh (2 + 1) P = false := by
          simp only [GameState.safeCh, AuthL9.realGS, hstL, hrt, healedBy, decide_eq_false_iff_not]
          omega
        simp [GameState.record, hsafe]
      · exfalso
        simp only [AuthL9.realGS, htr1] at hr'
        have hinv := hs.baseSync.trans_inv r' hr'
        dsimp only at hinv
        have hsnd : r'.pos.sender = Party.senderOf tStar :=
          AuthL9.eq_senderOf_of_sendsIn (by rw [← hrt]; exact hinv.2.1)
        have hle := hinv.2.2.1; rw [hrt, hsnd] at hle; omega

theorem doomed4ShiftedStrong_or_local_of_safeInj_tStar {cka : CKAScheme KC Γ CCoins T I}
    {l tStar : ℕ} {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T} (hs : Sync9Shifted cka l tStar s es sc)
    (hsafe : es.g.safeInj (2 + 1) = true) {P : Party} (ht : es.g.epoch P + 1 = tStar) :
    AuthL9.isLocal (some (l - 1)) 1 (es.g.epoch P) = true ∨ Doomed4ShiftedStrong l tStar s := by
  rcases hs.baseSync.doomed4_or_local_of_safeInj_tStar hsafe ht with
    hloc | ⟨l', hl', hnl, _, _⟩
  · exact Or.inl hloc
  · injection hl' with hl'; subst hl'
    have hvg := hs.baseSync.valid
    simp only [lastLeakGuessAdmissible, healedBy, decide_eq_true_eq] at hvg
    have hle1 := hs.baseSync.epoch_le P; dsimp only at hle1
    have hhl := hs.hl
    refine Or.inr ⟨hs.hl, by omega, hnl, ?_, ?_⟩ <;>
      (rw [hs.baseSync.s_eq]; cases P <;> simp [AuthL9.realGS, Party.other] at hle1 ht ⊢ <;> omega)

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem step_coins_DFShiftedPaper {α : Type} (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (qep l tStar : ℕ) (n : unifSpec.Domain)
    (k : (unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Range (Sum.inl n) →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9Shifted cka l tStar s es sc)
    (ih : ∀ u {s' es' sc'}, Sync9Shifted cka l tStar s' es' sc' →
      𝒟[runLDFShiftedPaper cka prng fs lam qep l tStar (k u) s'] =
        𝒟[runRDFShiftedPaper cka prng fs qep l tStar (k u) es' sc']) :
    𝒟[runLDFShiftedPaper cka prng fs lam qep l tStar
        (query (spec := unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E))
          (Sum.inl n) >>= k) s] =
      𝒟[runRDFShiftedPaper cka prng fs qep l tStar
        (query (spec := unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E))
          (Sum.inl n) >>= k) es sc] := by
  rw [runLDFShiftedPaper_query_bind, runRDFShiftedPaper_query_bind]
  dsimp only [implEDFShiftedPaper, fullImplBaseDFShiftedPaper]
  simp only [QueryImpl.add_apply, coinsE, StateT.run_lift, simulateQ_bind,
    AuthL9.simulateQ_query_eq, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    bind_assoc, pure_bind]
  rw [AuthL9.liftTarget_ofLift_unifSpec_run, AuthL9.liftTarget_ofLift_unifSpec_run]
  simp only [bind_assoc, pure_bind]
  apply evalDist_bind_congr
  intro u
  exact ih u hs

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem step_chall_DFShiftedPaper {α : Type} (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (qep l tStar : ℕ) (P : Party) (m₀ m₁ : M) (r : Option CCoins)
    (k : (unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Range
      (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr (P, m₀, m₁, r))))))) →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9Shifted cka l tStar s es sc)
    (ih : ∀ u {s' es' sc'}, Sync9Shifted cka l tStar s' es' sc' →
      𝒟[runLDFShiftedPaper cka prng fs lam qep l tStar (k u) s'] =
        𝒟[runRDFShiftedPaper cka prng fs qep l tStar (k u) es' sc']) :
    𝒟[runLDFShiftedPaper cka prng fs lam qep l tStar
        (query (spec := unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E))
          (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr (P, m₀, m₁, r))))))) >>= k) s] =
      𝒟[runRDFShiftedPaper cka prng fs qep l tStar
        (query (spec := unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E))
          (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr (P, m₀, m₁, r))))))) >>= k)
          es sc] := by
  rw [runLDFShiftedPaper_query_bind, runRDFShiftedPaper_query_bind]
  dsimp only [QueryImpl.add_apply, fullImplBaseDFShiftedPaper, oracleImplBaseDFShiftedPaper,
    oracleImplShiftedPaper, implEDFShiftedPaper, challImpl, challE, Config.auth]
  have habort : es.abort = false := hs.baseSync.no_abort
  have hwin : s.win = es.g.win := by rw [hs.baseSync.s_eq]; rfl
  simp only [habort, Bool.false_or, hwin, StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hw : es.g.win = true
  · simp [hw, ih none hs]
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.or_true]
    cases r with
    | none =>
      simp only [samIfNec, Option.isSome, StateT.run_monadLift, monadLift_self,
        StateT.run_bind, bind_assoc, pure_bind]
      cases s.epMgmt (2 + 1) qep P false <;> cases es.g.epMgmt (2 + 1) qep P false <;>
        simp [OracleComp.evalDist_bind_const, ih none hs]
    | some c =>
      simp only [samIfNec, Option.isSome, StateT.run_monadLift, monadLift_self,
        StateT.run_bind, pure_bind]
      cases s.epMgmt (2 + 1) qep P true <;> cases es.g.epMgmt (2 + 1) qep P true <;>
        simp [ih none hs]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem doomedShiftedK4Free_of_corr_doom {cka : CKAScheme KC Γ CCoins T I} {l tStar : ℕ}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9Shifted cka l tStar s es sc)
    (hwin : es.g.win = false) {P : Party}
    (hd : ((Policy.mk true (some (l - 1)) tStar).leakDoom es.g (afterCorrShifted l es.g P) ||
      (Policy.mk true (some (l - 1)) tStar).corrDoom es.g P) = true) :
    DoomedAuthShiftedK4Free l tStar (afterCorrShifted l s P) := by
  rw [Bool.or_eq_true] at hd
  rcases hd with hld | hcd
  · unfold Policy.leakDoom at hld
    rw [Bool.or_eq_true] at hld
    rcases hld with h1 | h2
    · left
      rw [hs.baseSync.s_eq]
      simpa [AuthL9.Doomed1, afterCorrShifted, GameState.leak, AuthL9.realGS] using h1
    · right; left
      simp only [Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq] at h2
      rcases h2 with ⟨⟨x, hx, htle⟩, hlt⟩
      rw [hs.baseSync.s_eq]
      let e_leak := if max (es.g.epoch .A) (es.g.epoch .B) = l ∧ es.g.epoch P + 1 ≤ l
        then l - 1 else max (es.g.epoch .A) (es.g.epoch .B)
      let m' := maxOpt es.g.tL e_leak
      have hm' : tStar ≤ m' := by
        simp only [afterCorrShifted, GameState.leak, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact htle
        · cases hstL : es.g.tL with
          | none =>
            rw [hs.baseSync.tL_none hstL] at hx
            nomatch hx
          | some m₀ =>
            have hle := (hs.baseSync.tL_some m₀ hstL).2 x hx
            simp only [m', maxOpt, hstL]; omega
      refine ⟨by simp [afterCorrShifted, GameState.leak, AuthL9.realGS, hwin],
        ⟨m', by simp [afterCorrShifted, GameState.leak, AuthL9.realGS, m', e_leak], hm'⟩, ?_⟩
      intro r' hr' hrt
      simp only [afterCorrShifted, GameState.leak, AuthL9.realGS] at hr'
      exfalso
      have hinv := hs.baseSync.trans_inv r' hr'
      dsimp only at hinv
      have hsnd : r'.pos.sender = Party.senderOf tStar := by
        apply AuthL9.eq_senderOf_of_sendsIn
        rw [← hrt]; exact hinv.2.1
      have hle := hinv.2.2.1
      rw [hrt, hsnd] at hle
      omega
  · right; right; left
    rw [hs.baseSync.s_eq]
    unfold AuthL9.Doomed3
    simp only [afterCorrShifted, GameState.leak, AuthL9.realGS, List.any_cons, Bool.or_eq_true]
    left
    simpa [Policy.corrDoom] using hcd

omit [SampleableType KR] [SampleableType K] in
theorem step_corr_DFShiftedPaper {α : Type} (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (qep l tStar : ℕ) (P : Party)
    (k : (unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Range
      (Sum.inr (Sum.inl (Sum.inr P))) →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9Shifted cka l tStar s es sc)
    (ih : ∀ u {s' es' sc'}, Sync9Shifted cka l tStar s' es' sc' →
      𝒟[runLDFShiftedPaper cka prng fs lam qep l tStar (k u) s'] =
        𝒟[runRDFShiftedPaper cka prng fs qep l tStar (k u) es' sc']) :
    𝒟[runLDFShiftedPaper cka prng fs lam qep l tStar
        (query (spec := unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E))
          (Sum.inr (Sum.inl (Sum.inr P))) >>= k) s] =
      𝒟[runRDFShiftedPaper cka prng fs qep l tStar
        (query (spec := unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E))
          (Sum.inr (Sum.inl (Sum.inr P))) >>= k) es sc] := by
  rw [runLDFShiftedPaper_query_bind, runRDFShiftedPaper_query_bind]
  dsimp only [QueryImpl.add_apply, fullImplBaseDFShiftedPaper, oracleImplBaseDFShiftedPaper,
    oracleImplShiftedPaper, implEDFShiftedPaper, corrImplShiftedPaper, corrEShiftedPaper]
  have habort : es.abort = false := hs.baseSync.no_abort
  have hwin : s.win = es.g.win := by rw [hs.baseSync.s_eq]; rfl
  have hca : s.corrAllowedPaper P = es.g.corrAllowedPaper P := by
    rw [hs.baseSync.s_eq]; rfl
  simp only [habort, Bool.false_or, hwin, hca, StateT.run_bind, StateT.run_get,
    pure_bind]
  by_cases hguard : (es.g.win || !es.g.corrAllowedPaper P) = true
  · simp [hguard, ih none hs]
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte]
    have hwin_f : es.g.win = false := by
      cases hw : es.g.win
      · rfl
      · simp [hw] at hguard
    by_cases hd :
        ((Policy.mk true (some (l - 1)) tStar).leakDoom es.g (afterCorrShifted l es.g P) ||
        (Policy.mk true (some (l - 1)) tStar).corrDoom es.g P) = true
    · simp only [hd, ↓reduceIte, abortE]
      have hdoom : DoomedAuthShiftedK4Free l tStar (afterCorrShifted l s P) :=
        doomedShiftedK4Free_of_corr_doom hs hwin_f hd
      have hL := evalDist_runLDFShiftedPaper_eq_pure_false_of_doomed cka prng fs lam qep l tStar
        (k (some (s.st P))) (afterCorrShifted l s P) hdoom
      have hR := evalDist_runRDFShiftedPaper_eq_pure_false_of_abort cka prng fs qep l tStar
        (k none) { es with abort := true } sc rfl
      simpa using hL.trans hR.symm
    · simp only [hd, Bool.false_eq_true, ↓reduceIte]
      have hld : (Policy.mk true (some (l - 1)) tStar).leakDoom es.g
          (afterCorrShifted l es.g P) = false := by
        cases h : (Policy.mk true (some (l - 1)) tStar).leakDoom es.g (afterCorrShifted l es.g P)
        · rfl
        · simp [h] at hd
      have hcd : (Policy.mk true (some (l - 1)) tStar).corrDoom es.g P = false := by
        cases h : (Policy.mk true (some (l - 1)) tStar).corrDoom es.g P
        · rfl
        · simp [h] at hd
      have hγ := hs.baseSync.γ_eq P
      dsimp only at hγ
      have hst_eq : realParty (es.g.st P) (s.st P).γ (es.g.st P).root (es.g.st P).vS
          (es.g.st P).vR = s.st P := by
        rw [hs.baseSync.s_eq]; rfl
      by_cases hloc : AuthL9.isLocal (some (l - 1)) 1 (es.g.epoch P) = true
      · simp only [hloc, ↓reduceIte] at hγ
        simp only [hooksCKAShifted, hγ, pure_bind, hst_eq, liftH_run, StateT.run_bind,
          StateT.run_modify, StateT.run_set, StateT.run_pure, simulateQ_pure]
        exact ih (some (s.st P)) (sync9Shifted_corr hs P)
      · simp only [hloc, Bool.false_eq_true, ↓reduceIte] at hγ
        have hhl := hs.hl
        have hloc' : es.g.epoch P < (l - 1) + 2 + 1 := by
          simpa [AuthL9.isLocal] using hloc
        have htcur := hs.baseSync.st_tcur P
        dsimp only at htcur
        have hle_ep : es.g.epoch P + 1 ≤ l := by
          by_contra hnot
          have hafter : afterCorrShifted l es.g P = es.g.afterCorr P :=
            afterCorrShifted_eq_afterCorr_of_not l es.g P (fun ⟨_, h⟩ => hnot h)
          rw [hafter] at hld
          have hall := hs.baseSync.allowCorr_of_corr rfl hloc' hld hcd
          have hscP := hs.baseSync.sc_epoch (l - 1) rfl P
          dsimp only at hscP
          unfold CKA.GameState.allowCorr at hall
          simp only [decide_eq_true_eq] at hall
          have hP_le : sc.epoch P ≤ max (sc.epoch .A) (sc.epoch .B) := by
            cases P <;> simp
          omega
        have hle_tcur : (es.g.st P).tcur + 1 ≤ l := by rw [htcur]; exact hle_ep
        have hpre := hs.γPre_eq P hle_ep
        simp only [hooksCKAShifted, hγ, hle_tcur, ↓reduceIte, hpre, liftH_run,
          StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, hst_eq,
          StateT.run_modify, StateT.run_set, simulateQ_pure]
        exact ih (some (s.st P)) (sync9Shifted_corr hs P)

theorem step_deliver_DFShiftedPaper {α : Type} (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (qep l tStar : ℕ) (P : Party) (c : Header T × E)
    (k : (unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Range
      (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr (P, c)))))) →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9Shifted cka l tStar s es sc)
    (ih : ∀ u {s' es' sc'}, Sync9Shifted cka l tStar s' es' sc' →
      𝒟[runLDFShiftedPaper cka prng fs lam qep l tStar (k u) s'] =
        𝒟[runRDFShiftedPaper cka prng fs qep l tStar (k u) es' sc']) :
    𝒟[runLDFShiftedPaper cka prng fs lam qep l tStar
        (query (spec := unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E))
          (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr (P, c)))))) >>= k) s] =
      𝒟[runRDFShiftedPaper cka prng fs qep l tStar
        (query (spec := unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E))
          (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr (P, c)))))) >>= k) es sc] := by
  rw [runLDFShiftedPaper_query_bind, runRDFShiftedPaper_query_bind]
  dsimp only [QueryImpl.add_apply, fullImplBaseDFShiftedPaper, oracleImplBaseDFShiftedPaper,
    oracleImplShiftedPaper, implEDFShiftedPaper, deliverImpl, deliverE, Config.auth]
  have habort : es.abort = false := hs.baseSync.no_abort
  have hwin : s.win = es.g.win := by rw [hs.baseSync.s_eq]; rfl
  have hin_eq : s.inTransit P.other c = es.g.inTransit P.other c := by rw [hs.baseSync.s_eq]; rfl
  have hch_eq : s.chall = es.g.chall := by rw [hs.baseSync.s_eq]; rfl
  simp only [habort, Bool.false_or, hwin, hin_eq, StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hw : es.g.win = true
  · simp [hw, ih none hs]
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, Bool.false_and]
    cases hin : es.g.inTransit P.other c with
    | none => simp [ih none hs]
    | some r =>
      simp only []
      obtain ⟨hmem, hsnd, hct⟩ := AuthL9.mem_trans_of_inTransit hin
      obtain ⟨ht_ep, hsnd_sends, hle_snd, hTcur⟩ := hs.baseSync.trans_inv r hmem
      dsimp only at ht_ep hsnd_sends hle_snd hTcur
      have hpos_c : r.pos.epoch = c.1.1 := by rw [← hct, ht_ep]
      have hnsend : P.sendsIn c.1.1 = false := by
        have h1 : P.other.sendsIn c.1.1 = true := by
          rw [← hpos_c, ← hsnd]; exact hsnd_sends
        rw [AuthL9.sendsIn_other, Bool.not_eq_true'] at h1
        exact h1
      have hle_other : c.1.1 ≤ es.g.epoch P.other := by
        rw [← hpos_c, ← hsnd]; exact hle_snd
      have hle_P1 : c.1.1 ≤ es.g.epoch P + 1 := by
        have hle2 := hs.baseSync.epoch_le P.other
        dsimp only at hle2
        rw [Party.other_other] at hle2
        omega
      by_cases hstep : c.1.1 = es.g.epoch P + 1
      · have heq_other : es.g.epoch P + 1 = es.g.epoch P.other :=
          hs.baseSync.epoch_eq_of_deliver_step hmem hsnd (by rw [hct]; exact hstep)
        obtain ⟨T_t, I_t, hcache, hT_other, hl_msg, hI, hagr⟩ := hs.baseSync.cka_step P heq_other
        dsimp only at hcache hT_other hl_msg hI hagr
        have hcT : c.1.2 = some T_t := by
          rw [← hct, hTcur (by rw [hsnd]; omega), hsnd, hT_other]
        have hcache' : es.h.base.cache c.1.1 = some (T_t, I_t) := by rwa [hstep, heq_other]
        obtain ⟨hrcvL, hrcvR⟩ :=
          AuthL9.vRecv_new_honest cka prng fs 1 (some (l - 1)) tStar (rec := some r)
            hs.baseSync hnsend hstep hcT hcache' hI
        dsimp only at hrcvL hrcvR
        dsimp only [scheme]
        rw [hrcvL, StateT.run_bind, vRecv_hooksCKAShifted_run, hrcvR]
        simp only [pure_bind]
        cases hfs : fs.receive (fs.initReceiver (prng.up (es.g.st P).root I_t).2) c.1 c.2 with
        | none =>
          simp [ih (some .rejected) hs]
        | some val =>
          rcases val with ⟨v', i', m'⟩
          have hpos_ep : r.pos.epoch = es.g.epoch P + 1 := by omega
          have hnsend_pos : P.sendsIn r.pos.epoch = false := by rwa [hpos_c]
          have hcom := commitE_new_shifted cka prng fs (pos := r.pos)
            (prng.up (es.g.st P).root I_t).1
            (Function.update (es.g.st P).vR c.1.1 (some v'))
            hs hpos_ep heq_other T_t (hl_msg (l - 1) rfl)
          have hsync := sync9Shifted_accept_new hs (pos := r.pos)
            (prng.up (es.g.st P).root I_t).1
            (Function.update (es.g.st P).vR c.1.1 (some v'))
            hpos_ep heq_other hnsend_pos T_t hagr
          dsimp only at hcom hsync
          rw [hpos_c] at hcom hsync
          simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
            simulateQ_bind, hcom, StateT.run_modify, simulateQ_pure, hch_eq]
          exact ih _ hsync
      · have hle_P : c.1.1 ≤ es.g.epoch P := by omega
        obtain ⟨hrcvL, hrcvR⟩ :=
          AuthL9.vRecv_same_epoch cka prng fs 1 (some (l - 1)) tStar (rec := some r)
            hs.baseSync hnsend hle_P
        dsimp only at hrcvL hrcvR
        dsimp only [scheme]
        rw [hrcvL, StateT.run_bind, vRecv_hooksCKAShifted_run, hrcvR]
        simp only [pure_bind]
        cases hv : (es.g.st P).vR c.1.1 with
        | none =>
          simp [ih (some .rejected) hs]
        | some v =>
          simp only []
          cases hfs : fs.receive v c.1 c.2 with
          | none =>
            simp [ih (some .rejected) hs]
          | some val =>
            rcases val with ⟨v', i', m'⟩
            have hpos_le : r.pos.epoch ≤ es.g.epoch P := by omega
            have hcom := commitE_same_shifted cka prng fs l tStar
              (P := P)
              (new := { es.g.st P with vR := Function.update (es.g.st P).vR c.1.1 (some v') })
              (pos := r.pos) (es := es) (sc := sc) rfl
            have hsync := sync9Shifted_accept_same hs
              (Function.update (es.g.st P).vR c.1.1 (some v')) hpos_le
            simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
              simulateQ_bind, hcom, StateT.run_modify, simulateQ_pure, hch_eq]
            exact ih _ hsync

theorem step_inject_DFShiftedPaper {α : Type} (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (qep l tStar : ℕ) (P : Party) (c : Header T × E)
    (k : (unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Range
      (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9Shifted cka l tStar s es sc)
    (ih : ∀ u {s' es' sc'}, Sync9Shifted cka l tStar s' es' sc' →
      𝒟[runLDFShiftedPaper cka prng fs lam qep l tStar (k u) s'] =
        𝒟[runRDFShiftedPaper cka prng fs qep l tStar (k u) es' sc']) :
    𝒟[runLDFShiftedPaper cka prng fs lam qep l tStar
        (query (spec := unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E))
          (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) >>= k) s] =
      𝒟[runRDFShiftedPaper cka prng fs qep l tStar
        (query (spec := unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E))
          (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) >>= k) es sc] := by
  rw [runLDFShiftedPaper_query_bind, runRDFShiftedPaper_query_bind]
  dsimp only [QueryImpl.add_apply, fullImplBaseDFShiftedPaper, oracleImplBaseDFShiftedPaper,
    oracleImplShiftedPaper, implEDFShiftedPaper, injectImpl, injectE, Config.auth]
  have habort : es.abort = false := hs.baseSync.no_abort
  have hwin : s.win = es.g.win := by rw [hs.baseSync.s_eq]; rfl
  have hin_eq : s.inTransit P.other c = es.g.inTransit P.other c := by rw [hs.baseSync.s_eq]; rfl
  have hsafe_eq : s.safeInj (2 + 1) = es.g.safeInj (2 + 1) := by rw [hs.baseSync.s_eq]; rfl
  have htriv_eq : ∀ pos, s.trivial (2 + 1) pos = es.g.trivial (2 + 1) pos :=
    fun pos => by rw [hs.baseSync.s_eq]; rfl
  simp only [habort, Bool.false_or, hwin, hin_eq, hsafe_eq,
    StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hcond :
      (es.g.win || (es.g.inTransit P.other c).isSome || !es.g.safeInj (2 + 1)) = true
  · simp [hcond, ih none hs]
  · simp only [hcond, Bool.false_eq_true, ↓reduceIte]
    have hsafe : es.g.safeInj (2 + 1) = true := by
      cases h : es.g.safeInj (2 + 1)
      · simp [h] at hcond
      · rfl
    by_cases hguard : (P.sendsIn c.1.1 || decide (es.g.epoch P + 1 < c.1.1)) = true
    · obtain ⟨hrcvL, hrcvR⟩ :=
        AuthL9.vRecv_guard_true cka prng fs 1 (some (l - 1)) tStar (rec := none) hs.baseSync hguard
      dsimp only at hrcvL hrcvR
      dsimp only [scheme]
      rw [hrcvL, StateT.run_bind, vRecv_hooksCKAShifted_run, hrcvR]
      simp [ih (some .rejected) hs]
    · have hnsend : P.sendsIn c.1.1 = false := by
        cases h : P.sendsIn c.1.1
        · rfl
        · simp [h] at hguard
      have hle_P1 : c.1.1 ≤ es.g.epoch P + 1 := by
        simp [hnsend] at hguard
        omega
      by_cases hstep : c.1.1 = es.g.epoch P + 1
      · have htriv_f : ∀ i', es.g.trivial (2 + 1) ⟨P.other, c.1.1, i'⟩ = false := by
          intro i'
          exact hs.baseSync.trivial_false_of_safeInj (P := P) hsafe (by dsimp; omega)
        cases hc2 : c.1.2 with
        | none =>
          obtain ⟨hrcvL, hrcvR⟩ :=
            AuthL9.vRecv_new_none cka prng fs 1 (some (l - 1)) tStar (rec := none)
              hs.baseSync hnsend hstep hc2
          dsimp only at hrcvL hrcvR
          dsimp only [scheme]
          rw [hrcvL, StateT.run_bind, vRecv_hooksCKAShifted_run, hrcvR]
          simp [ih (some .rejected) hs]
        | some Tn =>
          by_cases hhon_ex : ∃ I_t, es.h.base.cache c.1.1 = some (Tn, I_t)
          · rcases hhon_ex with ⟨I_t, hcache'⟩
            have hle_max : c.1.1 ≤ max (es.g.epoch .A) (es.g.epoch .B) := by
              by_contra hgt
              have hnone := hs.baseSync.cache_gt c.1.1 (by dsimp; omega)
              dsimp only at hnone
              rw [hnone] at hcache'
              nomatch hcache'
            have heq_other : es.g.epoch P + 1 = es.g.epoch P.other := by
              have hle2 := hs.baseSync.epoch_le P.other
              dsimp only at hle2
              rw [Party.other_other] at hle2
              cases P <;> simp [Party.other] at hle_max hstep hle2 ⊢ <;> omega
            obtain ⟨T_t, I_t', hcache_step, _, _, hI, _⟩ := hs.baseSync.cka_step P heq_other
            dsimp only at hcache_step hI
            rw [← heq_other, ← hstep, hcache'] at hcache_step
            injection hcache_step with hpair
            injection hpair with hT_eq hI_eq
            subst hT_eq hI_eq
            obtain ⟨hrcvL, hrcvR⟩ :=
              AuthL9.vRecv_new_honest cka prng fs 1 (some (l - 1)) tStar (rec := none)
                hs.baseSync hnsend hstep hc2 hcache' hI
            dsimp only at hrcvL hrcvR
            dsimp only [scheme]
            rw [hrcvL, StateT.run_bind, vRecv_hooksCKAShifted_run, hrcvR]
            simp only [pure_bind]
            cases hfs : fs.receive (fs.initReceiver (prng.up (es.g.st P).root I_t).2) c.1 c.2 with
            | none =>
              simp [ih (some .rejected) hs]
            | some val =>
              rcases val with ⟨v', i', m'⟩
              simp only [htriv_eq, htriv_f, Bool.false_eq_true, ↓reduceIte]
              by_cases hqep : qep + 1 < c.1.1
              · simp [hqep, ih (some .rejected) hs]
              · simp only [hqep, ↓reduceIte]
                by_cases hfull : (c.1.1 == tStar) = true
                · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_set,
                    StateT.run_modify, pure_bind, StateT.run_pure, simulateQ_pure]
                  exact ih (some .rejected) (sync9Shifted_win hs true)
                · simp [hfull, ih (some .rejected) hs]
          · have hhon : ∀ Tc Ik, es.h.base.cache c.1.1 = some (Tc, Ik) → Tc ≠ Tn := by
              intro Tc Ik hc heq
              subst heq
              exact hhon_ex ⟨Ik, hc⟩
            by_cases htStar : c.1.1 = tStar
            · by_cases hloc : AuthL9.isLocal (some (l - 1)) 1 (es.g.epoch P) = true
              · obtain ⟨hrcvL, hrcvR⟩ :=
                  AuthL9.vRecv_new_dishonest_tStar_local cka prng fs 1 (some (l - 1)) tStar
                    (rec := none) hs.baseSync hnsend hstep hc2 hhon htStar hloc
                dsimp only at hrcvL hrcvR
                dsimp only [scheme]
                rw [hrcvL, StateT.run_bind, vRecv_hooksCKAShifted_run, hrcvR]
                simp only [pure_bind]
                cases hfs : fs.receive
                    (fs.initReceiver (prng.up (es.g.st P).root (cka.receive (s.st P).γ Tn).2).2)
                    c.1 c.2 with
                | none =>
                  simp [ih (some .rejected) hs]
                | some val =>
                  rcases val with ⟨v', i', m'⟩
                  simp only [htriv_eq, htriv_f, Bool.false_eq_true, ↓reduceIte]
                  by_cases hqep : qep + 1 < c.1.1
                  · simp [hqep, ih (some .rejected) hs]
                  · have hfull : (c.1.1 == tStar) = true := beq_iff_eq.mpr htStar
                    simp only [hqep, ↓reduceIte, hfull, StateT.run_bind,
                      StateT.run_set, StateT.run_modify, pure_bind, StateT.run_pure,
                      simulateQ_pure]
                    exact ih (some .rejected) (sync9Shifted_win hs true)
              · have hloc_f : AuthL9.isLocal (some (l - 1)) 1 (es.g.epoch P) = false :=
                  Bool.eq_false_iff.mpr hloc
                have hd4 : Doomed4ShiftedStrong l tStar s := by
                  rcases doomed4ShiftedStrong_or_local_of_safeInj_tStar hs hsafe (P := P) (by omega)
                    with h | hd4
                  · exact False.elim (hloc h)
                  · exact hd4
                have hrcvR :=
                  AuthL9.vRecv_new_dishonest_tStar_nonlocal cka prng fs 1 (some (l - 1)) tStar
                    (rec := none) hs.baseSync hnsend hstep hc2 hhon htStar hloc_f
                dsimp only at hrcvR
                rw [StateT.run_bind, vRecv_hooksCKAShifted_run, hrcvR]
                simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify,
                  StateT.run_pure, simulateQ_pure]
                have hR : 𝒟[runRDFShiftedPaper cka prng fs qep l tStar (k none)
                    { es with abort := true } sc] = 𝒟[(pure false : ProbComp Bool)] :=
                  evalDist_runRDFShiftedPaper_eq_pure_false_of_abort cka prng fs qep l tStar
                    (k none) { es with abort := true } sc rfl
                have hdoom : DoomedAuthShiftedK4Free l tStar s := Or.inr (Or.inr (Or.inr hd4))
                have hrun : 𝒟[runLDFShiftedPaper cka prng fs lam qep l tStar
                    (query (spec := ASpecDF)
                      (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) >>= k) s] =
                    𝒟[(pure false : ProbComp Bool)] :=
                  evalDist_runLDFShiftedPaper_eq_pure_false_of_doomed cka prng fs lam qep l tStar
                    (query (spec := ASpecDF)
                      (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) >>= k) s hdoom
                rw [runLDFShiftedPaper_query_bind] at hrun
                dsimp only [QueryImpl.add_apply, fullImplBaseDFShiftedPaper,
                  oracleImplBaseDFShiftedPaper, oracleImplShiftedPaper, injectImpl,
                  Config.auth] at hrun
                simp only [hwin, hin_eq, hsafe_eq, StateT.run_bind, StateT.run_get, pure_bind,
                  hcond, Bool.false_eq_true, ↓reduceIte] at hrun
                exact hrun.trans hR.symm
            · have hrcvR :=
                AuthL9.vRecv_new_dishonest_ne cka prng fs 1 (some (l - 1)) tStar (rec := none)
                  hs.baseSync hnsend hstep hc2 hhon htStar
              dsimp only at hrcvR
              rw [StateT.run_bind, vRecv_hooksCKAShifted_run, hrcvR]
              simp only [pure_bind, StateT.run_pure, simulateQ_pure]
              dsimp only [scheme]
              cases hrcvL : receive cka prng fs (s.st P) c with
              | none =>
                simp [ih (some .rejected) hs]
              | some res =>
                rcases res with ⟨st', t', i', m'⟩
                have ht' : t' = c.1.1 := AuthL9.receive_t_eq cka prng fs hrcvL
                subst ht'
                have hfull : (c.1.1 == tStar) = false := beq_false_of_ne htStar
                simp only [htriv_eq, htriv_f, hfull, Bool.false_eq_true, ↓reduceIte]
                by_cases hqep : qep + 1 < c.1.1 <;> simp [hqep, ih (some .rejected) hs]
      · have hle_P : c.1.1 ≤ es.g.epoch P := by omega
        obtain ⟨hrcvL, hrcvR⟩ :=
          AuthL9.vRecv_same_epoch cka prng fs 1 (some (l - 1)) tStar (rec := none)
            hs.baseSync hnsend hle_P
        dsimp only at hrcvL hrcvR
        dsimp only [scheme]
        rw [hrcvL, StateT.run_bind, vRecv_hooksCKAShifted_run, hrcvR]
        simp only [pure_bind]
        cases hv : (es.g.st P).vR c.1.1 with
        | none =>
          simp [ih (some .rejected) hs]
        | some v =>
          simp only []
          cases hfs : fs.receive v c.1 c.2 with
          | none =>
            simp [ih (some .rejected) hs]
          | some val =>
            rcases val with ⟨v', i', m'⟩
            simp only []
            by_cases hqep : qep + 1 < c.1.1
            · simp [hqep, ih (some .rejected) hs]
            · simp only [hqep, ↓reduceIte, htriv_eq]
              by_cases htriv : es.g.trivial (2 + 1) ⟨P.other, c.1.1, i'⟩ = true
              · have hcom := commitE_same_shifted cka prng fs l tStar
                  (P := P)
                  (new := { es.g.st P with vR := Function.update (es.g.st P).vR c.1.1 (some v') })
                  (pos := ⟨P.other, c.1.1, i'⟩) (es := es) (sc := sc) rfl
                have hsync := sync9Shifted_accept_same hs
                  (Function.update (es.g.st P).vR c.1.1 (some v'))
                  (pos := ⟨P.other, c.1.1, i'⟩) hle_P
                simp only [htriv, ↓reduceIte, StateT.run_bind, StateT.run_set, pure_bind,
                  StateT.run_pure, simulateQ_bind, hcom, StateT.run_modify,
                  simulateQ_pure]
                exact ih _ hsync
              · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
                by_cases hfull : (c.1.1 == tStar) = true
                · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_set,
                    StateT.run_modify, pure_bind, StateT.run_pure, simulateQ_pure]
                  exact ih (some .rejected) (sync9Shifted_win hs true)
                · simp [hfull, ih (some .rejected) hs]

theorem step_transmit_DFShiftedPaper {α : Type} (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (qep l tStar : ℕ) (P : Party) (m : M)
    (k : (unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Range
      (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (P, m, none))))))) →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9Shifted cka l tStar s es sc)
    (ih : ∀ u {s' es' sc'}, Sync9Shifted cka l tStar s' es' sc' →
      𝒟[runLDFShiftedPaper cka prng fs lam qep l tStar (k u) s'] =
        𝒟[runRDFShiftedPaper cka prng fs qep l tStar (k u) es' sc']) :
    𝒟[runLDFShiftedPaper cka prng fs lam qep l tStar
        (query (spec := unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E))
          (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (P, m, none))))))) >>= k) s] =
      𝒟[runRDFShiftedPaper cka prng fs qep l tStar
        (query (spec := unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E))
          (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (P, m, none))))))) >>= k)
          es sc] := by
  rw [runLDFShiftedPaper_query_bind, runRDFShiftedPaper_query_bind]
  dsimp only [QueryImpl.add_apply, fullImplBaseDFShiftedPaper, oracleImplBaseDFShiftedPaper,
    oracleImplShiftedPaper, implEDFShiftedPaper]
  have habort : es.abort = false := hs.baseSync.no_abort
  by_cases hw : es.g.win = true
  · have hwin : s.win = true := by rw [hs.baseSync.s_eq]; exact hw
    dsimp only [transmitImpl, transmitE]
    simp [habort, hw, hwin, ih none hs]
  · have hw_f : es.g.win = false := Bool.eq_false_iff.mpr hw
    have htr := AuthL9.transmitImpl_run_eq cka prng fs lam 1 qep (some (l - 1)) tStar
      (P := P) (m := m) (r := none) hs.baseSync hw_f
    dsimp only at htr
    rw [htr]
    dsimp only [transmitE]
    simp only [habort, hw_f, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, StateT.run_get, pure_bind, bind_assoc, Option.isSome_none]
    cases hep : es.g.epMgmt (2 + 1) qep P false with
    | none =>
      simp only [pure_bind, StateT.run_pure, simulateQ_pure, OracleComp.evalDist_bind_const]
      exact ih none hs
    | some s₁ =>
      have hs₁_st : s₁.st = es.g.st := by
        unfold GameState.epMgmt at hep
        split_ifs at hep <;> (injection hep with hep; subst hep; simp [GameState.leak])
      simp only []
      by_cases hld : (Policy.mk true (some (l - 1)) tStar).leakDoom es.g s₁ = true
      · simp only [hld, ↓reduceIte, abortE, StateT.run_bind, StateT.run_modify, pure_bind,
          StateT.run_pure, simulateQ_pure]
        have hR : 𝒟[runRDFShiftedPaper cka prng fs qep l tStar (k none)
            { es with abort := true } sc] = 𝒟[(pure false : ProbComp Bool)] :=
          evalDist_runRDFShiftedPaper_eq_pure_false_of_abort cka prng fs qep l tStar
            (k none) { es with abort := true } sc rfl
        rw [hR]
        refine evalDist_bind_eq_pure_false _ _ fun coins _ => ?_
        have hdoom := doomedShiftedK4Free_of_leakDoom_epMgmt hs hw_f hep hld
          (send cka prng fs (s.st P) m coins).1 m (send cka prng fs (s.st P) m coins).2 false
        exact evalDist_runLDFShiftedPaper_eq_pure_false_of_doomed cka prng fs lam qep l tStar
          (k (some (send cka prng fs (s.st P) m coins).2)) _ hdoom
      · simp only [hld, Bool.false_eq_true, ↓reduceIte, hs₁_st]
        by_cases hsend : P.sendsIn (es.g.epoch P + 1) = true
        · have hq : ¬qep < es.g.epoch P + 1 := by
            intro hq; simp [GameState.epMgmt, hsend, hq] at hep
          have hs₁_ep : s₁.epoch P = es.g.epoch P + 1 := by
            unfold GameState.epMgmt at hep
            simp only [hsend, hq, ↓reduceIte] at hep
            split_ifs at hep <;>
              (injection hep with hep; subst hep; simp [GameState.leak])
          have hs₁_idx : s₁.idx P = 0 := by
            unfold GameState.epMgmt at hep
            simp only [hsend, hq, ↓reduceIte] at hep
            split_ifs at hep <;>
              (injection hep with hep; subst hep; simp [GameState.leak])
          have hsend_eq := fun coins =>
            AuthL9.send_new_eq cka prng fs 1 (some (l - 1)) tStar (m := m) (coins := coins)
              hs.baseSync hsend
          dsimp only at hsend_eq
          by_cases hloc : AuthL9.isLocal (some (l - 1)) 1 (es.g.epoch P) = true
          · have hvR := vSend_new_local_shifted cka prng fs (m := m) (r := none) (s₁ := s₁)
              hs hsend hloc
            rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, hvR]
            simp only [bind_assoc, pure_bind, hs₁_ep, hs₁_idx]
            refine evalDist_bind_congr _ _ _ fun coins => ?_
            rw [hsend_eq coins]
            exact ih _ (sync9Shifted_send_new prng fs hs hsend hep coins m false)
          · have hloc_f : AuthL9.isLocal (some (l - 1)) 1 (es.g.epoch P) = false :=
              Bool.eq_false_iff.mpr hloc
            have hvR := vSend_new_nonlocal_none_shifted cka prng fs
              (m := m) (s₁ := s₁) hs hsend hloc_f
            rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, hvR]
            simp only [bind_assoc, pure_bind, hs₁_ep, hs₁_idx]
            refine evalDist_bind_congr _ _ _ fun coins => ?_
            rw [hsend_eq coins]
            exact ih _ (sync9Shifted_send_new prng fs hs hsend hep coins m false)
        · have hnsend : P.sendsIn (es.g.epoch P + 1) = false :=
            Bool.eq_false_iff.mpr hsend
          have hs₁_eq : s₁ = es.g := by
            unfold GameState.epMgmt at hep
            simp only [hnsend, Bool.false_eq_true, ↓reduceIte] at hep
            split_ifs at hep
            injection hep with hep
            exact hep.symm
          subst hs₁_eq
          obtain ⟨hsendL, hsendR⟩ :=
            vSend_same_epoch_shifted cka prng fs (m := m) (r := none) hs hnsend
          have hreal_eq : AuthL9.realGS sc es.g = s := hs.baseSync.s_eq.symm
          rw [StateT.run_bind, hsendR]
          simp only [hsendL, hreal_eq, pure_bind, OracleComp.evalDist_bind_const]
          exact ih _ (sync9Shifted_send_same hs hnsend _ m _ false)

theorem step_deliverForge_DFShiftedPaper {α : Type} (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (qep l tStar : ℕ) (P : Party) (c c' : Header T × E)
    (k : (unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Range
      (Sum.inr (Sum.inr (P, c, c'))) →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9Shifted cka l tStar s es sc)
    (ih : ∀ u {s' es' sc'}, Sync9Shifted cka l tStar s' es' sc' →
      𝒟[runLDFShiftedPaper cka prng fs lam qep l tStar (k u) s'] =
        𝒟[runRDFShiftedPaper cka prng fs qep l tStar (k u) es' sc']) :
    𝒟[runLDFShiftedPaper cka prng fs lam qep l tStar
        (query (spec := unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E))
          (Sum.inr (Sum.inr (P, c, c'))) >>= k) s] =
      𝒟[runRDFShiftedPaper cka prng fs qep l tStar
        (query (spec := unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E))
          (Sum.inr (Sum.inr (P, c, c'))) >>= k) es sc] := by
  rw [runLDFShiftedPaper_query_bind, runRDFShiftedPaper_query_bind]
  dsimp only [QueryImpl.add_apply, fullImplBaseDFShiftedPaper, oracleImplBaseDFShiftedPaper,
    implEDFShiftedPaper, deliverForgeBaseImpl, deliverForgeE, sameHdrScheme, Config.auth]
  have habort : es.abort = false := hs.baseSync.no_abort
  have hwin : s.win = es.g.win := by rw [hs.baseSync.s_eq]; rfl
  have hin_eq : s.inTransit P.other c = es.g.inTransit P.other c := by rw [hs.baseSync.s_eq]; rfl
  have hin'_eq : s.inTransit P.other c' = es.g.inTransit P.other c' := by rw [hs.baseSync.s_eq]; rfl
  have hcomp_eq : ∀ pos, s.comp.contains pos = es.g.comp.contains pos :=
    fun pos => by rw [hs.baseSync.s_eq]; rfl
  have htriv_eq : ∀ pos, s.trivial (2 + 1) pos = es.g.trivial (2 + 1) pos :=
    fun pos => by rw [hs.baseSync.s_eq]; rfl
  have hbne : (!(c.1 == c'.1)) = (c.1 != c'.1) := rfl
  simp only [habort, Bool.false_or, hwin, hin_eq, hin'_eq, hcomp_eq, hbne,
    StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hw : es.g.win = true
  · simp [hw, ih none hs]
  · simp only [hw, Bool.false_eq_true, ↓reduceIte]
    cases hin : es.g.inTransit P.other c with
    | none => simp [ih none hs]
    | some r =>
      simp only []
      by_cases hguard :
          ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos ||
            (c.1 != c'.1)) = true
      · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure, pure_bind]
        exact ih none hs
      · simp only [hguard, Bool.false_eq_true, ↓reduceIte]
        have hhdr : c'.1 = c.1 := by
          rcases Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hguard) with ⟨_, h2⟩
          exact (bne_eq_false_iff_eq.mp h2).symm
        obtain ⟨hmem, hsnd, hct⟩ := AuthL9.mem_trans_of_inTransit hin
        obtain ⟨ht_ep, hsnd_sends, hle_snd, hTcur⟩ := hs.baseSync.trans_inv r hmem
        dsimp only at ht_ep hsnd_sends hle_snd hTcur
        have hpos_c : r.pos.epoch = c'.1.1 := by rw [hhdr, ← hct, ht_ep]
        have hnsend : P.sendsIn c'.1.1 = false := by
          have h1 : P.other.sendsIn c'.1.1 = true := by
            rw [← hpos_c, ← hsnd]; exact hsnd_sends
          rw [AuthL9.sendsIn_other, Bool.not_eq_true'] at h1
          exact h1
        have hle_other : c'.1.1 ≤ es.g.epoch P.other := by
          rw [← hpos_c, ← hsnd]; exact hle_snd
        have hle_P1 : c'.1.1 ≤ es.g.epoch P + 1 := by
          have hle2 := hs.baseSync.epoch_le P.other
          dsimp only at hle2
          rw [Party.other_other] at hle2
          omega
        by_cases hstep : c'.1.1 = es.g.epoch P + 1
        · have heq_other : es.g.epoch P + 1 = es.g.epoch P.other :=
            hs.baseSync.epoch_eq_of_deliver_step hmem hsnd (by rw [hct, ← hhdr]; exact hstep)
          obtain ⟨T_t, I_t, hcache, hT_other, hl_msg, hI, hagr⟩ := hs.baseSync.cka_step P heq_other
          dsimp only at hcache hT_other hl_msg hI hagr
          have hcT : c'.1.2 = some T_t := by
            rw [hhdr, ← hct, hTcur (by rw [hsnd]; omega), hsnd, hT_other]
          have hcache' : es.h.base.cache c'.1.1 = some (T_t, I_t) := by rwa [hstep, heq_other]
          obtain ⟨hrcvL, hrcvR⟩ :=
            AuthL9.vRecv_new_honest cka prng fs 1 (some (l - 1)) tStar (rec := none)
              hs.baseSync hnsend hstep hcT hcache' hI
          dsimp only at hrcvL hrcvR
          dsimp only [scheme]
          rw [hrcvL, StateT.run_bind, vRecv_hooksCKAShifted_run, hrcvR]
          simp only [pure_bind]
          cases hfs : fs.receive (fs.initReceiver (prng.up (es.g.st P).root I_t).2) c'.1 c'.2 with
          | none =>
            simp [ih (some .rejected) hs]
          | some val =>
            rcases val with ⟨v', i', m'⟩
            have hne_ep : (c'.1.1 != r.pos.epoch) = false := by
              rw [bne_eq_false_iff_eq, hpos_c]
            simp only [hne_ep, Bool.or_false]
            by_cases hqep : decide (qep + 1 < c'.1.1) = true
            · simp [hqep, ih (some .rejected) hs]
            · simp only [hqep, Bool.false_eq_true, ↓reduceIte, htriv_eq]
              by_cases htriv : es.g.trivial (2 + 1) ⟨P.other, c'.1.1, i'⟩ = true
              · have hcom := commitE_new_shifted cka prng fs
                  (pos := ⟨P.other, c'.1.1, i'⟩)
                  (prng.up (es.g.st P).root I_t).1
                  (Function.update (es.g.st P).vR c'.1.1 (some v'))
                  hs hstep heq_other T_t (hl_msg (l - 1) rfl)
                have hsync := sync9Shifted_accept_new hs
                  (pos := ⟨P.other, c'.1.1, i'⟩)
                  (prng.up (es.g.st P).root I_t).1
                  (Function.update (es.g.st P).vR c'.1.1 (some v'))
                  hstep heq_other hnsend T_t hagr
                dsimp only at hcom hsync
                simp only [htriv, ↓reduceIte, StateT.run_bind, StateT.run_set, pure_bind,
                  StateT.run_pure, simulateQ_bind, hcom, StateT.run_modify,
                  simulateQ_pure]
                exact ih _ hsync
              · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
                by_cases hfull : (c'.1.1 == tStar) = true
                · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_set,
                    StateT.run_modify, pure_bind, StateT.run_pure, simulateQ_pure]
                  exact ih (some .rejected) (sync9Shifted_win hs true)
                · simp [hfull, ih (some .rejected) hs]
        · have hle_P : c'.1.1 ≤ es.g.epoch P := by omega
          obtain ⟨hrcvL, hrcvR⟩ :=
            AuthL9.vRecv_same_epoch cka prng fs 1 (some (l - 1)) tStar (rec := none)
              hs.baseSync hnsend hle_P
          dsimp only at hrcvL hrcvR
          dsimp only [scheme]
          rw [hrcvL, StateT.run_bind, vRecv_hooksCKAShifted_run, hrcvR]
          simp only [pure_bind]
          cases hv : (es.g.st P).vR c'.1.1 with
          | none =>
            simp [ih (some .rejected) hs]
          | some v =>
            simp only []
            cases hfs : fs.receive v c'.1 c'.2 with
            | none =>
              simp [ih (some .rejected) hs]
            | some val =>
              rcases val with ⟨v', i', m'⟩
              have hne_ep : (c'.1.1 != r.pos.epoch) = false := by
                rw [bne_eq_false_iff_eq, hpos_c]
              simp only [hne_ep, Bool.or_false]
              by_cases hqep : decide (qep + 1 < c'.1.1) = true
              · simp [hqep, ih (some .rejected) hs]
              · simp only [hqep, Bool.false_eq_true, ↓reduceIte, htriv_eq]
                by_cases htriv : es.g.trivial (2 + 1) ⟨P.other, c'.1.1, i'⟩ = true
                · have hcom := commitE_same_shifted cka prng fs l tStar
                    (P := P)
                    (new :=
                      { es.g.st P with vR := Function.update (es.g.st P).vR c'.1.1 (some v') })
                    (pos := ⟨P.other, c'.1.1, i'⟩) (es := es) (sc := sc) rfl
                  have hsync := sync9Shifted_accept_same hs
                    (Function.update (es.g.st P).vR c'.1.1 (some v'))
                    (pos := ⟨P.other, c'.1.1, i'⟩) hle_P
                  simp only [htriv, ↓reduceIte, StateT.run_bind, StateT.run_set, pure_bind,
                    StateT.run_pure, simulateQ_bind, hcom, StateT.run_modify,
                    simulateQ_pure]
                  exact ih _ hsync
                · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
                  by_cases hfull : (c'.1.1 == tStar) = true
                  · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_set,
                      StateT.run_modify, pure_bind, StateT.run_pure, simulateQ_pure]
                    exact ih (some .rejected) (sync9Shifted_win hs true)
                  · simp [hfull, ih (some .rejected) hs]

theorem runLDFShiftedPaper_eq_runRDFShiftedPaper_of_sync {α : Type}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (qep l tStar : ℕ)
    {oa : AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α}
    (hnbc : AuthL9DFDir2.NoBadCoinsDF oa)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9Shifted cka l tStar s es sc) :
    𝒟[runLDFShiftedPaper cka prng fs lam qep l tStar oa s] =
      𝒟[runRDFShiftedPaper cka prng fs qep l tStar oa es sc] := by
  induction hnbc generalizing s es sc with
  | pure a =>
    rw [runLDFShiftedPaper_pure, runRDFShiftedPaper_pure]
    have habort : es.abort = false := hs.baseSync.no_abort
    have hwin : s.win = es.g.win := by rw [hs.baseSync.s_eq]; rfl
    have hok : authLosingConditionsAvoided (2 + 1) (some (l - 1)) tStar s = authLosingConditionsAvoided (2 + 1) (some (l - 1)) tStar es.g :=
      by rw [hs.baseSync.s_eq]; rfl
    simp [authOut, habort, hwin, hok]
  | query_bind t k hno_bad _ ih =>
    rcases t with n | (((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩)
    · exact step_coins_DFShiftedPaper cka prng fs lam qep l tStar n k hs @ih
    · have hr : r = none := hno_bad P m r rfl
      subst hr
      exact step_transmit_DFShiftedPaper cka prng fs lam qep l tStar P m k hs @ih
    · exact step_chall_DFShiftedPaper cka prng fs lam qep l tStar P m₀ m₁ r k hs @ih
    · exact step_deliver_DFShiftedPaper cka prng fs lam qep l tStar P c k hs @ih
    · exact step_inject_DFShiftedPaper cka prng fs lam qep l tStar P c k hs @ih
    · exact step_corr_DFShiftedPaper cka prng fs lam qep l tStar P k hs @ih
    · exact step_deliverForge_DFShiftedPaper cka prng fs lam qep l tStar P c c' k hs @ih

omit [DecidableEq I] [SampleableType I] [SampleableType K] in
theorem forgeGameGuessedShiftedPaper_eq_runLDFShiftedPaper (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (qep l tStar : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    forgeGameGuessedShiftedPaper (scheme cka prng fs lam) (2 + 1) qep sameHdrScheme l tStar A =
      ($ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
        runLDFShiftedPaper cka prng fs lam qep l tStar A
          (initState (scheme cka prng fs lam) (kr, kc) false)) := by
  unfold forgeGameGuessedShiftedPaper runBaseDFShiftedPaper runLDFShiftedPaper
  simp only [uniformSample, SampleableType.selectElem, seq_eq_bind_map, map_eq_bind_pure_comp,
    Function.comp_apply, pure_bind, bind_assoc]

/-- Shifted-paper Lemma 9 for `DeliverForge` at `t_CKA = l + 1` and `Δcka = 1`. -/
theorem lemma9_df_shifted_paper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (qep l tStar : ℕ)
    (hc : cka.Correct) (hl : 1 ≤ l)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E)
    (hnbc : AuthL9DFDir2.NoBadCoinsDF A) :
    forgeGuessedAdvantageShiftedPaper (scheme cka prng fs lam) (2 + 1) qep sameHdrScheme l tStar A ≤
      𝒟[CKA.branch cka 1 (l + 1) false
        (redCKAAuthDFShiftedPaper cka prng fs lam 1 qep l tStar A)] {true} := by
  by_cases hvg : lastLeakGuessAdmissible 2 (some l) tStar = true
  · apply le_of_eq
    unfold forgeGuessedAdvantageShiftedPaper
    rw [forgeGameGuessedShiftedPaper_eq_runLDFShiftedPaper]
    congr 1
    unfold CKA.branch redCKAAuthDFShiftedPaper authSimDFShiftedPaper engRunDFShiftedPaper
      initCKAShifted
    simp only [hl, ↓reduceIte, liftCShifted, setγPreShifted, StateT.run'_eq, StateT.run_bind,
      StateT.run_lift, StateT.run_modify, StateT.run_pure, pure_bind, bind_assoc,
      simulateQ_bind, simulateQ_pure, AuthL9.simulateQ_sampleT_run, map_bind]
    rw [OracleComp.evalDist_bind_bind_swap ($ᵗ KR) ($ᵗ KC)]
    refine evalDist_bind_congr _ _ _ fun kc => ?_
    refine evalDist_bind_congr _ _ _ fun kr => ?_
    have hall : (CKA.initState cka kc false).allowCorr (l + 1) = true :=
      allowCorr_initState_of_one_le cka kc false hl
    have hstA : (CKA.initState cka kc false).st .A = cka.initA kc := rfl
    have hstB : (CKA.initState cka kc false).st .B = cka.initB kc := rfl
    have hγPre_init :
        Function.update
          (Function.update (fun _ : Party => (none : Option Γ)) .A (some (cka.initA kc)))
          .B (some (cka.initB kc)) =
        (fun P => match P with | .A => some (cka.initA kc) | .B => some (cka.initB kc)) := by
      funext P; cases P <;> rfl
    simp only [CKA.corrQuery, AuthL9.simulateQ_query_eq, QueryImpl.add_apply, CKA.oracleImpl,
      CKA.corrImpl, hall, Bool.true_or, ↓reduceIte, StateT.run_bind, StateT.run_get,
      StateT.run_pure, pure_bind, hstA, hstB, hγPre_init]
    refine (runLDFShiftedPaper_eq_runRDFShiftedPaper_of_sync cka prng fs lam qep l tStar hnbc
      (sync9Shifted_init cka prng fs lam hc hl hvg kr kc)).trans ?_
    simp only [runRDFShiftedPaper, bind_pure_comp, map_pure]
    rfl
  · have hvg_f : lastLeakGuessAdmissible (2 + 1) (some (l - 1)) tStar = false := by
      rw [validGuess_three_sub_one_eq_validGuess_two hl]
      exact Bool.eq_false_iff.mpr hvg
    have hzero :
        forgeGuessedAdvantageShiftedPaper (scheme cka prng fs lam) (2 + 1) qep sameHdrScheme
          l tStar A = 0 := by
      unfold forgeGuessedAdvantageShiftedPaper forgeGameGuessedShiftedPaper
      simp only []
      refine AuthL9.evalDist_true_eq_zero_of_support _ _ fun res _ => ?_
      simp [authLosingConditionsAvoided, hvg_f]
    rw [hzero]
    exact zero_le

end AuthL9ShiftedPaper

end CryptoGames.SM.Construction.DeliverForge

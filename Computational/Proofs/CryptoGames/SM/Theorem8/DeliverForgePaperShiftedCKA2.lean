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
# Shifted-Paper Hop 1 at `Δ = 2`

Step lemmas and synchronization invariant for `lemma9_df_shifted_dir2_paper`, bounding
`forgeGuessedAdvantageShiftedDir2Paper` by the real-world CKA branch `CKA.branch cka 1 (l + 1) false`
of `redCKAAuthDFShiftedDir2Paper`.
-/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory OracleComp OracleSpec

namespace CryptoGames.SM.Construction.DeliverForge

open CryptoGames.SM CryptoGames.SM.Engine CryptoGames.SM.Construction
open CryptoGames.SM.Construction.AuthL9 CryptoGames.SM.Construction.DeliverForge.AuthL9DF
open CryptoGames.SM.Construction.AuthL9DFDir2
open CryptoGames.LibsignalSM.Proofs.Refinement

section AuthL9ShiftedDir2Paper

variable {KC Γ CCoins T I KR Sig K SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

def DoomedAuthShiftedDir2Paper {St Msg C : Type} (l : ℕ) (s : GameState St Msg C) : Prop :=
  Doomed1 (some (l - 1)) (l + 1) s ∨ Doomed2 (l + 1) s ∨
    Doomed3 (some (l - 1)) (l + 1) s ∨ (Party.senderOf (l + 1), l + 1) ∈ s.corrs ∨
    (s.win = true ∧ l - 1 ∉ s.leaks)

theorem doomedAuthShiftedDir2Paper_not_win {St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    (l : ℕ) (s : GameState St Msg C) (hd : DoomedAuthShiftedDir2Paper l s) :
    (s.win && authOKDir2 (some (l - 1)) (l + 1) s) = false := by
  rcases hd with h1 | h2 | h3 | hk4 | ⟨_, hnl⟩
  · unfold authOKDir2
    rw [← Bool.and_assoc, doomedAuth_not_win 2 (some (l - 1)) (l + 1) s (Or.inl h1),
      Bool.false_and]
  · unfold authOKDir2
    rw [← Bool.and_assoc, doomedAuth_not_win 2 (some (l - 1)) (l + 1) s (Or.inr (Or.inl h2)),
      Bool.false_and]
  · unfold authOKDir2
    rw [← Bool.and_assoc,
      doomedAuth_not_win 2 (some (l - 1)) (l + 1) s (Or.inr (Or.inr (Or.inl h3))),
      Bool.false_and]
  · simp [authOKDir2, hk4]
  · have hcan : (canon (l + 1) s == some (l - 1)) = false := by
      rw [beq_eq_false_iff_ne]
      intro hc
      have hm := list_max?_mem hc
      rw [List.mem_filter] at hm
      exact hnl hm.1
    simp [authOKDir2, authLosingConditionsAvoided, hcan]

theorem doomedAuthShiftedDir2Paper_epMgmt {St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    {qep l : ℕ} {s s₁ : GameState St Msg C} {P : Party} {bad : Bool}
    (hw : s.win = false)
    (hd : DoomedAuthShiftedDir2Paper l s) (hep : s.epMgmt 2 qep P bad = some s₁) :
    DoomedAuthShiftedDir2Paper l s₁ := by
  unfold GameState.epMgmt at hep
  split_ifs at hep with hs hq1 hb hq2
  · injection hep with hep; subst hep
    rcases hd with h1 | ⟨hw2, ⟨m, hm, htm⟩, htr⟩ | h3 | hk4 | ⟨hw5, _⟩
    · exact Or.inl (doomed1_of_leaks_sub h1 fun x hx => by
        simp [GameState.leak, List.mem_cons, hx])
    · refine Or.inr (Or.inl ⟨hw2, ⟨maxOpt s.tL (s.epoch P + 1), rfl, ?_⟩, htr⟩)
      exact le_trans htm (le_maxOpt_left hm _)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hk4)))
    · rw [hw] at hw5; nomatch hw5
  · injection hep with hep; subst hep
    rcases hd with h1 | h2 | h3 | hk4 | ⟨hw5, _⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hk4)))
    · rw [hw] at hw5; nomatch hw5
  · injection hep with hep; subst hep; exact hd

theorem doomedAuthShiftedDir2Paper_record {St Msg C : Type} {l : ℕ}
    {s : GameState St Msg C} (P : Party) (st' : St) (r : Record Msg C) (isChall : Bool)
    (hr : r.pos.epoch = s.epoch P) (hd : DoomedAuthShiftedDir2Paper l s) :
    DoomedAuthShiftedDir2Paper l (s.record 2 P st' r isChall) := by
  rcases hd with h1 | ⟨hw2, ⟨m, hm, htm⟩, htr⟩ | h3 | hk4 | ⟨hw5, hnl⟩
  · exact Or.inl h1
  · refine Or.inr (Or.inl ⟨hw2, ⟨m, hm, htm⟩, ?_⟩)
    intro r' hr' heq
    simp only [GameState.record, List.mem_cons] at hr' ⊢
    rcases hr' with rfl | hr'
    · have hsafe : s.safeCh 2 P = false := by
        simp only [GameState.safeCh, healedBy, hm, ← hr, heq, decide_eq_false_iff_not]
        omega
      simp [hsafe]
    · have hmem := htr r' hr' heq
      split_ifs <;> simp [hmem]
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hk4)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hw5, hnl⟩)))

theorem doomedAuthShiftedDir2Paper_accept {St Msg C : Type} {l : ℕ}
    {s : GameState St Msg C} (P : Party) (st' : St) (pos : Pos)
    (hd : DoomedAuthShiftedDir2Paper l s) :
    DoomedAuthShiftedDir2Paper l (s.accept P st' pos) := by
  rcases hd with h1 | ⟨hw2, ⟨m, hm, htm⟩, htr⟩ | h3 | hk4 | ⟨hw5, hnl⟩
  · exact Or.inl h1
  · refine Or.inr (Or.inl ⟨hw2, ⟨m, hm, htm⟩, ?_⟩)
    intro r hr heq
    simp only [GameState.accept, GameState.delete, List.mem_filter] at hr ⊢
    exact ⟨htr r hr.1 heq, hr.2⟩
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hk4)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hw5, hnl⟩)))

theorem doomedAuthShiftedDir2Paper_afterCorrShifted {St Msg C : Type}
    [DecidableEq Msg] [DecidableEq C] {l : ℕ}
    {s : GameState St Msg C} (P : Party) (hw : s.win = false)
    (hd : DoomedAuthShiftedDir2Paper l s) :
    DoomedAuthShiftedDir2Paper l (afterCorrShifted l s P) := by
  rcases hd with h1 | ⟨hw2, ⟨m, hm, htm⟩, htr⟩ | h3 | hk4 | ⟨hw5, _⟩
  · exact Or.inl (doomed1_of_leaks_sub h1 fun x hx => by
      simp [afterCorrShifted, GameState.leak, List.mem_cons, hx])
  · refine Or.inr (Or.inl ⟨hw2, ⟨_, rfl, ?_⟩, ?_⟩)
    · exact le_trans htm (le_maxOpt_left hm _)
    · intro r hr heq
      simp only [afterCorrShifted, GameState.leak, List.mem_append] at hr ⊢
      exact Or.inr (htr r hr heq)
  · exact Or.inr (Or.inr (Or.inl (doomed3_of_corrs_sub h3 fun x hx => by
      simp [afterCorrShifted, List.mem_cons, hx])))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by simp [afterCorrShifted, List.mem_cons, hk4]))))
  · rw [hw] at hw5; nomatch hw5

theorem doomedAuthShiftedDir2Paper_oracleImplShiftedPaper {Key St Msg Coins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (l qep : ℕ)
    (t : (unifSpec + spec St Msg Coins C).Domain)
    {s s' : GameState St Msg C} {u : (unifSpec + spec St Msg Coins C).Range t}
    (hd : DoomedAuthShiftedDir2Paper l s)
    (hmem : (u, s') ∈ support
      ((((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (GameState St Msg C) ProbComp) +
        oracleImplShiftedDir2Paper sm l qep (l + 1) (Config.auth (l + 1))) t).run s)) :
    DoomedAuthShiftedDir2Paper l s' := by
  rcases t with n | ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
  · dsimp only [QueryImpl.add_apply, QueryImpl.liftTarget, QueryImpl.ofLift] at hmem
    rw [(mem_support_liftProb hmem).2]
    exact hd
  · dsimp only [QueryImpl.add_apply, oracleImplShiftedDir2Paper, transmitImpl] at hmem
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hw : s.win = true
    · simp only [hw, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.ext_iff] at hmem
      rw [hmem.2]; exact hd
    · simp only [hw, Bool.false_eq_true, ↓reduceIte] at hmem
      have hw_f : s.win = false := Bool.eq_false_iff.mpr hw
      rw [StateT.run_bind, MonadAttach.mem_support_bind] at hmem
      rcases hmem with ⟨⟨⟨coins, bad⟩, s₀⟩, h₀, hmem⟩
      have hs₀ := (mem_support_liftProb h₀).2
      rw [hs₀] at hmem
      dsimp only at hmem
      cases hep : s.epMgmt 2 qep P bad with
      | none =>
        rw [hep] at hmem
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
        rw [hmem.2]; exact hd
      | some s₁ =>
        rw [hep] at hmem
        simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
          support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
        rw [hmem.2]
        exact doomedAuthShiftedDir2Paper_record P _ _ false rfl
          (doomedAuthShiftedDir2Paper_epMgmt hw_f hd hep)
  · dsimp only [QueryImpl.add_apply, oracleImplShiftedDir2Paper, challImpl, Config.auth] at hmem
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
      cases hep : s.epMgmt 2 qep P bad <;>
        simp only [hep, Bool.not_false, Bool.or_true, ↓reduceIte, StateT.run_pure,
          support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem <;>
        (rw [hmem.2]; exact hd)
  · dsimp only [QueryImpl.add_apply, oracleImplShiftedDir2Paper, deliverImpl, Config.auth] at hmem
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
          exact doomedAuthShiftedDir2Paper_accept P st' r.pos hd
  · dsimp only [QueryImpl.add_apply, oracleImplShiftedDir2Paper, injectImplB1] at hmem
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
          exact doomedAuthShiftedDir2Paper_accept P st' ⟨P.other, t', i'⟩ hd
        · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
            support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
          rw [hmem.2]
          simp only [Config.auth, beq_iff_eq] at hfull
          rcases hd with h1 | h2 | h3 | hk4 | ⟨_, hnl⟩
          · exact Or.inl h1
          · exfalso
            exact htriv (trivB1_of_trivial (doomed2_trivial_tStar (by omega) h2 ⟨P.other, t', i'⟩
              hfull))
          · exact Or.inr (Or.inr (Or.inl h3))
          · exact Or.inr (Or.inr (Or.inr (Or.inl hk4)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hnl⟩)))
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
          rw [hmem.2]; exact hd
  · dsimp only [QueryImpl.add_apply, oracleImplShiftedDir2Paper, corrImplShiftedPaper] at hmem
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    split_ifs at hmem with hcond
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
      rw [hmem.2]; exact hd
    · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
        support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
      rw [hmem.2]
      have hw_f : s.win = false := by
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hcond
        exact hcond.1
      exact doomedAuthShiftedDir2Paper_afterCorrShifted P hw_f hd

omit [Inhabited E] in
theorem doomedAuthShiftedDir2Paper_deliverForgeBaseImpl {Key St Msg Coins : Type}
    [DecidableEq Msg] (sm : SMScheme Key St Msg Coins (Header T × E)) (qep l : ℕ)
    (q : Party × (Header T × E) × (Header T × E))
    {s s' : GameState St Msg (Header T × E)} {u : Option (RecvResult Msg)}
    (hd : DoomedAuthShiftedDir2Paper l s)
    (hmem : (u, s') ∈ support
      ((deliverForgeBaseImplB1 sm qep (l + 1) sameHdrScheme (Config.auth (l + 1)) q).run s)) :
    DoomedAuthShiftedDir2Paper l s' := by
  rcases q with ⟨P, c, c'⟩
  dsimp only [deliverForgeBaseImplB1] at hmem
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
            exact doomedAuthShiftedDir2Paper_accept P st' ⟨P.other, t', i'⟩ hd
          · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
              support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
            rw [hmem.2]
            simp only [Config.auth, beq_iff_eq] at hfull
            rcases hd with h1 | h2 | h3 | hk4 | ⟨_, hnl⟩
            · exact Or.inl h1
            · exfalso
              exact htriv (trivB1_of_trivial (doomed2_trivial_tStar (by omega) h2 ⟨P.other, t', i'⟩
                hfull))
            · exact Or.inr (Or.inr (Or.inl h3))
            · exact Or.inr (Or.inr (Or.inr (Or.inl hk4)))
            · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hnl⟩)))
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
            rw [hmem.2]; exact hd

omit [Inhabited E] in
theorem doomedAuthShiftedDir2Paper_simulateQ_DF {Key St Msg Coins : Type}
    [DecidableEq Msg] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins (Header T × E)) (l qep : ℕ)
    {α : Type} (oa : AdversaryCompDF St Msg Coins (Header T × E) α) :
    ∀ {s s' : GameState St Msg (Header T × E)} {a : α},
      DoomedAuthShiftedDir2Paper l s →
      (a, s') ∈ support
        ((simulateQ
          (fullImplBaseDFShiftedDir2Paper sm l qep (l + 1) sameHdrScheme (Config.auth (l + 1)))
          oa).run s) →
      DoomedAuthShiftedDir2Paper l s' := by
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
    · exact ih u (doomedAuthShiftedDir2Paper_oracleImplShiftedPaper sm l qep (.inl n) hd h₁) h₂
    · exact ih u (doomedAuthShiftedDir2Paper_oracleImplShiftedPaper sm l qep (.inr q) hd h₁) h₂
    · exact ih u (doomedAuthShiftedDir2Paper_deliverForgeBaseImpl sm qep l qdf hd h₁) h₂

/-- Synchronization invariant for `lemma9_df_shifted_dir2_paper` at `(some (l - 1), l + 1)`: wraps
`Sync9Dir2 cka (l - 1)` together with `1 ≤ l` and the pre-challenge cache invariant `γPre_eq`. -/
structure Sync9ShiftedDir2 (cka : CKAScheme KC Γ CCoins T I) (l : ℕ)
    (s : GameState (PartyState Γ T Sig SS RS) M (Header T × E))
    (esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I))
    (sc : CKA.GameState Γ T) : Prop where
  hl : 1 ≤ l
  base : Sync9Dir2 cka (l - 1) s { g := esS.g, h := esS.h.base, abort := esS.abort } sc
  γPre_eq : ∀ P, esS.g.epoch P + 1 ≤ l → esS.h.γPre P = some (s.st P).γ

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem Sync9ShiftedDir2.toSync9Shifted {cka : CKAScheme KC Γ CCoins T I} {l : ℕ}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9ShiftedDir2 cka l s esS sc) :
    Sync9Shifted cka l ((l - 1) + 3) s esS sc :=
  ⟨hs.hl, hs.base.base, hs.γPre_eq⟩

theorem sync9ShiftedDir2_win {cka : CKAScheme KC Γ CCoins T I} {l : ℕ}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9ShiftedDir2 cka l s es sc) (w : Bool) :
    Sync9ShiftedDir2 cka l
      { s with win := w }
      { es with g := { es.g with win := w } }
      sc :=
  ⟨hs.hl, hs.base.sync9_win w, hs.γPre_eq⟩

theorem sync9ShiftedDir2_accept_same {cka : CKAScheme KC Γ CCoins T I} {l : ℕ}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9ShiftedDir2 cka l s es sc) {P : Party}
    (vR' : ℕ → Option RS) {pos : Pos} (hpos_le : pos.epoch ≤ es.g.epoch P) :
    let st_v' := { es.g.st P with vR := vR' }
    let st_r' := { s.st P with vR := vR' }
    Sync9ShiftedDir2 cka l
      (s.accept P st_r' pos)
      { es with g := es.g.accept P st_v' pos }
      sc :=
  ⟨hs.hl, hs.base.sync9_accept_same vR' hpos_le,
    (sync9Shifted_accept_same hs.toSync9Shifted vR' hpos_le).γPre_eq⟩

theorem sync9ShiftedDir2_accept_new {cka : CKAScheme KC Γ CCoins T I} {l : ℕ}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9ShiftedDir2 cka l s es sc) {P : Party}
    (σ' : Sig) (vR' : ℕ → Option RS) {pos : Pos}
    (ht : pos.epoch = es.g.epoch P + 1)
    (heq_other : es.g.epoch P + 1 = es.g.epoch P.other)
    (hnsend : P.sendsIn pos.epoch = false)
    (T_t : T)
    (hagr_step : ∀ rs, cka.AgreesFrom (cka.receive (s.st P).γ T_t).1 (s.st P.other).γ rs) :
    let t := pos.epoch
    let γ_r' := (cka.receive (s.st P).γ T_t).1
    let γ_v' : Option Γ := if AuthL9.isLocal (some (l - 1)) 1 t then some γ_r' else none
    let st_v' : PartyState (Option Γ) T Sig SS RS :=
      { es.g.st P with tcur := t, γ := γ_v', root := σ', vR := vR' }
    let st_r' : PartyState Γ T Sig SS RS :=
      { s.st P with tcur := t, γ := γ_r', root := σ', vR := vR' }
    let h' : CKAStateShifted Γ T I :=
      if t + 1 ≤ l then { es.h with γPre := Function.update es.h.γPre P (some γ_r') } else es.h
    let sc' : CKA.GameState Γ T :=
      if AuthL9.isLocal (some (l - 1)) 1 (es.g.epoch P) then sc else sc.afterReceive P γ_r'
    Sync9ShiftedDir2 cka l
      (s.accept P st_r' pos)
      { es with g := es.g.accept P st_v' pos, h := h' }
      sc' := by
  intro t γ_r' γ_v' st_v' st_r' h' sc'
  have hbase_eq : h'.base = es.h.base := by dsimp only [h']; split_ifs <;> rfl
  refine ⟨hs.hl, ?_,
    (sync9Shifted_accept_new hs.toSync9Shifted σ' vR' ht heq_other hnsend T_t hagr_step).γPre_eq⟩
  rw [hbase_eq]
  exact hs.base.sync9_accept_new σ' vR' ht heq_other hnsend T_t hagr_step

theorem sync9ShiftedDir2_send_same {cka : CKAScheme KC Γ CCoins T I} {l : ℕ}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9ShiftedDir2 cka l s es sc) {P : Party}
    (hnsend : P.sendsIn (es.g.epoch P + 1) = false) (vS' : Option SS) (m : M) (e : E)
    (isChall : Bool) :
    let h : Header T := (es.g.epoch P, (es.g.st P).curCkaMsg)
    let st_v' := { es.g.st P with vS := vS' }
    let st_r' := { s.st P with vS := vS' }
    let rec_P : Record M (Header T × E) := ⟨⟨P, es.g.epoch P, es.g.idx P + 1⟩, m, (h, e)⟩
    Sync9ShiftedDir2 cka l
      (s.record 2 P st_r' rec_P isChall)
      { es with g := es.g.record 2 P st_v' rec_P isChall }
      sc := by
  intro h st_v' st_r' rec_P
  refine ⟨hs.hl, hs.base.sync9_send_same hnsend vS' m e isChall, fun Q hQ => ?_⟩
  have hγ : ((s.record 2 P st_r' rec_P isChall).st Q).γ = (s.st Q).γ := by
    by_cases hQP : Q = P
    · subst Q; simp [GameState.record, Function.update, st_r']
    · simp [GameState.record, Function.update_of_ne hQP]
  rw [hγ]
  exact hs.γPre_eq Q hQ

theorem sync9ShiftedDir2_send_new (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    {cka : CKAScheme KC Γ CCoins T I} {l : ℕ}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9ShiftedDir2 cka l s es sc) {qep : ℕ} {P : Party} {bad : Bool}
    (hsend : P.sendsIn (es.g.epoch P + 1) = true)
    {s₁ : GameState (PartyState (Option Γ) T Sig SS RS) M (Header T × E)}
    (hep : es.g.epMgmt 2 qep P bad = some s₁)
    (coins : CCoins) (m : M) (isChall : Bool) :
    let t := es.g.epoch P + 1
    let c_cka := cka.send (s.st P).γ coins
    let p := prng.up (es.g.st P).root c_cka.2.2
    let ss := fs.initSender p.2
    let h : Header T := (t, some c_cka.2.1)
    let out_fs := fs.send ss h m
    let γv' : Option Γ := if AuthL9.isLocal (some (l - 1)) 1 t then some c_cka.1 else none
    let st_v' : PartyState (Option Γ) T Sig SS RS :=
      { es.g.st P with
        tcur := t, γ := γv', curCkaMsg := some c_cka.2.1, root := p.1, vS := some out_fs.1 }
    let st_r' : PartyState Γ T Sig SS RS :=
      { s.st P with
        tcur := t, γ := c_cka.1, curCkaMsg := some c_cka.2.1, root := p.1, vS := some out_fs.1 }
    let rec_P : Record M (Header T × E) := ⟨⟨P, t, 1⟩, m, (h, out_fs.2)⟩
    let h' : CKAStateShifted Γ T I :=
      { base := { cache := Function.update es.h.base.cache t (some (c_cka.2.1, c_cka.2.2)) }
        γPre := if t + 1 ≤ l then Function.update es.h.γPre P (some c_cka.1) else es.h.γPre }
    let sc' : CKA.GameState Γ T :=
      if AuthL9.isLocal (some (l - 1)) 1 (es.g.epoch P) then sc
      else sc.afterSend P c_cka.1 c_cka.2.1
    Sync9ShiftedDir2 cka l
      ((AuthL9.realGS sc s₁).record 2 P st_r' rec_P isChall)
      { es with g := s₁.record 2 P st_v' rec_P isChall, h := h' }
      sc' := by
  intro t c_cka p ss h out_fs γv' st_v' st_r' rec_P h' sc'
  have hq : ¬qep < es.g.epoch P + 1 := by intro hq; simp [GameState.epMgmt, hsend, hq] at hep
  have hs₁_epoch : s₁.epoch = Function.update es.g.epoch P t := by
    by_cases h3 : (bad && !(es.g.safeCh 2 P)) = true
    · simp only [GameState.epMgmt, hsend, hq, h3, ↓reduceIte, Option.some.injEq] at hep
      subst hep; rfl
    · simp only [Bool.not_eq_true] at h3
      simp [GameState.epMgmt, hsend, hq, h3] at hep
      subst hep; rfl
  have hs₁_st : s₁.st = es.g.st := by
    by_cases h3 : (bad && !(es.g.safeCh 2 P)) = true
    · simp only [GameState.epMgmt, hsend, hq, h3, ↓reduceIte, Option.some.injEq] at hep
      subst hep; rfl
    · simp only [Bool.not_eq_true] at h3
      simp [GameState.epMgmt, hsend, hq, h3] at hep
      subst hep; rfl
  refine ⟨hs.hl, hs.base.sync9_send_new prng fs hsend hep coins m isChall, fun Q hQ => ?_⟩
  simp only [GameState.record, hs₁_epoch] at hQ ⊢
  by_cases hQP : Q = P
  · subst Q
    simp only [Function.update_self] at hQ
    simp [h', hQ, Function.update, st_r']
  · simp only [Function.update_of_ne hQP] at hQ
    have hγQ : (Function.update (AuthL9.realGS sc s₁).st P st_r' Q).γ = (s.st Q).γ := by
      simp [Function.update_of_ne hQP, hs.base.base.s_eq, AuthL9.realGS, hs₁_st]
    rw [hγQ]
    dsimp only [h']
    split_ifs <;> simp [Function.update_of_ne hQP, hs.γPre_eq Q hQ]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem sync9ShiftedDir2_corr {cka : CKAScheme KC Γ CCoins T I} {l : ℕ}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9ShiftedDir2 cka l s es sc) (P : Party) :
    Sync9ShiftedDir2 cka l
      (afterCorrShifted l s P)
      { es with g := afterCorrShifted l es.g P }
      sc := by
  refine ⟨hs.hl, ⟨(sync9Shifted_corr hs.toSync9Shifted P).baseSync, ?_⟩, hs.γPre_eq⟩
  intro pos hpos
  simp only [afterCorrShifted, GameState.leak, List.mem_append, List.mem_map,
    List.mem_filter] at hpos
  have he_ge : max (es.g.epoch .A) (es.g.epoch .B) ≤
      (if max (es.g.epoch .A) (es.g.epoch .B) = l ∧ es.g.epoch P + 1 ≤ l
       then l - 1 else max (es.g.epoch .A) (es.g.epoch .B)) + 1 := by
    split_ifs <;> omega
  rcases hpos with ⟨r, ⟨hr, _⟩, rfl⟩ | hpos
  · have hinv := (hs.base.base.trans_inv r hr).2.2.1
    dsimp only at hinv
    have hmax : es.g.epoch r.pos.sender ≤ max (es.g.epoch .A) (es.g.epoch .B) := by
      cases r.pos.sender <;> simp
    cases hstL : es.g.tL <;>
      simp only [afterCorrShifted, GameState.leak, hstL, maxOpt, healedBy,
        decide_eq_false_iff_not] <;> omega
  · have hun := hs.base.comp_unhealed2 pos hpos
    dsimp only at hun
    cases hstL : es.g.tL with
    | none => simp [hstL, healedBy] at hun
    | some m₀ =>
      simp only [hstL, healedBy, decide_eq_false_iff_not] at hun
      simp only [afterCorrShifted, GameState.leak, hstL, maxOpt, healedBy,
        decide_eq_false_iff_not]
      omega

theorem sync9ShiftedDir2_init (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) {l : ℕ}
    (hc : cka.Correct) (hl : 1 ≤ l) (kr : KR) (kc : KC) :
    let out := prng.up (prng.init kr) lam
    let vp := mkParties (T := T) none none out.1 (fs.initSender out.2) (fs.initReceiver out.2)
    let g₀ : Ctx (Option Γ) T Sig SS RS M E :=
      { st := fun P => match P with | .A => vp.1 | .B => vp.2, b := false }
    let h₀ : CKAStateShifted Γ T I :=
      { base := {}
        γPre := fun P => match P with | .A => some (cka.initA kc) | .B => some (cka.initB kc) }
    Sync9ShiftedDir2 cka l
      (initState (scheme cka prng fs lam) (kr, kc) false)
      { g := g₀, h := h₀ }
      (CKA.initState cka kc false) := by
  refine ⟨hl, Sync9Dir2.sync9_init prng fs lam hc kr kc, ?_⟩
  intro P _
  cases P <;> rfl

local notation "ASpecDF" =>
  unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)

def runLDFShiftedDir2Paper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (qep l : ℕ) {α : Type}
    (oa : AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)) : ProbComp Bool :=
  ((simulateQ
    (fullImplBaseDFShiftedDir2Paper (scheme cka prng fs lam) l qep (l + 1) sameHdrScheme
      (Config.auth (l + 1))) oa).run s) >>=
    fun res => pure (res.2.win && authOKDir2 (some (l - 1)) (l + 1) res.2)

def runRDFShiftedDir2Paper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (qep l : ℕ) {α : Type}
    (oa : AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I))
    (sc : CKA.GameState Γ T) : ProbComp Bool :=
  ((simulateQ
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (CKA.GameState Γ T) ProbComp) +
      CKA.oracleImpl cka 1 (l + 1))
    ((simulateQ
      (implEDFShiftedDir2Paper l (hooksCKAShifted cka prng fs l 0)
        qep fs.maxSkip (l + 1) (Config.auth (l + 1)) ⟨true, some (l - 1), l + 1⟩)
      oa).run es)).run sc) >>=
    fun res => pure (authOut 2 ⟨true, some (l - 1), l + 1⟩ res.1.2)

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType I]
  [SampleableType K] in
theorem runLDFShiftedDir2Paper_pure (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (qep l : ℕ) {α : Type} (a : α)
    (s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)) :
    runLDFShiftedDir2Paper cka prng fs lam qep l (pure a) s =
      pure (s.win && authOKDir2 (some (l - 1)) (l + 1) s) := by
  simp [runLDFShiftedDir2Paper]

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem runRDFShiftedDir2Paper_pure (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (qep l : ℕ) {α : Type} (a : α)
    (es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I))
    (sc : CKA.GameState Γ T) :
    runRDFShiftedDir2Paper cka prng fs qep l (pure a) es sc =
      pure (authOut 2 ⟨true, some (l - 1), l + 1⟩ es) := by
  simp [runRDFShiftedDir2Paper]

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType I]
  [SampleableType K] in
theorem runLDFShiftedDir2Paper_query_bind (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (qep l : ℕ) {α : Type} (t : (ASpecDF).Domain)
    (k : (ASpecDF).Range t →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)) :
    runLDFShiftedDir2Paper cka prng fs lam qep l (query (spec := ASpecDF) t >>= k) s =
      (((fullImplBaseDFShiftedDir2Paper (scheme cka prng fs lam) l qep (l + 1) sameHdrScheme
        (Config.auth (l + 1))) t).run s >>=
        fun res => runLDFShiftedDir2Paper cka prng fs lam qep l (k res.1) res.2) := by
  simp [runLDFShiftedDir2Paper, StateT.run_bind]

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem runRDFShiftedDir2Paper_query_bind (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (qep l : ℕ) {α : Type} (t : (ASpecDF).Domain)
    (k : (ASpecDF).Range t →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I))
    (sc : CKA.GameState Γ T) :
    runRDFShiftedDir2Paper cka prng fs qep l (query (spec := ASpecDF) t >>= k) es sc =
      (((simulateQ
        ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (CKA.GameState Γ T) ProbComp) +
          CKA.oracleImpl cka 1 (l + 1))
        ((implEDFShiftedDir2Paper l (hooksCKAShifted cka prng fs l 0)
          qep fs.maxSkip (l + 1) (Config.auth (l + 1))
          ⟨true, some (l - 1), l + 1⟩ t).run es)).run sc)
        >>= fun res => runRDFShiftedDir2Paper cka prng fs qep l (k res.1.1) res.1.2 res.2) := by
  simp [runRDFShiftedDir2Paper, StateT.run_bind]

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType I]
  [SampleableType K] in
theorem evalDist_runLDFShiftedDir2Paper_true_eq_zero_of_doomed
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (qep l : ℕ)
    {α : Type} (oa : AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (s : GameState (PartyState Γ T Sig SS RS) M (Header T × E))
    (hdoom : DoomedAuthShiftedDir2Paper l s) :
    𝒟[runLDFShiftedDir2Paper cka prng fs lam qep l oa s] {true} = 0 := by
  apply AuthL9.evalDist_true_eq_zero_of_support
  rintro ⟨a, s'⟩ hmem
  exact doomedAuthShiftedDir2Paper_not_win l s'
    (doomedAuthShiftedDir2Paper_simulateQ_DF (scheme cka prng fs lam) l qep oa hdoom hmem)

omit [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
  [Inhabited E] [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
  [SampleableType I] [SampleableType K] in
theorem doomed_of_leakDoom_epMgmt_shifted_dir2 {cka : CKAScheme KC Γ CCoins T I} {l : ℕ}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9ShiftedDir2 cka l s es sc)
    (hwin : es.g.win = false) {qep : ℕ} {P : Party} {bad : Bool}
    {s₁ : GameState (PartyState (Option Γ) T Sig SS RS) M (Header T × E)}
    (hep : es.g.epMgmt 2 qep P bad = some s₁)
    (hld : (Policy.mk true (some (l - 1)) (l + 1)).leakDoom es.g s₁ = true)
    (st' : PartyState Γ T Sig SS RS) (m : M) (c : Header T × E) (isChall : Bool) :
    DoomedAuthShiftedDir2Paper l
      ((AuthL9.realGS sc s₁).record 2 P st' ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, c⟩ isChall) := by
  obtain ⟨hwin1, htr1, hcomp1, htL1, htL2⟩ := hs.base.epMgmt_tL_inv hep
  rw [hwin] at hwin1
  unfold Policy.leakDoom at hld
  rw [Bool.or_eq_true] at hld
  rcases hld with h1 | h2
  · left
    simpa [AuthL9.Doomed1, GameState.record, AuthL9.realGS] using h1
  · right; left
    simp only [Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq] at h2
    rcases h2 with ⟨⟨l', hl', htle⟩, hlt⟩
    cases hstL : s₁.tL with
    | none =>
      rw [htL1 hstL] at hl'
      nomatch hl'
    | some m' =>
      have hm' : l + 1 ≤ m' := le_trans htle ((htL2 m' hstL).2 l' hl')
      refine ⟨by simp [GameState.record, AuthL9.realGS, hwin1],
        ⟨m', by simp [GameState.record, AuthL9.realGS, hstL], hm'⟩, ?_⟩
      intro r' hr' hrt
      simp only [GameState.record, List.mem_cons] at hr'
      rcases hr' with rfl | hr'
      · dsimp only at hrt
        have hsafe : (AuthL9.realGS sc s₁).safeCh 2 P = false := by
          simp only [GameState.safeCh, AuthL9.realGS, hstL, hrt, healedBy, decide_eq_false_iff_not]
          omega
        simp [GameState.record, hsafe]
      · exfalso
        simp only [AuthL9.realGS, htr1] at hr'
        have hinv := hs.base.base.trans_inv r' hr'
        dsimp only at hinv
        have hsnd : r'.pos.sender = Party.senderOf (l + 1) := by
          apply AuthL9.eq_senderOf_of_sendsIn
          rw [← hrt]; exact hinv.2.1
        have hle := hinv.2.2.1
        rw [hrt, hsnd] at hle
        omega

omit [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
  [Inhabited E] [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
  [SampleableType I] [SampleableType K] in
theorem doomed_of_corr_doom_shifted_dir2 {cka : CKAScheme KC Γ CCoins T I} {l : ℕ}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9ShiftedDir2 cka l s es sc)
    (hwin : es.g.win = false) {P : Party}
    (hd : ((Policy.mk true (some (l - 1)) (l + 1)).leakDoom es.g (afterCorrShifted l es.g P) ||
      (Policy.mk true (some (l - 1)) (l + 1)).corrDoom es.g P) = true) :
    DoomedAuthShiftedDir2Paper l (afterCorrShifted l s P) := by
  rw [Bool.or_eq_true] at hd
  rcases hd with hld | hcd
  · unfold Policy.leakDoom at hld
    rw [Bool.or_eq_true] at hld
    rcases hld with h1 | h2
    · left
      rw [hs.base.base.s_eq]
      simpa [AuthL9.Doomed1, afterCorrShifted, GameState.leak, AuthL9.realGS] using h1
    · right; left
      simp only [Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq] at h2
      rcases h2 with ⟨⟨x, hx, htle⟩, hlt⟩
      rw [hs.base.base.s_eq]
      let e_leak := if max (es.g.epoch .A) (es.g.epoch .B) = l ∧ es.g.epoch P + 1 ≤ l
        then l - 1 else max (es.g.epoch .A) (es.g.epoch .B)
      let m' := maxOpt es.g.tL e_leak
      have hm' : l + 1 ≤ m' := by
        simp only [afterCorrShifted, GameState.leak, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact htle
        · cases hstL : es.g.tL with
          | none =>
            rw [hs.base.base.tL_none hstL] at hx
            nomatch hx
          | some m₀ =>
            have hle := (hs.base.base.tL_some m₀ hstL).2 x hx
            simp only [m', maxOpt, hstL]; omega
      refine ⟨by simp [afterCorrShifted, GameState.leak, AuthL9.realGS, hwin],
        ⟨m', by simp [afterCorrShifted, GameState.leak, AuthL9.realGS, m', e_leak], hm'⟩, ?_⟩
      intro r' hr' hrt
      simp only [afterCorrShifted, GameState.leak, AuthL9.realGS] at hr'
      exfalso
      have hinv := hs.base.base.trans_inv r' hr'
      dsimp only at hinv
      have hsnd : r'.pos.sender = Party.senderOf (l + 1) := by
        apply AuthL9.eq_senderOf_of_sendsIn
        rw [← hrt]; exact hinv.2.1
      have hle := hinv.2.2.1
      rw [hrt, hsnd] at hle
      omega
  · right; right; left
    rw [hs.base.base.s_eq]
    unfold AuthL9.Doomed3
    simp only [afterCorrShifted, GameState.leak, AuthL9.realGS, List.any_cons, Bool.or_eq_true]
    left
    simpa [Policy.corrDoom] using hcd

omit [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
  [Inhabited E] [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
  [SampleableType I] [SampleableType K] in
theorem doomed_win_of_safeInj_two_epoch_eq {cka : CKAScheme KC Γ CCoins T I} {l : ℕ}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9ShiftedDir2 cka l s es sc) (P : Party)
    (heq : es.g.epoch P + 1 = l + 1) (hsafe : es.g.safeInj 2 = true) :
    DoomedAuthShiftedDir2Paper l { s with win := true } := by
  refine Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, ?_⟩)))
  dsimp only
  rw [hs.base.base.s_eq]
  dsimp only [AuthL9.realGS]
  intro hl
  cases hstL : es.g.tL with
  | none =>
    rw [hs.base.base.tL_none hstL] at hl
    nomatch hl
  | some m =>
    have hle := (hs.base.base.tL_some m hstL).2 (l - 1) hl
    unfold GameState.safeInj at hsafe
    simp only [hstL, healedBy, decide_eq_true_eq] at hsafe
    have hmin : min (es.g.epoch .A) (es.g.epoch .B) ≤ es.g.epoch P := by
      cases P <;> simp
    omega

omit [DecidableEq M] [DecidableEq E] [DecidableEq I]
  [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K] in
theorem vSend_hooksCKAShifted_zero_eq (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (l tStar : ℕ) :
    vSend (hooksCKAShifted cka prng fs l 0) = vSend (hooksCKAShifted cka prng fs l tStar) := rfl

omit [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K] in
theorem commitE_hooksCKAShifted_zero_eq (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (l tStar : ℕ) :
    commitE (hooksCKAShifted cka prng fs l 0) = commitE (hooksCKAShifted cka prng fs l tStar) := rfl

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem step_coins_DFShiftedDir2Paper {α : Type} (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (qep l : ℕ) (n : unifSpec.Domain)
    (k : (ASpecDF).Range (Sum.inl n) →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9ShiftedDir2 cka l s es sc)
    (ih : ∀ u {s' es' sc'}, Sync9ShiftedDir2 cka l s' es' sc' →
      𝒟[runLDFShiftedDir2Paper cka prng fs lam qep l (k u) s'] {true} ≤
        𝒟[runRDFShiftedDir2Paper cka prng fs qep l (k u) es' sc'] {true}) :
    𝒟[runLDFShiftedDir2Paper cka prng fs lam qep l (query (spec := ASpecDF) (Sum.inl n) >>= k) s]
        {true} ≤
      𝒟[runRDFShiftedDir2Paper cka prng fs qep l
        (query (spec := ASpecDF) (Sum.inl n) >>= k) es sc] {true} := by
  rw [runLDFShiftedDir2Paper_query_bind, runRDFShiftedDir2Paper_query_bind]
  dsimp only [implEDFShiftedDir2Paper, fullImplBaseDFShiftedDir2Paper]
  simp only [QueryImpl.add_apply, coinsE, StateT.run_lift, simulateQ_bind,
    AuthL9.simulateQ_query_eq, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    bind_assoc, pure_bind]
  rw [AuthL9.liftTarget_ofLift_unifSpec_run, AuthL9.liftTarget_ofLift_unifSpec_run]
  simp only [bind_assoc, pure_bind]
  exact OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
    fun u _ => ih u hs

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem step_chall_DFShiftedDir2Paper {α : Type} (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (qep l : ℕ) (P : Party) (m₀ m₁ : M) (r : Option CCoins)
    (k : (ASpecDF).Range
      (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr (P, m₀, m₁, r))))))) →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9ShiftedDir2 cka l s es sc)
    (ih : ∀ u {s' es' sc'}, Sync9ShiftedDir2 cka l s' es' sc' →
      𝒟[runLDFShiftedDir2Paper cka prng fs lam qep l (k u) s'] {true} ≤
        𝒟[runRDFShiftedDir2Paper cka prng fs qep l (k u) es' sc'] {true}) :
    𝒟[runLDFShiftedDir2Paper cka prng fs lam qep l
        (query (spec := ASpecDF)
          (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr (P, m₀, m₁, r))))))) >>= k) s]
        {true} ≤
      𝒟[runRDFShiftedDir2Paper cka prng fs qep l
        (query (spec := ASpecDF)
          (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr (P, m₀, m₁, r))))))) >>= k)
          es sc] {true} := by
  rw [runLDFShiftedDir2Paper_query_bind, runRDFShiftedDir2Paper_query_bind]
  dsimp only [QueryImpl.add_apply, fullImplBaseDFShiftedDir2Paper, oracleImplBaseDFShiftedDir2Paper,
    oracleImplShiftedDir2Paper, implEDFShiftedDir2Paper, challImpl, challE, Config.auth]
  have habort : es.abort = false := hs.base.base.no_abort
  have hwin : s.win = es.g.win := by rw [hs.base.base.s_eq]; rfl
  simp only [habort, Bool.false_or, hwin, StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hw : es.g.win = true
  · simp [hw, ih none hs]
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.or_true]
    cases r with
    | none =>
      simp only [samIfNec, Option.isSome, StateT.run_monadLift, monadLift_self,
        StateT.run_bind, bind_assoc, pure_bind]
      cases s.epMgmt 2 qep P false <;> cases es.g.epMgmt 2 qep P false <;>
        simp [OracleComp.evalDist_bind_const, ih none hs]
    | some c =>
      simp only [samIfNec, Option.isSome, StateT.run_monadLift, monadLift_self,
        StateT.run_bind, pure_bind]
      cases s.epMgmt 2 qep P true <;> cases es.g.epMgmt 2 qep P true <;>
        simp [ih none hs]

omit [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
  [Inhabited E] [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
  [SampleableType I] [SampleableType K] in
theorem epoch_succ_le_of_corr_shifted_dir2 {cka : CKAScheme KC Γ CCoins T I} {l : ℕ}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9ShiftedDir2 cka l s es sc) {P : Party}
    (hloc : AuthL9.isLocal (some (l - 1)) 1 (es.g.epoch P) = false)
    (hld : (Policy.mk true (some (l - 1)) (l + 1)).leakDoom es.g
      (afterCorrShifted l es.g P) = false)
    (hcd : (Policy.mk true (some (l - 1)) (l + 1)).corrDoom es.g P = false)
    (hk4 : ¬(P = Party.senderOf (l + 1) ∧ es.g.epoch P = l + 1)) :
    es.g.epoch P + 1 ≤ l := by
  by_contra hnot
  have hhl := hs.hl
  have hloc' : es.g.epoch P < (l - 1) + 2 + 1 := by
    simpa [AuthL9.isLocal] using hloc
  have hafter : afterCorrShifted l es.g P = es.g.afterCorr P :=
    afterCorrShifted_eq_afterCorr_of_not l es.g P (fun ⟨_, h⟩ => hnot h)
  rw [hafter] at hld
  have hP_ne_rcv : P ≠ Party.receiverOf (l + 1) := by
    intro hrcv
    unfold Policy.corrDoom at hcd
    rw [← hrcv] at hcd
    have hlt : l - 1 < es.g.epoch P := by omega
    simp [ltOpt, hlt] at hcd
  have hP_snd : P = Party.senderOf (l + 1) := by
    cases P <;> cases h : Party.senderOf (l + 1) <;>
      simp [Party.receiverOf, Party.other, h] at hP_ne_rcv ⊢
  have hepP : es.g.epoch P = l := by
    have hne : es.g.epoch P ≠ l + 1 := fun heq => hk4 ⟨hP_snd, heq⟩
    omega
  have hle_other : es.g.epoch P.other ≤ es.g.epoch P + 1 := by
    have h := hs.base.base.epoch_le P.other
    dsimp only at h
    rwa [Party.other_other] at h
  have hne_other : es.g.epoch P.other ≠ l + 1 := by
    intro heq_o
    have hsnd_o : P.other.sendsIn (l + 1) = true := by
      rw [← heq_o]
      apply hs.base.base.epoch_step_sends P.other
      rw [Party.other_other, hepP, heq_o]
    have hPo_snd : P.other = Party.senderOf (l + 1) :=
      AuthL9.eq_senderOf_of_sendsIn hsnd_o
    exact Party.other_ne P (hPo_snd.trans hP_snd.symm)
  have hmax_eq : max (es.g.epoch .A) (es.g.epoch .B) = l := by
    cases P <;> simp [Party.other] at hepP hle_other hne_other ⊢ <;> omega
  have hm'_eq : maxOpt es.g.tL (max (es.g.epoch .A) (es.g.epoch .B)) = l := by
    rw [hmax_eq]
    cases hstL : es.g.tL with
    | none => simp [maxOpt]
    | some m₀ =>
      have hm₀ := hs.base.base.leaks_ub m₀ (hs.base.base.tL_some m₀ hstL).1
      dsimp only at hm₀
      simp only [maxOpt]; omega
  unfold Policy.leakDoom at hld
  simp only [Bool.or_eq_false_iff, List.any_eq_false] at hld
  have h1 := hld.1 (maxOpt es.g.tL (max (es.g.epoch .A) (es.g.epoch .B)))
    (by simp [GameState.afterCorr, GameState.leak])
  rw [hm'_eq] at h1
  have hlt1 : l - 1 < l := by omega
  have hlt2 : l < l + 1 := by omega
  simp [ltOpt, hlt1, hlt2] at h1

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem step_corr_DFShiftedDir2Paper {α : Type} (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (qep l : ℕ) (P : Party)
    (k : (ASpecDF).Range (Sum.inr (Sum.inl (Sum.inr P))) →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9ShiftedDir2 cka l s es sc)
    (ih : ∀ u {s' es' sc'}, Sync9ShiftedDir2 cka l s' es' sc' →
      𝒟[runLDFShiftedDir2Paper cka prng fs lam qep l (k u) s'] {true} ≤
        𝒟[runRDFShiftedDir2Paper cka prng fs qep l (k u) es' sc'] {true}) :
    𝒟[runLDFShiftedDir2Paper cka prng fs lam qep l
        (query (spec := ASpecDF) (Sum.inr (Sum.inl (Sum.inr P))) >>= k) s] {true} ≤
      𝒟[runRDFShiftedDir2Paper cka prng fs qep l
        (query (spec := ASpecDF) (Sum.inr (Sum.inl (Sum.inr P))) >>= k) es sc] {true} := by
  rw [runLDFShiftedDir2Paper_query_bind, runRDFShiftedDir2Paper_query_bind]
  dsimp only [QueryImpl.add_apply, fullImplBaseDFShiftedDir2Paper, oracleImplBaseDFShiftedDir2Paper,
    oracleImplShiftedDir2Paper, implEDFShiftedDir2Paper, corrImplShiftedPaper, corrEShiftedPaper]
  have habort : es.abort = false := hs.base.base.no_abort
  have hwin : s.win = es.g.win := by rw [hs.base.base.s_eq]; rfl
  have hca : s.corrAllowedPaper P = es.g.corrAllowedPaper P := by
    rw [hs.base.base.s_eq]; rfl
  simp only [habort, Bool.false_or, hwin, hca, StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hguard : (es.g.win || !es.g.corrAllowedPaper P) = true
  · simp [hguard, ih none hs]
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
      StateT.run_pure, pure_bind]
    have hwin_f : es.g.win = false := by
      cases hw : es.g.win
      · rfl
      · simp [hw] at hguard
    by_cases hd :
        ((Policy.mk true (some (l - 1)) (l + 1)).leakDoom es.g (afterCorrShifted l es.g P) ||
        (Policy.mk true (some (l - 1)) (l + 1)).corrDoom es.g P) = true
    · have hdoom : DoomedAuthShiftedDir2Paper l (afterCorrShifted l s P) :=
        doomed_of_corr_doom_shifted_dir2 hs hwin_f hd
      rw [evalDist_runLDFShiftedDir2Paper_true_eq_zero_of_doomed cka prng fs lam qep l
        (k (some (s.st P))) (afterCorrShifted l s P) hdoom]
      simp
    · simp only [hd, Bool.false_eq_true, ↓reduceIte]
      by_cases hk4 : P = Party.senderOf (l + 1) ∧ es.g.epoch P = l + 1
      · have hdoom : DoomedAuthShiftedDir2Paper l (afterCorrShifted l s P) := by
          refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
          rw [hs.base.base.s_eq]
          rcases hk4 with ⟨rfl, hk4_ep⟩
          simp [afterCorrShifted, AuthL9.realGS, hk4_ep]
        rw [evalDist_runLDFShiftedDir2Paper_true_eq_zero_of_doomed cka prng fs lam qep l
          (k (some (s.st P))) (afterCorrShifted l s P) hdoom]
        simp
      · have hld : (Policy.mk true (some (l - 1)) (l + 1)).leakDoom es.g
            (afterCorrShifted l es.g P) = false := by
          cases h : (Policy.mk true (some (l - 1)) (l + 1)).leakDoom es.g
            (afterCorrShifted l es.g P)
          · rfl
          · simp [h] at hd
        have hcd : (Policy.mk true (some (l - 1)) (l + 1)).corrDoom es.g P = false := by
          cases h : (Policy.mk true (some (l - 1)) (l + 1)).corrDoom es.g P
          · rfl
          · simp [h] at hd
        have hγ := hs.base.base.γ_eq P
        dsimp only at hγ
        have hst_eq : realParty (es.g.st P) (s.st P).γ (es.g.st P).root (es.g.st P).vS
            (es.g.st P).vR = s.st P := by
          rw [hs.base.base.s_eq]; rfl
        by_cases hloc : AuthL9.isLocal (some (l - 1)) 1 (es.g.epoch P) = true
        · simp only [hloc, ↓reduceIte] at hγ
          simp only [hooksCKAShifted, hγ, pure_bind, hst_eq, liftH_run, StateT.run_bind,
            StateT.run_modify, StateT.run_pure, simulateQ_pure]
          exact ih (some (s.st P)) (sync9ShiftedDir2_corr hs P)
        · simp only [hloc, Bool.false_eq_true, ↓reduceIte] at hγ
          have hloc_f : AuthL9.isLocal (some (l - 1)) 1 (es.g.epoch P) = false :=
            Bool.eq_false_iff.mpr hloc
          have hle_ep : es.g.epoch P + 1 ≤ l :=
            epoch_succ_le_of_corr_shifted_dir2 hs hloc_f hld hcd hk4
          have htcur := hs.base.base.st_tcur P
          dsimp only at htcur
          have hle_tcur : (es.g.st P).tcur + 1 ≤ l := by rw [htcur]; exact hle_ep
          have hpre := hs.γPre_eq P hle_ep
          simp only [hooksCKAShifted, hγ, hle_tcur, ↓reduceIte, hpre, liftH_run,
            StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, hst_eq,
            StateT.run_modify, simulateQ_pure]
          exact ih (some (s.st P)) (sync9ShiftedDir2_corr hs P)

omit [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E] [SampleableType KC]
  [SampleableType KR] [SampleableType I] [SampleableType K] in
theorem vRecv_guard_true_shifted_dir2 (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (l : ℕ) {P : Party} {c : Header T × E}
    {rec : Option (Record M (Header T × E))}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9ShiftedDir2 cka l s es sc)
    (hguard : (P.sendsIn c.1.1 || decide (es.g.epoch P + 1 < c.1.1)) = true) :
    receive cka prng fs (s.st P) c = none ∧
    (liftH (vRecv (hooksCKAShifted cka prng fs l 0)
      es.g P (es.g.st P) c rec)).run es = pure (some none, es) := by
  have hid_r : (s.st P).id = P := by rw [hs.base.base.s_eq]; exact hs.base.base.st_id P
  have htcur_r : (s.st P).tcur = es.g.epoch P := by
    rw [hs.base.base.s_eq]; exact hs.base.base.st_tcur P
  have hid_v := hs.base.base.st_id P; dsimp only at hid_v
  have htcur_v := hs.base.base.st_tcur P; dsimp only at htcur_v
  constructor
  · unfold receive; simp [hid_r, htcur_r, hguard]
  · unfold vRecv; simp [hid_v, htcur_v, hguard]

omit [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E] [SampleableType KC]
  [SampleableType KR] [SampleableType I] [SampleableType K] in
theorem vRecv_same_epoch_shifted_dir2 (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (l : ℕ) {P : Party} {c : Header T × E}
    {rec : Option (Record M (Header T × E))}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9ShiftedDir2 cka l s es sc)
    (hnsend : P.sendsIn c.1.1 = false)
    (hle : c.1.1 ≤ es.g.epoch P) :
    receive cka prng fs (s.st P) c =
      (match (es.g.st P).vR c.1.1 with
      | none => none
      | some v =>
        match fs.receive v c.1 c.2 with
        | none => none
        | some (v', i, m) =>
          some ({ s.st P with vR := Function.update (es.g.st P).vR c.1.1 (some v') },
            c.1.1, i, m)) ∧
    (liftH (vRecv (hooksCKAShifted cka prng fs l 0)
      es.g P (es.g.st P) c rec)).run es =
      pure (some (match (es.g.st P).vR c.1.1 with
        | none => none
        | some v =>
          match fs.receive v c.1 c.2 with
          | none => none
          | some (v', i, m) =>
            some ({ es.g.st P with vR := Function.update (es.g.st P).vR c.1.1 (some v') },
              c.1.1, i, m)), es) := by
  have hid_r : (s.st P).id = P := by rw [hs.base.base.s_eq]; exact hs.base.base.st_id P
  have htcur_r : (s.st P).tcur = es.g.epoch P := by
    rw [hs.base.base.s_eq]; exact hs.base.base.st_tcur P
  have hvR_r : (s.st P).vR = (es.g.st P).vR := by rw [hs.base.base.s_eq]; rfl
  have hid_v := hs.base.base.st_id P; dsimp only at hid_v
  have htcur_v := hs.base.base.st_tcur P; dsimp only at htcur_v
  have hlt : ¬(es.g.epoch P + 1 < c.1.1) := by omega
  have hne : c.1.1 ≠ es.g.epoch P + 1 := by omega
  constructor
  · unfold receive
    simp only [hid_r, htcur_r, hvR_r, hnsend, hlt, decide_false, Bool.or_self,
      Bool.false_eq_true, ↓reduceIte, hne]
    cases hv : (es.g.st P).vR c.1.1 with
    | none => rfl
    | some v =>
      dsimp only
      cases hfs : fs.receive v c.1 c.2 <;> rfl
  · rw [vRecv_hooksCKAShifted_run]
    unfold vRecv
    simp only [hid_v, htcur_v, hnsend, hlt, decide_false, Bool.or_self, Bool.false_eq_true,
      ↓reduceIte, hne, pure_bind, liftH_run]
    cases hv : (es.g.st P).vR c.1.1 with
    | none => simp
    | some v =>
      simp only [hooksCKA, pure_bind]
      cases hfs : fs.receive v c.1 c.2 <;> simp

omit [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E] [SampleableType KC]
  [SampleableType KR] [SampleableType I] [SampleableType K] in
theorem vRecv_new_honest_shifted_dir2 (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (l : ℕ) {P : Party} {c : Header T × E}
    {rec : Option (Record M (Header T × E))}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9ShiftedDir2 cka l s es sc)
    (hnsend : P.sendsIn c.1.1 = false)
    (heq : c.1.1 = es.g.epoch P + 1)
    {T_t : T} {I_t : I}
    (hcT : c.1.2 = some T_t)
    (hcache : es.h.base.cache c.1.1 = some (T_t, I_t))
    (hI : (cka.receive (s.st P).γ T_t).2 = I_t) :
    let p := prng.up (es.g.st P).root I_t
    receive cka prng fs (s.st P) c =
      (match fs.receive (fs.initReceiver p.2) c.1 c.2 with
      | none => none
      | some (v', i, m) =>
        some ({ s.st P with tcur := c.1.1, γ := (cka.receive (s.st P).γ T_t).1, root := p.1,
                            vR := Function.update (es.g.st P).vR c.1.1 (some v') },
          c.1.1, i, m)) ∧
    (liftH (vRecv (hooksCKAShifted cka prng fs l 0)
      es.g P (es.g.st P) c rec)).run es =
      pure (some (match fs.receive (fs.initReceiver p.2) c.1 c.2 with
        | none => none
        | some (v', i, m) =>
          some ({ es.g.st P with tcur := c.1.1,
                                 γ := (es.g.st P).γ.map (fun γ => (cka.receive γ T_t).1),
                                 root := p.1,
                                 vR := Function.update (es.g.st P).vR c.1.1 (some v') },
            c.1.1, i, m)), es) := by
  intro p
  have hid_r : (s.st P).id = P := by rw [hs.base.base.s_eq]; exact hs.base.base.st_id P
  have htcur_r : (s.st P).tcur = es.g.epoch P := by
    rw [hs.base.base.s_eq]; exact hs.base.base.st_tcur P
  have hroot_r : (s.st P).root = (es.g.st P).root := by rw [hs.base.base.s_eq]; rfl
  have hvR_r : (s.st P).vR = (es.g.st P).vR := by rw [hs.base.base.s_eq]; rfl
  have hid_v := hs.base.base.st_id P; dsimp only at hid_v
  have htcur_v := hs.base.base.st_tcur P; dsimp only at htcur_v
  have hnsend' : P.sendsIn (es.g.epoch P + 1) = false := by rwa [← heq]
  constructor
  · unfold receive
    simp only [hid_r, htcur_r, hroot_r, hvR_r, hnsend', ↓reduceIte, heq, hcT, hI,
      Function.update_self]
    cases hfs : fs.receive (fs.initReceiver p.2) c.1 c.2 <;> simp [p]
  · rw [heq] at hcache
    unfold vRecv
    cases hfs : fs.receive (fs.initReceiver p.2) c.1 c.2 <;>
      simp [hid_v, htcur_v, hnsend', heq, hcT, hooksCKAShifted, StateT.run_get, hcache, hfs, p]

omit [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E] [SampleableType KC]
  [SampleableType KR] [SampleableType I] [SampleableType K] in
theorem vRecv_new_none_shifted_dir2 (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (l : ℕ) {P : Party} {c : Header T × E}
    {rec : Option (Record M (Header T × E))}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9ShiftedDir2 cka l s es sc)
    (hnsend : P.sendsIn c.1.1 = false)
    (heq : c.1.1 = es.g.epoch P + 1)
    (hcT : c.1.2 = none) :
    receive cka prng fs (s.st P) c = none ∧
    (liftH (vRecv (hooksCKAShifted cka prng fs l 0)
      es.g P (es.g.st P) c rec)).run es = pure (some none, es) := by
  have hid_r : (s.st P).id = P := by rw [hs.base.base.s_eq]; exact hs.base.base.st_id P
  have htcur_r : (s.st P).tcur = es.g.epoch P := by
    rw [hs.base.base.s_eq]; exact hs.base.base.st_tcur P
  have hid_v := hs.base.base.st_id P; dsimp only at hid_v
  have htcur_v := hs.base.base.st_tcur P; dsimp only at htcur_v
  have hnsend' : P.sendsIn (es.g.epoch P + 1) = false := by rwa [← heq]
  constructor
  · unfold receive; simp [hid_r, htcur_r, hnsend', heq, hcT]
  · unfold vRecv; simp [hid_v, htcur_v, hnsend', heq, hcT]

omit [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E] [SampleableType KC]
  [SampleableType KR] [SampleableType I] [SampleableType K] in
theorem vRecv_new_dishonest_shifted_dir2 (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (l : ℕ)
    {P : Party} {c : Header T × E} {rec : Option (Record M (Header T × E))}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9ShiftedDir2 cka l s es sc)
    (hnsend : P.sendsIn c.1.1 = false)
    (heq : c.1.1 = es.g.epoch P + 1)
    {Tn : T} (hcT : c.1.2 = some Tn)
    (hhon : ∀ Tc Ik, es.h.base.cache c.1.1 = some (Tc, Ik) → Tc ≠ Tn) :
    (liftH (vRecv (hooksCKAShifted cka prng fs l 0)
      es.g P (es.g.st P) c rec)).run es = pure (some none, es) := by
  have hid_v := hs.base.base.st_id P; dsimp only at hid_v
  have htcur_v := hs.base.base.st_tcur P; dsimp only at htcur_v
  have hnsend' : P.sendsIn (es.g.epoch P + 1) = false := by rwa [← heq]
  rw [heq] at hhon
  unfold vRecv
  cases hcache : es.h.base.cache (es.g.epoch P + 1) with
  | none =>
    simp [hid_v, htcur_v, hnsend', heq, hcT, hooksCKAShifted, StateT.run_get, hcache]
  | some p =>
    rcases p with ⟨Tc, Ik⟩
    have hTc : Tc ≠ Tn := hhon Tc Ik hcache
    simp [hid_v, htcur_v, hnsend', heq, hcT, hooksCKAShifted, StateT.run_get, hcache, hTc]

omit [SampleableType KR] [SampleableType K] in
theorem step_deliver_DFShiftedDir2Paper {α : Type} (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (qep l : ℕ) (P : Party) (c : Header T × E)
    (k : (ASpecDF).Range (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr (P, c)))))) →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9ShiftedDir2 cka l s es sc)
    (ih : ∀ u {s' es' sc'}, Sync9ShiftedDir2 cka l s' es' sc' →
      𝒟[runLDFShiftedDir2Paper cka prng fs lam qep l (k u) s'] {true} ≤
        𝒟[runRDFShiftedDir2Paper cka prng fs qep l (k u) es' sc'] {true}) :
    𝒟[runLDFShiftedDir2Paper cka prng fs lam qep l
        (query (spec := ASpecDF)
          (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr (P, c)))))) >>= k) s] {true} ≤
      𝒟[runRDFShiftedDir2Paper cka prng fs qep l
        (query (spec := ASpecDF)
          (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr (P, c)))))) >>= k) es sc] {true} := by
  rw [runLDFShiftedDir2Paper_query_bind, runRDFShiftedDir2Paper_query_bind]
  dsimp only [QueryImpl.add_apply, fullImplBaseDFShiftedDir2Paper, oracleImplBaseDFShiftedDir2Paper,
    oracleImplShiftedDir2Paper, implEDFShiftedDir2Paper, deliverImpl, deliverE, Config.auth]
  have habort : es.abort = false := hs.base.base.no_abort
  have hwin : s.win = es.g.win := by rw [hs.base.base.s_eq]; rfl
  have hin_eq : s.inTransit P.other c = es.g.inTransit P.other c := by rw [hs.base.base.s_eq]; rfl
  have hch_eq : s.chall = es.g.chall := by rw [hs.base.base.s_eq]; rfl
  simp only [habort, Bool.false_or, hwin, hin_eq, StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hw : es.g.win = true
  · simp [hw, ih none hs]
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, Bool.false_and]
    cases hin : es.g.inTransit P.other c with
    | none => simp [ih none hs]
    | some r =>
      simp only []
      obtain ⟨hmem, hsnd, hct⟩ := AuthL9.mem_trans_of_inTransit hin
      obtain ⟨ht_ep, hsnd_sends, hle_snd, hTcur⟩ := hs.base.base.trans_inv r hmem
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
        have hle2 := hs.base.base.epoch_le P.other
        dsimp only at hle2
        rw [Party.other_other] at hle2
        omega
      by_cases hstep : c.1.1 = es.g.epoch P + 1
      · have heq_other : es.g.epoch P + 1 = es.g.epoch P.other :=
          hs.base.base.epoch_eq_of_deliver_step hmem hsnd (by rw [hct]; exact hstep)
        obtain ⟨T_t, I_t, hcache, hT_other, hl_msg, hI, hagr⟩ := hs.base.base.cka_step P heq_other
        dsimp only at hcache hT_other hl_msg hI hagr
        have hcT : c.1.2 = some T_t := by
          rw [← hct, hTcur (by rw [hsnd]; omega), hsnd, hT_other]
        have hcache' : es.h.base.cache c.1.1 = some (T_t, I_t) := by rwa [hstep, heq_other]
        obtain ⟨hrcvL, hrcvR⟩ :=
          vRecv_new_honest_shifted_dir2 cka prng fs l (rec := some r)
            hs hnsend hstep hcT hcache' hI
        dsimp only at hrcvL hrcvR
        dsimp only [scheme]
        rw [hrcvL, StateT.run_bind, hrcvR]
        simp only [pure_bind]
        cases hfs : fs.receive (fs.initReceiver (prng.up (es.g.st P).root I_t).2) c.1 c.2 with
        | none =>
          simp [ih (some .rejected) hs]
        | some val =>
          rcases val with ⟨v', i', m'⟩
          have hpos_ep : r.pos.epoch = es.g.epoch P + 1 := by omega
          have hnsend_pos : P.sendsIn r.pos.epoch = false := by rwa [hpos_c]
          rw [commitE_hooksCKAShifted_zero_eq cka prng fs l ((l - 1) + 3)]
          have hcom := commitE_new_shifted cka prng fs (pos := r.pos)
            (prng.up (es.g.st P).root I_t).1
            (Function.update (es.g.st P).vR c.1.1 (some v'))
            hs.toSync9Shifted hpos_ep heq_other T_t (hl_msg (l - 1) rfl)
          have hsync := sync9ShiftedDir2_accept_new hs (pos := r.pos)
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
          vRecv_same_epoch_shifted_dir2 cka prng fs l (rec := some r)
            hs hnsend hle_P
        dsimp only at hrcvL hrcvR
        dsimp only [scheme]
        rw [hrcvL, StateT.run_bind, hrcvR]
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
            have hcom := commitE_same_shifted cka prng fs l 0
              (P := P)
              (new := { es.g.st P with vR := Function.update (es.g.st P).vR c.1.1 (some v') })
              (pos := r.pos) (es := es) (sc := sc) rfl
            have hsync := sync9ShiftedDir2_accept_same hs
              (Function.update (es.g.st P).vR c.1.1 (some v')) hpos_le
            simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
              simulateQ_bind, hcom, StateT.run_modify, simulateQ_pure, hch_eq]
            exact ih _ hsync

end AuthL9ShiftedDir2Paper

end CryptoGames.SM.Construction.DeliverForge

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeCKA
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePRNG
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperDefs
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFS
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma9
import VCVio.OracleComp.EvalDist.Measure

/-!
# `DeliverForgePaper` Lemma 9 and Stage-2 Bucket Game

**Checked by Lean.** Proves Lemma 9 (`lemma9_df_paper`), initial step lemmas of Lemma 10, and the
Stage-2 `(tL, par)` bucket game for `DeliverForge` under `corrAllowedPaper`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.SM.Construction.DeliverForge.AuthL9DF

open CryptoGames.SM CryptoGames.SM.Engine CryptoGames.SM.Construction.AuthL9

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

variable (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
  (tL : Option ℕ) (tStar : ℕ)

local notation "ASpecDF" =>
  unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)

def runLDFPaper {α : Type}
    (oa : AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)) : ProbComp Bool :=
  ((simulateQ
    (fullImplBaseDFPaper (scheme cka prng fs lam) (2 + Δcka) qep sameHdrScheme (Config.auth tStar))
    oa).run s) >>= fun res => pure (res.2.win && authLosingConditionsAvoided (2 + Δcka) tL tStar res.2)

def runRDFPaper {α : Type}
    (oa : AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I))
    (sc : CKA.GameState Γ T) : ProbComp Bool :=
  ((simulateQ
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (CKA.GameState Γ T) ProbComp) +
      CKA.oracleImpl cka Δcka (healEpoch tL))
    ((simulateQ
      (implEDFPaper (hooksCKA cka prng fs Δcka ⟨true, tL, tStar⟩)
        (2 + Δcka) qep fs.maxSkip (Config.auth tStar) ⟨true, tL, tStar⟩)
      oa).run es)).run sc) >>= fun res => pure (authOut (2 + Δcka) ⟨true, tL, tStar⟩ res.1.2)

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K]
  in
theorem runLDFPaper_pure {α : Type} (a : α)
    (s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)) :
    runLDFPaper cka prng fs lam Δcka qep tL tStar (pure a) s =
      pure (s.win && authLosingConditionsAvoided (2 + Δcka) tL tStar s) := by
  simp [runLDFPaper]

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem runRDFPaper_pure {α : Type} (a : α)
    (es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I))
    (sc : CKA.GameState Γ T) :
    runRDFPaper cka prng fs Δcka qep tL tStar (pure a) es sc =
      pure (authOut (2 + Δcka) ⟨true, tL, tStar⟩ es) := by
  simp [runRDFPaper]

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K]
  in
theorem runLDFPaper_query_bind {α : Type} (t : (ASpecDF).Domain)
    (k : (ASpecDF).Range t →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)) :
    runLDFPaper cka prng fs lam Δcka qep tL tStar (query (spec := ASpecDF) t >>= k) s =
      (((fullImplBaseDFPaper (scheme cka prng fs lam) (2 + Δcka) qep sameHdrScheme
        (Config.auth tStar)) t).run s >>=
        fun res => runLDFPaper cka prng fs lam Δcka qep tL tStar (k res.1) res.2) := by
  simp [runLDFPaper, StateT.run_bind]

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem runRDFPaper_query_bind {α : Type} (t : (ASpecDF).Domain)
    (k : (ASpecDF).Range t →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I))
    (sc : CKA.GameState Γ T) :
    runRDFPaper cka prng fs Δcka qep tL tStar (query (spec := ASpecDF) t >>= k) es sc =
      (((simulateQ
        ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (CKA.GameState Γ T) ProbComp) +
          CKA.oracleImpl cka Δcka (healEpoch tL))
        ((implEDFPaper (hooksCKA cka prng fs Δcka ⟨true, tL, tStar⟩)
          (2 + Δcka) qep fs.maxSkip (Config.auth tStar) ⟨true, tL, tStar⟩ t).run es)).run sc) >>=
        fun res => runRDFPaper cka prng fs Δcka qep tL tStar (k res.1.1) res.1.2 res.2) := by
  simp [runRDFPaper, StateT.run_bind]

omit [Inhabited E] in
theorem doomedAuth_simulateQ_DFPaper {Key St Msg Coins : Type}
    [DecidableEq Msg] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins (Header T × E)) {Δ : ℕ} (hΔ : 0 < Δ)
    {α : Type} (oa : AdversaryCompDF St Msg Coins (Header T × E) α) :
    ∀ {s s' : GameState St Msg (Header T × E)} {a : α},
      DoomedAuth tL tStar s →
      (a, s') ∈ support
        ((simulateQ (fullImplBaseDFPaper sm Δ qep sameHdrScheme (Config.auth tStar)) oa).run s) →
      DoomedAuth tL tStar s' := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s s' a' hd hmem
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.ext_iff] at hmem
    rw [hmem.2]; exact hd
  | query_bind t k ih =>
    intro s s' a' hd hmem
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, MonadAttach.mem_support_bind] at hmem
    rcases hmem with ⟨⟨u, s₁⟩, h₁, h₂⟩
    rcases t with n | ((q14 | P) | qdf)
    · exact ih u (doomedAuth_oracleImpl (qep := qep) sm hΔ tL tStar (.inl n) hd h₁) h₂
    · exact ih u (doomedAuth_oracleImpl (qep := qep) sm hΔ tL tStar (.inr (.inl q14)) hd h₁) h₂
    · dsimp only [QueryImpl.add_apply, fullImplBaseDFPaper, oracleImplBaseDFPaper,
        oracleImplPaper, corrImplPaper] at h₁
      rw [StateT.run_bind, StateT.run_get, pure_bind] at h₁
      split_ifs at h₁ with hcond
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₁
        rw [← h₁.2] at hd; exact ih u hd h₂
      · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
          support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₁
        exact ih u (h₁.2 ▸ doomedAuth_afterCorr P hd) h₂
    · exact ih u (doomedAuth_deliverForgeBaseImpl qep tL tStar sm hΔ qdf hd h₁) h₂

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K]
  in
theorem evalDist_runLDFPaper_eq_pure_false_of_doomed
    {α : Type} (oa : AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (s : GameState (PartyState Γ T Sig SS RS) M (Header T × E))
    (hdoom : DoomedAuth tL tStar s) :
    𝒟[runLDFPaper cka prng fs lam Δcka qep tL tStar oa s] =
      𝒟[(pure false : ProbComp Bool)] := by
  apply evalDist_bind_eq_pure_false
  rintro ⟨a, s'⟩ hmem
  have hΔ : 0 < 2 + Δcka := by omega
  have hdoom' : DoomedAuth tL tStar s' :=
    doomedAuth_simulateQ_DFPaper qep tL tStar (scheme cka prng fs lam) hΔ oa hdoom hmem
  rw [doomedAuth_not_win (2 + Δcka) tL tStar s' hdoom']

omit [SampleableType CCoins] in
theorem abort_simulateQ_DFPaper {Γv Sv SSv RSv HS : Type} {ι : Type}
    {tspec : OracleSpec.{0, 0} ι} {S : Type}
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ maxSkip : ℕ) (cfg : Config M) (π : Policy)
    (tImpl : QueryImpl tspec (StateT S ProbComp))
    {α : Type} (oa : AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α) :
    ∀ {es es' : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS} {sc sc' : S} {a : α},
      es.abort = true →
      ((a, es'), sc') ∈ support ((simulateQ
        ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT S ProbComp) + tImpl)
        ((simulateQ (implEDFPaper hk Δ qep maxSkip cfg π) oa).run es)).run sc) →
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
    · dsimp only [implEDFPaper, coinsE, HAdd.hAdd, Add.add, QueryImpl.add] at h₁
      simp only [StateT.run_lift, simulateQ_bind, QueryImpl.liftTarget,
        simulateQ_pure, StateT.run_bind, StateT.run_pure, MonadAttach.mem_support_bind,
        support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₁
      rcases h₁ with ⟨_, _, ⟨_, rfl⟩, rfl⟩
      exact ih u hab h₂
    all_goals
      dsimp only [implEDFPaper, transmitE, challE, deliverE, injectE, corrEPaper, deliverForgeE,
        HAdd.hAdd, Add.add, QueryImpl.add] at h₁
      simp only [hab, Bool.true_or, ↓reduceIte,
        StateT.run_bind, StateT.run_get, pure_bind, StateT.run_pure,
        simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₁
      rw [← h₁.1.2] at hab
      exact ih u hab h₂

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem evalDist_runRDFPaper_eq_pure_false_of_abort
    {α : Type} (oa : AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I))
    (sc : CKA.GameState Γ T)
    (hab : es.abort = true) :
    𝒟[runRDFPaper cka prng fs Δcka qep tL tStar oa es sc] =
      𝒟[(pure false : ProbComp Bool)] := by
  apply evalDist_bind_eq_pure_false
  rintro ⟨⟨a, es'⟩, sc'⟩ hmem
  have hab' : es'.abort = true :=
    abort_simulateQ_DFPaper qep (hooksCKA cka prng fs Δcka ⟨true, tL, tStar⟩)
      (2 + Δcka) fs.maxSkip (Config.auth tStar) ⟨true, tL, tStar⟩
      (CKA.oracleImpl cka Δcka (healEpoch tL)) oa hab hmem
  simp [authOut, hab']

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem step_coins_DFPaper {α : Type} (n : unifSpec.Domain)
    (k : (ASpecDF).Range (Sum.inl n) →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar s es sc)
    (ih : ∀ u {s' es' sc'}, Sync9 cka Δcka tL tStar s' es' sc' →
      𝒟[runLDFPaper cka prng fs lam Δcka qep tL tStar (k u) s'] =
        𝒟[runRDFPaper cka prng fs Δcka qep tL tStar (k u) es' sc']) :
    𝒟[runLDFPaper cka prng fs lam Δcka qep tL tStar (query (spec := ASpecDF) (Sum.inl n) >>= k) s] =
      𝒟[runRDFPaper cka prng fs Δcka qep tL tStar
        (query (spec := ASpecDF) (Sum.inl n) >>= k) es sc] := by
  rw [runLDFPaper_query_bind, runRDFPaper_query_bind]
  dsimp only [implEDFPaper, fullImplBaseDFPaper]
  simp only [QueryImpl.add_apply, coinsE, StateT.run_lift, simulateQ_bind, simulateQ_query_eq,
    simulateQ_pure, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
  rw [liftTarget_ofLift_unifSpec_run, liftTarget_ofLift_unifSpec_run]
  simp only [bind_assoc, pure_bind]
  apply evalDist_bind_congr
  intro u
  exact ih u hs

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem step_chall_DFPaper {α : Type} (P : Party) (m₀ m₁ : M) (r : Option CCoins)
    (k : (ASpecDF).Range
      (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr (P, m₀, m₁, r))))))) →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar s es sc)
    (ih : ∀ u {s' es' sc'}, Sync9 cka Δcka tL tStar s' es' sc' →
      𝒟[runLDFPaper cka prng fs lam Δcka qep tL tStar (k u) s'] =
        𝒟[runRDFPaper cka prng fs Δcka qep tL tStar (k u) es' sc']) :
    𝒟[runLDFPaper cka prng fs lam Δcka qep tL tStar
        (query (spec := ASpecDF)
          (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr (P, m₀, m₁, r))))))) >>= k) s] =
      𝒟[runRDFPaper cka prng fs Δcka qep tL tStar
        (query (spec := ASpecDF)
          (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr (P, m₀, m₁, r))))))) >>= k)
          es sc] := by
  rw [runLDFPaper_query_bind, runRDFPaper_query_bind]
  dsimp only [QueryImpl.add_apply, fullImplBaseDFPaper, oracleImplBaseDFPaper, oracleImplPaper,
    implEDFPaper, challImpl, challE, Config.auth]
  have hwin : s.win = es.g.win := by rw [hs.s_eq]; rfl
  simp only [hs.no_abort, Bool.false_or, hwin, StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hw : es.g.win = true
  · simp [hw, ih none hs]
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.or_true]
    cases r with
    | none =>
      simp only [samIfNec, Option.isSome, StateT.run_monadLift, monadLift_self,
        StateT.run_bind, bind_assoc, pure_bind]
      cases s.epMgmt (2 + Δcka) qep P false <;> cases es.g.epMgmt (2 + Δcka) qep P false <;>
        simp [OracleComp.evalDist_bind_const, ih none hs]
    | some c =>
      simp only [samIfNec, Option.isSome, StateT.run_monadLift, monadLift_self,
        StateT.run_bind, pure_bind]
      cases s.epMgmt (2 + Δcka) qep P true <;> cases es.g.epMgmt (2 + Δcka) qep P true <;>
        simp [ih none hs]

omit [SampleableType KR] [SampleableType K] in
theorem step_corr_DFPaper {α : Type} (P : Party)
    (k : (ASpecDF).Range (Sum.inr (Sum.inl (Sum.inr P))) →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar s es sc)
    (ih : ∀ u {s' es' sc'}, Sync9 cka Δcka tL tStar s' es' sc' →
      𝒟[runLDFPaper cka prng fs lam Δcka qep tL tStar (k u) s'] =
        𝒟[runRDFPaper cka prng fs Δcka qep tL tStar (k u) es' sc']) :
    𝒟[runLDFPaper cka prng fs lam Δcka qep tL tStar
        (query (spec := ASpecDF) (Sum.inr (Sum.inl (Sum.inr P))) >>= k) s] =
      𝒟[runRDFPaper cka prng fs Δcka qep tL tStar
        (query (spec := ASpecDF) (Sum.inr (Sum.inl (Sum.inr P))) >>= k) es sc] := by
  rw [runLDFPaper_query_bind, runRDFPaper_query_bind]
  dsimp only [QueryImpl.add_apply, fullImplBaseDFPaper, oracleImplBaseDFPaper, oracleImplPaper,
    implEDFPaper, corrImplPaper, corrEPaper]
  have hwin : s.win = es.g.win := by rw [hs.s_eq]; rfl
  have hca : s.corrAllowedPaper P = es.g.corrAllowedPaper P := by rw [hs.s_eq]; rfl
  simp only [hs.no_abort, Bool.false_or, hwin, hca, StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hguard : (es.g.win || !es.g.corrAllowedPaper P) = true
  · simp [hguard, ih none hs]
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte]
    have hwin_f : es.g.win = false := by
      cases hw : es.g.win
      · rfl
      · simp [hw] at hguard
    by_cases hd : ((Policy.mk true tL tStar).leakDoom es.g (es.g.afterCorr P) ||
        (Policy.mk true tL tStar).corrDoom es.g P) = true
    · simp only [hd, ↓reduceIte, abortE]
      have hdoom : DoomedAuth tL tStar (s.afterCorr P) := hs.doomed_of_corr_doom hwin_f hd
      have hL := evalDist_runLDFPaper_eq_pure_false_of_doomed cka prng fs lam Δcka qep tL tStar
        (k (some (s.st P))) (s.afterCorr P) hdoom
      have hR := evalDist_runRDFPaper_eq_pure_false_of_abort cka prng fs Δcka qep tL tStar
        (k none) { es with abort := true } sc rfl
      exact hL.trans hR.symm
    · simp only [hd, Bool.false_eq_true, ↓reduceIte]
      have hld : (Policy.mk true tL tStar).leakDoom es.g (es.g.afterCorr P) = false := by
        cases h : (Policy.mk true tL tStar).leakDoom es.g (es.g.afterCorr P)
        · rfl
        · simp [h] at hd
      have hcd : (Policy.mk true tL tStar).corrDoom es.g P = false := by
        cases h : (Policy.mk true tL tStar).corrDoom es.g P
        · rfl
        · simp [h] at hd
      have hγ := hs.γ_eq P
      by_cases hloc : isLocal tL Δcka (es.g.epoch P) = true
      · simp only [hloc, ↓reduceIte] at hγ
        have hst_eq : realParty (es.g.st P) (s.st P).γ (es.g.st P).root (es.g.st P).vS
            (es.g.st P).vR = s.st P := by
          rw [hs.s_eq]; rfl
        simp only [hooksCKA, hγ, pure_bind, hst_eq]
        exact ih (some (s.st P)) (hs.sync9_corr P)
      · simp only [hloc, Bool.false_eq_true, ↓reduceIte] at hγ
        rcases htL : tL with _ | l
        · simp [isLocal, htL] at hloc
        · have hloc' : es.g.epoch P < l + 2 + Δcka := by
            simp [isLocal, htL] at hloc
            exact hloc
          have hall : sc.allowCorr (healEpoch (some l)) = true :=
            hs.allowCorr_of_corr htL hloc' hld hcd
          have hall' : sc.allowCorr (healEpoch tL) = true := by
            simpa [htL] using hall
          have hst_eq : realParty (es.g.st P) (sc.st P) (es.g.st P).root (es.g.st P).vS
              (es.g.st P).vR = s.st P := by
            rw [hs.s_eq]
            simp [realGS, realVP, realParty, hγ]
          simp only [hooksCKA, hγ, liftH_run, liftC, CKA.corrQuery, StateT.run_bind,
            StateT.run_lift, simulateQ_bind, simulateQ_query_eq, QueryImpl.add_apply,
            CKA.oracleImpl, CKA.corrImpl, hall', Bool.true_or, ↓reduceIte, StateT.run_get,
            pure_bind, StateT.run_pure, simulateQ_pure, StateT.run_modify, StateT.run_set,
            bind_assoc, hst_eq, ← htL]
          exact ih (some (s.st P)) (hs.sync9_corr P)

theorem step_deliver_DFPaper {α : Type} (P : Party) (c : Header T × E)
    (k : (ASpecDF).Range (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr (P, c)))))) →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar s es sc)
    (ih : ∀ u {s' es' sc'}, Sync9 cka Δcka tL tStar s' es' sc' →
      𝒟[runLDFPaper cka prng fs lam Δcka qep tL tStar (k u) s'] =
        𝒟[runRDFPaper cka prng fs Δcka qep tL tStar (k u) es' sc']) :
    𝒟[runLDFPaper cka prng fs lam Δcka qep tL tStar
        (query (spec := ASpecDF)
          (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr (P, c)))))) >>= k) s] =
      𝒟[runRDFPaper cka prng fs Δcka qep tL tStar
        (query (spec := ASpecDF)
          (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr (P, c)))))) >>= k) es sc] := by
  rw [runLDFPaper_query_bind, runRDFPaper_query_bind]
  dsimp only [QueryImpl.add_apply, fullImplBaseDFPaper, oracleImplBaseDFPaper, oracleImplPaper,
    implEDFPaper, deliverImpl, deliverE, Config.auth]
  have hwin : s.win = es.g.win := by rw [hs.s_eq]; rfl
  have hin_eq : s.inTransit P.other c = es.g.inTransit P.other c := by rw [hs.s_eq]; rfl
  have hch_eq : s.chall = es.g.chall := by rw [hs.s_eq]; rfl
  simp only [hs.no_abort, Bool.false_or, hwin, hin_eq, StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hw : es.g.win = true
  · simp [hw, ih none hs]
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, Bool.false_and]
    cases hin : es.g.inTransit P.other c with
    | none => simp [ih none hs]
    | some r =>
      simp only []
      obtain ⟨hmem, hsnd, hct⟩ := mem_trans_of_inTransit hin
      obtain ⟨ht_ep, hsnd_sends, hle_snd, hTcur⟩ := hs.trans_inv r hmem
      have hpos_c : r.pos.epoch = c.1.1 := by rw [← hct, ht_ep]
      have hnsend : P.sendsIn c.1.1 = false := by
        have h1 : P.other.sendsIn c.1.1 = true := by
          rw [← hpos_c, ← hsnd]
          exact hsnd_sends
        rw [sendsIn_other, Bool.not_eq_true'] at h1
        exact h1
      have hle_other : c.1.1 ≤ es.g.epoch P.other := by
        rw [← hpos_c, ← hsnd]
        exact hle_snd
      have hle_P1 : c.1.1 ≤ es.g.epoch P + 1 := by
        have hle2 := hs.epoch_le P.other
        rw [Party.other_other] at hle2
        omega
      by_cases hstep : c.1.1 = es.g.epoch P + 1
      · have heq_other : es.g.epoch P + 1 = es.g.epoch P.other :=
          hs.epoch_eq_of_deliver_step hmem hsnd (by rw [hct]; exact hstep)
        obtain ⟨T_t, I_t, hcache, hT_other, hl_msg, hI, hagr⟩ := hs.cka_step P heq_other
        have hcT : c.1.2 = some T_t := by
          rw [← hct, hTcur (by rw [hsnd]; omega), hsnd, hT_other]
        have hcache' : es.h.cache c.1.1 = some (T_t, I_t) := by rwa [hstep, heq_other]
        obtain ⟨hrcvL, hrcvR⟩ :=
          vRecv_new_honest cka prng fs Δcka tL tStar (rec := some r) hs hnsend hstep hcT hcache' hI
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
          have hcom := commitE_new cka prng fs Δcka tL tStar
            (prng.up (es.g.st P).root I_t).1
            (Function.update (es.g.st P).vR c.1.1 (some v'))
            hs hpos_ep heq_other T_t hl_msg
          have hsync := hs.sync9_accept_new
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
          vRecv_same_epoch cka prng fs Δcka tL tStar (rec := some r) hs hnsend hle_P
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
            have hcom := commitE_same cka prng fs Δcka tL tStar
              (P := P)
              (new := { es.g.st P with vR := Function.update (es.g.st P).vR c.1.1 (some v') })
              (pos := r.pos) (es := es) (sc := sc) rfl
            have hsync := hs.sync9_accept_same
              (Function.update (es.g.st P).vR c.1.1 (some v')) hpos_le
            simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
              simulateQ_bind, hcom, StateT.run_modify, simulateQ_pure, hch_eq]
            exact ih _ hsync

theorem step_inject_DFPaper {α : Type} (P : Party) (c : Header T × E)
    (k : (ASpecDF).Range (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar s es sc)
    (ih : ∀ u {s' es' sc'}, Sync9 cka Δcka tL tStar s' es' sc' →
      𝒟[runLDFPaper cka prng fs lam Δcka qep tL tStar (k u) s'] =
        𝒟[runRDFPaper cka prng fs Δcka qep tL tStar (k u) es' sc']) :
    𝒟[runLDFPaper cka prng fs lam Δcka qep tL tStar
        (query (spec := ASpecDF) (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) >>= k) s] =
      𝒟[runRDFPaper cka prng fs Δcka qep tL tStar
        (query (spec := ASpecDF) (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) >>= k) es sc] := by
  rw [runLDFPaper_query_bind, runRDFPaper_query_bind]
  dsimp only [QueryImpl.add_apply, fullImplBaseDFPaper, oracleImplBaseDFPaper, oracleImplPaper,
    implEDFPaper, injectImpl, injectE, Config.auth]
  have hwin : s.win = es.g.win := by rw [hs.s_eq]; rfl
  have hin_eq : s.inTransit P.other c = es.g.inTransit P.other c := by rw [hs.s_eq]; rfl
  have hsafe_eq : s.safeInj (2 + Δcka) = es.g.safeInj (2 + Δcka) := by rw [hs.s_eq]; rfl
  have htriv_eq : ∀ pos, s.trivial (2 + Δcka) pos = es.g.trivial (2 + Δcka) pos :=
    fun pos => by rw [hs.s_eq]; rfl
  simp only [hs.no_abort, Bool.false_or, hwin, hin_eq, hsafe_eq,
    StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hcond :
      (es.g.win || (es.g.inTransit P.other c).isSome || !es.g.safeInj (2 + Δcka)) = true
  · simp [hcond, ih none hs]
  · simp only [hcond, Bool.false_eq_true, ↓reduceIte]
    have hsafe : es.g.safeInj (2 + Δcka) = true := by
      cases h : es.g.safeInj (2 + Δcka)
      · simp [h] at hcond
      · rfl
    by_cases hguard : (P.sendsIn c.1.1 || decide (es.g.epoch P + 1 < c.1.1)) = true
    · obtain ⟨hrcvL, hrcvR⟩ :=
        vRecv_guard_true cka prng fs Δcka tL tStar (rec := none) hs hguard
      dsimp only [scheme]
      rw [hrcvL, StateT.run_bind, hrcvR]
      simp [ih (some .rejected) hs]
    · have hnsend : P.sendsIn c.1.1 = false := by
        cases h : P.sendsIn c.1.1
        · rfl
        · simp [h] at hguard
      have hle_P1 : c.1.1 ≤ es.g.epoch P + 1 := by
        simp [hnsend] at hguard
        omega
      by_cases hstep : c.1.1 = es.g.epoch P + 1
      · have htriv_f : ∀ i', es.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = false := by
          intro i'
          exact hs.trivial_false_of_safeInj (P := P) hsafe (by dsimp; omega)
        cases hc2 : c.1.2 with
        | none =>
          obtain ⟨hrcvL, hrcvR⟩ :=
            vRecv_new_none cka prng fs Δcka tL tStar (rec := none) hs hnsend hstep hc2
          dsimp only [scheme]
          rw [hrcvL, StateT.run_bind, hrcvR]
          simp [ih (some .rejected) hs]
        | some Tn =>
          by_cases hhon_ex : ∃ I_t, es.h.cache c.1.1 = some (Tn, I_t)
          · rcases hhon_ex with ⟨I_t, hcache'⟩
            have hle_max : c.1.1 ≤ max (es.g.epoch .A) (es.g.epoch .B) := by
              by_contra hgt
              have hnone := hs.cache_gt c.1.1 (by omega)
              rw [hnone] at hcache'
              nomatch hcache'
            have heq_other : es.g.epoch P + 1 = es.g.epoch P.other := by
              have hle2 := hs.epoch_le P.other
              rw [Party.other_other] at hle2
              cases P <;> simp [Party.other] at hle_max hstep hle2 ⊢ <;> omega
            obtain ⟨T_t, I_t', hcache_step, _, _, hI, _⟩ := hs.cka_step P heq_other
            rw [← heq_other, ← hstep, hcache'] at hcache_step
            injection hcache_step with hpair
            injection hpair with hT_eq hI_eq
            subst hT_eq hI_eq
            obtain ⟨hrcvL, hrcvR⟩ :=
              vRecv_new_honest cka prng fs Δcka tL tStar (rec := none)
                hs hnsend hstep hc2 hcache' hI
            dsimp only [scheme]
            rw [hrcvL, StateT.run_bind, hrcvR]
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
                  exact ih (some .rejected) (hs.sync9_win true)
                · simp [hfull, ih (some .rejected) hs]
          · have hhon : ∀ Tc Ik, es.h.cache c.1.1 = some (Tc, Ik) → Tc ≠ Tn := by
              intro Tc Ik hc heq
              subst heq
              exact hhon_ex ⟨Ik, hc⟩
            by_cases htStar : c.1.1 = tStar
            · by_cases hloc : isLocal tL Δcka (es.g.epoch P) = true
              · obtain ⟨hrcvL, hrcvR⟩ :=
                  vRecv_new_dishonest_tStar_local cka prng fs Δcka tL tStar (rec := none)
                    hs hnsend hstep hc2 hhon htStar hloc
                dsimp only [scheme]
                rw [hrcvL, StateT.run_bind, hrcvR]
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
                    exact ih (some .rejected) (hs.sync9_win true)
              · have hloc_f : isLocal tL Δcka (es.g.epoch P) = false :=
                  Bool.eq_false_iff.mpr hloc
                have hd4 : Doomed4 tL s := by
                  rcases hs.doomed4_or_local_of_safeInj_tStar (P := P) hsafe (by omega) with h | hd4
                  · exact False.elim (hloc h)
                  · exact hd4
                have hrcvR :=
                  vRecv_new_dishonest_tStar_nonlocal cka prng fs Δcka tL tStar (rec := none)
                    hs hnsend hstep hc2 hhon htStar hloc_f
                rw [StateT.run_bind, hrcvR]
                simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify,
                  StateT.run_pure, simulateQ_pure]
                have hR : 𝒟[runRDFPaper cka prng fs Δcka qep tL tStar (k none)
                    { es with abort := true } sc] = 𝒟[(pure false : ProbComp Bool)] :=
                  evalDist_runRDFPaper_eq_pure_false_of_abort cka prng fs Δcka qep tL tStar
                    (k none) { es with abort := true } sc rfl
                have hdoom : DoomedAuth tL tStar s := Or.inr (Or.inr (Or.inr hd4))
                have hrun : 𝒟[runLDFPaper cka prng fs lam Δcka qep tL tStar
                    (query (spec := ASpecDF)
                      (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) >>= k) s] =
                    𝒟[(pure false : ProbComp Bool)] :=
                  evalDist_runLDFPaper_eq_pure_false_of_doomed cka prng fs lam Δcka qep tL tStar
                    (query (spec := ASpecDF)
                      (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) >>= k) s hdoom
                rw [runLDFPaper_query_bind] at hrun
                dsimp only [QueryImpl.add_apply, fullImplBaseDFPaper, oracleImplBaseDFPaper,
                  oracleImplPaper, injectImpl, Config.auth] at hrun
                simp only [hwin, hin_eq, hsafe_eq, StateT.run_bind, StateT.run_get, pure_bind,
                  hcond, Bool.false_eq_true, ↓reduceIte] at hrun
                exact hrun.trans hR.symm
            · have hrcvR :=
                vRecv_new_dishonest_ne cka prng fs Δcka tL tStar (rec := none)
                  hs hnsend hstep hc2 hhon htStar
              rw [StateT.run_bind, hrcvR]
              simp only [pure_bind, StateT.run_pure, simulateQ_pure]
              dsimp only [scheme]
              cases hrcvL : receive cka prng fs (s.st P) c with
              | none =>
                simp [ih (some .rejected) hs]
              | some res =>
                rcases res with ⟨st', t', i', m'⟩
                have ht' : t' = c.1.1 := receive_t_eq cka prng fs hrcvL
                subst ht'
                have hfull : (c.1.1 == tStar) = false := beq_false_of_ne htStar
                simp only [htriv_eq, htriv_f, hfull, Bool.false_eq_true, ↓reduceIte]
                by_cases hqep : qep + 1 < c.1.1 <;> simp [hqep, ih (some .rejected) hs]
      · have hle_P : c.1.1 ≤ es.g.epoch P := by omega
        obtain ⟨hrcvL, hrcvR⟩ :=
          vRecv_same_epoch cka prng fs Δcka tL tStar (rec := none) hs hnsend hle_P
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
            simp only []
            by_cases hqep : qep + 1 < c.1.1
            · simp [hqep, ih (some .rejected) hs]
            · simp only [hqep, ↓reduceIte, htriv_eq]
              by_cases htriv : es.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = true
              · have hcom := commitE_same cka prng fs Δcka tL tStar
                  (P := P)
                  (new := { es.g.st P with vR := Function.update (es.g.st P).vR c.1.1 (some v') })
                  (pos := ⟨P.other, c.1.1, i'⟩) (es := es) (sc := sc) rfl
                have hsync := hs.sync9_accept_same
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
                  exact ih (some .rejected) (hs.sync9_win true)
                · simp [hfull, ih (some .rejected) hs]

theorem step_transmit_DFPaper {α : Type} (P : Party) (m : M) (r : Option CCoins)
    (k : (ASpecDF).Range
      (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (P, m, r))))))) →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar s es sc)
    (ih : ∀ u {s' es' sc'}, Sync9 cka Δcka tL tStar s' es' sc' →
      𝒟[runLDFPaper cka prng fs lam Δcka qep tL tStar (k u) s'] =
        𝒟[runRDFPaper cka prng fs Δcka qep tL tStar (k u) es' sc']) :
    𝒟[runLDFPaper cka prng fs lam Δcka qep tL tStar
        (query (spec := ASpecDF)
          (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (P, m, r))))))) >>= k) s] =
      𝒟[runRDFPaper cka prng fs Δcka qep tL tStar
        (query (spec := ASpecDF)
          (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (P, m, r))))))) >>= k) es sc] := by
  rw [runLDFPaper_query_bind, runRDFPaper_query_bind]
  dsimp only [QueryImpl.add_apply, fullImplBaseDFPaper, oracleImplBaseDFPaper, oracleImplPaper,
    implEDFPaper]
  by_cases hw : es.g.win = true
  · have hwin : s.win = true := by rw [hs.s_eq]; exact hw
    dsimp only [transmitImpl, transmitE]
    simp [hs.no_abort, hw, hwin, ih none hs]
  · have hw_f : es.g.win = false := Bool.eq_false_iff.mpr hw
    rw [transmitImpl_run_eq cka prng fs lam Δcka qep tL tStar hs hw_f]
    dsimp only [transmitE]
    simp only [hs.no_abort, hw_f, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, StateT.run_get, pure_bind, bind_assoc]
    cases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with
    | none =>
      simp only [pure_bind, StateT.run_pure, simulateQ_pure, OracleComp.evalDist_bind_const]
      exact ih none hs
    | some s₁ =>
      have hs₁_st : s₁.st = es.g.st := by
        unfold GameState.epMgmt at hep
        split_ifs at hep <;> (injection hep with hep; subst hep; simp [GameState.leak])
      simp only []
      by_cases hld : (Policy.mk true tL tStar).leakDoom es.g s₁ = true
      · simp only [hld, ↓reduceIte, abortE, StateT.run_bind, StateT.run_modify, pure_bind,
          StateT.run_pure, simulateQ_pure]
        have hR : 𝒟[runRDFPaper cka prng fs Δcka qep tL tStar (k none)
            { es with abort := true } sc] = 𝒟[(pure false : ProbComp Bool)] :=
          evalDist_runRDFPaper_eq_pure_false_of_abort cka prng fs Δcka qep tL tStar
            (k none) { es with abort := true } sc rfl
        rw [hR]
        refine evalDist_bind_eq_pure_false _ _ fun coins _ => ?_
        have hdoom := hs.doomed_of_leakDoom_epMgmt hw_f hep hld
          (send cka prng fs (s.st P) m coins).1 m (send cka prng fs (s.st P) m coins).2 false
        exact evalDist_runLDFPaper_eq_pure_false_of_doomed cka prng fs lam Δcka qep tL tStar
          (k (some (send cka prng fs (s.st P) m coins).2)) _ hdoom
      · simp only [hld, Bool.false_eq_true, ↓reduceIte, hs₁_st]
        have hld_f : (Policy.mk true tL tStar).leakDoom es.g s₁ = false :=
          Bool.eq_false_iff.mpr hld
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
            send_new_eq cka prng fs Δcka tL tStar (m := m) (coins := coins) hs hsend
          dsimp only at hsend_eq
          by_cases hloc : isLocal tL Δcka (es.g.epoch P) = true
          · have hvR := vSend_new_local cka prng fs Δcka tL tStar (m := m) (r := r) (s₁ := s₁)
              hs hsend hloc
            rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, hvR]
            simp only [bind_assoc, pure_bind, hs₁_ep, hs₁_idx]
            refine evalDist_bind_congr _ _ _ fun coins => ?_
            rw [hsend_eq coins]
            exact ih _ (hs.sync9_send_new prng fs hsend hep coins m false)
          · have hloc_f : isLocal tL Δcka (es.g.epoch P) = false :=
              Bool.eq_false_iff.mpr hloc
            obtain ⟨l, htL⟩ : ∃ l, tL = some l := by
              cases h : tL
              · simp [isLocal, h] at hloc_f
              · exact ⟨_, rfl⟩
            have hloc' : es.g.epoch P < l + 2 + Δcka := by
              simpa [isLocal, htL] using hloc_f
            cases r with
            | none =>
              have hvR := vSend_new_nonlocal_none cka prng fs Δcka tL tStar
                (m := m) (s₁ := s₁) hs hsend hloc_f
              rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, hvR]
              simp only [bind_assoc, pure_bind, hs₁_ep, hs₁_idx]
              refine evalDist_bind_congr _ _ _ fun coins => ?_
              rw [hsend_eq coins]
              exact ih _ (hs.sync9_send_new prng fs hsend hep coins m false)
            | some coins =>
              by_cases hle : es.g.epoch P + 1 ≤ l
              · have hvR := vSend_new_nonlocal_some_le cka prng fs Δcka tL tStar
                  (m := m) (coins := coins) (s₁ := s₁) hs htL hsend hle
                rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, hvR]
                simp only [pure_bind, hs₁_ep, hs₁_idx]
                rw [hsend_eq coins]
                exact ih _ (hs.sync9_send_new prng fs hsend hep coins m false)
              · have hgt : l < es.g.epoch P + 1 := by omega
                have hvR := vSend_new_nonlocal_some_gt cka prng fs Δcka tL tStar
                  (m := m) (coins := coins) (s₁ := s₁) hs htL hsend hloc_f hgt
                rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, hvR]
                simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify,
                  StateT.run_pure, simulateQ_pure]
                have hR : 𝒟[runRDFPaper cka prng fs Δcka qep tL tStar (k none)
                    { es with abort := true } sc] = 𝒟[(pure false : ProbComp Bool)] :=
                  evalDist_runRDFPaper_eq_pure_false_of_abort cka prng fs Δcka qep tL tStar
                    (k none) { es with abort := true } sc rfl
                have hdoom := hs.doomed4_of_sendBad_gt htL hloc' hsend hep hld_f hgt
                  (send cka prng fs (s.st P) m coins).1 m
                  (send cka prng fs (s.st P) m coins).2 false
                have hL : 𝒟[runLDFPaper cka prng fs lam Δcka qep tL tStar
                    (k (some (send cka prng fs (s.st P) m coins).2))
                    ((realGS sc s₁).record (2 + Δcka) P (send cka prng fs (s.st P) m coins).1
                      ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m,
                        (send cka prng fs (s.st P) m coins).2⟩ false)] =
                    𝒟[(pure false : ProbComp Bool)] :=
                  evalDist_runLDFPaper_eq_pure_false_of_doomed cka prng fs lam Δcka qep tL tStar
                    (k (some (send cka prng fs (s.st P) m coins).2)) _ hdoom
                exact hL.trans hR.symm
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
            vSend_same_epoch cka prng fs Δcka tL tStar (m := m) (r := r) hs hnsend
          have hreal_eq : realGS sc es.g = s := hs.s_eq.symm
          rw [StateT.run_bind, hsendR]
          simp only [hsendL, hreal_eq, pure_bind, OracleComp.evalDist_bind_const]
          exact ih _ (hs.sync9_send_same hnsend _ m _ false)

theorem step_deliverForge_DFPaper {α : Type} (P : Party) (c c' : Header T × E)
    (k : (ASpecDF).Range (Sum.inr (Sum.inr (P, c, c'))) →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar s es sc)
    (ih : ∀ u {s' es' sc'}, Sync9 cka Δcka tL tStar s' es' sc' →
      𝒟[runLDFPaper cka prng fs lam Δcka qep tL tStar (k u) s'] =
        𝒟[runRDFPaper cka prng fs Δcka qep tL tStar (k u) es' sc']) :
    𝒟[runLDFPaper cka prng fs lam Δcka qep tL tStar
        (query (spec := ASpecDF) (Sum.inr (Sum.inr (P, c, c'))) >>= k) s] =
      𝒟[runRDFPaper cka prng fs Δcka qep tL tStar
        (query (spec := ASpecDF) (Sum.inr (Sum.inr (P, c, c'))) >>= k) es sc] := by
  rw [runLDFPaper_query_bind, runRDFPaper_query_bind]
  dsimp only [QueryImpl.add_apply, fullImplBaseDFPaper, oracleImplBaseDFPaper, implEDFPaper,
    deliverForgeBaseImpl, deliverForgeE, sameHdrScheme, Config.auth]
  have hwin : s.win = es.g.win := by rw [hs.s_eq]; rfl
  have hin_eq : s.inTransit P.other c = es.g.inTransit P.other c := by rw [hs.s_eq]; rfl
  have hin'_eq : s.inTransit P.other c' = es.g.inTransit P.other c' := by rw [hs.s_eq]; rfl
  have hcomp_eq : ∀ pos, s.comp.contains pos = es.g.comp.contains pos :=
    fun pos => by rw [hs.s_eq]; rfl
  have htriv_eq : ∀ pos, s.trivial (2 + Δcka) pos = es.g.trivial (2 + Δcka) pos :=
    fun pos => by rw [hs.s_eq]; rfl
  have hbne : (!(c.1 == c'.1)) = (c.1 != c'.1) := rfl
  simp only [hs.no_abort, Bool.false_or, hwin, hin_eq, hin'_eq, hcomp_eq, hbne,
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
        obtain ⟨hmem, hsnd, hct⟩ := mem_trans_of_inTransit hin
        obtain ⟨ht_ep, hsnd_sends, hle_snd, hTcur⟩ := hs.trans_inv r hmem
        have hpos_c : r.pos.epoch = c'.1.1 := by rw [hhdr, ← hct, ht_ep]
        have hnsend : P.sendsIn c'.1.1 = false := by
          have h1 : P.other.sendsIn c'.1.1 = true := by
            rw [← hpos_c, ← hsnd]
            exact hsnd_sends
          rw [sendsIn_other, Bool.not_eq_true'] at h1
          exact h1
        have hle_other : c'.1.1 ≤ es.g.epoch P.other := by
          rw [← hpos_c, ← hsnd]
          exact hle_snd
        have hle_P1 : c'.1.1 ≤ es.g.epoch P + 1 := by
          have hle2 := hs.epoch_le P.other
          rw [Party.other_other] at hle2
          omega
        by_cases hstep : c'.1.1 = es.g.epoch P + 1
        · have heq_other : es.g.epoch P + 1 = es.g.epoch P.other :=
            hs.epoch_eq_of_deliver_step hmem hsnd (by rw [hct, ← hhdr]; exact hstep)
          obtain ⟨T_t, I_t, hcache, hT_other, hl_msg, hI, hagr⟩ := hs.cka_step P heq_other
          have hcT : c'.1.2 = some T_t := by
            rw [hhdr, ← hct, hTcur (by rw [hsnd]; omega), hsnd, hT_other]
          have hcache' : es.h.cache c'.1.1 = some (T_t, I_t) := by rwa [hstep, heq_other]
          obtain ⟨hrcvL, hrcvR⟩ :=
            vRecv_new_honest cka prng fs Δcka tL tStar (rec := none) hs hnsend hstep hcT hcache' hI
          dsimp only [scheme]
          rw [hrcvL, StateT.run_bind, hrcvR]
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
              by_cases htriv : es.g.trivial (2 + Δcka) ⟨P.other, c'.1.1, i'⟩ = true
              · have hcom := commitE_new cka prng fs Δcka tL tStar
                  (pos := ⟨P.other, c'.1.1, i'⟩)
                  (prng.up (es.g.st P).root I_t).1
                  (Function.update (es.g.st P).vR c'.1.1 (some v'))
                  hs hstep heq_other T_t hl_msg
                have hsync := hs.sync9_accept_new
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
                  exact ih (some .rejected) (hs.sync9_win true)
                · simp [hfull, ih (some .rejected) hs]
        · have hle_P : c'.1.1 ≤ es.g.epoch P := by omega
          obtain ⟨hrcvL, hrcvR⟩ :=
            vRecv_same_epoch cka prng fs Δcka tL tStar (rec := none) hs hnsend hle_P
          dsimp only [scheme]
          rw [hrcvL, StateT.run_bind, hrcvR]
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
                by_cases htriv : es.g.trivial (2 + Δcka) ⟨P.other, c'.1.1, i'⟩ = true
                · have hcom := commitE_same cka prng fs Δcka tL tStar
                    (P := P)
                    (new :=
                      { es.g.st P with vR := Function.update (es.g.st P).vR c'.1.1 (some v') })
                    (pos := ⟨P.other, c'.1.1, i'⟩) (es := es) (sc := sc) rfl
                  have hsync := hs.sync9_accept_same
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
                    exact ih (some .rejected) (hs.sync9_win true)
                  · simp [hfull, ih (some .rejected) hs]

theorem runLDFPaper_eq_runRDFPaper_of_sync {α : Type}
    (oa : AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar s es sc) :
    𝒟[runLDFPaper cka prng fs lam Δcka qep tL tStar oa s] =
      𝒟[runRDFPaper cka prng fs Δcka qep tL tStar oa es sc] := by
  induction oa using OracleComp.inductionOn generalizing s es sc with
  | pure a =>
    rw [runLDFPaper_pure, runRDFPaper_pure]
    have hwin : s.win = es.g.win := by rw [hs.s_eq]; rfl
    have hok : authLosingConditionsAvoided (2 + Δcka) tL tStar s = authLosingConditionsAvoided (2 + Δcka) tL tStar es.g := by
      rw [hs.s_eq]; rfl
    simp [authOut, hs.no_abort, hwin, hok]
  | query_bind t k ih =>
    rcases t with n | (((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩)
    · exact step_coins_DFPaper cka prng fs lam Δcka qep tL tStar n k hs @ih
    · exact step_transmit_DFPaper cka prng fs lam Δcka qep tL tStar P m r k hs @ih
    · exact step_chall_DFPaper cka prng fs lam Δcka qep tL tStar P m₀ m₁ r k hs @ih
    · exact step_deliver_DFPaper cka prng fs lam Δcka qep tL tStar P c k hs @ih
    · exact step_inject_DFPaper cka prng fs lam Δcka qep tL tStar P c k hs @ih
    · exact step_corr_DFPaper cka prng fs lam Δcka qep tL tStar P k hs @ih
    · exact step_deliverForge_DFPaper cka prng fs lam Δcka qep tL tStar P c c' k hs @ih

omit [DecidableEq I] [SampleableType I] [SampleableType K] in
theorem forgeGameGuessedPaper_eq_runLDFPaper (t : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    forgeGameGuessedPaper (scheme cka prng fs lam) (2 + Δcka) qep sameHdrScheme tL t A =
      ($ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
        runLDFPaper cka prng fs lam Δcka qep tL t A
          (initState (scheme cka prng fs lam) (kr, kc) false)) := by
  unfold forgeGameGuessedPaper runBaseDFPaper runLDFPaper
  simp only [uniformSample, SampleableType.selectElem, seq_eq_bind_map, map_eq_bind_pure_comp,
    Function.comp_apply, pure_bind, bind_assoc]

/-- Bounds `forgeGuessedAdvantagePaper` at `(tL, t)` by the real-world CKA branch of
`redCKAAuthDFPaper`. -/
theorem lemma9_df_paper (hc : cka.Correct) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    forgeGuessedAdvantagePaper (scheme cka prng fs lam) (2 + Δcka) qep sameHdrScheme tL t A ≤
      𝒟[CKA.branch cka Δcka (healEpoch tL) false
        (redCKAAuthDFPaper cka prng fs lam Δcka qep tL t A)] {true} := by
  by_cases hvg : lastLeakGuessAdmissible (2 + Δcka) tL t = true
  · apply le_of_eq
    unfold forgeGuessedAdvantagePaper
    rw [forgeGameGuessedPaper_eq_runLDFPaper]
    congr 1
    cases htL : tL with
    | none =>
      subst htL
      unfold CKA.branch redCKAAuthDFPaper authSimDFPaper engRunDFPaper initCKA
      simp only [StateT.run'_eq, StateT.run_bind, StateT.run_lift, StateT.run_pure,
        pure_bind, bind_assoc, simulateQ_bind, simulateQ_pure, simulateQ_sampleT_run,
        map_bind]
      symm
      refine (evalDist_bind_congr ($ᵗ KC) _
        (fun _ => $ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
          runLDFPaper cka prng fs lam Δcka qep none t A
            (initState (scheme cka prng fs lam) (kr, kc) false)) ?_).trans ?_
      · intro kc_ext
        refine evalDist_bind_congr _ _ _ fun kr => ?_
        refine evalDist_bind_congr _ _ _ fun kc => ?_
        symm
        refine (runLDFPaper_eq_runRDFPaper_of_sync cka prng fs lam Δcka qep none t A
          (sync9_init_none cka prng fs lam Δcka t hc hvg kr kc kc_ext)).trans ?_
        simp only [runRDFPaper, bind_pure_comp, map_pure]
        rfl
      · exact OracleComp.evalDist_bind_const ($ᵗ KC) _
    | some l =>
      subst htL
      unfold CKA.branch redCKAAuthDFPaper authSimDFPaper engRunDFPaper initCKA
      simp only [StateT.run'_eq, StateT.run_bind, StateT.run_lift, StateT.run_pure,
        pure_bind, bind_assoc, simulateQ_bind, simulateQ_pure, simulateQ_sampleT_run,
        map_bind]
      rw [OracleComp.evalDist_bind_bind_swap ($ᵗ KR) ($ᵗ KC)]
      refine evalDist_bind_congr _ _ _ fun kc => ?_
      refine evalDist_bind_congr _ _ _ fun kr => ?_
      refine (runLDFPaper_eq_runRDFPaper_of_sync cka prng fs lam Δcka qep (some l) t A
        (Sync9.sync9_init prng fs lam hc hvg kr kc)).trans ?_
      simp only [runRDFPaper, bind_pure_comp, map_pure]
      rfl
  · have hvg_f : lastLeakGuessAdmissible (2 + Δcka) tL t = false := Bool.eq_false_iff.mpr hvg
    have hzero :
        forgeGuessedAdvantagePaper (scheme cka prng fs lam) (2 + Δcka) qep sameHdrScheme tL t A =
          0 := by
      unfold forgeGuessedAdvantagePaper forgeGameGuessedPaper
      simp only []
      refine evalDist_true_eq_zero_of_support _ _ fun res _ => ?_
      simp [authLosingConditionsAvoided, hvg_f]
    rw [hzero]
    exact zero_le

end CryptoGames.SM.Construction.DeliverForge.AuthL9DF

namespace CryptoGames.SM.Construction.DeliverForge.AuthL10DF

open CryptoGames.SM CryptoGames.SM.Engine CryptoGames.SM.Construction.AuthL10

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

variable (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)

def stepCDFPaper (mo : Mode)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esC : EStateC Γ T Sig SS RS M E I) (sc : CKA.GameState Γ T) :
    ProbComp (((SMSpecDF Γ T Sig SS RS M CCoins E).Range q ×
      EStateC Γ T Sig SS RS M E I) × CKA.GameState Γ T) :=
  (simulateQ (cImpl cka Δcka mo.tH)
    ((implEDFPaper (hooksCKA cka prng fs Δcka mo) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy q).run
      esC)).run sc

def stepPDFPaper (mo : Mode)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) :
    ProbComp (((SMSpecDF Γ T Sig SS RS M CCoins E).Range q ×
      EStateP Γ T Sig SS RS M E K) × PRFPRNG.GameState Sig I K) :=
  (simulateQ (pImpl prng)
    ((implEDFPaper (hooksPRNG cka prng fs mo) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy q).run
      esP)).run sp

def runLDFPaper (mo : Mode) (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esC : EStateC Γ T Sig SS RS M E I) (sc : CKA.GameState Γ T) : ProbComp Bool := do
  let r ← (simulateQ (cImpl cka Δcka mo.tH)
    ((simulateQ
      (implEDFPaper (hooksCKA cka prng fs Δcka mo) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy)
      oa).run esC)).run sc
  pure (authOut (2 + Δcka) mo.policy r.1.2)

def runRDFPaper (mo : Mode) (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) : ProbComp Bool := do
  let r ← (simulateQ (pImpl prng)
    ((simulateQ
      (implEDFPaper (hooksPRNG cka prng fs mo) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy)
      oa).run esP)).run sp
  pure (authOut (2 + Δcka) mo.policy r.1.2)

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem runLDFPaper_pure (mo : Mode) (b' : Bool) (esC : EStateC Γ T Sig SS RS M E I)
    (sc : CKA.GameState Γ T) :
    runLDFPaper cka prng fs Δcka qep mo (pure b') esC sc =
      pure (authOut (2 + Δcka) mo.policy esC) := by
  simp [runLDFPaper, map_eq_bind_pure_comp]

omit [SampleableType KR] [SampleableType KC] in
theorem runRDFPaper_pure (mo : Mode) (b' : Bool) (esP : EStateP Γ T Sig SS RS M E K)
    (sp : PRFPRNG.GameState Sig I K) :
    runRDFPaper cka prng fs Δcka qep mo (pure b') esP sp =
      pure (authOut (2 + Δcka) mo.policy esP) := by
  simp [runRDFPaper, map_eq_bind_pure_comp]

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem runLDFPaper_query_bind (mo : Mode)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (k : (SMSpecDF Γ T Sig SS RS M CCoins E).Range q → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esC : EStateC Γ T Sig SS RS M E I) (sc : CKA.GameState Γ T) :
    runLDFPaper cka prng fs Δcka qep mo (liftM (OracleSpec.query q) >>= k) esC sc =
      stepCDFPaper cka prng fs Δcka qep mo q esC sc >>= fun r =>
        runLDFPaper cka prng fs Δcka qep mo (k r.1.1) r.1.2 r.2 := by
  simp [runLDFPaper, stepCDFPaper, simulateQ_bind, StateT.run_bind, map_eq_bind_pure_comp,
    bind_assoc]

omit [SampleableType KR] [SampleableType KC] in
theorem runRDFPaper_query_bind (mo : Mode)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (k : (SMSpecDF Γ T Sig SS RS M CCoins E).Range q → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) :
    runRDFPaper cka prng fs Δcka qep mo (liftM (OracleSpec.query q) >>= k) esP sp =
      stepPDFPaper cka prng fs Δcka qep mo q esP sp >>= fun r =>
        runRDFPaper cka prng fs Δcka qep mo (k r.1.1) r.1.2 r.2 := by
  simp [runRDFPaper, stepPDFPaper, simulateQ_bind, StateT.run_bind, map_eq_bind_pure_comp,
    bind_assoc]

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
@[simp]
theorem stepCDFPaper_coins (mo : Mode) (n : unifSpec.Domain)
    (esC : EStateC Γ T Sig SS RS M E I) (sc : CKA.GameState Γ T) :
    stepCDFPaper cka prng fs Δcka qep mo (.inl n) esC sc =
      stepC cka prng fs Δcka qep mo (.inl n) esC sc := rfl

omit [SampleableType KR] [SampleableType KC] in
@[simp]
theorem stepPDFPaper_coins (mo : Mode) (n : unifSpec.Domain)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) :
    stepPDFPaper cka prng fs Δcka qep mo (.inl n) esP sp =
      stepP cka prng fs Δcka qep mo (.inl n) esP sp := rfl

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
@[simp]
theorem stepCDFPaper_deliverForge (mo : Mode)
    (df : Party × (Header T × E) × (Header T × E))
    (esC : EStateC Γ T Sig SS RS M E I) (sc : CKA.GameState Γ T) :
    stepCDFPaper cka prng fs Δcka qep mo (.inr (.inr df)) esC sc =
      stepCDF cka prng fs Δcka qep mo (.inr (.inr df)) esC sc := rfl

omit [SampleableType KR] [SampleableType KC] in
@[simp]
theorem stepPDFPaper_deliverForge (mo : Mode)
    (df : Party × (Header T × E) × (Header T × E))
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) :
    stepPDFPaper cka prng fs Δcka qep mo (.inr (.inr df)) esP sp =
      stepPDF cka prng fs Δcka qep mo (.inr (.inr df)) esP sp := rfl

theorem stepCDFPaper_abort (mo : Mode)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esC : EStateC Γ T Sig SS RS M E I) (sc : CKA.GameState Γ T) (hab : esC.abort = true) :
    ∀ r ∈ support (stepCDFPaper cka prng fs Δcka qep mo q esC sc), r.1.2.abort = true := by
  intro r hr
  rcases q with n | ((q14 | P) | ⟨P, c, c'⟩)
  · exact stepC_abort cka prng fs Δcka qep mo (.inl n) esC sc hab r hr
  · exact stepC_abort cka prng fs Δcka qep mo (.inr (.inl q14)) esC sc hab r hr
  · simp only [stepCDFPaper, implEDFPaper, QueryImpl.add_apply, corrEPaper, StateT.run_bind,
      StateT.run_get, pure_bind, hab, Bool.true_or, ↓reduceIte, StateT.run_pure, simulateQ_pure,
      support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact hab
  · exact stepCDF_abort cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esC sc hab r hr

theorem runLDFPaper_abort (mo : Mode) (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T} (hab : esC.abort = true) :
    𝒟[runLDFPaper cka prng fs Δcka qep mo oa esC sc] = 𝒟[(pure false : ProbComp Bool)] := by
  induction oa using OracleComp.inductionOn generalizing esC sc with
  | pure b' =>
    rw [runLDFPaper_pure]
    simp [authOut, hab]
  | query_bind q k ih =>
    rw [runLDFPaper_query_bind]
    exact evalDist_bind_false_of_support _ _ fun r hr =>
      ih r.1.1 (stepCDFPaper_abort cka prng fs Δcka qep mo q esC sc hab r hr)

theorem runLDFPaper_abort_apply_true_le (mo : Mode) (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T} (hab : esC.abort = true)
    (rhs : ℝ≥0∞) :
    𝒟[runLDFPaper cka prng fs Δcka qep mo oa esC sc] {true} ≤ rhs := by
  rw [runLDFPaper_abort cka prng fs Δcka qep mo oa hab]
  simp

theorem step_coinsE_DFPaper_le (mo : Mode) (n : unifSpec.Domain)
    (k : (SMSpec Γ T Sig SS RS M CCoins E).Range (.inl n) → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp)
    (ih : ∀ u {esC' sc' esP' sp'}, Sync prng Δcka mo esC' sc' esP' sp' →
      𝒟[runLDFPaper cka prng fs Δcka qep mo (k u) esC' sc'] {true} ≤
        𝒟[runRDFPaper cka prng fs Δcka qep mo (k u) esP' sp'] {true}) :
    𝒟[stepC cka prng fs Δcka qep mo (.inl n) esC sc >>= fun r =>
        runLDFPaper cka prng fs Δcka qep mo (k r.1.1) r.1.2 r.2] {true} ≤
      𝒟[stepP cka prng fs Δcka qep mo (.inl n) esP sp >>= fun r =>
        runRDFPaper cka prng fs Δcka qep mo (k r.1.1) r.1.2 r.2] {true} := by
  rw [stepC_coinsE, stepP_coinsE, bind_map_left, bind_map_left]
  exact OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
    fun u _ => ih u hS

theorem step_challE_DFPaper_le (mo : Mode) (hauth : mo.auth = true)
    (q : Party × M × M × Option CCoins)
    (k : Option (Header T × E) → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp)
    (ih : ∀ u {esC' sc' esP' sp'}, Sync prng Δcka mo esC' sc' esP' sp' →
      𝒟[runLDFPaper cka prng fs Δcka qep mo (k u) esC' sc'] {true} ≤
        𝒟[runRDFPaper cka prng fs Δcka qep mo (k u) esP' sp'] {true}) :
    𝒟[stepC cka prng fs Δcka qep mo (.inr (.inl (.inl (.inl (.inr q))))) esC sc >>= fun r =>
        runLDFPaper cka prng fs Δcka qep mo (k r.1.1) r.1.2 r.2] {true} ≤
      𝒟[stepP cka prng fs Δcka qep mo (.inr (.inl (.inl (.inl (.inr q))))) esP sp >>= fun r =>
        runRDFPaper cka prng fs Δcka qep mo (k r.1.1) r.1.2 r.2] {true} := by
  rw [stepC_challE cka prng fs Δcka qep mo hauth, stepP_challE cka prng fs Δcka qep mo hauth,
    pure_bind, pure_bind]
  exact ih none hS

theorem step_corrE_DFPaper_le (mo : Mode) (hauth : mo.auth = true) (P : Party)
    (k : Option (PartyState Γ T Sig SS RS) → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp)
    (ih : ∀ u {esC' sc' esP' sp'}, Sync prng Δcka mo esC' sc' esP' sp' →
      𝒟[runLDFPaper cka prng fs Δcka qep mo (k u) esC' sc'] {true} ≤
        𝒟[runRDFPaper cka prng fs Δcka qep mo (k u) esP' sp'] {true}) :
    𝒟[stepCDFPaper cka prng fs Δcka qep mo (.inr (.inl (.inr P))) esC sc >>= fun r =>
        runLDFPaper cka prng fs Δcka qep mo (k r.1.1) r.1.2 r.2] {true} ≤
      𝒟[stepPDFPaper cka prng fs Δcka qep mo (.inr (.inl (.inr P))) esP sp >>= fun r =>
        runRDFPaper cka prng fs Δcka qep mo (k r.1.1) r.1.2 r.2] {true} := by
  have hwin : esP.g.win = esC.g.win := eraseSt_win hS.g_eq
  have hca : esP.g.corrAllowedPaper P = esC.g.corrAllowedPaper P :=
    AuthL11.eraseSt_corrAllowedPaper hS.g_eq P
  by_cases hguard : esC.g.win || !esC.g.corrAllowedPaper P
  · simp only [Bool.or_eq_true, Bool.not_eq_true'] at hguard
    have hC :
        stepCDFPaper cka prng fs Δcka qep mo (.inr (.inl (.inr P))) esC sc =
          pure ((none, esC), sc) := by
      simp [stepCDFPaper, implEDFPaper, corrEPaper, hS.abort_C, hguard, StateT.run_pure]
    have hP :
        stepPDFPaper cka prng fs Δcka qep mo (.inr (.inl (.inr P))) esP sp =
          pure ((none, esP), sp) := by
      simp [stepPDFPaper, implEDFPaper, corrEPaper, hS.abort_P, hwin, hca, hguard, StateT.run_pure]
    rw [hC, hP, pure_bind, pure_bind]
    exact ih none hS
  · simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Bool.not_eq_false'] at hguard
    have hld : mo.policy.leakDoom esP.g (esP.g.afterCorr P) =
        mo.policy.leakDoom esC.g (esC.g.afterCorr P) :=
      eraseSt_leakDoom hS.g_eq (eraseSt_afterCorr hS.g_eq P) mo.policy
    have hcd : mo.policy.corrDoom esP.g P = mo.policy.corrDoom esC.g P :=
      eraseSt_corrDoom hS.g_eq mo.policy P
    by_cases hdoom : mo.policy.leakDoom esC.g (esC.g.afterCorr P) || mo.policy.corrDoom esC.g P
    · simp only [Bool.or_eq_true] at hdoom
      have hC : stepCDFPaper cka prng fs Δcka qep mo (.inr (.inl (.inr P))) esC sc =
          pure ((none, { esC with abort := true }), sc) := by
        simp [stepCDFPaper, implEDFPaper, corrEPaper, abortE, hS.abort_C, hguard, hdoom,
          StateT.run_modify]
      rw [hC, pure_bind]
      exact runLDFPaper_abort_apply_true_le cka prng fs Δcka qep mo (k none) rfl _
    · simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at hdoom
      have hkr : knownRoot mo (esC.g.epoch P) = true :=
        knownRoot_of_not_doom mo hauth esC.g P hdoom.1 hdoom.2
      have hrootP : (esP.g.st P).root = some (esC.g.st P).root := by
        rw [hS.root_P P, hkr]
        rfl
      have hP : stepPDFPaper cka prng fs Δcka qep mo (.inr (.inl (.inr P))) esP sp =
          pure ((some (realParty (esC.g.st P) (esP.g.st P).γ (esC.g.st P).root
            (esC.g.st P).vS (esC.g.st P).vR), { esP with g := esP.g.afterCorr P }), sp) := by
        simp [stepPDFPaper, implEDFPaper, corrEPaper, hooksPRNG, hS.abort_P, hwin, hca, hguard,
          hld, hcd, hdoom.1, hdoom.2, hrootP, StateT.run_modify, hS.realParty_eq P]
      by_cases hloc : localCKA mo Δcka (esC.g.epoch P)
      · have hγC : (esC.g.st P).γ = some (esP.g.st P).γ := by
          rw [hS.γ_C P, hloc]
          rfl
        have hC : stepCDFPaper cka prng fs Δcka qep mo (.inr (.inl (.inr P))) esC sc =
            pure ((some (realParty (esC.g.st P) (esP.g.st P).γ (esC.g.st P).root
              (esC.g.st P).vS (esC.g.st P).vR), { esC with g := esC.g.afterCorr P }), sc) := by
          simp [stepCDFPaper, implEDFPaper, corrEPaper, hooksCKA, hS.abort_C, hguard, hdoom.1,
            hdoom.2, hγC, StateT.run_modify]
        rw [hC, hP, pure_bind, pure_bind]
        exact ih _ (hS.afterCorr P)
      · simp only [Bool.not_eq_true] at hloc
        have hγC : (esC.g.st P).γ = none := by
          rw [hS.γ_C P, hloc]
          rfl
        have hcka := (hS.cka_st P (Or.inl hloc)).1
        by_cases hcorr : sc.allowCorr mo.tH || sc.finished Δcka mo.tH P
        · simp only [Bool.or_eq_true] at hcorr
          have hC : stepCDFPaper cka prng fs Δcka qep mo (.inr (.inl (.inr P))) esC sc =
              pure ((some (realParty (esC.g.st P) (esP.g.st P).γ (esC.g.st P).root
                (esC.g.st P).vS (esC.g.st P).vR), { esC with g := esC.g.afterCorr P }), sc) := by
            simp [stepCDFPaper, implEDFPaper, corrEPaper, hooksCKA, liftC, CKA.corrQuery, cImpl,
              CKA.oracleImpl, CKA.corrImpl, hS.abort_C, hguard, hdoom.1, hdoom.2, hγC,
              hcorr, hcka, simulateQ_bind, simulateQ_query, map_eq_bind_pure_comp,
              StateT.run_modify]
          rw [hC, hP, pure_bind, pure_bind]
          exact ih _ (hS.afterCorr P)
        · simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at hcorr
          have hC : stepCDFPaper cka prng fs Δcka qep mo (.inr (.inl (.inr P))) esC sc =
              pure ((none, { esC with abort := true }), sc) := by
            simp [stepCDFPaper, implEDFPaper, corrEPaper, abortE, hooksCKA, liftC, CKA.corrQuery,
              cImpl, CKA.oracleImpl, CKA.corrImpl, hS.abort_C, hguard, hdoom.1, hdoom.2, hγC,
              hcorr, simulateQ_bind, simulateQ_query, map_eq_bind_pure_comp,
              StateT.run_modify]
          rw [hC, pure_bind]
          exact runLDFPaper_abort_apply_true_le cka prng fs Δcka qep mo (k none) rfl _

end CryptoGames.SM.Construction.DeliverForge.AuthL10DF

/-! ## Stage-2 bucket game under `corrAllowedPaper` -/

namespace CryptoGames.SM.Construction.DeliverForge

open CryptoGames.SM CryptoGames.SM.Engine

section BucketGamePaper

variable {Key St Msg Coins : Type} {T E : Type} [DecidableEq Msg] [DecidableEq T] [DecidableEq E]

def fullImplBaseDFPaperBucket (sm : SMScheme Key St Msg Coins (Header T × E)) (Δcka qep : ℕ)
    [SampleableType Coins] (sameHdr : (Header T × E) → (Header T × E) → Bool)
    (tL : Option ℕ) (par : Bool) :
    QueryImpl (unifSpec + specDF St Msg Coins (Header T × E))
      (StateT (GameState St Msg (Header T × E) × Option ℕ) ProbComp) :=
  withWinEpDF (fun c => c.1.1) GameState.win
    (fullImplBaseDFPaper sm (2 + Δcka) qep sameHdr (bucketAuthCfg Δcka tL par))

/-- Single-win Stage-2 `(tL, par)` bucket authenticity game under `corrAllowedPaper`. -/
def forgeGameBucketPaper (sm : SMScheme Key St Msg Coins (Header T × E)) (Δcka qep : ℕ)
    [SampleableType Key] [SampleableType Coins]
    (sameHdr : (Header T × E) → (Header T × E) → Bool) (tL : Option ℕ) (par : Bool)
    (B : AdversaryDF St Msg Coins (Header T × E)) : ProbComp Bool := do
  let k ← $ᵗ Key
  let (_, (s, winEp)) ←
    (simulateQ (fullImplBaseDFPaperBucket sm Δcka qep sameHdr tL par) B).run
      (initState sm k false, none)
  return match winEp with
    | none => false
    | some tWin => s.win && authLosingConditionsAvoided (2 + Δcka) tL tWin s

noncomputable def forgeBucketAdvantagePaper (sm : SMScheme Key St Msg Coins (Header T × E))
    (Δcka qep : ℕ) [SampleableType Key] [SampleableType Coins]
    (sameHdr : (Header T × E) → (Header T × E) → Bool) (tL : Option ℕ) (par : Bool)
    (B : AdversaryDF St Msg Coins (Header T × E)) : ℝ≥0∞ :=
  𝒟[forgeGameBucketPaper sm Δcka qep sameHdr tL par B] {true}

end BucketGamePaper

end CryptoGames.SM.Construction.DeliverForge

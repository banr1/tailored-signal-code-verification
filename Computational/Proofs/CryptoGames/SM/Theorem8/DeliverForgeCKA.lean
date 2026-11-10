/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForge
public import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma9Aux
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma9
import VCVio.OracleComp.EvalDist.Measure

/-!
# Lemma 9 for `DeliverForge` (Hop H0 → H1)

**Checked by Lean.** Lifts ACD19 Lemma 9 to `specDF` (`lemma9_df`), bounding
`forgeGuessedAdvantage` at `(tL, t)` by the real-world CKA game on `redCKAAuthDF`, and defines
the Stage-2 `(tL, par)` bucket authenticity game.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.SM.Construction.DeliverForge

open CryptoGames.SM CryptoGames.SM.Engine CryptoGames.SM.Construction.AuthL9

def sameHdrScheme {T E : Type} [DecidableEq T] (c c' : Header T × E) : Bool :=
  c.1 == c'.1

namespace AuthL9DF

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

variable (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
  (tL : Option ℕ) (tStar : ℕ)

local notation "ASpecDF" =>
  unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)

def runLDF {α : Type}
    (oa : AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)) : ProbComp Bool :=
  ((simulateQ
    (fullImplBaseDF (scheme cka prng fs lam) (2 + Δcka) qep sameHdrScheme (Config.auth tStar))
    oa).run s) >>= fun res => pure (res.2.win && authLosingConditionsAvoided (2 + Δcka) tL tStar res.2)

def runRDF {α : Type}
    (oa : AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I))
    (sc : CKA.GameState Γ T) : ProbComp Bool :=
  ((simulateQ
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (CKA.GameState Γ T) ProbComp) +
      CKA.oracleImpl cka Δcka (healEpoch tL))
    ((simulateQ
      (implEDF (hooksCKA cka prng fs Δcka ⟨true, tL, tStar⟩)
        (2 + Δcka) qep fs.maxSkip (Config.auth tStar) ⟨true, tL, tStar⟩)
      oa).run es)).run sc) >>= fun res => pure (authOut (2 + Δcka) ⟨true, tL, tStar⟩ res.1.2)

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K]
  in
theorem runLDF_pure {α : Type} (a : α)
    (s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)) :
    runLDF cka prng fs lam Δcka qep tL tStar (pure a) s =
      pure (s.win && authLosingConditionsAvoided (2 + Δcka) tL tStar s) := by
  simp [runLDF]

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem runRDF_pure {α : Type} (a : α)
    (es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I))
    (sc : CKA.GameState Γ T) :
    runRDF cka prng fs Δcka qep tL tStar (pure a) es sc =
      pure (authOut (2 + Δcka) ⟨true, tL, tStar⟩ es) := by
  simp [runRDF]

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K]
  in
theorem runLDF_query_bind {α : Type} (t : (ASpecDF).Domain)
    (k : (ASpecDF).Range t →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)) :
    runLDF cka prng fs lam Δcka qep tL tStar (query (spec := ASpecDF) t >>= k) s =
      (((fullImplBaseDF (scheme cka prng fs lam) (2 + Δcka) qep sameHdrScheme
        (Config.auth tStar)) t).run s >>=
        fun res => runLDF cka prng fs lam Δcka qep tL tStar (k res.1) res.2) := by
  simp [runLDF, StateT.run_bind]

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem runRDF_query_bind {α : Type} (t : (ASpecDF).Domain)
    (k : (ASpecDF).Range t →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I))
    (sc : CKA.GameState Γ T) :
    runRDF cka prng fs Δcka qep tL tStar (query (spec := ASpecDF) t >>= k) es sc =
      (((simulateQ
        ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (CKA.GameState Γ T) ProbComp) +
          CKA.oracleImpl cka Δcka (healEpoch tL))
        ((implEDF (hooksCKA cka prng fs Δcka ⟨true, tL, tStar⟩)
          (2 + Δcka) qep fs.maxSkip (Config.auth tStar) ⟨true, tL, tStar⟩ t).run es)).run sc) >>=
        fun res => runRDF cka prng fs Δcka qep tL tStar (k res.1.1) res.1.2 res.2) := by
  simp [runRDF, StateT.run_bind]

omit [Inhabited E] in
theorem doomedAuth_deliverForgeBaseImpl {Key St Msg Coins : Type} [DecidableEq Msg]
    (sm : SMScheme Key St Msg Coins (Header T × E)) {Δ : ℕ} (hΔ : 0 < Δ)
    (q : Party × (Header T × E) × (Header T × E))
    {s s' : GameState St Msg (Header T × E)} {u : Option (RecvResult Msg)}
    (hd : DoomedAuth tL tStar s)
    (hmem : (u, s') ∈ support
      ((deliverForgeBaseImpl sm Δ qep sameHdrScheme (Config.auth tStar) q).run s)) :
    DoomedAuth tL tStar s' := by
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

omit [Inhabited E] in
theorem doomedAuth_simulateQ_DF {Key St Msg Coins : Type} [DecidableEq Msg] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins (Header T × E)) {Δ : ℕ} (hΔ : 0 < Δ)
    {α : Type} (oa : AdversaryCompDF St Msg Coins (Header T × E) α) :
    ∀ {s s' : GameState St Msg (Header T × E)} {a : α},
      DoomedAuth tL tStar s →
      (a, s') ∈ support
        ((simulateQ (fullImplBaseDF sm Δ qep sameHdrScheme (Config.auth tStar)) oa).run s) →
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
    rcases t with n | (q | qdf)
    · exact ih u (doomedAuth_oracleImpl (qep := qep) sm hΔ tL tStar (.inl n) hd h₁) h₂
    · exact ih u (doomedAuth_oracleImpl (qep := qep) sm hΔ tL tStar (.inr q) hd h₁) h₂
    · exact ih u (doomedAuth_deliverForgeBaseImpl qep tL tStar sm hΔ qdf hd h₁) h₂

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K]
  in
theorem evalDist_runLDF_eq_pure_false_of_doomed
    {α : Type} (oa : AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (s : GameState (PartyState Γ T Sig SS RS) M (Header T × E))
    (hdoom : DoomedAuth tL tStar s) :
    𝒟[runLDF cka prng fs lam Δcka qep tL tStar oa s] =
      𝒟[(pure false : ProbComp Bool)] := by
  apply evalDist_bind_eq_pure_false
  rintro ⟨a, s'⟩ hmem
  have hΔ : 0 < 2 + Δcka := by omega
  have hdoom' : DoomedAuth tL tStar s' :=
    doomedAuth_simulateQ_DF qep tL tStar (scheme cka prng fs lam) hΔ oa hdoom hmem
  rw [doomedAuth_not_win (2 + Δcka) tL tStar s' hdoom']

omit [SampleableType CCoins] in
theorem abort_simulateQ_DF {Γv Sv SSv RSv HS : Type} {ι : Type}
    {tspec : OracleSpec.{0, 0} ι} {S : Type}
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ maxSkip : ℕ) (cfg : Config M) (π : Policy)
    (tImpl : QueryImpl tspec (StateT S ProbComp))
    {α : Type} (oa : AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α) :
    ∀ {es es' : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS} {sc sc' : S} {a : α},
      es.abort = true →
      ((a, es'), sc') ∈ support ((simulateQ
        ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT S ProbComp) + tImpl)
        ((simulateQ (implEDF hk Δ qep maxSkip cfg π) oa).run es)).run sc) →
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
    · dsimp only [implEDF, coinsE, HAdd.hAdd, Add.add, QueryImpl.add] at h₁
      simp only [StateT.run_lift, simulateQ_bind, QueryImpl.liftTarget,
        simulateQ_pure, StateT.run_bind, StateT.run_pure, MonadAttach.mem_support_bind,
        support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₁
      rcases h₁ with ⟨_, _, ⟨_, rfl⟩, rfl⟩
      exact ih u hab h₂
    all_goals
      dsimp only [implEDF, transmitE, challE, deliverE, injectE, corrE, deliverForgeE,
        HAdd.hAdd, Add.add, QueryImpl.add] at h₁
      simp only [hab, Bool.true_or, ↓reduceIte,
        StateT.run_bind, StateT.run_get, pure_bind, StateT.run_pure,
        simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₁
      rw [← h₁.1.2] at hab
      exact ih u hab h₂

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem evalDist_runRDF_eq_pure_false_of_abort
    {α : Type} (oa : AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I))
    (sc : CKA.GameState Γ T)
    (hab : es.abort = true) :
    𝒟[runRDF cka prng fs Δcka qep tL tStar oa es sc] =
      𝒟[(pure false : ProbComp Bool)] := by
  apply evalDist_bind_eq_pure_false
  rintro ⟨⟨a, es'⟩, sc'⟩ hmem
  have hab' : es'.abort = true :=
    abort_simulateQ_DF qep (hooksCKA cka prng fs Δcka ⟨true, tL, tStar⟩)
      (2 + Δcka) fs.maxSkip (Config.auth tStar) ⟨true, tL, tStar⟩
      (CKA.oracleImpl cka Δcka (healEpoch tL)) oa hab hmem
  simp [authOut, hab']

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem step_coins_DF {α : Type} (n : unifSpec.Domain)
    (k : (ASpecDF).Range (Sum.inl n) →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar s es sc)
    (ih : ∀ u {s' es' sc'}, Sync9 cka Δcka tL tStar s' es' sc' →
      𝒟[runLDF cka prng fs lam Δcka qep tL tStar (k u) s'] =
        𝒟[runRDF cka prng fs Δcka qep tL tStar (k u) es' sc']) :
    𝒟[runLDF cka prng fs lam Δcka qep tL tStar (query (spec := ASpecDF) (Sum.inl n) >>= k) s] =
      𝒟[runRDF cka prng fs Δcka qep tL tStar
        (query (spec := ASpecDF) (Sum.inl n) >>= k) es sc] := by
  rw [runLDF_query_bind, runRDF_query_bind]
  dsimp only [implEDF, fullImplBaseDF]
  simp only [QueryImpl.add_apply, coinsE, StateT.run_lift, simulateQ_bind, simulateQ_query_eq,
    simulateQ_pure, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
  rw [liftTarget_ofLift_unifSpec_run, liftTarget_ofLift_unifSpec_run]
  simp only [bind_assoc, pure_bind]
  apply evalDist_bind_congr
  intro u
  exact ih u hs

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem step_chall_DF {α : Type} (P : Party) (m₀ m₁ : M) (r : Option CCoins)
    (k : (ASpecDF).Range
      (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr (P, m₀, m₁, r))))))) →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar s es sc)
    (ih : ∀ u {s' es' sc'}, Sync9 cka Δcka tL tStar s' es' sc' →
      𝒟[runLDF cka prng fs lam Δcka qep tL tStar (k u) s'] =
        𝒟[runRDF cka prng fs Δcka qep tL tStar (k u) es' sc']) :
    𝒟[runLDF cka prng fs lam Δcka qep tL tStar
        (query (spec := ASpecDF)
          (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr (P, m₀, m₁, r))))))) >>= k) s] =
      𝒟[runRDF cka prng fs Δcka qep tL tStar
        (query (spec := ASpecDF)
          (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr (P, m₀, m₁, r))))))) >>= k)
          es sc] := by
  rw [runLDF_query_bind, runRDF_query_bind]
  dsimp only [QueryImpl.add_apply, fullImplBaseDF, oracleImplBaseDF, oracleImpl, implEDF,
    challImpl, challE, Config.auth]
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
theorem step_corr_DF {α : Type} (P : Party)
    (k : (ASpecDF).Range (Sum.inr (Sum.inl (Sum.inr P))) →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar s es sc)
    (ih : ∀ u {s' es' sc'}, Sync9 cka Δcka tL tStar s' es' sc' →
      𝒟[runLDF cka prng fs lam Δcka qep tL tStar (k u) s'] =
        𝒟[runRDF cka prng fs Δcka qep tL tStar (k u) es' sc']) :
    𝒟[runLDF cka prng fs lam Δcka qep tL tStar
        (query (spec := ASpecDF) (Sum.inr (Sum.inl (Sum.inr P))) >>= k) s] =
      𝒟[runRDF cka prng fs Δcka qep tL tStar
        (query (spec := ASpecDF) (Sum.inr (Sum.inl (Sum.inr P))) >>= k) es sc] := by
  rw [runLDF_query_bind, runRDF_query_bind]
  dsimp only [QueryImpl.add_apply, fullImplBaseDF, oracleImplBaseDF, oracleImpl, implEDF,
    corrImpl, corrE]
  have hwin : s.win = es.g.win := by rw [hs.s_eq]; rfl
  have hca : s.corrAllowed P = es.g.corrAllowed P := by rw [hs.s_eq]; rfl
  simp only [hs.no_abort, Bool.false_or, hwin, hca, StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hguard : (es.g.win || !es.g.corrAllowed P) = true
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
      have hL := evalDist_runLDF_eq_pure_false_of_doomed cka prng fs lam Δcka qep tL tStar
        (k (some (s.st P))) (s.afterCorr P) hdoom
      have hR := evalDist_runRDF_eq_pure_false_of_abort cka prng fs Δcka qep tL tStar
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

theorem step_deliver_DF {α : Type} (P : Party) (c : Header T × E)
    (k : (ASpecDF).Range (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr (P, c)))))) →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar s es sc)
    (ih : ∀ u {s' es' sc'}, Sync9 cka Δcka tL tStar s' es' sc' →
      𝒟[runLDF cka prng fs lam Δcka qep tL tStar (k u) s'] =
        𝒟[runRDF cka prng fs Δcka qep tL tStar (k u) es' sc']) :
    𝒟[runLDF cka prng fs lam Δcka qep tL tStar
        (query (spec := ASpecDF)
          (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr (P, c)))))) >>= k) s] =
      𝒟[runRDF cka prng fs Δcka qep tL tStar
        (query (spec := ASpecDF)
          (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr (P, c)))))) >>= k) es sc] := by
  rw [runLDF_query_bind, runRDF_query_bind]
  dsimp only [QueryImpl.add_apply, fullImplBaseDF, oracleImplBaseDF, oracleImpl, implEDF,
    deliverImpl, deliverE, Config.auth]
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
      simp only 
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
          simp only 
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

theorem step_inject_DF {α : Type} (P : Party) (c : Header T × E)
    (k : (ASpecDF).Range (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar s es sc)
    (ih : ∀ u {s' es' sc'}, Sync9 cka Δcka tL tStar s' es' sc' →
      𝒟[runLDF cka prng fs lam Δcka qep tL tStar (k u) s'] =
        𝒟[runRDF cka prng fs Δcka qep tL tStar (k u) es' sc']) :
    𝒟[runLDF cka prng fs lam Δcka qep tL tStar
        (query (spec := ASpecDF) (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) >>= k) s] =
      𝒟[runRDF cka prng fs Δcka qep tL tStar
        (query (spec := ASpecDF) (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) >>= k) es sc] := by
  rw [runLDF_query_bind, runRDF_query_bind]
  dsimp only [QueryImpl.add_apply, fullImplBaseDF, oracleImplBaseDF, oracleImpl, implEDF,
    injectImpl, injectE, Config.auth]
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
                have hR : 𝒟[runRDF cka prng fs Δcka qep tL tStar (k none)
                    { es with abort := true } sc] = 𝒟[(pure false : ProbComp Bool)] :=
                  evalDist_runRDF_eq_pure_false_of_abort cka prng fs Δcka qep tL tStar
                    (k none) { es with abort := true } sc rfl
                have hdoom : DoomedAuth tL tStar s := Or.inr (Or.inr (Or.inr hd4))
                have hrun : 𝒟[runLDF cka prng fs lam Δcka qep tL tStar
                    (query (spec := ASpecDF)
                      (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) >>= k) s] =
                    𝒟[(pure false : ProbComp Bool)] :=
                  evalDist_runLDF_eq_pure_false_of_doomed cka prng fs lam Δcka qep tL tStar
                    (query (spec := ASpecDF)
                      (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) >>= k) s hdoom
                rw [runLDF_query_bind] at hrun
                dsimp only [QueryImpl.add_apply, fullImplBaseDF, oracleImplBaseDF, oracleImpl,
                  injectImpl, Config.auth] at hrun
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
          simp only 
          cases hfs : fs.receive v c.1 c.2 with
          | none =>
            simp [ih (some .rejected) hs]
          | some val =>
            rcases val with ⟨v', i', m'⟩
            simp only 
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

theorem step_transmit_DF {α : Type} (P : Party) (m : M) (r : Option CCoins)
    (k : (ASpecDF).Range
      (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (P, m, r))))))) →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar s es sc)
    (ih : ∀ u {s' es' sc'}, Sync9 cka Δcka tL tStar s' es' sc' →
      𝒟[runLDF cka prng fs lam Δcka qep tL tStar (k u) s'] =
        𝒟[runRDF cka prng fs Δcka qep tL tStar (k u) es' sc']) :
    𝒟[runLDF cka prng fs lam Δcka qep tL tStar
        (query (spec := ASpecDF)
          (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (P, m, r))))))) >>= k) s] =
      𝒟[runRDF cka prng fs Δcka qep tL tStar
        (query (spec := ASpecDF)
          (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (P, m, r))))))) >>= k) es sc] := by
  rw [runLDF_query_bind, runRDF_query_bind]
  dsimp only [QueryImpl.add_apply, fullImplBaseDF, oracleImplBaseDF, oracleImpl, implEDF]
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
        have hR : 𝒟[runRDF cka prng fs Δcka qep tL tStar (k none)
            { es with abort := true } sc] = 𝒟[(pure false : ProbComp Bool)] :=
          evalDist_runRDF_eq_pure_false_of_abort cka prng fs Δcka qep tL tStar
            (k none) { es with abort := true } sc rfl
        rw [hR]
        refine evalDist_bind_eq_pure_false _ _ fun coins _ => ?_
        have hdoom := hs.doomed_of_leakDoom_epMgmt hw_f hep hld
          (send cka prng fs (s.st P) m coins).1 m (send cka prng fs (s.st P) m coins).2 false
        exact evalDist_runLDF_eq_pure_false_of_doomed cka prng fs lam Δcka qep tL tStar
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
                have hR : 𝒟[runRDF cka prng fs Δcka qep tL tStar (k none)
                    { es with abort := true } sc] = 𝒟[(pure false : ProbComp Bool)] :=
                  evalDist_runRDF_eq_pure_false_of_abort cka prng fs Δcka qep tL tStar
                    (k none) { es with abort := true } sc rfl
                have hdoom := hs.doomed4_of_sendBad_gt htL hloc' hsend hep hld_f hgt
                  (send cka prng fs (s.st P) m coins).1 m
                  (send cka prng fs (s.st P) m coins).2 false
                have hL : 𝒟[runLDF cka prng fs lam Δcka qep tL tStar
                    (k (some (send cka prng fs (s.st P) m coins).2))
                    ((realGS sc s₁).record (2 + Δcka) P (send cka prng fs (s.st P) m coins).1
                      ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m,
                        (send cka prng fs (s.st P) m coins).2⟩ false)] =
                    𝒟[(pure false : ProbComp Bool)] :=
                  evalDist_runLDF_eq_pure_false_of_doomed cka prng fs lam Δcka qep tL tStar
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

theorem step_deliverForge_DF {α : Type} (P : Party) (c c' : Header T × E)
    (k : (ASpecDF).Range (Sum.inr (Sum.inr (P, c, c'))) →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar s es sc)
    (ih : ∀ u {s' es' sc'}, Sync9 cka Δcka tL tStar s' es' sc' →
      𝒟[runLDF cka prng fs lam Δcka qep tL tStar (k u) s'] =
        𝒟[runRDF cka prng fs Δcka qep tL tStar (k u) es' sc']) :
    𝒟[runLDF cka prng fs lam Δcka qep tL tStar
        (query (spec := ASpecDF) (Sum.inr (Sum.inr (P, c, c'))) >>= k) s] =
      𝒟[runRDF cka prng fs Δcka qep tL tStar
        (query (spec := ASpecDF) (Sum.inr (Sum.inr (P, c, c'))) >>= k) es sc] := by
  rw [runLDF_query_bind, runRDF_query_bind]
  dsimp only [QueryImpl.add_apply, fullImplBaseDF, oracleImplBaseDF, implEDF,
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
      simp only 
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
            simp only 
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

theorem runLDF_eq_runRDF_of_sync {α : Type}
    (oa : AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar s es sc) :
    𝒟[runLDF cka prng fs lam Δcka qep tL tStar oa s] =
      𝒟[runRDF cka prng fs Δcka qep tL tStar oa es sc] := by
  induction oa using OracleComp.inductionOn generalizing s es sc with
  | pure a =>
    rw [runLDF_pure, runRDF_pure]
    have hwin : s.win = es.g.win := by rw [hs.s_eq]; rfl
    have hok : authLosingConditionsAvoided (2 + Δcka) tL tStar s = authLosingConditionsAvoided (2 + Δcka) tL tStar es.g := by
      rw [hs.s_eq]; rfl
    simp [authOut, hs.no_abort, hwin, hok]
  | query_bind t k ih =>
    rcases t with n | (((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩)
    · exact step_coins_DF cka prng fs lam Δcka qep tL tStar n k hs @ih
    · exact step_transmit_DF cka prng fs lam Δcka qep tL tStar P m r k hs @ih
    · exact step_chall_DF cka prng fs lam Δcka qep tL tStar P m₀ m₁ r k hs @ih
    · exact step_deliver_DF cka prng fs lam Δcka qep tL tStar P c k hs @ih
    · exact step_inject_DF cka prng fs lam Δcka qep tL tStar P c k hs @ih
    · exact step_corr_DF cka prng fs lam Δcka qep tL tStar P k hs @ih
    · exact step_deliverForge_DF cka prng fs lam Δcka qep tL tStar P c c' k hs @ih

omit [DecidableEq I] [SampleableType I] [SampleableType K] in
theorem forgeGameGuessed_eq_runLDF (t : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    forgeGameGuessed (scheme cka prng fs lam) (2 + Δcka) qep sameHdrScheme tL t A =
      ($ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
        runLDF cka prng fs lam Δcka qep tL t A
          (initState (scheme cka prng fs lam) (kr, kc) false)) := by
  unfold forgeGameGuessed runBaseDF runLDF
  simp only [uniformSample, SampleableType.selectElem, seq_eq_bind_map, map_eq_bind_pure_comp,
    Function.comp_apply, pure_bind, bind_assoc]

/-- Bounds `forgeGuessedAdvantage` at `(tL, t)` by the real-world CKA branch of `redCKAAuthDF`. -/
theorem lemma9_df (hc : cka.Correct) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    forgeGuessedAdvantage (scheme cka prng fs lam) (2 + Δcka) qep sameHdrScheme tL t A ≤
      𝒟[CKA.branch cka Δcka (healEpoch tL) false
        (redCKAAuthDF cka prng fs lam Δcka qep tL t A)] {true} := by
  by_cases hvg : lastLeakGuessAdmissible (2 + Δcka) tL t = true
  · apply le_of_eq
    unfold forgeGuessedAdvantage
    rw [forgeGameGuessed_eq_runLDF]
    congr 1
    cases htL : tL with
    | none =>
      subst htL
      unfold CKA.branch redCKAAuthDF authSimDF engRunDF initCKA
      simp only [StateT.run'_eq, StateT.run_bind, StateT.run_lift, StateT.run_pure,
        pure_bind, bind_assoc, simulateQ_bind, simulateQ_pure, simulateQ_sampleT_run,
        map_bind]
      symm
      refine (evalDist_bind_congr ($ᵗ KC) _
        (fun _ => $ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
          runLDF cka prng fs lam Δcka qep none t A
            (initState (scheme cka prng fs lam) (kr, kc) false)) ?_).trans ?_
      · intro kc_ext
        refine evalDist_bind_congr _ _ _ fun kr => ?_
        refine evalDist_bind_congr _ _ _ fun kc => ?_
        symm
        refine (runLDF_eq_runRDF_of_sync cka prng fs lam Δcka qep none t A
          (sync9_init_none cka prng fs lam Δcka t hc hvg kr kc kc_ext)).trans ?_
        simp only [runRDF, bind_pure_comp, map_pure]
        rfl
      · exact OracleComp.evalDist_bind_const ($ᵗ KC) _
    | some l =>
      subst htL
      unfold CKA.branch redCKAAuthDF authSimDF engRunDF initCKA
      simp only [StateT.run'_eq, StateT.run_bind, StateT.run_lift, StateT.run_pure,
        pure_bind, bind_assoc, simulateQ_bind, simulateQ_pure, simulateQ_sampleT_run,
        map_bind]
      rw [OracleComp.evalDist_bind_bind_swap ($ᵗ KR) ($ᵗ KC)]
      refine evalDist_bind_congr _ _ _ fun kc => ?_
      refine evalDist_bind_congr _ _ _ fun kr => ?_
      refine (runLDF_eq_runRDF_of_sync cka prng fs lam Δcka qep (some l) t A
        (Sync9.sync9_init prng fs lam hc hvg kr kc)).trans ?_
      simp only [runRDF, bind_pure_comp, map_pure]
      rfl
  · have hvg_f : lastLeakGuessAdmissible (2 + Δcka) tL t = false := Bool.eq_false_iff.mpr hvg
    have hzero :
        forgeGuessedAdvantage (scheme cka prng fs lam) (2 + Δcka) qep sameHdrScheme tL t A = 0 := by
      unfold forgeGuessedAdvantage forgeGameGuessed
      simp only 
      refine evalDist_true_eq_zero_of_support _ _ fun res _ => ?_
      simp [authLosingConditionsAvoided, hvg_f]
    rw [hzero]
    exact zero_le

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType I] in
theorem allowCorr_and_ne_tStar_of_corr_dir2_k4Free
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T} {l : ℕ} {P : Party}
    (hvg2 : lastLeakGuessAdmissible 2 (some l) tStar = true)
    (hloc : isLocal (some l) 1 (es.g.epoch P) = false)
    (hld : (Policy.mk true (some l) tStar).leakDoom es.g (es.g.afterCorr P) = false)
    (hcd : (Policy.mk true (some l) tStar).corrDoom es.g P = false)
    (hsc : ∀ Q, sc.epoch Q ≤ es.g.epoch Q)
    (hm_eq : maxOpt es.g.tL (max (es.g.epoch .A) (es.g.epoch .B)) =
      max (es.g.epoch .A) (es.g.epoch .B))
    (hle_other : es.g.epoch P.other ≤ es.g.epoch P + 1)
    (hsnd_step : es.g.epoch P + 1 = es.g.epoch P.other →
      P.other.sendsIn (es.g.epoch P.other) = true)
    (hk4 : ¬(tStar = l + 2 ∧ P = Party.senderOf tStar ∧ es.g.epoch P = tStar)) :
    max (es.g.epoch .A) (es.g.epoch .B) ≤ l ∧
      es.g.epoch P ≠ tStar ∧
      sc.allowCorr (healEpoch (some l)) = true := by
  simp only [lastLeakGuessAdmissible, healedBy, decide_eq_true_eq] at hvg2
  simp only [isLocal, decide_eq_false_iff_not, not_le] at hloc
  have hmax : max (es.g.epoch .A) (es.g.epoch .B) ≤ l := by
    by_contra hgt
    have hld1 : ¬(l < max (es.g.epoch .A) (es.g.epoch .B) ∧
        max (es.g.epoch .A) (es.g.epoch .B) < tStar) := by
      intro ⟨h1, h2⟩
      unfold Policy.leakDoom at hld
      simp only [Bool.or_eq_false_iff, List.any_eq_false] at hld
      have h3 := hld.1 (maxOpt es.g.tL (max (es.g.epoch .A) (es.g.epoch .B)))
        (by simp [GameState.afterCorr, GameState.leak])
      rw [hm_eq] at h3
      simp [ltOpt, h1, h2] at h3
    have hmax_le : max (es.g.epoch .A) (es.g.epoch .B) ≤ es.g.epoch P + 1 := by
      cases P <;> simp [Party.other] at hle_other ⊢ <;> omega
    by_cases hep_t : es.g.epoch P = tStar
    · have ht_eq : tStar = l + 2 := by omega
      by_cases hP : P = Party.senderOf tStar
      · exact hk4 ⟨ht_eq, hP, hep_t⟩
      · have hrcv : P = Party.receiverOf tStar := by
          cases P <;> cases h : Party.senderOf tStar <;>
            simp_all [Party.receiverOf, Party.senderOf, Party.other]
        have hgt_P : l < es.g.epoch P := by omega
        unfold Policy.corrDoom at hcd
        rw [← hrcv] at hcd
        simp [ltOpt, hgt_P] at hcd
    · have htStar_eq :
          es.g.epoch P + 1 = tStar ∧ es.g.epoch P.other = tStar ∧ l < es.g.epoch P := by
        cases P <;> simp [Party.other] at hle_other hmax_le hgt hld1 hep_t ⊢ <;> omega
      have hsnd_other : P.other.sendsIn tStar = true := by
        rw [← htStar_eq.2.1]
        exact hsnd_step (by omega)
      have hrcv : P = Party.receiverOf tStar := by
        apply eq_receiverOf_of_sendsIn_false
        have h := sendsIn_other P.other tStar
        rw [Party.other_other, hsnd_other] at h
        exact h
      unfold Policy.corrDoom at hcd
      rw [← hrcv] at hcd
      simp [ltOpt, htStar_eq.2.2] at hcd
  have hP_le : es.g.epoch P ≤ l := by
    have : es.g.epoch P ≤ max (es.g.epoch .A) (es.g.epoch .B) := by
      cases P <;> simp
    omega
  refine ⟨hmax, by omega, ?_⟩
  unfold CKA.GameState.allowCorr healEpoch
  dsimp only
  rw [decide_eq_true_eq]
  have hscA := hsc .A
  have hscB := hsc .B
  omega

end AuthL9DF

/-! ## Stage-2 bucket game -/

def partyPar : Party → Bool
  | .A => false
  | .B => true

@[simp] theorem partyPar_A : partyPar .A = false := rfl
@[simp] theorem partyPar_B : partyPar .B = true := rfl

/-- Membership of epoch `t` in the Stage-2 `(tL, par)` bucket (`3 + Δcka` healing gap and sender
parity `par`). -/
def inStage2Bucket (Δcka : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) : Bool :=
  lastLeakGuessAdmissible (3 + Δcka) tL t && (partyPar (Party.senderOf t) == par)

def bucketAuthCfg {Msg : Type} (Δcka : ℕ) (tL : Option ℕ) (par : Bool) : Config Msg where
  deliverWin := false
  injectFull t' := inStage2Bucket Δcka tL par t'
  challAllowedIn _ := false
  challMsg _ := none

def dfQueryTargetEpoch {St Msg Coins C : Type} (ctEpoch : C → ℕ) :
    (unifSpec + specDF St Msg Coins C).Domain → Option ℕ
  | .inr (.inl (.inl (.inr (_, c)))) => some (ctEpoch c)
  | .inr (.inr (_, _, c')) => some (ctEpoch c')
  | _ => none

def withWinEpDF {M : Type → Type} [Monad M] {St Msg Coins C S : Type}
    (ctEpoch : C → ℕ) (hasWin : S → Bool)
    (impl : QueryImpl (unifSpec + specDF St Msg Coins C) (StateT S M)) :
    QueryImpl (unifSpec + specDF St Msg Coins C) (StateT (S × Option ℕ) M) :=
  fun q => StateT.mk fun ⟨s, winEp⟩ => do
    let (r, s') ← (impl q).run s
    let winEp' := if !hasWin s && hasWin s' then dfQueryTargetEpoch ctEpoch q else winEp
    pure (r, (s', winEp'))

section BucketGame

variable {Key St Msg Coins : Type} {T E : Type} [DecidableEq Msg] [DecidableEq T] [DecidableEq E]

def fullImplBaseDFBucket (sm : SMScheme Key St Msg Coins (Header T × E)) (Δcka qep : ℕ)
    [SampleableType Coins] (sameHdr : (Header T × E) → (Header T × E) → Bool)
    (tL : Option ℕ) (par : Bool) :
    QueryImpl (unifSpec + specDF St Msg Coins (Header T × E))
      (StateT (GameState St Msg (Header T × E) × Option ℕ) ProbComp) :=
  withWinEpDF (fun c => c.1.1) GameState.win
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (GameState St Msg (Header T × E)) ProbComp) +
      (oracleImpl sm (2 + Δcka) qep (bucketAuthCfg Δcka tL par) +
        deliverForgeBaseImpl sm (2 + Δcka) qep sameHdr (bucketAuthCfg Δcka tL par)))

/-- Single-win Stage-2 `(tL, par)` bucket authenticity game. -/
def forgeGameBucket (sm : SMScheme Key St Msg Coins (Header T × E)) (Δcka qep : ℕ)
    [SampleableType Key] [SampleableType Coins]
    (sameHdr : (Header T × E) → (Header T × E) → Bool) (tL : Option ℕ) (par : Bool)
    (B : AdversaryDF St Msg Coins (Header T × E)) : ProbComp Bool := do
  let k ← $ᵗ Key
  let (_, (s, winEp)) ←
    (simulateQ (fullImplBaseDFBucket sm Δcka qep sameHdr tL par) B).run
      (initState sm k false, none)
  return match winEp with
    | none => false
    | some tWin => s.win && authLosingConditionsAvoided (2 + Δcka) tL tWin s

noncomputable def forgeBucketAdvantage (sm : SMScheme Key St Msg Coins (Header T × E))
    (Δcka qep : ℕ) [SampleableType Key] [SampleableType Coins]
    (sameHdr : (Header T × E) → (Header T × E) → Bool) (tL : Option ℕ) (par : Bool)
    (B : AdversaryDF St Msg Coins (Header T × E)) : ℝ≥0∞ :=
  𝒟[forgeGameBucket sm Δcka qep sameHdr tL par B] {true}

end BucketGame

end CryptoGames.SM.Construction.DeliverForge

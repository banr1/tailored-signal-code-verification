/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma9Aux
import VCVio.OracleComp.EvalDist.Measure

/-!
# Proof of Lemma 9 (Theorem 8, hop H0 → H1)

**Checked by Lean.**

Proves ACD19 §5.3.2 Lemma 9 (`lemma9` in `SM/Theorem8.lean`), bounding the authenticity game by the
real world (`b = false`) of `redCKAAuth` in the CKA game via oracle-by-oracle coupling up to doomed
runs.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames.SM.Construction.AuthL9

open Engine

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

variable (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
  (tL : Option ℕ) (tStar : ℕ)

def runL {α : Type} (oa : AdversaryComp (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)) : ProbComp Bool :=
  ((simulateQ
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (GameState (PartyState Γ T Sig SS RS) M (Header T × E)) ProbComp) +
      oracleImpl (scheme cka prng fs lam) (2 + Δcka) qep (Config.auth tStar))
    oa).run s) >>= fun res => pure (res.2.win && authLosingConditionsAvoided (2 + Δcka) tL tStar res.2)

def runR {α : Type} (oa : AdversaryComp (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I))
    (sc : CKA.GameState Γ T) : ProbComp Bool :=
  ((simulateQ
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (CKA.GameState Γ T) ProbComp) +
      CKA.oracleImpl cka Δcka (healEpoch tL))
    ((simulateQ
      (implE (hooksCKA cka prng fs Δcka ⟨true, tL, tStar⟩)
        (2 + Δcka) qep fs.maxSkip (Config.auth tStar) ⟨true, tL, tStar⟩)
      oa).run es)).run sc) >>= fun res => pure (authOut (2 + Δcka) ⟨true, tL, tStar⟩ res.1.2)

theorem runL_pure {α : Type} (a : α)
    (s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)) :
    runL cka prng fs lam Δcka qep tL tStar (pure a) s =
      pure (s.win && authLosingConditionsAvoided (2 + Δcka) tL tStar s) := by
  simp [runL]

theorem runR_pure {α : Type} (a : α)
    (es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I))
    (sc : CKA.GameState Γ T) :
    runR cka prng fs Δcka qep tL tStar (pure a) es sc =
      pure (authOut (2 + Δcka) ⟨true, tL, tStar⟩ es) := by
  simp [runR]

local notation "ASpec" => unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)

theorem runL_query_bind {α : Type} (t : (ASpec).Domain)
    (k : (ASpec).Range t → AdversaryComp (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)) :
    runL cka prng fs lam Δcka qep tL tStar (query (spec := ASpec) t >>= k) s =
      ((((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (GameState (PartyState Γ T Sig SS RS) M (Header T × E)) ProbComp) +
        oracleImpl (scheme cka prng fs lam) (2 + Δcka) qep (Config.auth tStar)) t).run s >>=
        fun res => runL cka prng fs lam Δcka qep tL tStar (k res.1) res.2) := by
  simp [runL, StateT.run_bind, bind_assoc]

theorem runR_query_bind {α : Type} (t : (ASpec).Domain)
    (k : (ASpec).Range t → AdversaryComp (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I))
    (sc : CKA.GameState Γ T) :
    runR cka prng fs Δcka qep tL tStar (query (spec := ASpec) t >>= k) es sc =
      (((simulateQ
        ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (CKA.GameState Γ T) ProbComp) +
          CKA.oracleImpl cka Δcka (healEpoch tL))
        ((implE (hooksCKA cka prng fs Δcka ⟨true, tL, tStar⟩)
          (2 + Δcka) qep fs.maxSkip (Config.auth tStar) ⟨true, tL, tStar⟩ t).run es)).run sc) >>=
        fun res => runR cka prng fs Δcka qep tL tStar (k res.1.1) res.1.2 res.2) := by
  simp [runR, StateT.run_bind, bind_assoc]

@[simp]
theorem simulateQ_query_eq {ι : Type} {ospec : OracleSpec.{0, 0} ι}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (so : QueryImpl ospec m) (t : ospec.Domain) :
    simulateQ so (query (spec := ospec) t) = so t := by
  simp [OracleSpec.query]

@[simp]
theorem liftH_run {ι : Type} {tspec : OracleSpec.{0, 0} ι} {HS α : Type}
    (x : HM tspec HS α)
    (es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) HS) :
    (liftH x).run es = (x.run es.h >>= fun p => pure (p.1, { es with h := p.2 })) := rfl

@[simp]
theorem liftTarget_ofLift_unifSpec_run {S : Type} (n : unifSpec.Domain) (s : S) :
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT S ProbComp) n).run s =
      (query (spec := unifSpec) n >>= fun u => pure (u, s)) := rfl

theorem step_coins {HS : Type} {Δ' tCKA : ℕ} (n : unifSpec.Domain)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) HS}
    {sc : CKA.GameState Γ T}
    {contL : Fin (n + 1) × GameState (PartyState Γ T Sig SS RS) M (Header T × E) → ProbComp Bool}
    {contR : (Fin (n + 1) × EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) HS) ×
      CKA.GameState Γ T → ProbComp Bool}
    (ih : ∀ u, 𝒟[contL (u, s)] = 𝒟[contR ((u, es), sc)]) :
    𝒟[(((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (GameState (PartyState Γ T Sig SS RS) M (Header T × E)) ProbComp)) n).run s >>=
        contL] =
      𝒟[((simulateQ
        ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (CKA.GameState Γ T) ProbComp) +
          CKA.oracleImpl cka Δ' tCKA)
        ((coinsE (tspec := CKA.spec Γ CCoins T I) n).run es)).run sc) >>= contR] := by
  simp only [coinsE, StateT.run_lift, simulateQ_bind, simulateQ_query_eq,
    simulateQ_pure, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind,
    liftTarget_ofLift_unifSpec_run]
  exact evalDist_bind_congr _ _ _ ih

theorem step_chall {HS : Type} {Δ Δ' tCKA : ℕ} {π : Policy}
    {hk : Hooks (CKA.spec Γ CCoins T I) HS Γ T Sig SS RS M E CCoins (Option Γ) Sig SS RS}
    (P : Party) (m₀ m₁ : M) (r : Option CCoins)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) HS}
    {sc : CKA.GameState Γ T}
    (habort : es.abort = false) (hwin : s.win = es.g.win)
    {contL : Option (Header T × E) × GameState (PartyState Γ T Sig SS RS) M (Header T × E) → ProbComp Bool}
    {contR : (Option (Header T × E) × EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) HS) ×
      CKA.GameState Γ T → ProbComp Bool}
    (ih : 𝒟[contL (none, s)] = 𝒟[contR ((none, es), sc)]) :
    𝒟[(challImpl (scheme cka prng fs lam) Δ qep (Config.auth tStar) (P, m₀, m₁, r)).run s >>= contL] =
      𝒟[((simulateQ
        ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (CKA.GameState Γ T) ProbComp) +
          CKA.oracleImpl cka Δ' tCKA)
        ((challE hk Δ qep (Config.auth tStar) π (P, m₀, m₁, r)).run es)).run sc) >>= contR] := by
  dsimp only [challImpl, challE, Config.auth]
  simp only [habort, Bool.false_or, hwin, StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hw : es.g.win = true
  · simp [hw, ih]
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.or_true]
    cases r with
    | none =>
      simp only [samIfNec, Option.isSome, StateT.run_monadLift, monadLift_self,
        StateT.run_bind, bind_assoc, pure_bind]
      cases s.epMgmt Δ qep P false <;> cases es.g.epMgmt Δ qep P false <;>
        simp [OracleComp.evalDist_bind_const, ih]
    | some c =>
      simp only [samIfNec, Option.isSome, StateT.run_monadLift, monadLift_self,
        StateT.run_bind, bind_assoc, pure_bind]
      cases s.epMgmt Δ qep P true <;> cases es.g.epMgmt Δ qep P true <;>
        simp [ih]

theorem step_corr {α : Type} (P : Party)
    (k : (ASpec).Range (Sum.inr (Sum.inr P)) →
      AdversaryComp (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar s es sc)
    (ih : ∀ u {s' es' sc'}, Sync9 cka Δcka tL tStar s' es' sc' →
      𝒟[runL cka prng fs lam Δcka qep tL tStar (k u) s'] =
        𝒟[runR cka prng fs Δcka qep tL tStar (k u) es' sc']) :
    𝒟[runL cka prng fs lam Δcka qep tL tStar
        (query (spec := ASpec) (Sum.inr (Sum.inr P)) >>= k) s] =
      𝒟[runR cka prng fs Δcka qep tL tStar
        (query (spec := ASpec) (Sum.inr (Sum.inr P)) >>= k) es sc] := by
  rw [runL_query_bind, runR_query_bind]
  dsimp only [QueryImpl.add_apply, oracleImpl, implE, corrImpl, corrE]
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
    · simp only [hd, ↓reduceIte, abortE, StateT.run_modify, StateT.run_set, pure_bind,
        StateT.run_pure, simulateQ_pure]
      have hdoom : DoomedAuth tL tStar (s.afterCorr P) := hs.doomed_of_corr_doom hwin_f hd
      have hL := evalDist_runL_eq_pure_false_of_doomed cka prng fs lam Δcka qep tL tStar
        (k (some (s.st P))) (s.afterCorr P) hdoom
      have hR := evalDist_runR_eq_pure_false_of_abort
        (hooksCKA cka prng fs Δcka ⟨true, tL, tStar⟩)
        (2 + Δcka) qep fs.maxSkip (Config.auth tStar) ⟨true, tL, tStar⟩
        (CKA.oracleImpl cka Δcka (healEpoch tL))
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
        simp only [hooksCKA, hγ, liftH_run, pure_bind, StateT.run_pure, StateT.run_modify,
          StateT.run_set, simulateQ_pure, hst_eq]
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
          simp only [hooksCKA, hγ, liftH_run, liftC, CKA.corrQuery, StateT.run_bind, StateT.run_lift,
            simulateQ_bind, simulateQ_query_eq, QueryImpl.add_apply, CKA.oracleImpl, CKA.corrImpl,
            hall', Bool.true_or, ↓reduceIte, StateT.run_get, pure_bind, StateT.run_pure,
            simulateQ_pure, StateT.run_modify, StateT.run_set, bind_assoc, hst_eq, ← htL]
          exact ih (some (s.st P)) (hs.sync9_corr P)

@[simp]
theorem accept_update_st {St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    (g : GameState St Msg C) (P : Party) (st₁ st₂ : St) (pos : Pos) :
    { g.accept P st₁ pos with st := Function.update (g.accept P st₁ pos).st P st₂ } =
      g.accept P st₂ pos := by
  simp only [GameState.accept, GameState.delete]
  congr 1
  funext Q
  by_cases h : Q = P <;> simp [h]

theorem commitE_same {P : Party} {new : VP (Option Γ) T Sig SS RS} {pos : Pos}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (ht : new.tcur = (es.g.st P).tcur) :
    ((simulateQ
      ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (CKA.GameState Γ T) ProbComp) +
        CKA.oracleImpl cka Δcka (healEpoch tL))
      ((commitE (hooksCKA cka prng fs Δcka ⟨true, tL, tStar⟩)
        es.g P (es.g.st P) new pos).run es)).run sc) =
      pure ((some (es.g.accept P new pos), es), sc) := by
  simp [commitE, hooksCKA, ht]

theorem commitE_new {P : Party} (σ' : Sig) (vR' : ℕ → Option RS) {pos : Pos}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar s es sc)
    (ht : pos.epoch = es.g.epoch P + 1)
    (heq_other : es.g.epoch P + 1 = es.g.epoch P.other)
    (T_t : T)
    (hl_msg : ∀ l, tL = some l → es.g.epoch P.other ≤ l + 2 + Δcka → sc.lastMsg = some T_t) :
    let t := pos.epoch
    let γ_r' := (cka.receive (s.st P).γ T_t).1
    let γ_v' : Option Γ := if isLocal tL Δcka t then some γ_r' else none
    let new : PartyState (Option Γ) T Sig SS RS :=
      { es.g.st P with tcur := t, γ := (es.g.st P).γ.map (fun γ => (cka.receive γ T_t).1),
                       root := σ', vR := vR' }
    let st_v' : PartyState (Option Γ) T Sig SS RS :=
      { es.g.st P with tcur := t, γ := γ_v', root := σ', vR := vR' }
    let sc' : CKA.GameState Γ T :=
      if isLocal tL Δcka (es.g.epoch P) then sc else sc.afterReceive P γ_r'
    ((simulateQ
      ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (CKA.GameState Γ T) ProbComp) +
        CKA.oracleImpl cka Δcka (healEpoch tL))
      ((commitE (hooksCKA cka prng fs Δcka ⟨true, tL, tStar⟩)
        es.g P (es.g.st P) new pos).run es)).run sc) =
      pure ((some (es.g.accept P st_v' pos), es), sc') := by
  intro t γ_r' γ_v' new st_v' sc'
  have hγ := hs.γ_eq P
  have htcur := hs.st_tcur P
  by_cases hloc : isLocal tL Δcka (es.g.epoch P) = true
  · simp only [hloc, ↓reduceIte] at hγ
    have hloc_t : isLocal tL Δcka t = true := by
      rcases htL : tL with _ | l
      · rfl
      · simp only [isLocal, htL, decide_eq_true_eq] at hloc ⊢
        dsimp only [t]; omega
    have hnew_eq : new = st_v' := by
      simp [new, st_v', γ_v', γ_r', hγ, hloc_t]
    simp [commitE, hooksCKA, hγ, hloc, hnew_eq, sc']
  · simp only [hloc, Bool.false_eq_true, ↓reduceIte] at hγ
    rcases htL : tL with _ | l
    · simp [isLocal, htL] at hloc
    · have hloc' : es.g.epoch P < l + 2 + Δcka := by
        simp [isLocal, htL] at hloc
        exact hloc
      have hnew_tcur : new.tcur = t := rfl
      have hlt_tcur : (es.g.st P).tcur < t := by
        dsimp only [t]
        rw [htcur, ht]
        omega
      have hcan : sc.canReceive P = true := by
        simp only [CKA.GameState.canReceive, hs.sc_epoch l htL, ← heq_other, beq_iff_eq]
        omega
      have hmsg : sc.lastMsg = some T_t := hl_msg l htL (by omega)
      have hstP : sc.st P = (s.st P).γ := by
        rw [hs.s_eq]
        simp [realGS, realVP, hγ]
      by_cases hloc_t : isLocal (some l) Δcka t = true
      · have hfin_le : healEpoch (some l) + Δcka ≤ t := by
          simpa [isLocal, healEpoch] using hloc_t
        have hfin : (sc.afterReceive P γ_r').finished Δcka (healEpoch (some l)) P = true := by
          simp only [CKA.GameState.finished, CKA.GameState.afterReceive, Function.update_self,
            hs.sc_epoch l htL P, decide_eq_true_eq]
          dsimp only [t] at hfin_le
          omega
        have hafter_st : (sc.afterReceive P γ_r').st P = γ_r' := by
          simp [CKA.GameState.afterReceive]
        have hst_v_eq : { new with γ := some γ_r' } = st_v' := by
          simp [new, st_v', γ_v', htL, hloc_t]
        simp only [commitE, hooksCKA, hnew_tcur, hγ, hlt_tcur, decide_true, Option.isNone,
          Bool.and_self, ↓reduceIte, liftH_run, liftC, CKA.receiveQuery, CKA.corrQuery, Mode.tH,
          StateT.run_bind, StateT.run_lift, simulateQ_bind, simulateQ_query_eq,
          QueryImpl.add_apply, CKA.oracleImpl, CKA.receiveImpl, CKA.corrImpl,
          StateT.run_get, pure_bind, hcan, Bool.not_true, Bool.false_eq_true, hmsg,
          StateT.run_set, StateT.run_pure, simulateQ_pure, bind_assoc, hstP, γ_r',
          hfin_le, hfin, Bool.or_true, hafter_st, accept_update_st, sc', hloc]
        rw [← hnew_tcur, hst_v_eq]
      · have hfin_lt : ¬(healEpoch (some l) + Δcka ≤ t) := by
          simpa [isLocal, healEpoch] using hloc_t
        have hst_v_eq : new = st_v' := by
          simp [new, st_v', γ_v', hγ, htL, hloc_t]
        simp only [commitE, hooksCKA, hnew_tcur, hγ, hlt_tcur, decide_true, Option.isNone,
          Bool.and_self, ↓reduceIte, liftH_run, liftC, CKA.receiveQuery, Mode.tH,
          StateT.run_bind, StateT.run_lift, simulateQ_bind, simulateQ_query_eq,
          QueryImpl.add_apply, CKA.oracleImpl, CKA.receiveImpl,
          StateT.run_get, pure_bind, hcan, Bool.not_true, Bool.false_eq_true, hmsg,
          StateT.run_set, StateT.run_pure, simulateQ_pure, bind_assoc, hstP, γ_r',
          hfin_lt, accept_update_st, sc', hloc]
        rw [hst_v_eq]

theorem vRecv_guard_true {tStar_hs : ℕ} {P : Party} {c : Header T × E}
    {rec : Option (Record M (Header T × E))}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar_hs s es sc)
    (hguard : (P.sendsIn c.1.1 || decide (es.g.epoch P + 1 < c.1.1)) = true) :
    receive cka prng fs (s.st P) c = none ∧
    (liftH (vRecv (hooksCKA cka prng fs Δcka ⟨true, tL, tStar⟩)
      es.g P (es.g.st P) c rec)).run es = pure (some none, es) := by
  have hid_r : (s.st P).id = P := by rw [hs.s_eq]; exact hs.st_id P
  have htcur_r : (s.st P).tcur = es.g.epoch P := by rw [hs.s_eq]; exact hs.st_tcur P
  have hid_v := hs.st_id P
  have htcur_v := hs.st_tcur P
  constructor
  · unfold receive
    simp [hid_r, htcur_r, hguard]
  · unfold vRecv
    simp [hid_v, htcur_v, hguard]

theorem vRecv_same_epoch {tStar_hs : ℕ} {P : Party} {c : Header T × E}
    {rec : Option (Record M (Header T × E))}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar_hs s es sc)
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
    (liftH (vRecv (hooksCKA cka prng fs Δcka ⟨true, tL, tStar⟩)
      es.g P (es.g.st P) c rec)).run es =
      pure (some (match (es.g.st P).vR c.1.1 with
        | none => none
        | some v =>
          match fs.receive v c.1 c.2 with
          | none => none
          | some (v', i, m) =>
            some ({ es.g.st P with vR := Function.update (es.g.st P).vR c.1.1 (some v') },
              c.1.1, i, m)), es) := by
  have hid_r : (s.st P).id = P := by rw [hs.s_eq]; exact hs.st_id P
  have htcur_r : (s.st P).tcur = es.g.epoch P := by rw [hs.s_eq]; exact hs.st_tcur P
  have hvR_r : (s.st P).vR = (es.g.st P).vR := by rw [hs.s_eq]; rfl
  have hid_v := hs.st_id P
  have htcur_v := hs.st_tcur P
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
  · unfold vRecv
    simp only [hid_v, htcur_v, hnsend, hlt, decide_false, Bool.or_self, Bool.false_eq_true,
      ↓reduceIte, hne, pure_bind, liftH_run]
    cases hv : (es.g.st P).vR c.1.1 with
    | none => simp [hv]
    | some v =>
      simp only [hv, hooksCKA, StateT.run_bind, StateT.run_pure, pure_bind]
      cases hfs : fs.receive v c.1 c.2 <;> simp [hfs]

theorem vRecv_new_honest {tStar_hs : ℕ} {P : Party} {c : Header T × E}
    {rec : Option (Record M (Header T × E))}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar_hs s es sc)
    (hnsend : P.sendsIn c.1.1 = false)
    (heq : c.1.1 = es.g.epoch P + 1)
    {T_t : T} {I_t : I}
    (hcT : c.1.2 = some T_t)
    (hcache : es.h.cache c.1.1 = some (T_t, I_t))
    (hI : (cka.receive (s.st P).γ T_t).2 = I_t) :
    let p := prng.up (es.g.st P).root I_t
    receive cka prng fs (s.st P) c =
      (match fs.receive (fs.initReceiver p.2) c.1 c.2 with
      | none => none
      | some (v', i, m) =>
        some ({ s.st P with tcur := c.1.1, γ := (cka.receive (s.st P).γ T_t).1, root := p.1,
                            vR := Function.update (es.g.st P).vR c.1.1 (some v') },
          c.1.1, i, m)) ∧
    (liftH (vRecv (hooksCKA cka prng fs Δcka ⟨true, tL, tStar⟩)
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
  have hid_r : (s.st P).id = P := by rw [hs.s_eq]; exact hs.st_id P
  have htcur_r : (s.st P).tcur = es.g.epoch P := by rw [hs.s_eq]; exact hs.st_tcur P
  have hroot_r : (s.st P).root = (es.g.st P).root := by rw [hs.s_eq]; rfl
  have hvR_r : (s.st P).vR = (es.g.st P).vR := by rw [hs.s_eq]; rfl
  have hid_v := hs.st_id P
  have htcur_v := hs.st_tcur P
  have hlt : ¬(es.g.epoch P + 1 < c.1.1) := by omega
  have hnsend' : P.sendsIn (es.g.epoch P + 1) = false := by rwa [← heq]
  constructor
  · unfold receive
    simp only [hid_r, htcur_r, hroot_r, hvR_r, hnsend, hnsend', hlt, decide_false, Bool.or_self,
      Bool.false_eq_true, ↓reduceIte, heq, hcT, hI, Function.update_self]
    cases hfs : fs.receive (fs.initReceiver p.2) c.1 c.2 <;> simp [hfs, p, heq]
  · rw [heq] at hcache
    unfold vRecv
    cases hfs : fs.receive (fs.initReceiver p.2) c.1 c.2 <;>
      simp [hid_v, htcur_v, hnsend, hnsend', hlt, heq, hcT, hooksCKA,
        StateT.run_get, hcache, hfs, p]

theorem vRecv_new_none {tStar_hs : ℕ} {P : Party} {c : Header T × E}
    {rec : Option (Record M (Header T × E))}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar_hs s es sc)
    (hnsend : P.sendsIn c.1.1 = false)
    (heq : c.1.1 = es.g.epoch P + 1)
    (hcT : c.1.2 = none) :
    receive cka prng fs (s.st P) c = none ∧
    (liftH (vRecv (hooksCKA cka prng fs Δcka ⟨true, tL, tStar⟩)
      es.g P (es.g.st P) c rec)).run es = pure (some none, es) := by
  have hid_r : (s.st P).id = P := by rw [hs.s_eq]; exact hs.st_id P
  have htcur_r : (s.st P).tcur = es.g.epoch P := by rw [hs.s_eq]; exact hs.st_tcur P
  have hid_v := hs.st_id P
  have htcur_v := hs.st_tcur P
  have hlt : ¬(es.g.epoch P + 1 < c.1.1) := by omega
  have hnsend' : P.sendsIn (es.g.epoch P + 1) = false := by rwa [← heq]
  constructor
  · unfold receive
    simp [hid_r, htcur_r, hnsend, hnsend', hlt, heq, hcT]
  · unfold vRecv
    simp [hid_v, htcur_v, hnsend, hnsend', hlt, heq, hcT]

theorem vRecv_new_dishonest_ne {tStar_hs : ℕ} {P : Party} {c : Header T × E}
    {rec : Option (Record M (Header T × E))}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar_hs s es sc)
    (hnsend : P.sendsIn c.1.1 = false)
    (heq : c.1.1 = es.g.epoch P + 1)
    {Tn : T} (hcT : c.1.2 = some Tn)
    (hhon : ∀ Tc Ik, es.h.cache c.1.1 = some (Tc, Ik) → Tc ≠ Tn)
    (hne : c.1.1 ≠ tStar) :
    (liftH (vRecv (hooksCKA cka prng fs Δcka ⟨true, tL, tStar⟩)
      es.g P (es.g.st P) c rec)).run es = pure (some none, es) := by
  have hid_v := hs.st_id P
  have htcur_v := hs.st_tcur P
  have hlt : ¬(es.g.epoch P + 1 < c.1.1) := by omega
  have hnsend' : P.sendsIn (es.g.epoch P + 1) = false := by rwa [← heq]
  have hne' : es.g.epoch P + 1 ≠ tStar := by rwa [← heq]
  rw [heq] at hhon
  unfold vRecv
  cases hcache : es.h.cache (es.g.epoch P + 1) with
  | none =>
    simp [hid_v, htcur_v, hnsend, hnsend', hlt, heq, hcT, hooksCKA,
      StateT.run_get, hcache, hne']
  | some p =>
    rcases p with ⟨Tc, Ik⟩
    have hTc : Tc ≠ Tn := hhon Tc Ik hcache
    simp [hid_v, htcur_v, hnsend, hnsend', hlt, heq, hcT, hooksCKA,
      StateT.run_get, hcache, hTc, hne']

theorem vRecv_new_dishonest_tStar_local {P : Party} {c : Header T × E}
    {rec : Option (Record M (Header T × E))}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar s es sc)
    (hnsend : P.sendsIn c.1.1 = false)
    (heq : c.1.1 = es.g.epoch P + 1)
    {Tn : T} (hcT : c.1.2 = some Tn)
    (hhon : ∀ Tc Ik, es.h.cache c.1.1 = some (Tc, Ik) → Tc ≠ Tn)
    (htStar : c.1.1 = tStar)
    (hloc : isLocal tL Δcka (es.g.epoch P) = true) :
    let k := cka.receive (s.st P).γ Tn
    let p := prng.up (es.g.st P).root k.2
    receive cka prng fs (s.st P) c =
      (match fs.receive (fs.initReceiver p.2) c.1 c.2 with
      | none => none
      | some (v', i, m) =>
        some ({ s.st P with tcur := c.1.1, γ := k.1, root := p.1,
                            vR := Function.update (es.g.st P).vR c.1.1 (some v') },
          c.1.1, i, m)) ∧
    (liftH (vRecv (hooksCKA cka prng fs Δcka ⟨true, tL, tStar⟩)
      es.g P (es.g.st P) c rec)).run es =
      pure (some (match fs.receive (fs.initReceiver p.2) c.1 c.2 with
        | none => none
        | some (v', i, m) =>
          some ({ es.g.st P with tcur := c.1.1, γ := some k.1, root := p.1,
                                 vR := Function.update (es.g.st P).vR c.1.1 (some v') },
            c.1.1, i, m)), es) := by
  intro k p
  subst htStar
  have hid_r : (s.st P).id = P := by rw [hs.s_eq]; exact hs.st_id P
  have htcur_r : (s.st P).tcur = es.g.epoch P := by rw [hs.s_eq]; exact hs.st_tcur P
  have hroot_r : (s.st P).root = (es.g.st P).root := by rw [hs.s_eq]; rfl
  have hvR_r : (s.st P).vR = (es.g.st P).vR := by rw [hs.s_eq]; rfl
  have hid_v := hs.st_id P
  have htcur_v := hs.st_tcur P
  have hlt : ¬(es.g.epoch P + 1 < c.1.1) := by omega
  have hnsend' : P.sendsIn (es.g.epoch P + 1) = false := by rwa [← heq]
  have hγ := hs.γ_eq P
  simp only [hloc, ↓reduceIte] at hγ
  constructor
  · unfold receive
    simp only [hid_r, htcur_r, hroot_r, hvR_r, hnsend, hnsend', hlt, decide_false, Bool.or_self,
      Bool.false_eq_true, ↓reduceIte, heq, hcT, Function.update_self]
    cases hfs : fs.receive (fs.initReceiver p.2) c.1 c.2 <;> simp [hfs, p, k, heq]
  · rw [heq] at hhon
    unfold vRecv
    cases hcache : es.h.cache (es.g.epoch P + 1) with
    | none =>
      cases hfs : fs.receive (fs.initReceiver p.2) c.1 c.2 <;>
        simp [hid_v, htcur_v, hnsend, hnsend', hlt, heq, hcT, hooksCKA,
          StateT.run_get, hcache, hγ, hfs, p, k]
    | some pair =>
      rcases pair with ⟨Tc, Ik⟩
      have hTc : Tc ≠ Tn := hhon Tc Ik hcache
      cases hfs : fs.receive (fs.initReceiver p.2) c.1 c.2 <;>
        simp [hid_v, htcur_v, hnsend, hnsend', hlt, heq, hcT, hooksCKA,
          StateT.run_get, hcache, hTc, hγ, hfs, p, k]

theorem vRecv_new_dishonest_tStar_nonlocal {P : Party} {c : Header T × E}
    {rec : Option (Record M (Header T × E))}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar s es sc)
    (hnsend : P.sendsIn c.1.1 = false)
    (heq : c.1.1 = es.g.epoch P + 1)
    {Tn : T} (hcT : c.1.2 = some Tn)
    (hhon : ∀ Tc Ik, es.h.cache c.1.1 = some (Tc, Ik) → Tc ≠ Tn)
    (htStar : c.1.1 = tStar)
    (hloc : isLocal tL Δcka (es.g.epoch P) = false) :
    (liftH (vRecv (hooksCKA cka prng fs Δcka ⟨true, tL, tStar⟩)
      es.g P (es.g.st P) c rec)).run es = pure (none, es) := by
  subst htStar
  have hid_v := hs.st_id P
  have htcur_v := hs.st_tcur P
  have hlt : ¬(es.g.epoch P + 1 < c.1.1) := by omega
  have hnsend' : P.sendsIn (es.g.epoch P + 1) = false := by rwa [← heq]
  have hγ := hs.γ_eq P
  simp only [hloc, Bool.false_eq_true, ↓reduceIte] at hγ
  rw [heq] at hhon
  unfold vRecv
  cases hcache : es.h.cache (es.g.epoch P + 1) with
  | none =>
    simp [hid_v, htcur_v, hnsend, hnsend', hlt, heq, hcT, hooksCKA,
      StateT.run_get, hcache, hγ]
  | some pair =>
    rcases pair with ⟨Tc, Ik⟩
    have hTc : Tc ≠ Tn := hhon Tc Ik hcache
    simp [hid_v, htcur_v, hnsend, hnsend', hlt, heq, hcT, hooksCKA,
      StateT.run_get, hcache, hTc, hγ]

theorem mem_trans_of_inTransit {St Msg C : Type} [DecidableEq C]
    {g : GameState St Msg C} {Q : Party} {c : C} {r : Record Msg C}
    (h : g.inTransit Q c = some r) :
    r ∈ g.trans ∧ r.pos.sender = Q ∧ r.ct = c := by
  unfold GameState.inTransit at h
  have hmem := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
  exact ⟨hmem, hp.1, hp.2⟩

theorem receive_t_eq {st st' : PartyState Γ T Sig SS RS} {c : Header T × E}
    {t' i' : ℕ} {m' : M}
    (h : receive cka prng fs st c = some (st', t', i', m')) :
    t' = c.1.1 := by
  dsimp only [receive] at h
  split_ifs at h
  · cases hc2 : c.1.2 <;> simp [hc2] at h
    rename_i h1 h2 Tn
    cases hfs : fs.receive (fs.initReceiver (prng.up st.root (cka.receive st.γ Tn).2).2)
      c.1 c.2 <;> simp [hfs] at h
    exact h.2.1.symm
  · cases hv : st.vR c.1.1 <;> simp [hv] at h
    rename_i v
    cases hfs : fs.receive v c.1 c.2 <;> simp [hfs] at h
    exact h.2.1.symm

theorem step_deliver (P : Party) (c : Header T × E)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar s es sc)
    {contL : Option (RecvResult M) × GameState (PartyState Γ T Sig SS RS) M (Header T × E) → ProbComp Bool}
    {contR : (Option (RecvResult M) × EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)) ×
      CKA.GameState Γ T → ProbComp Bool}
    (ih : ∀ u {s' es' sc'}, Sync9 cka Δcka tL tStar s' es' sc' →
      𝒟[contL (u, s')] = 𝒟[contR ((u, es'), sc')]) :
    𝒟[(deliverImpl (scheme cka prng fs lam) (Config.auth tStar) (P, c)).run s >>= contL] =
      𝒟[((simulateQ
        ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (CKA.GameState Γ T) ProbComp) +
          CKA.oracleImpl cka Δcka (healEpoch tL))
        ((deliverE (hooksCKA cka prng fs Δcka ⟨true, tL, tStar⟩)
          fs.maxSkip (Config.auth tStar) (P, c)).run es)).run sc) >>= contR] := by
  dsimp only [deliverImpl, deliverE, Config.auth]
  have hwin : s.win = es.g.win := by rw [hs.s_eq]; rfl
  have hin_eq : s.inTransit P.other c = es.g.inTransit P.other c := by rw [hs.s_eq]; rfl
  have hch_eq : s.chall = es.g.chall := by rw [hs.s_eq]; rfl
  simp only [hs.no_abort, Bool.false_or, hwin, hin_eq, StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hw : es.g.win = true
  · simp [hw, ih none hs]
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, Bool.false_and]
    cases hin : es.g.inTransit P.other c with
    | none => simp [hin, ih none hs]
    | some r =>
      simp only [hin]
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
        simp only [pure_bind, simulateQ_bind, simulateQ_pure, StateT.run_pure, bind_assoc]
        cases hfs : fs.receive (fs.initReceiver (prng.up (es.g.st P).root I_t).2) c.1 c.2 with
        | none =>
          simp [hfs, ih (some .rejected) hs]
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
          simp only [hfs, StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
            simulateQ_bind, bind_assoc, hcom, StateT.run_modify, simulateQ_pure, hch_eq]
          exact ih _ hsync
      · have hle_P : c.1.1 ≤ es.g.epoch P := by omega
        obtain ⟨hrcvL, hrcvR⟩ :=
          vRecv_same_epoch cka prng fs Δcka tL tStar (rec := some r) hs hnsend hle_P
        dsimp only [scheme]
        rw [hrcvL, StateT.run_bind, hrcvR]
        simp only [pure_bind, simulateQ_bind, simulateQ_pure, StateT.run_pure, bind_assoc]
        cases hv : (es.g.st P).vR c.1.1 with
        | none =>
          simp [hv, ih (some .rejected) hs]
        | some v =>
          simp only [hv]
          cases hfs : fs.receive v c.1 c.2 with
          | none =>
            simp [hfs, ih (some .rejected) hs]
          | some val =>
            rcases val with ⟨v', i', m'⟩
            have hpos_le : r.pos.epoch ≤ es.g.epoch P := by omega
            have hcom := commitE_same cka prng fs Δcka tL tStar
              (P := P)
              (new := { es.g.st P with vR := Function.update (es.g.st P).vR c.1.1 (some v') })
              (pos := r.pos) (es := es) (sc := sc) rfl
            have hsync := hs.sync9_accept_same
              (Function.update (es.g.st P).vR c.1.1 (some v')) hpos_le
            simp only [hfs, StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
              simulateQ_bind, bind_assoc, hcom, StateT.run_modify, simulateQ_pure, hch_eq]
            exact ih _ hsync

theorem step_inject (P : Party) (c : Header T × E)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar s es sc)
    {contL : Option (RecvResult M) × GameState (PartyState Γ T Sig SS RS) M (Header T × E) → ProbComp Bool}
    {contR : (Option (RecvResult M) × EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)) ×
      CKA.GameState Γ T → ProbComp Bool}
    (ih : ∀ u {s' es' sc'}, Sync9 cka Δcka tL tStar s' es' sc' →
      𝒟[contL (u, s')] = 𝒟[contR ((u, es'), sc')])
    (hdoomed : ∀ u {s'}, DoomedAuth tL tStar s' → 𝒟[contL (u, s')] = 𝒟[(pure false : ProbComp Bool)])
    (habort : ∀ u {es' : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)} {sc'},
      es'.abort = true → 𝒟[contR ((u, es'), sc')] = 𝒟[(pure false : ProbComp Bool)]) :
    𝒟[(injectImpl (scheme cka prng fs lam) (2 + Δcka) qep (Config.auth tStar) (P, c)).run s >>= contL] =
      𝒟[((simulateQ
        ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (CKA.GameState Γ T) ProbComp) +
          CKA.oracleImpl cka Δcka (healEpoch tL))
        ((injectE (hooksCKA cka prng fs Δcka ⟨true, tL, tStar⟩)
          (2 + Δcka) qep (Config.auth tStar) (P, c)).run es)).run sc) >>= contR] := by
  dsimp only [injectImpl, injectE, Config.auth]
  have hwin : s.win = es.g.win := by rw [hs.s_eq]; rfl
  have hin_eq : s.inTransit P.other c = es.g.inTransit P.other c := by rw [hs.s_eq]; rfl
  have hsafe_eq : s.safeInj (2 + Δcka) = es.g.safeInj (2 + Δcka) := by rw [hs.s_eq]; rfl
  have htriv_eq : ∀ pos, s.trivial (2 + Δcka) pos = es.g.trivial (2 + Δcka) pos :=
    fun pos => by rw [hs.s_eq]; rfl
  simp only [hs.no_abort, Bool.false_or, hwin, hin_eq, hsafe_eq,
    StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hcond : (es.g.win || (es.g.inTransit P.other c).isSome || !es.g.safeInj (2 + Δcka)) = true
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
              vRecv_new_honest cka prng fs Δcka tL tStar (rec := none) hs hnsend hstep hc2 hcache' hI
            dsimp only [scheme]
            rw [hrcvL, StateT.run_bind, hrcvR]
            simp only [pure_bind, simulateQ_bind, simulateQ_pure, StateT.run_pure, bind_assoc]
            cases hfs : fs.receive (fs.initReceiver (prng.up (es.g.st P).root I_t).2) c.1 c.2 with
            | none =>
              simp [hfs, ih (some .rejected) hs]
            | some val =>
              rcases val with ⟨v', i', m'⟩
              simp only [hfs, htriv_eq, htriv_f, Bool.false_eq_true, ↓reduceIte]
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
                simp only [pure_bind, simulateQ_bind, simulateQ_pure, StateT.run_pure, bind_assoc]
                cases hfs : fs.receive
                    (fs.initReceiver (prng.up (es.g.st P).root (cka.receive (s.st P).γ Tn).2).2)
                    c.1 c.2 with
                | none =>
                  simp [hfs, ih (some .rejected) hs]
                | some val =>
                  rcases val with ⟨v', i', m'⟩
                  simp only [hfs, htriv_eq, htriv_f, Bool.false_eq_true, ↓reduceIte]
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
                  StateT.run_set, StateT.run_pure, simulateQ_pure]
                have hR : 𝒟[contR ((none, { es with abort := true }), sc)] =
                    𝒟[(pure false : ProbComp Bool)] :=
                  habort none rfl
                have hdoom : DoomedAuth tL tStar s := Or.inr (Or.inr (Or.inr hd4))
                have hrun : 𝒟[(injectImpl (scheme cka prng fs lam) (2 + Δcka) qep (Config.auth tStar) (P, c)).run s >>= contL] =
                    𝒟[(pure false : ProbComp Bool)] :=
                  evalDist_bind_eq_pure_false _ _ fun ⟨u, s'⟩ hmem =>
                    hdoomed u (doomedAuth_oracleImpl (scheme cka prng fs lam) (by omega) tL tStar
                      (.inr (.inl (.inr (P, c)))) hdoom hmem)
                dsimp only [injectImpl, Config.auth] at hrun
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
                simp [hrcvL, ih (some .rejected) hs]
              | some res =>
                rcases res with ⟨st', t', i', m'⟩
                have ht' : t' = c.1.1 := receive_t_eq cka prng fs hrcvL
                subst ht'
                have hfull : (c.1.1 == tStar) = false := beq_false_of_ne htStar
                simp only [hrcvL, htriv_eq, htriv_f, hfull, Bool.false_eq_true, ↓reduceIte]
                by_cases hqep : qep + 1 < c.1.1 <;> simp [hqep, ih (some .rejected) hs]
      · have hle_P : c.1.1 ≤ es.g.epoch P := by omega
        obtain ⟨hrcvL, hrcvR⟩ :=
          vRecv_same_epoch cka prng fs Δcka tL tStar (rec := none) hs hnsend hle_P
        dsimp only [scheme]
        rw [hrcvL, StateT.run_bind, hrcvR]
        simp only [pure_bind, simulateQ_bind, simulateQ_pure, StateT.run_pure, bind_assoc]
        cases hv : (es.g.st P).vR c.1.1 with
        | none =>
          simp [hv, ih (some .rejected) hs]
        | some v =>
          simp only [hv]
          cases hfs : fs.receive v c.1 c.2 with
          | none =>
            simp [hfs, ih (some .rejected) hs]
          | some val =>
            rcases val with ⟨v', i', m'⟩
            simp only [hfs]
            by_cases hqep : qep + 1 < c.1.1
            · simp [hqep, ih (some .rejected) hs]
            · simp only [hqep, ↓reduceIte, htriv_eq]
              by_cases htriv : es.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = true
              · have hcom := commitE_same cka prng fs Δcka tL tStar
                  (P := P)
                  (new := { es.g.st P with vR := Function.update (es.g.st P).vR c.1.1 (some v') })
                  (pos := ⟨P.other, c.1.1, i'⟩) (es := es) (sc := sc) rfl
                have hsync := hs.sync9_accept_same
                  (Function.update (es.g.st P).vR c.1.1 (some v')) (pos := ⟨P.other, c.1.1, i'⟩) hle_P
                simp only [htriv, ↓reduceIte, StateT.run_bind, StateT.run_set, pure_bind,
                  StateT.run_pure, simulateQ_bind, bind_assoc, hcom, StateT.run_modify,
                  simulateQ_pure]
                exact ih _ hsync
              · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
                by_cases hfull : (c.1.1 == tStar) = true
                · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_set,
                    StateT.run_modify, pure_bind, StateT.run_pure, simulateQ_pure]
                  exact ih (some .rejected) (hs.sync9_win true)
                · simp [hfull, ih (some .rejected) hs]

theorem simulateQ_liftM_run {ι : Type} {tspec : OracleSpec.{0, 0} ι} {σ α : Type}
    (oimpl : QueryImpl tspec (StateT σ ProbComp)) (p : ProbComp α) (st : σ) :
    (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp) + oimpl)
      (liftM p : Engine.TComp tspec α)).run st =
    (p >>= fun a => pure (a, st)) := by
  rw [← liftComp_eq_liftM]
  induction p using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t r ih =>
    rw [liftComp_bind, liftComp_liftM_query]
    have hq : (liftM (OracleSpec.query t) : Engine.TComp tspec _) =
        (liftM (OracleSpec.query (spec := unifSpec + tspec) (.inl t)) : Engine.TComp tspec _) := rfl
    have hrun :
        ((liftM ((QueryImpl.liftTarget (StateT σ ProbComp) (QueryImpl.ofLift unifSpec ProbComp) + oimpl)
          (.inl t)) : StateT σ ProbComp (unifSpec.Range t))).run st =
        ((liftM (OracleSpec.query t) : ProbComp _) >>= fun u => pure (u, st)) := rfl
    rw [hq, simulateQ_query_bind]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, StateT.run_bind]
    rw [hrun]
    simp only [bind_assoc, pure_bind, ih]

theorem simulateQ_sampleT_run {ι : Type} {tspec : OracleSpec.{0, 0} ι} {σ α : Type}
    [SampleableType α] (oimpl : QueryImpl tspec (StateT σ ProbComp)) (st : σ) :
    (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp) + oimpl)
      (sampleT α)).run st =
    (($ᵗ α : ProbComp α) >>= fun a => pure (a, st)) :=
  simulateQ_liftM_run oimpl ($ᵗ α) st

theorem realGS_epMgmt (sc : CKA.GameState Γ T)
    (g : GameState (PartyState (Option Γ) T Sig SS RS) M (Header T × E))
    (Δ qep : ℕ) (P : Party) (bad : Bool) :
    (realGS sc g).epMgmt Δ qep P bad = (g.epMgmt Δ qep P bad).map (realGS sc) := by
  unfold GameState.epMgmt
  dsimp only
  cases bad <;>
    by_cases h1 : P.sendsIn (g.epoch P + 1) = true <;>
    by_cases h2 : qep < g.epoch P + 1 <;>
    by_cases h3 : qep < g.epoch P <;>
    by_cases h4 : healedBy g.tL Δ (g.epoch P) = true <;>
    simp [GameState.safeCh, GameState.leak, realGS, h1, h2, h3, h4]

theorem vSend_same_epoch {P : Party} {m : M} {r : Option CCoins}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar s es sc)
    (hnsend : P.sendsIn (es.g.epoch P + 1) = false) :
    let h : Header T := (es.g.epoch P, (es.g.st P).curCkaMsg)
    let vS_e : Option SS × E :=
      match (es.g.st P).vS with
      | some v => (some (fs.send v h m).1, (fs.send v h m).2)
      | none => (none, default)
    (∀ coins, send cka prng fs (s.st P) m coins =
      ({ s.st P with vS := vS_e.1 }, (h, vS_e.2))) ∧
    ((liftH (vSend (hooksCKA cka prng fs Δcka ⟨true, tL, tStar⟩)
      es.g P (es.g.st P) m none r)).run es =
      pure (some ({ es.g.st P with vS := vS_e.1 }, (h, vS_e.2)), es)) := by
  intro h vS_e
  have hid_r : (s.st P).id = P := by rw [hs.s_eq]; exact hs.st_id P
  have htcur_r : (s.st P).tcur = es.g.epoch P := by rw [hs.s_eq]; exact hs.st_tcur P
  have hTcur_r : (s.st P).curCkaMsg = (es.g.st P).curCkaMsg := by rw [hs.s_eq]; rfl
  have hvS_r : (s.st P).vS = (es.g.st P).vS := by rw [hs.s_eq]; rfl
  have hid_v := hs.st_id P
  have htcur_v := hs.st_tcur P
  constructor
  · intro coins
    unfold send
    have hcond : ((s.st P).id.sendsIn ((s.st P).tcur + 1)) = false := by
      rw [hid_r, htcur_r, hnsend]
    dsimp only [vS_e]
    rw [hcond]
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases hvS : (es.g.st P).vS with
    | none =>
      have hvS_r' : (s.st P).vS = none := hvS_r.trans hvS
      rw [hvS_r']
      simp only [htcur_r, hTcur_r, h, Prod.mk.injEq, and_true]
      cases hp : s.st P
      simp_all
    | some v =>
      have hvS_r' : (s.st P).vS = some v := hvS_r.trans hvS
      rw [hvS_r']
      simp [htcur_r, hTcur_r, h]
  · unfold vSend
    have hcond : ((es.g.st P).id.sendsIn ((es.g.st P).tcur + 1)) = false := by
      rw [hid_v, htcur_v, hnsend]
    dsimp only [vS_e]
    rw [hcond]
    simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, liftH_run]
    cases hvS : (es.g.st P).vS with
    | none =>
      simp only [StateT.run_pure, pure_bind, htcur_v, h]
      congr 3
      cases hp : es.g.st P
      simp_all
    | some v =>
      simp [hooksCKA, hvS, htcur_v, h]

theorem send_new_eq {P : Party} {m : M} {coins : CCoins}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar s es sc)
    (hsend : P.sendsIn (es.g.epoch P + 1) = true) :
    let t := es.g.epoch P + 1
    let c_cka := cka.send (s.st P).γ coins
    let p := prng.up (es.g.st P).root c_cka.2.2
    let ss := fs.initSender p.2
    let h : Header T := (t, some c_cka.2.1)
    let out_fs := fs.send ss h m
    let st_r' : PartyState Γ T Sig SS RS :=
      { s.st P with tcur := t, γ := c_cka.1, curCkaMsg := some c_cka.2.1, root := p.1, vS := some out_fs.1 }
    send cka prng fs (s.st P) m coins = (st_r', (h, out_fs.2)) := by
  intro t c_cka p ss h out_fs st_r'
  have hid_r : (s.st P).id = P := by rw [hs.s_eq]; exact hs.st_id P
  have htcur_r : (s.st P).tcur = es.g.epoch P := by rw [hs.s_eq]; exact hs.st_tcur P
  have hroot_r : (s.st P).root = (es.g.st P).root := by rw [hs.s_eq]; rfl
  unfold send
  simp [hid_r, htcur_r, hroot_r, hsend, t, c_cka, p, ss, h, out_fs, st_r']

theorem vSend_new_local {P : Party} {m : M} {r : Option CCoins}
    {s₁ : GameState (PartyState (Option Γ) T Sig SS RS) M (Header T × E)}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar s es sc)
    (hsend : P.sendsIn (es.g.epoch P + 1) = true)
    (hloc : isLocal tL Δcka (es.g.epoch P) = true) :
    ((simulateQ
      ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (CKA.GameState Γ T) ProbComp) +
        CKA.oracleImpl cka Δcka (healEpoch tL))
      ((liftH (vSend (hooksCKA cka prng fs Δcka ⟨true, tL, tStar⟩)
        s₁ P (es.g.st P) m none r)).run es)).run sc) =
      ((match r with | none => $ᵗ CCoins | some c => pure c) >>= fun coins =>
        let t := es.g.epoch P + 1
        let c_cka := cka.send (s.st P).γ coins
        let p := prng.up (es.g.st P).root c_cka.2.2
        let ss := fs.initSender p.2
        let h : Header T := (t, some c_cka.2.1)
        let out_fs := fs.send ss h m
        let γv' : Option Γ := if isLocal tL Δcka t then some c_cka.1 else none
        let st_v' : PartyState (Option Γ) T Sig SS RS :=
          { es.g.st P with tcur := t, γ := γv', curCkaMsg := some c_cka.2.1, root := p.1, vS := some out_fs.1 }
        let h' : CKAState T I := { cache := Function.update es.h.cache t (some (c_cka.2.1, c_cka.2.2)) }
        let sc' : CKA.GameState Γ T :=
          if isLocal tL Δcka (es.g.epoch P) then sc else sc.afterSend P c_cka.1 c_cka.2.1
        pure ((some (st_v', (h, out_fs.2)), { es with h := h' }), sc')) := by
  have hid_v := hs.st_id P
  have htcur_v := hs.st_tcur P
  have hγ := hs.γ_eq P
  simp only [hloc, ↓reduceIte] at hγ
  have hloc_t : isLocal tL Δcka (es.g.epoch P + 1) = true := by
    rcases htL : tL with _ | l
    · rfl
    · simp only [isLocal, htL, decide_eq_true_eq] at hloc ⊢; omega
  unfold vSend
  simp only [hid_v, htcur_v, hsend, ↓reduceIte, hooksCKA, hγ, cacheC, liftH_run]
  cases r with
  | some c =>
    simp [hloc, hloc_t]
  | none =>
    simp only [StateT.run_bind, StateT.run_lift, StateT.run_modify, pure_bind, StateT.run_pure,
      simulateQ_bind, simulateQ_pure, bind_assoc, simulateQ_sampleT_run, hloc, hloc_t, ↓reduceIte]

theorem vSend_new_nonlocal_none {P : Party} {m : M}
    {s₁ : GameState (PartyState (Option Γ) T Sig SS RS) M (Header T × E)}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar s es sc)
    (hsend : P.sendsIn (es.g.epoch P + 1) = true)
    (hloc : isLocal tL Δcka (es.g.epoch P) = false) :
    ((simulateQ
      ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (CKA.GameState Γ T) ProbComp) +
        CKA.oracleImpl cka Δcka (healEpoch tL))
      ((liftH (vSend (hooksCKA cka prng fs Δcka ⟨true, tL, tStar⟩)
        s₁ P (es.g.st P) m none none)).run es)).run sc) =
      (($ᵗ CCoins : ProbComp CCoins) >>= fun coins =>
        let t := es.g.epoch P + 1
        let c_cka := cka.send (s.st P).γ coins
        let p := prng.up (es.g.st P).root c_cka.2.2
        let ss := fs.initSender p.2
        let h : Header T := (t, some c_cka.2.1)
        let out_fs := fs.send ss h m
        let γv' : Option Γ := if isLocal tL Δcka t then some c_cka.1 else none
        let st_v' : PartyState (Option Γ) T Sig SS RS :=
          { es.g.st P with tcur := t, γ := γv', curCkaMsg := some c_cka.2.1, root := p.1, vS := some out_fs.1 }
        let h' : CKAState T I := { cache := Function.update es.h.cache t (some (c_cka.2.1, c_cka.2.2)) }
        let sc' : CKA.GameState Γ T :=
          if isLocal tL Δcka (es.g.epoch P) then sc else sc.afterSend P c_cka.1 c_cka.2.1
        pure ((some (st_v', (h, out_fs.2)), { es with h := h' }), sc')) := by
  have hid_v := hs.st_id P
  have htcur_v := hs.st_tcur P
  have hγ := hs.γ_eq P
  simp only [hloc, Bool.false_eq_true, ↓reduceIte] at hγ
  rcases htL : tL with _ | l
  · simp [isLocal, htL] at hloc
  · have hloc_l : isLocal (some l) Δcka (es.g.epoch P) = false := by
      simpa [htL] using hloc
    have hloc' : es.g.epoch P < l + 2 + Δcka := by
      simpa [isLocal] using hloc_l
    have heq := hs.epoch_eq_of_sendsIn_succ hsend
    have hsc_P : sc.epoch P = es.g.epoch P := by
      rw [hs.sc_epoch l htL P]; omega
    have hsc_Po : sc.epoch P.other = es.g.epoch P := by
      rw [hs.sc_epoch l htL P.other, ← heq]; omega
    have hcan : sc.canSend P = true := by
      simp [CKA.GameState.canSend, hsc_P, hsc_Po, hsend]
    have hstP : sc.st P = (s.st P).γ := by
      rw [hs.s_eq]
      simp [realGS, realVP, hγ]
    unfold vSend
    simp only [hid_v, htcur_v, hsend, ↓reduceIte, hooksCKA, hγ, cacheC, liftH_run, liftC]
    by_cases htH : es.g.epoch P + 1 = (Mode.mk true (some l) tStar).tH
    · have heq_tH : sc.epoch P + 1 = healEpoch (some l) := by
        rw [hsc_P]; exact htH
      simp only [eq_true htH, ↓reduceIte, CKA.challQuery, StateT.run_bind, StateT.run_lift,
        StateT.run_monadLift, monadLift_self, StateT.run_modify, simulateQ_bind,
        simulateQ_query_eq, simulateQ_pure, QueryImpl.add_apply, CKA.oracleImpl, CKA.challImpl,
        hcan, heq_tH, bne_self_eq_false, Bool.not_true, Bool.or_self, Bool.false_eq_true,
        StateT.run_get, pure_bind, StateT.run_set, hs.sc_b, StateT.run_pure,
        hstP, bind_assoc]
      refine bind_congr fun coins => ?_
      have hafter_st :
          (sc.afterSend P (cka.send (s.st P).γ coins).1 (cka.send (s.st P).γ coins).2.1).st P =
            (cka.send (s.st P).γ coins).1 := by
        simp [CKA.GameState.afterSend]
      by_cases hloc_t : isLocal (some l) Δcka (es.g.epoch P + 1) = true
      · have htH_le : (Mode.mk true (some l) tStar).tH + Δcka ≤ es.g.epoch P + 1 := by
          simpa [isLocal, Mode.tH, healEpoch] using hloc_t
        have hfin : (sc.afterSend P (cka.send (s.st P).γ coins).1 (cka.send (s.st P).γ coins).2.1).finished
            Δcka (healEpoch (some l)) P = true := by
          simp only [CKA.GameState.finished, CKA.GameState.afterSend, Function.update_self,
            hsc_P, decide_eq_true_eq]
          simpa [Mode.tH] using htH_le
        simp [htH_le, hloc_t, hloc_l, CKA.corrQuery, QueryImpl.add_apply, CKA.oracleImpl,
          CKA.corrImpl, hfin, hafter_st]
      · have htH_lt : ¬((Mode.mk true (some l) tStar).tH + Δcka ≤ es.g.epoch P + 1) := by
          simpa [isLocal, Mode.tH, healEpoch] using hloc_t
        simp [htH_lt, hloc_t, hloc_l]
    · have hne_tH : (sc.epoch P + 1 == healEpoch (some l)) = false := by
        rw [hsc_P, beq_eq_false_iff_ne]; exact htH
      simp only [eq_false htH, ↓reduceIte, CKA.sendQuery, StateT.run_bind, StateT.run_lift,
        StateT.run_monadLift, monadLift_self, StateT.run_modify, simulateQ_bind,
        simulateQ_query_eq, simulateQ_pure, QueryImpl.add_apply, CKA.oracleImpl, CKA.sendImpl,
        hcan, hne_tH, Bool.not_true, Bool.or_self, Bool.false_eq_true,
        StateT.run_get, pure_bind, StateT.run_set, StateT.run_pure, hstP, bind_assoc]
      refine bind_congr fun coins => ?_
      have hafter_st :
          (sc.afterSend P (cka.send (s.st P).γ coins).1 (cka.send (s.st P).γ coins).2.1).st P =
            (cka.send (s.st P).γ coins).1 := by
        simp [CKA.GameState.afterSend]
      by_cases hloc_t : isLocal (some l) Δcka (es.g.epoch P + 1) = true
      · have htH_le : (Mode.mk true (some l) tStar).tH + Δcka ≤ es.g.epoch P + 1 := by
          simpa [isLocal, Mode.tH, healEpoch] using hloc_t
        have hfin : (sc.afterSend P (cka.send (s.st P).γ coins).1 (cka.send (s.st P).γ coins).2.1).finished
            Δcka (healEpoch (some l)) P = true := by
          simp only [CKA.GameState.finished, CKA.GameState.afterSend, Function.update_self,
            hsc_P, decide_eq_true_eq]
          simpa [Mode.tH] using htH_le
        simp [htH_le, hloc_t, hloc_l, CKA.corrQuery, QueryImpl.add_apply, CKA.oracleImpl,
          CKA.corrImpl, hfin, hafter_st]
      · have htH_lt : ¬((Mode.mk true (some l) tStar).tH + Δcka ≤ es.g.epoch P + 1) := by
          simpa [isLocal, Mode.tH, healEpoch] using hloc_t
        simp [htH_lt, hloc_t, hloc_l]

theorem vSend_new_nonlocal_some_le {P : Party} {m : M} {coins : CCoins} {l : ℕ}
    {s₁ : GameState (PartyState (Option Γ) T Sig SS RS) M (Header T × E)}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar s es sc)
    (htL : tL = some l)
    (hsend : P.sendsIn (es.g.epoch P + 1) = true)
    (hle : es.g.epoch P + 1 ≤ l) :
    ((simulateQ
      ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (CKA.GameState Γ T) ProbComp) +
        CKA.oracleImpl cka Δcka (healEpoch tL))
      ((liftH (vSend (hooksCKA cka prng fs Δcka ⟨true, tL, tStar⟩)
        s₁ P (es.g.st P) m none (some coins))).run es)).run sc) =
      (let t := es.g.epoch P + 1
       let c_cka := cka.send (s.st P).γ coins
       let p := prng.up (es.g.st P).root c_cka.2.2
       let ss := fs.initSender p.2
       let h : Header T := (t, some c_cka.2.1)
       let out_fs := fs.send ss h m
       let γv' : Option Γ := if isLocal tL Δcka t then some c_cka.1 else none
       let st_v' : PartyState (Option Γ) T Sig SS RS :=
         { es.g.st P with tcur := t, γ := γv', curCkaMsg := some c_cka.2.1, root := p.1, vS := some out_fs.1 }
       let h' : CKAState T I := { cache := Function.update es.h.cache t (some (c_cka.2.1, c_cka.2.2)) }
       let sc' : CKA.GameState Γ T :=
         if isLocal tL Δcka (es.g.epoch P) then sc else sc.afterSend P c_cka.1 c_cka.2.1
       pure ((some (st_v', (h, out_fs.2)), { es with h := h' }), sc')) := by
  have hid_v := hs.st_id P
  have htcur_v := hs.st_tcur P
  have hloc : isLocal tL Δcka (es.g.epoch P) = false := by
    simp only [isLocal, htL, decide_eq_false_iff_not]; omega
  have hloc_t : isLocal tL Δcka (es.g.epoch P + 1) = false := by
    simp only [isLocal, htL, decide_eq_false_iff_not]; omega
  have htH_lt : ¬((Mode.mk true tL tStar).tH + Δcka ≤ es.g.epoch P + 1) := by
    simp only [Mode.tH, healEpoch, htL]; omega
  have hγ := hs.γ_eq P
  simp only [hloc, Bool.false_eq_true, ↓reduceIte] at hγ
  have heq := hs.epoch_eq_of_sendsIn_succ hsend
  have hsc_P : sc.epoch P = es.g.epoch P := by
    rw [hs.sc_epoch l htL P]; omega
  have hsc_Po : sc.epoch P.other = es.g.epoch P := by
    rw [hs.sc_epoch l htL P.other, ← heq]; omega
  have hcan : sc.canSend P = true := by
    simp [CKA.GameState.canSend, hsc_P, hsc_Po, hsend]
  have hbad_ok : ¬(healEpoch tL < sc.epoch P + 1 + 2) := by
    simp only [hsc_P, healEpoch, htL]; omega
  have hstP : sc.st P = (s.st P).γ := by
    rw [hs.s_eq]
    simp [realGS, realVP, hγ]
  unfold vSend
  simp [hid_v, htcur_v, hsend, hooksCKA, hγ, cacheC, liftH_run, liftC, CKA.sendWithAdversaryCoinsQuery,
    QueryImpl.add_apply, CKA.oracleImpl, CKA.sendWithAdversaryCoinsImpl, hcan, hbad_ok, hstP,
    htH_lt, hloc, hloc_t]

theorem vSend_new_nonlocal_some_gt {P : Party} {m : M} {coins : CCoins} {l : ℕ}
    {s₁ : GameState (PartyState (Option Γ) T Sig SS RS) M (Header T × E)}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar s es sc)
    (htL : tL = some l)
    (hsend : P.sendsIn (es.g.epoch P + 1) = true)
    (hloc : isLocal tL Δcka (es.g.epoch P) = false)
    (hgt : l < es.g.epoch P + 1) :
    ((simulateQ
      ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (CKA.GameState Γ T) ProbComp) +
        CKA.oracleImpl cka Δcka (healEpoch tL))
      ((liftH (vSend (hooksCKA cka prng fs Δcka ⟨true, tL, tStar⟩)
        s₁ P (es.g.st P) m none (some coins))).run es)).run sc) =
      pure ((none, es), sc) := by
  have hid_v := hs.st_id P
  have htcur_v := hs.st_tcur P
  have hγ := hs.γ_eq P
  simp only [hloc, Bool.false_eq_true, ↓reduceIte] at hγ
  have hloc' : es.g.epoch P < l + 2 + Δcka := by
    simpa [isLocal, htL] using hloc
  have hsc_P : sc.epoch P = es.g.epoch P := by
    rw [hs.sc_epoch l htL P]; omega
  have hbad_f : healEpoch tL < sc.epoch P + 1 + 2 := by
    simp only [hsc_P, healEpoch, htL]; omega
  unfold vSend
  simp [hid_v, htcur_v, hsend, hooksCKA, hγ, liftH_run, liftC, CKA.sendWithAdversaryCoinsQuery,
    QueryImpl.add_apply, CKA.oracleImpl, CKA.sendWithAdversaryCoinsImpl, hbad_f]

theorem transmitImpl_run_eq {P : Party} {m : M} {r : Option CCoins}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar s es sc)
    (hw : es.g.win = false) :
    ((transmitImpl (scheme cka prng fs lam) (2 + Δcka) qep (P, m, r)).run s) =
      ((match r with | none => $ᵗ CCoins | some c => pure c) >>= fun coins =>
        match es.g.epMgmt (2 + Δcka) qep P r.isSome with
        | none => pure (none, s)
        | some s₁ =>
          let out := send cka prng fs (s.st P) m coins
          pure (some out.2,
            (realGS sc s₁).record (2 + Δcka) P out.1
              ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, out.2⟩ false)) := by
  have hwin : s.win = false := by rw [hs.s_eq]; exact hw
  have hep : ∀ bad, s.epMgmt (2 + Δcka) qep P bad =
      (es.g.epMgmt (2 + Δcka) qep P bad).map (realGS sc) := by
    intro bad
    rw [hs.s_eq, realGS_epMgmt]
  have hst1 : ∀ bad s₁, es.g.epMgmt (2 + Δcka) qep P bad = some s₁ →
      realVP (sc.st P) (s₁.st P) = s.st P := by
    intro bad s₁ h1
    have hst_eq : s₁.st = es.g.st := by
      unfold GameState.epMgmt at h1
      split_ifs at h1 <;> (injection h1 with h1; subst h1; simp [GameState.leak])
    rw [hs.s_eq]
    simp [realGS, hst_eq]
  unfold transmitImpl samIfNec
  cases r with
  | none =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin, Bool.false_eq_true, ↓reduceIte,
      StateT.run_monadLift, monadLift_self, StateT.run_pure, bind_assoc, Option.isSome_none,
      hep false]
    refine bind_congr fun coins => ?_
    cases h1 : es.g.epMgmt (2 + Δcka) qep P false with
    | none => simp
    | some s₁ =>
      simp [realGS, hst1 false s₁ h1, scheme]
  | some c =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin, Bool.false_eq_true, ↓reduceIte,
      StateT.run_monadLift, monadLift_self, StateT.run_pure, bind_assoc, Option.isSome_some,
      hep true]
    cases h1 : es.g.epMgmt (2 + Δcka) qep P true with
    | none => simp
    | some s₁ =>
      simp [realGS, hst1 true s₁ h1, scheme]

theorem step_transmit (P : Party) (m : M) (r : Option CCoins)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar s es sc)
    {contL : Option (Header T × E) × GameState (PartyState Γ T Sig SS RS) M (Header T × E) → ProbComp Bool}
    {contR : (Option (Header T × E) × EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)) ×
      CKA.GameState Γ T → ProbComp Bool}
    (ih : ∀ u {s' es' sc'}, Sync9 cka Δcka tL tStar s' es' sc' →
      𝒟[contL (u, s')] = 𝒟[contR ((u, es'), sc')])
    (hdoomed : ∀ u {s'}, DoomedAuth tL tStar s' → 𝒟[contL (u, s')] = 𝒟[(pure false : ProbComp Bool)])
    (habort : ∀ u {es' : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)} {sc'},
      es'.abort = true → 𝒟[contR ((u, es'), sc')] = 𝒟[(pure false : ProbComp Bool)]) :
    𝒟[(transmitImpl (scheme cka prng fs lam) (2 + Δcka) qep (P, m, r)).run s >>= contL] =
      𝒟[((simulateQ
        ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (CKA.GameState Γ T) ProbComp) +
          CKA.oracleImpl cka Δcka (healEpoch tL))
        ((transmitE (hooksCKA cka prng fs Δcka ⟨true, tL, tStar⟩)
          (2 + Δcka) qep ⟨true, tL, tStar⟩ (P, m, r)).run es)).run sc) >>= contR] := by
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
      · simp only [hld, ↓reduceIte, abortE, StateT.run_bind, StateT.run_modify, StateT.run_set,
          pure_bind, StateT.run_pure, simulateQ_pure]
        have hR : 𝒟[contR ((none, { es with abort := true }), sc)] = 𝒟[(pure false : ProbComp Bool)] :=
          habort none rfl
        rw [hR]
        refine evalDist_bind_eq_pure_false _ _ fun coins _ => ?_
        have hdoom := hs.doomed_of_leakDoom_epMgmt hw_f hep hld
          (send cka prng fs (s.st P) m coins).1 m (send cka prng fs (s.st P) m coins).2 false
        exact hdoomed (some (send cka prng fs (s.st P) m coins).2) hdoom
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
          have hsend_eq := fun coins => send_new_eq cka prng fs Δcka tL tStar (m := m) (coins := coins) hs hsend
          dsimp only at hsend_eq
          by_cases hloc : isLocal tL Δcka (es.g.epoch P) = true
          · have hvR := vSend_new_local cka prng fs Δcka tL tStar (m := m) (r := r) (s₁ := s₁) hs hsend hloc
            rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, hvR]
            simp only [bind_assoc, pure_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure,
              hs₁_ep, hs₁_idx]
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
              simp only [bind_assoc, pure_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure,
                hs₁_ep, hs₁_idx]
              refine evalDist_bind_congr _ _ _ fun coins => ?_
              rw [hsend_eq coins]
              exact ih _ (hs.sync9_send_new prng fs hsend hep coins m false)
            | some coins =>
              by_cases hle : es.g.epoch P + 1 ≤ l
              · have hvR := vSend_new_nonlocal_some_le cka prng fs Δcka tL tStar
                  (m := m) (coins := coins) (s₁ := s₁) hs htL hsend hle
                rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, hvR]
                simp only [bind_assoc, pure_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure,
                  hs₁_ep, hs₁_idx]
                rw [hsend_eq coins]
                exact ih _ (hs.sync9_send_new prng fs hsend hep coins m false)
              · have hgt : l < es.g.epoch P + 1 := by omega
                have hvR := vSend_new_nonlocal_some_gt cka prng fs Δcka tL tStar
                  (m := m) (coins := coins) (s₁ := s₁) hs htL hsend hloc_f hgt
                rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, hvR]
                simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify,
                  StateT.run_set, StateT.run_pure, simulateQ_pure]
                have hR : 𝒟[contR ((none, { es with abort := true }), sc)] =
                    𝒟[(pure false : ProbComp Bool)] :=
                  habort none rfl
                have hdoom := hs.doomed4_of_sendBad_gt htL hloc' hsend hep hld_f hgt
                  (send cka prng fs (s.st P) m coins).1 m (send cka prng fs (s.st P) m coins).2 false
                have hL : 𝒟[contL
                    (some (send cka prng fs (s.st P) m coins).2,
                      (realGS sc s₁).record (2 + Δcka) P (send cka prng fs (s.st P) m coins).1
                        ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, (send cka prng fs (s.st P) m coins).2⟩ false)] =
                    𝒟[(pure false : ProbComp Bool)] :=
                  hdoomed (some (send cka prng fs (s.st P) m coins).2) hdoom
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
          simp only [hsendL, hreal_eq, pure_bind, StateT.run_modify, StateT.run_pure,
            simulateQ_bind, simulateQ_pure, bind_assoc, OracleComp.evalDist_bind_const]
          exact ih _ (hs.sync9_send_same hnsend _ m _ false)

theorem runL_eq_runR_of_sync {α : Type}
    (oa : AdversaryComp (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL tStar s es sc) :
    𝒟[runL cka prng fs lam Δcka qep tL tStar oa s] =
      𝒟[runR cka prng fs Δcka qep tL tStar oa es sc] := by
  induction oa using OracleComp.inductionOn generalizing s es sc with
  | pure a =>
    rw [runL_pure, runR_pure]
    have hwin : s.win = es.g.win := by rw [hs.s_eq]; rfl
    have hok : authLosingConditionsAvoided (2 + Δcka) tL tStar s = authLosingConditionsAvoided (2 + Δcka) tL tStar es.g := by
      rw [hs.s_eq]; rfl
    simp [authOut, hs.no_abort, hwin, hok]
  | query_bind t k ih =>
    change 𝒟[runL cka prng fs lam Δcka qep tL tStar (query (spec := ASpec) t >>= k) s] =
      𝒟[runR cka prng fs Δcka qep tL tStar (query (spec := ASpec) t >>= k) es sc]
    rcases t with n | ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
    · rw [runL_query_bind, runR_query_bind]
      exact step_coins cka n (fun u => ih u hs)
    · rw [runL_query_bind, runR_query_bind]
      exact step_transmit cka prng fs lam Δcka qep tL tStar P m r hs @ih
        (fun u _ hd => evalDist_runL_eq_pure_false_of_doomed cka prng fs lam Δcka qep tL tStar (k u) _ hd)
        (fun u _ _ hab => evalDist_runR_eq_pure_false_of_abort
          (hooksCKA cka prng fs Δcka ⟨true, tL, tStar⟩)
          (2 + Δcka) qep fs.maxSkip (Config.auth tStar) ⟨true, tL, tStar⟩
          (CKA.oracleImpl cka Δcka (healEpoch tL)) (k u) _ _ hab)
    · rw [runL_query_bind, runR_query_bind]
      exact step_chall cka prng fs lam qep tStar P m₀ m₁ r hs.no_abort (by rw [hs.s_eq]; rfl) (ih none hs)
    · rw [runL_query_bind, runR_query_bind]
      exact step_deliver cka prng fs lam Δcka tL tStar P c hs @ih
    · rw [runL_query_bind, runR_query_bind]
      exact step_inject cka prng fs lam Δcka qep tL tStar P c hs @ih
        (fun u _ hd => evalDist_runL_eq_pure_false_of_doomed cka prng fs lam Δcka qep tL tStar (k u) _ hd)
        (fun u _ _ hab => evalDist_runR_eq_pure_false_of_abort
          (hooksCKA cka prng fs Δcka ⟨true, tL, tStar⟩)
          (2 + Δcka) qep fs.maxSkip (Config.auth tStar) ⟨true, tL, tStar⟩
          (CKA.oracleImpl cka Δcka (healEpoch tL)) (k u) _ _ hab)
    · exact step_corr cka prng fs lam Δcka qep tL tStar P k hs @ih

theorem sync9_init_none (hc : cka.Correct)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) none tStar = true)
    (kr : KR) (kc kc_ext : KC) :
    let out := prng.up (prng.init kr) lam
    let γv := mkParties (T := T)
        (some (cka.initA kc)) (some (cka.initB kc))
        out.1 (fs.initSender out.2) (fs.initReceiver out.2)
    let g₀ : Ctx (Option Γ) T Sig SS RS M E :=
      { st := fun P => match P with | .A => γv.1 | .B => γv.2, b := false }
    Sync9 cka Δcka none tStar
      (initState (scheme cka prng fs lam) (kr, kc) false)
      { g := g₀, h := {} }
      (CKA.initState cka kc_ext false) := by
  intro out γv g₀
  have h0 := Sync9.sync9_init prng fs lam hc hvg kr kc
  dsimp only at h0
  exact
    { valid := h0.valid
      s_eq := by
        simp only [initState, scheme, realGS, g₀]
        congr 1
        funext P
        cases P <;> rfl
      no_abort := rfl
      b_eq := rfl
      sc_b := rfl
      st_id := h0.st_id
      st_tcur := h0.st_tcur
      γ_eq := fun P => by
        dsimp only [g₀, γv, mkParties, initState, scheme, initParty]
        cases P <;> simp [isLocal]
      sc_epoch := fun l htL => by nomatch htL
      tL_none := h0.tL_none
      tL_some := h0.tL_some
      leaks_ub := h0.leaks_ub
      comp_unhealed := h0.comp_unhealed
      epoch_le := h0.epoch_le
      epoch_step_sends := h0.epoch_step_sends
      trans_inv := h0.trans_inv
      cache_gt := h0.cache_gt
      cka_eq := h0.cka_eq
      cka_step := h0.cka_step }

theorem authGame_eq_runL (t : ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    authGame (scheme cka prng fs lam) (2 + Δcka) qep tL t A =
      ($ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
        runL cka prng fs lam Δcka qep tL t A
          (initState (scheme cka prng fs lam) (kr, kc) false)) := by
  unfold authGame CryptoGames.SM.run runL
  simp only [uniformSample, SampleableType.selectElem, seq_eq_bind_map, map_eq_bind_pure_comp,
    Function.comp_apply, pure_bind, bind_assoc]

theorem lemma9_proof (hc : cka.Correct) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    authAdvantage (scheme cka prng fs lam) (2 + Δcka) qep tL t A ≤
      𝒟[CKA.branch cka Δcka (healEpoch tL) false
        (redCKAAuth cka prng fs lam Δcka qep tL t A)] {true} := by
  by_cases hvg : lastLeakGuessAdmissible (2 + Δcka) tL t = true
  · apply le_of_eq
    unfold authAdvantage
    rw [authGame_eq_runL]
    congr 1
    cases htL : tL with
    | none =>
      subst htL
      unfold CKA.branch redCKAAuth runCKA engRun initCKA
      simp only [StateT.run'_eq, StateT.run_bind, StateT.run_lift, StateT.run_pure,
        pure_bind, bind_assoc, simulateQ_bind, simulateQ_pure, simulateQ_sampleT_run,
        map_bind, Functor.map_map]
      symm
      refine (evalDist_bind_congr ($ᵗ KC) _
        (fun _ => $ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
          runL cka prng fs lam Δcka qep none t A
            (initState (scheme cka prng fs lam) (kr, kc) false)) ?_).trans ?_
      · intro kc_ext
        refine evalDist_bind_congr _ _ _ fun kr => ?_
        refine evalDist_bind_congr _ _ _ fun kc => ?_
        symm
        refine (runL_eq_runR_of_sync cka prng fs lam Δcka qep none t A
          (sync9_init_none cka prng fs lam Δcka t hc hvg kr kc kc_ext)).trans ?_
        simp only [runR, Mode.cfg, Mode.policy, bind_pure_comp, ↓reduceIte, map_pure]
        rfl
      · exact OracleComp.evalDist_bind_const ($ᵗ KC) _
    | some l =>
      subst htL
      unfold CKA.branch redCKAAuth runCKA engRun initCKA
      simp only [StateT.run'_eq, StateT.run_bind, StateT.run_lift, StateT.run_pure,
        pure_bind, bind_assoc, simulateQ_bind, simulateQ_pure, simulateQ_sampleT_run,
        map_bind, Functor.map_map]
      rw [OracleComp.evalDist_bind_bind_swap ($ᵗ KR) ($ᵗ KC)]
      refine evalDist_bind_congr _ _ _ fun kc => ?_
      refine evalDist_bind_congr _ _ _ fun kr => ?_
      refine (runL_eq_runR_of_sync cka prng fs lam Δcka qep (some l) t A
        (Sync9.sync9_init prng fs lam hc hvg kr kc)).trans ?_
      simp only [runR, Mode.cfg, Mode.policy, bind_pure_comp, ↓reduceIte, map_pure]
      rfl
  · have hvg_f : lastLeakGuessAdmissible (2 + Δcka) tL t = false := Bool.eq_false_iff.mpr hvg
    have hzero : authAdvantage (scheme cka prng fs lam) (2 + Δcka) qep tL t A = 0 := by
      unfold authAdvantage authGame
      simp only [bind_assoc]
      refine evalDist_true_eq_zero_of_support _ _ fun res _ => ?_
      simp [authLosingConditionsAvoided, hvg_f]
    rw [hzero]
    exact zero_le

end CryptoGames.SM.Construction.AuthL9

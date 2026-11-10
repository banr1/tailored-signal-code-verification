/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperShiftedFS
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFS
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma9
import ProofLib.SepLogic.WP.StateNorm

/-!
# Shifted-Paper Hop 2, Part 1

Synchronization invariant `Sync10ShiftedPaper` and step lemmas (`coinsE`, `challE`, `corrE`,
`injectE`) for the shifted-paper Hop 2 (`CKA.branch cka 1 (l + 1) true` to
`PRFPRNG.branch prng false`).
-/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory OracleComp OracleSpec

namespace CryptoGames.SM.Construction.DeliverForge

open CryptoGames.SM
open CryptoGames.SM.Engine
open CryptoGames.SM.Construction
open CryptoGames.SM.Construction.AuthL9
open CryptoGames.SM.Construction.AuthL10
open CryptoGames.SM.Construction.DeliverForge.AuthL10DF
open CryptoGames.LibsignalSM.Proofs.Refinement

namespace AuthL10ShiftedPaper

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

def clearCompTL {St Msg C : Type} (g : SM.GameState St Msg C) : SM.GameState St Msg C :=
  { g with comp := [], tL := none, leaks := [], corrs := [] }

@[simp] theorem clearCompTL_st {St Msg C : Type} (g : SM.GameState St Msg C) :
    (clearCompTL g).st = g.st := rfl

@[simp] theorem clearCompTL_epoch {St Msg C : Type} (g : SM.GameState St Msg C) :
    (clearCompTL g).epoch = g.epoch := rfl

@[simp] theorem clearCompTL_idx {St Msg C : Type} (g : SM.GameState St Msg C) :
    (clearCompTL g).idx = g.idx := rfl

@[simp] theorem clearCompTL_tL {St Msg C : Type} (g : SM.GameState St Msg C) :
    (clearCompTL g).tL = none := rfl

@[simp] theorem clearCompTL_trans {St Msg C : Type} (g : SM.GameState St Msg C) :
    (clearCompTL g).trans = g.trans := rfl

@[simp] theorem clearCompTL_chall {St Msg C : Type} (g : SM.GameState St Msg C) :
    (clearCompTL g).chall = g.chall := rfl

@[simp] theorem clearCompTL_comp {St Msg C : Type} (g : SM.GameState St Msg C) :
    (clearCompTL g).comp = [] := rfl

@[simp] theorem clearCompTL_win {St Msg C : Type} (g : SM.GameState St Msg C) :
    (clearCompTL g).win = g.win := rfl

@[simp] theorem clearCompTL_accept {St Msg C : Type} [DecidableEq C]
    (g : SM.GameState St Msg C) (P : Party) (st' : St) (pos : SM.Pos) :
    clearCompTL (g.accept P st' pos) = (clearCompTL g).accept P st' pos := by
  simp [clearCompTL, SM.GameState.accept, SM.GameState.delete]

@[simp] theorem clearCompTL_record {St Msg C : Type}
    (g : SM.GameState St Msg C) (Δ : ℕ) (P : Party) (st' : St) (rcd : SM.Record Msg C) :
    clearCompTL (g.record Δ P st' rcd false) =
      (clearCompTL g).record (2 + 1) P st' rcd false := by
  simp [clearCompTL, SM.GameState.record, SM.GameState.safeCh, SM.healedBy]

@[simp] theorem clearCompTL_epMgmtNew {St Msg C : Type}
    (g : SM.GameState St Msg C) (Δ : ℕ) (P : Party) (bad : Bool) :
    clearCompTL (epMgmtNew g Δ P bad) = epMgmtNew (clearCompTL g) (2 + 1) P false := by
  dsimp only [epMgmtNew, clearCompTL, SM.GameState.leak]
  split <;> rfl

@[simp] theorem clearCompTL_afterCorrShifted {St Msg C : Type}
    (l : ℕ) (g : SM.GameState St Msg C) (P : Party) :
    clearCompTL (afterCorrShifted l g P) = clearCompTL g := by
  dsimp only [afterCorrShifted, clearCompTL, SM.GameState.leak]

abbrev toBaseCS (esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E)
    (CKAStateShifted Γ T I)) : EStateC Γ T Sig SS RS M E I :=
  { g := clearCompTL esS.g, h := esS.h.base, abort := esS.abort }

abbrev toBasePS (esP : EStateP Γ T Sig SS RS M E K) : EStateP Γ T Sig SS RS M E K :=
  { g := clearCompTL esP.g, h := esP.h, abort := esP.abort }

abbrev tStarHook (b_auth : Bool) (t : ℕ) : ℕ := if b_auth then t else 0

abbrev moHook (b_auth : Bool) (l t : ℕ) : Mode := ⟨b_auth, some (l - 1), t⟩

def trivHook {St Msg C : Type} (b_auth : Bool) (Δ_off tStar : ℕ)
    (s : SM.GameState St Msg C) (pos : SM.Pos) : Bool :=
  if b_auth then s.trivial (2 + Δ_off) pos
  else
    s.trivial (2 + Δ_off) pos ||
      (pos.epoch != tStar && decide (pos.epoch < min (s.epoch .A) (s.epoch .B)))

@[simp] theorem eraseSt_trivHook {St₁ St₂ Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    {g₁ : SM.GameState St₁ Msg C} {g₂ : SM.GameState St₂ Msg C}
    (h : AuthL10.eraseSt g₁ = AuthL10.eraseSt g₂) (b_auth : Bool) (Δ_off tStar : ℕ)
    (pos : SM.Pos) :
    trivHook b_auth Δ_off tStar g₁ pos = trivHook b_auth Δ_off tStar g₂ pos := by
  cases b_auth <;>
    simp [trivHook, AuthL10.eraseSt_trivial h, AuthL10.eraseSt_epoch h]

theorem trivHook_eq_trivial_of_new_epoch {St Msg C : Type} (b_auth : Bool) (Δ_off tStar : ℕ)
    (s : SM.GameState St Msg C) (P : Party) (i' : ℕ) :
    trivHook b_auth Δ_off tStar s ⟨P.other, s.epoch P + 1, i'⟩ =
      s.trivial (2 + Δ_off) ⟨P.other, s.epoch P + 1, i'⟩ := by
  have hnot : ¬ s.epoch P + 1 < min (s.epoch .A) (s.epoch .B) := by
    have : min (s.epoch .A) (s.epoch .B) ≤ s.epoch P := by cases P <;> simp
    omega
  cases b_auth <;> simp [trivHook, hnot]

def injectEG {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {HS Γv Sv SSv RSv : Type} (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (b_auth : Bool) (Δ_off qep tStar : ℕ) (cfg : SM.Config M) :
    QueryImpl ((Party × (Header T × E)) →ₒ Option (SM.RecvResult M))
      (EM tspec Γv T Sv SSv RSv M E HS) := fun ⟨P, c⟩ => do
  let es ← get; let s := es.g
  if es.abort || s.win || (s.inTransit P.other c).isSome || !(s.safeInj (2 + Δ_off)) then
    return none
  match ← liftH (vRecv hk s P (s.st P) c none) with
  | none => abortE; return none
  | some none => return some .rejected
  | some (some (st', t', i', m')) =>
    if qep + 1 < t' then return some .rejected
    let pos : SM.Pos := ⟨P.other, t', i'⟩
    if trivHook b_auth Δ_off tStar s pos then
      match ← commitE hk s P (s.st P) st' pos with
      | none => return none
      | some s₁ => modify fun es => { es with g := s₁ }; return some (.accepted t' i' (some m'))
    else
      if cfg.injectFull t' then modify fun es => { es with g := { es.g with win := true } }
      return some .rejected

def deliverForgeEG {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {HS Γv Sv SSv RSv : Type} (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (b_auth : Bool) (Δ_off qep tStar : ℕ) (cfg : SM.Config M) :
    QueryImpl ((Party × (Header T × E) × (Header T × E)) →ₒ Option (SM.RecvResult M))
      (EM tspec Γv T Sv SSv RSv M E HS) := fun ⟨P, c, c'⟩ => do
  let es ← get; let s := es.g
  if es.abort || s.win then return none
  match s.inTransit P.other c with
  | none => return none
  | some r =>
    if (s.inTransit P.other c').isSome || s.comp.contains r.pos || c.1 != c'.1 then return none
    match ← liftH (vRecv hk s P (s.st P) c' none) with
    | none => abortE; return none
    | some none => return some .rejected
    | some (some (st', t', i', m')) =>
      if qep + 1 < t' || t' != r.pos.epoch then return some .rejected
      let pos : SM.Pos := ⟨P.other, t', i'⟩
      if trivHook b_auth Δ_off tStar s pos then
        match ← commitE hk s P (s.st P) st' pos with
        | none => return none
        | some s₁ => modify fun es => { es with g := s₁ }; return some (.accepted t' i' (some m'))
      else
        if cfg.injectFull t' then modify fun es => { es with g := { es.g with win := true } }
        return some .rejected

def implEDFG {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {HS Γv Sv SSv RSv : Type} (b_auth : Bool) (l : ℕ)
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ_off qep maxSkip tStar : ℕ) (cfg : SM.Config M) (π : Policy) :
    QueryImpl (unifSpec + DeliverForge.specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E))
      (EM tspec Γv T Sv SSv RSv M E HS) :=
  let i₀ : QueryImpl unifSpec (EM tspec Γv T Sv SSv RSv M E HS) := coinsE
  let i₁ : QueryImpl (SM.spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E))
      (EM tspec Γv T Sv SSv RSv M E HS) :=
    HAdd.hAdd (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd (transmitE hk (2 + Δ_off) qep π)
      (challE hk (2 + Δ_off) qep cfg π)) (deliverE hk maxSkip cfg))
      (injectEG hk b_auth Δ_off qep tStar cfg)) (corrEShiftedPaper l hk π)
  let i₂ : QueryImpl ((Party × (Header T × E) × (Header T × E)) →ₒ Option (SM.RecvResult M))
      (EM tspec Γv T Sv SSv RSv M E HS) := deliverForgeEG hk b_auth Δ_off qep tStar cfg
  HAdd.hAdd i₀ (HAdd.hAdd i₁ i₂)

def stepCDFShiftedPaper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δ_off : ℕ) (b_auth : Bool) (qep l t : ℕ)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I))
    (sc : CKA.GameState Γ T) :
    ProbComp (((SMSpecDF Γ T Sig SS RS M CCoins E).Range q ×
      EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)) ×
      CKA.GameState Γ T) :=
  (simulateQ (cImpl cka 1 (l + 1))
    ((implEDFG b_auth l (hooksCKAShifted cka prng fs l (tStarHook b_auth t))
      Δ_off qep fs.maxSkip t (SM.Config.auth t) ⟨true, some (l - 1), t⟩ q).run esS)).run sc

def stepPDFShiftedPaperGen (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δ_off : ℕ) (b_auth : Bool) (qep l t : ℕ)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) :
    ProbComp (((SMSpecDF Γ T Sig SS RS M CCoins E).Range q ×
      EStateP Γ T Sig SS RS M E K) × PRFPRNG.GameState Sig I K) :=
  (simulateQ (pImpl prng)
    ((implEDFG b_auth l (hooksPRNG cka prng fs (moHook b_auth l t))
      Δ_off qep fs.maxSkip t (SM.Config.auth t) ⟨true, some (l - 1), t⟩ q).run esP)).run sp

def runRDFShiftedPaper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δ_off : ℕ) (b_auth : Bool) (qep l tStar : ℕ)
    {α : Type} (oa : AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I))
    (sc : CKA.GameState Γ T) : ProbComp Bool :=
  ((simulateQ (cImpl cka 1 (l + 1))
    ((simulateQ
      (implEDFG b_auth l (hooksCKAShifted cka prng fs l (tStarHook b_auth tStar))
        Δ_off qep fs.maxSkip tStar (SM.Config.auth tStar) ⟨true, some (l - 1), tStar⟩)
      oa).run es)).run sc) >>=
    fun res => pure (authOut (2 + Δ_off) ⟨true, some (l - 1), tStar⟩ res.1.2)

def runRDFShifted10Paper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δ_off : ℕ) (b_auth : Bool) (qep l t : ℕ)
    (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) : ProbComp Bool := do
  let r ← (simulateQ (pImpl prng)
    ((simulateQ
      (implEDFG b_auth l (hooksPRNG cka prng fs (moHook b_auth l t))
        Δ_off qep fs.maxSkip t (SM.Config.auth t) ⟨true, some (l - 1), t⟩)
      oa).run esP)).run sp
  pure (authOut (2 + Δ_off) ⟨true, some (l - 1), t⟩ r.1.2)

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem runRDFShiftedPaper_pure (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δ_off : ℕ) (b_auth : Bool) (qep l tStar : ℕ)
    {α : Type} (a : α)
    (es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I))
    (sc : CKA.GameState Γ T) :
    runRDFShiftedPaper cka prng fs Δ_off b_auth qep l tStar (pure a) es sc =
      pure (authOut (2 + Δ_off) ⟨true, some (l - 1), tStar⟩ es) := by
  simp [runRDFShiftedPaper]

omit [SampleableType KR] [SampleableType KC] in
theorem runRDFShifted10Paper_pure (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δ_off : ℕ) (b_auth : Bool) (qep l t : ℕ)
    (b' : Bool) (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) :
    runRDFShifted10Paper cka prng fs Δ_off b_auth qep l t (pure b') esP sp =
      pure (authOut (2 + Δ_off) ⟨true, some (l - 1), t⟩ esP) := by
  simp [runRDFShifted10Paper]

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem runRDFShiftedPaper_query_bind (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δ_off : ℕ) (b_auth : Bool) (qep l tStar : ℕ)
    {α : Type} (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (k : (SMSpecDF Γ T Sig SS RS M CCoins E).Range q →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I))
    (sc : CKA.GameState Γ T) :
    runRDFShiftedPaper cka prng fs Δ_off b_auth qep l tStar
      (OracleSpec.query (spec := SMSpecDF Γ T Sig SS RS M CCoins E) q >>= k) es sc =
      (stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l tStar q es sc >>=
        fun res => runRDFShiftedPaper cka prng fs Δ_off b_auth qep l tStar (k res.1.1)
          res.1.2 res.2) := by
  simp [runRDFShiftedPaper, stepCDFShiftedPaper, StateT.run_bind]

omit [SampleableType KR] [SampleableType KC] in
theorem runRDFShifted10Paper_query_bind (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δ_off : ℕ) (b_auth : Bool) (qep l t : ℕ)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (k : (SMSpecDF Γ T Sig SS RS M CCoins E).Range q → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) :
    runRDFShifted10Paper cka prng fs Δ_off b_auth qep l t (liftM (OracleSpec.query q) >>= k)
      esP sp =
      stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t q esP sp >>= fun r =>
        runRDFShifted10Paper cka prng fs Δ_off b_auth qep l t (k r.1.1) r.1.2 r.2 := by
  simp [runRDFShifted10Paper, stepPDFShiftedPaperGen, simulateQ_bind, StateT.run_bind]
omit [SampleableType CCoins] in
theorem abort_simulateQ_DFShiftedPaper {Γv Sv SSv RSv HS : Type} {ι : Type}
    {tspec : OracleSpec.{0, 0} ι} {S : Type}
    (b_auth : Bool) (l : ℕ) (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ_off qep maxSkip tStar : ℕ) (cfg : SM.Config M) (π : Policy)
    (tImpl : QueryImpl tspec (StateT S ProbComp))
    {α : Type} (oa : AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α) :
    ∀ {es es' : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS} {sc sc' : S} {a : α},
      es.abort = true →
      ((a, es'), sc') ∈ support ((simulateQ
        ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT S ProbComp) + tImpl)
        ((simulateQ (implEDFG b_auth l hk Δ_off qep maxSkip tStar cfg π)
          oa).run es)).run sc) →
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
    · dsimp only [implEDFG, coinsE, HAdd.hAdd, Add.add, QueryImpl.add] at h₁
      simp only [StateT.run_lift, simulateQ_bind, QueryImpl.liftTarget,
        simulateQ_pure, StateT.run_bind, StateT.run_pure, MonadAttach.mem_support_bind,
        support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₁
      rcases h₁ with ⟨_, _, ⟨_, rfl⟩, rfl⟩
      exact ih u hab h₂
    all_goals
      dsimp only [implEDFG, transmitE, challE, deliverE, injectEG,
        corrEShiftedPaper, deliverForgeEG, HAdd.hAdd, Add.add, QueryImpl.add] at h₁
      simp only [hab, Bool.true_or, ↓reduceIte,
        StateT.run_bind, StateT.run_get, pure_bind, StateT.run_pure,
        simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₁
      rw [← h₁.1.2] at hab
      exact ih u hab h₂

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem evalDist_runRDFShiftedPaper_eq_pure_false_of_abort
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δ_off : ℕ) (b_auth : Bool) (qep l tStar : ℕ)
    {α : Type} (oa : AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I))
    (sc : CKA.GameState Γ T) (hab : es.abort = true) :
    𝒟[runRDFShiftedPaper cka prng fs Δ_off b_auth qep l tStar oa es sc] =
      𝒟[(pure false : ProbComp Bool)] := by
  apply evalDist_bind_eq_pure_false
  rintro ⟨⟨a, es'⟩, sc'⟩ hmem
  have hab' : es'.abort = true :=
    abort_simulateQ_DFShiftedPaper b_auth l
      (hooksCKAShifted cka prng fs l (tStarHook b_auth tStar))
      Δ_off qep fs.maxSkip tStar (SM.Config.auth tStar) ⟨true, some (l - 1), tStar⟩
      (CKA.oracleImpl cka 1 (l + 1)) oa hab hmem
  simp [authOut, hab']

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem runRDFShiftedPaper_abort_apply_true_le (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δ_off : ℕ) (b_auth : Bool) (qep l t : ℕ)
    (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hab : esS.abort = true) (rhs : ℝ≥0∞) :
    𝒟[runRDFShiftedPaper cka prng fs Δ_off b_auth qep l t oa esS sc] {true} ≤ rhs := by
  rw [evalDist_runRDFShiftedPaper_eq_pure_false_of_abort cka prng fs Δ_off b_auth qep l t oa
    esS sc hab]
  simp
/-- Synchronization invariant for `lemma10_df_shifted_paper` / `lemma10_df_shifted_dir2_paper`,
extending `AuthL10.Sync` on `toBaseCS esS` and `toBasePS esP` with `g_eq`, `comp_inv` at
`2 + Δ_off`, and `γPre_eq` for `esS.g.epoch P + 1 ≤ l`. -/
structure Sync10ShiftedPaper (prng : PRFPRNG KR Sig I K) (Δ_off l t : ℕ)
    (esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I))
    (sc : CKA.GameState Γ T)
    (esP : EStateP Γ T Sig SS RS M E K)
    (sp : PRFPRNG.GameState Sig I K) : Prop where
  hl : 1 ≤ l
  baseSync : AuthL10.Sync prng 1 ⟨true, some (l - 1), t⟩ (toBaseCS esS) sc (toBasePS esP) sp
  g_eq : eraseSt esP.g = eraseSt esS.g
  comp_inv : ∀ pos ∈ esS.g.comp, SM.healedBy esS.g.tL (2 + Δ_off) pos.epoch = false
  γPre_eq : ∀ P, esS.g.epoch P + 1 ≤ l → esS.h.γPre P = some (esP.g.st P).γ

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem Sync10ShiftedPaper.abort_C {prng : PRFPRNG KR Sig I K} {Δ_off l t : ℕ}
    {esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T} {esP : EStateP Γ T Sig SS RS M E K}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp) : esS.abort = false :=
  hS.baseSync.abort_C

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem Sync10ShiftedPaper.abort_P {prng : PRFPRNG KR Sig I K} {Δ_off l t : ℕ}
    {esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T} {esP : EStateP Γ T Sig SS RS M E K}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp) : esP.abort = false :=
  hS.baseSync.abort_P

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem Sync10ShiftedPaper.id_C {prng : PRFPRNG KR Sig I K} {Δ_off l t : ℕ}
    {esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T} {esP : EStateP Γ T Sig SS RS M E K}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp) (P : Party) :
    (esS.g.st P).id = P :=
  hS.baseSync.id_C P

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem Sync10ShiftedPaper.id_P {prng : PRFPRNG KR Sig I K} {Δ_off l t : ℕ}
    {esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T} {esP : EStateP Γ T Sig SS RS M E K}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp) (P : Party) :
    (esP.g.st P).id = P :=
  hS.baseSync.id_P P

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem Sync10ShiftedPaper.tcur_C {prng : PRFPRNG KR Sig I K} {Δ_off l t : ℕ}
    {esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T} {esP : EStateP Γ T Sig SS RS M E K}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp) (P : Party) :
    (esS.g.st P).tcur = esS.g.epoch P :=
  hS.baseSync.tcur_C P

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem Sync10ShiftedPaper.tcur_P {prng : PRFPRNG KR Sig I K} {Δ_off l t : ℕ}
    {esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T} {esP : EStateP Γ T Sig SS RS M E K}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp) (P : Party) :
    (esP.g.st P).tcur = esS.g.epoch P :=
  hS.baseSync.tcur_P P
omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem Sync10ShiftedPaper.vS_eq {prng : PRFPRNG KR Sig I K} {Δ_off l t : ℕ}
    {esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T} {esP : EStateP Γ T Sig SS RS M E K}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp) (P : Party) :
    (esP.g.st P).vS = (esS.g.st P).vS :=
  hS.baseSync.vS_eq P

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem Sync10ShiftedPaper.vR_eq {prng : PRFPRNG KR Sig I K} {Δ_off l t : ℕ}
    {esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T} {esP : EStateP Γ T Sig SS RS M E K}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp) (P : Party) :
    (esP.g.st P).vR = (esS.g.st P).vR :=
  hS.baseSync.vR_eq P

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem Sync10ShiftedPaper.Tcur_eq {prng : PRFPRNG KR Sig I K} {Δ_off l t : ℕ}
    {esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T} {esP : EStateP Γ T Sig SS RS M E K}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp) (P : Party) :
    (esP.g.st P).curCkaMsg = (esS.g.st P).curCkaMsg :=
  hS.baseSync.Tcur_eq P

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem Sync10ShiftedPaper.b_C {prng : PRFPRNG KR Sig I K} {Δ_off l t : ℕ}
    {esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T} {esP : EStateP Γ T Sig SS RS M E K}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp) : sc.b = true :=
  hS.baseSync.b_C

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem Sync10ShiftedPaper.γ_C {prng : PRFPRNG KR Sig I K} {Δ_off l t : ℕ}
    {esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T} {esP : EStateP Γ T Sig SS RS M E K}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp) (P : Party) :
    (esS.g.st P).γ =
      if localCKA ⟨true, some (l - 1), t⟩ 1 (esS.g.epoch P) then some (esP.g.st P).γ else none :=
  hS.baseSync.γ_C P

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem Sync10ShiftedPaper.root_P {prng : PRFPRNG KR Sig I K} {Δ_off l t : ℕ}
    {esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T} {esP : EStateP Γ T Sig SS RS M E K}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp) (P : Party) :
    (esP.g.st P).root =
      if knownRoot ⟨true, some (l - 1), t⟩ (esS.g.epoch P) then some (esS.g.st P).root else none :=
  hS.baseSync.root_P P

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem Sync10ShiftedPaper.b_P {prng : PRFPRNG KR Sig I K} {Δ_off l t : ℕ}
    {esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T} {esP : EStateP Γ T Sig SS RS M E K}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp) : sp.b = false :=
  hS.baseSync.b_P

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem Sync10ShiftedPaper.cka_st {prng : PRFPRNG KR Sig I K} {Δ_off l t : ℕ}
    {esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T} {esP : EStateP Γ T Sig SS RS M E K}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp) (P : Party)
    (h : localCKA ⟨true, some (l - 1), t⟩ 1 (esS.g.epoch P) = false ∨
      localCKA ⟨true, some (l - 1), t⟩ 1 (esS.g.epoch P.other) = false) :
    sc.st P = (esP.g.st P).γ ∧ sc.epoch P = esS.g.epoch P :=
  hS.baseSync.cka_st P h
omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem Sync10ShiftedPaper.trans_inv {prng : PRFPRNG KR Sig I K} {Δ_off l t : ℕ}
    {esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T} {esP : EStateP Γ T Sig SS RS M E K}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp)
    (r : SM.Record M (Header T × E)) (hr : r ∈ esS.g.trans) :
    r.ct.1.1 = r.pos.epoch ∧
    r.pos.sender.sendsIn r.pos.epoch = true ∧
    r.pos.epoch ≤ esS.g.epoch r.pos.sender ∧
    (r.pos.epoch = esS.g.epoch r.pos.sender → r.ct.1.2 = (esS.g.st r.pos.sender).curCkaMsg) :=
  hS.baseSync.trans_inv r hr

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem Sync10ShiftedPaper.epoch_S {prng : PRFPRNG KR Sig I K} {Δ_off l t : ℕ}
    {esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T} {esP : EStateP Γ T Sig SS RS M E K}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp) :
    esS.g.epoch (Party.senderOf (max (esS.g.epoch .A) (esS.g.epoch .B))) =
      max (esS.g.epoch .A) (esS.g.epoch .B) :=
  hS.baseSync.epoch_S

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem Sync10ShiftedPaper.ping_pong {prng : PRFPRNG KR Sig I K} {Δ_off l t : ℕ}
    {esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T} {esP : EStateP Γ T Sig SS RS M E K}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp) :
    let m := max (esS.g.epoch .A) (esS.g.epoch .B)
    let S := Party.senderOf m
    let R := Party.receiverOf m
    (esS.g.epoch R = m ∧ (esS.g.st .A).root = (esS.g.st .B).root) ∨
    (0 < m ∧ esS.g.epoch R + 1 = m ∧
      ∃ Tm Im,
        esS.h.base.cache m = some (Tm, Im) ∧
        (esS.g.st S).curCkaMsg = some Tm ∧
        (esS.g.st S).root = (prng.up (esS.g.st R).root Im).1 ∧
        esP.h.cache m = some (Tm, (esP.g.st S).root, (prng.up (esS.g.st R).root Im).2) ∧
        (localCKA ⟨true, some (l - 1), t⟩ 1 (m - 1) = false → sc.lastMsg = some Tm)) :=
  hS.baseSync.ping_pong

theorem Sync10ShiftedPaper.sp_at_recv_tStar {prng : PRFPRNG KR Sig I K} {Δ_off l t : ℕ}
    {esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T} {esP : EStateP Γ T Sig SS RS M E K}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp) (P : Party)
    (htStar : esS.g.epoch P + 1 = t)
    (hloc : localCKA ⟨true, some (l - 1), t⟩ 1 (esS.g.epoch P) = true) :
    sp.σ = (esS.g.st P).root ∧ sp.corr = false ∧ sp.prng = false :=
  hS.baseSync.sp_at_recv_tStar P htStar hloc

theorem Sync10ShiftedPaper.cache_at_succ {prng : PRFPRNG KR Sig I K} {Δ_off l t : ℕ}
    {esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T} {esP : EStateP Γ T Sig SS RS M E K}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp) (P : Party) (m : ℕ)
    (hm : m = esS.g.epoch P + 1) :
    (esS.h.base.cache m = none ∧ esP.h.cache m = none) ∨
      ∃ Tm Im,
        esS.h.base.cache m = some (Tm, Im) ∧
        esP.h.cache m = some (Tm, (esP.g.st (Party.senderOf m)).root,
          (prng.up (esS.g.st P).root Im).2) :=
  hS.baseSync.cache_at_succ P m hm

theorem Sync10ShiftedPaper.deliver_new_info {prng : PRFPRNG KR Sig I K} {Δ_off l t : ℕ}
    {esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T} {esP : EStateP Γ T Sig SS RS M E K}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp) {P : Party} {c : Header T × E}
    {r : SM.Record M (Header T × E)}
    (hr : esS.g.inTransit P.other c = some r) (hnew : c.1.1 = esS.g.epoch P + 1) :
    let m := esS.g.epoch P + 1
    r.pos.epoch = m ∧
    P = Party.receiverOf m ∧
    P.other = Party.senderOf m ∧
    esS.g.epoch P.other = m ∧
    max (esS.g.epoch .A) (esS.g.epoch .B) = m ∧
    ∃ Tm Im,
      c.1.2 = some Tm ∧
      esS.h.base.cache m = some (Tm, Im) ∧
      (esS.g.st P.other).curCkaMsg = some Tm ∧
      (esS.g.st P.other).root = (prng.up (esS.g.st P).root Im).1 ∧
      esP.h.cache m = some (Tm, (esP.g.st P.other).root, (prng.up (esS.g.st P).root Im).2) ∧
      (localCKA ⟨true, some (l - 1), t⟩ 1 (esS.g.epoch P) = false → sc.lastMsg = some Tm) :=
  hS.baseSync.deliver_new_info hr hnew

theorem Sync10ShiftedPaper.ping_pong_synced {prng : PRFPRNG KR Sig I K} {Δ_off l t : ℕ}
    {esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T} {esP : EStateP Γ T Sig SS RS M E K}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp) (P : Party)
    (hsend : P.sendsIn (esS.g.epoch P + 1) = true) :
    esS.g.epoch P.other = esS.g.epoch P ∧
    max (esS.g.epoch .A) (esS.g.epoch .B) = esS.g.epoch P ∧
    (esS.g.st P.other).root = (esS.g.st P).root :=
  hS.baseSync.ping_pong_synced P hsend
omit [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem Sync10ShiftedPaper.authOut_eq {prng : PRFPRNG KR Sig I K} {Δ_off l t : ℕ}
    {esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T} {esP : EStateP Γ T Sig SS RS M E K}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp) :
    authOut (2 + Δ_off) ⟨true, some (l - 1), t⟩ esS =
      authOut (2 + Δ_off) ⟨true, some (l - 1), t⟩ esP := by
  simp [authOut, hS.abort_C, hS.abort_P, eraseSt_win hS.g_eq, eraseSt_authOK hS.g_eq]

theorem Sync10ShiftedPaper.set_prf {prng : PRFPRNG KR Sig I K} {Δ_off l t : ℕ}
    {esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T} {esP : EStateP Γ T Sig SS RS M E K}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp) (p : Bool)
    (hp : p = sp.prf ∨ (sp.corr = false ∧ max (esS.g.epoch .A) (esS.g.epoch .B) + 1 ≥ t)) :
    Sync10ShiftedPaper prng Δ_off l t esS sc esP { sp with prf := p } :=
  ⟨hS.hl, hS.baseSync.set_prf p hp, hS.g_eq, hS.comp_inv, hS.γPre_eq⟩

theorem Sync10ShiftedPaper.set_win_prf {prng : PRFPRNG KR Sig I K} {Δ_off l t : ℕ}
    {esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T} {esP : EStateP Γ T Sig SS RS M E K}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp) (w : Bool) (p : Bool)
    (hp : p = sp.prf ∨ (sp.corr = false ∧ max (esS.g.epoch .A) (esS.g.epoch .B) + 1 ≥ t)) :
    Sync10ShiftedPaper prng Δ_off l t { esS with g := { esS.g with win := w } } sc
      { esP with g := { esP.g with win := w } } { sp with prf := p } :=
  ⟨hS.hl, hS.baseSync.set_win_prf w p hp,
    by simp [eraseSt, eraseSt_epoch hS.g_eq, eraseSt_idx hS.g_eq, eraseSt_tL hS.g_eq,
      eraseSt_trans hS.g_eq, eraseSt_chall hS.g_eq, eraseSt_comp hS.g_eq, eraseSt_maxAcc hS.g_eq,
      eraseSt_b hS.g_eq, eraseSt_leaks hS.g_eq, eraseSt_corrs hS.g_eq],
    hS.comp_inv, hS.γPre_eq⟩

theorem Sync10ShiftedPaper.accept_old {prng : PRFPRNG KR Sig I K} {Δ_off l t : ℕ}
    {esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T} {esP : EStateP Γ T Sig SS RS M E K}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp)
    (P : Party) (vR' : ℕ → Option RS) (pos : SM.Pos)
    (hle : pos.epoch ≤ esS.g.epoch P) :
    Sync10ShiftedPaper prng Δ_off l t
      { esS with g := esS.g.accept P { esS.g.st P with vR := vR' } pos }
      sc
      { esP with g := esP.g.accept P { esP.g.st P with vR := vR' } pos }
      sp := by
  have hbaseC : toBaseCS { esS with g := esS.g.accept P { esS.g.st P with vR := vR' } pos } =
      { toBaseCS esS with g := (toBaseCS esS).g.accept P { esS.g.st P with vR := vR' } pos } := by
    simp [toBaseCS]
  have hbaseP : toBasePS { esP with g := esP.g.accept P { esP.g.st P with vR := vR' } pos } =
      { toBasePS esP with g := (toBasePS esP).g.accept P { esP.g.st P with vR := vR' } pos } := by
    simp [toBasePS]
  refine ⟨hS.hl, ?_, eraseSt_accept hS.g_eq P _ _ pos,
    comp_inv_accept esS.g (2 + Δ_off) P _ pos hS.comp_inv, ?_⟩
  · rw [hbaseC, hbaseP]
    exact hS.baseSync.accept_old P vR' pos hle
  · intro Q hQ
    rw [accept_epoch_of_le _ _ _ _ hle] at hQ
    rcases party_eq_or_eq_other Q P with rfl | rfl <;>
      simpa [accept_st, Party.other_ne] using hS.γPre_eq _ hQ

theorem Sync10ShiftedPaper.accept_new {prng : PRFPRNG KR Sig I K} {Δ_off l t : ℕ}
    {esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc sc' : CKA.GameState Γ T} {esP : EStateP Γ T Sig SS RS M E K}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp)
    (P : Party) (γP' : Γ) (vR' : ℕ → Option RS) (pos : SM.Pos)
    (hpos : pos.epoch = esS.g.epoch P + 1)
    (hother : esS.g.epoch P.other = esS.g.epoch P + 1)
    (hsc_b : sc'.b = true)
    (hcka' : localCKA ⟨true, some (l - 1), t⟩ 1 (esS.g.epoch P + 1) = false →
      sc'.st P = γP' ∧ sc'.epoch P = esS.g.epoch P + 1 ∧
      sc'.st P.other = (esP.g.st P.other).γ ∧ sc'.epoch P.other = esS.g.epoch P + 1) :
    let m := esS.g.epoch P + 1
    let γC' := if localCKA ⟨true, some (l - 1), t⟩ 1 m then some γP' else none
    let stC' : VP (Option Γ) T Sig SS RS :=
      { esS.g.st P with tcur := m, γ := γC', root := (esS.g.st P.other).root, vR := vR' }
    let stP' : VP Γ T (Option Sig) SS RS :=
      { esP.g.st P with tcur := m, γ := γP', root := (esP.g.st P.other).root, vR := vR' }
    let h' : CKAStateShifted Γ T I :=
      if m + 1 ≤ l then { esS.h with γPre := Function.update esS.h.γPre P (some γP') }
      else esS.h
    Sync10ShiftedPaper prng Δ_off l t { esS with g := esS.g.accept P stC' pos, h := h' } sc'
      { esP with g := esP.g.accept P stP' pos } sp := by
  intro m γC' stC' stP' h'
  have hbaseC : toBaseCS { esS with g := esS.g.accept P stC' pos, h := h' } =
      { toBaseCS esS with g := (toBaseCS esS).g.accept P stC' pos } := by
    dsimp only [toBaseCS, h']
    split <;> simp [clearCompTL_accept]
  have hbaseP : toBasePS { esP with g := esP.g.accept P stP' pos } =
      { toBasePS esP with g := (toBasePS esP).g.accept P stP' pos } := by
    simp [toBasePS]
  refine ⟨hS.hl, ?_, eraseSt_accept hS.g_eq P stP' stC' pos,
    comp_inv_accept esS.g (2 + Δ_off) P stC' pos hS.comp_inv, ?_⟩
  · rw [hbaseC, hbaseP]
    exact hS.baseSync.accept_new P γP' vR' pos hpos hother hsc_b hcka'
  · intro Q hQ
    dsimp only at hQ ⊢
    rw [accept_epoch_of_succ _ _ _ _ hpos hother] at hQ
    dsimp only at hQ
    have hm_le : m + 1 ≤ l := hQ
    rcases party_eq_or_eq_other Q P with rfl | rfl
    · simp [h', hm_le, accept_st, stP']
    · simp only [h', hm_le, ↓reduceIte, accept_st, Function.update_of_ne (Party.other_ne P)]
      exact hS.γPre_eq P.other (by omega)

theorem Sync10ShiftedPaper.record_same_epoch {prng : PRFPRNG KR Sig I K} {Δ_off l t : ℕ}
    {esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T} {esP : EStateP Γ T Sig SS RS M E K}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp)
    (P : Party) (vS' : Option SS) (m_msg : M) (e : E)
    (hsend : P.sendsIn (esS.g.epoch P) = true) :
    let c : Header T × E := ((esS.g.epoch P, (esS.g.st P).curCkaMsg), e)
    let rcd : SM.Record M (Header T × E) := ⟨⟨P, esS.g.epoch P, esS.g.idx P + 1⟩, m_msg, c⟩
    Sync10ShiftedPaper prng Δ_off l t
      { esS with g := esS.g.record (2 + Δ_off) P { esS.g.st P with vS := vS' } rcd false } sc
      { esP with g := esP.g.record (2 + Δ_off) P { esP.g.st P with vS := vS' } rcd false } sp := by
  intro c rcd
  have hbaseC : toBaseCS
      { esS with g := esS.g.record (2 + Δ_off) P { esS.g.st P with vS := vS' } rcd false } =
      { toBaseCS esS with
        g := (toBaseCS esS).g.record (2 + 1) P { esS.g.st P with vS := vS' } rcd false } := by
    simp [toBaseCS]
  have hbaseP : toBasePS
      { esP with g := esP.g.record (2 + Δ_off) P { esP.g.st P with vS := vS' } rcd false } =
      { toBasePS esP with
        g := (toBasePS esP).g.record (2 + 1) P { esP.g.st P with vS := vS' } rcd false } := by
    simp [toBasePS]
  refine ⟨hS.hl, ?_, eraseSt_record hS.g_eq (2 + Δ_off) P _ _ rcd false,
    comp_inv_record esS.g (2 + Δ_off) P _ rcd false rfl hS.comp_inv, ?_⟩
  · rw [hbaseC, hbaseP]
    exact hS.baseSync.record_same_epoch P vS' m_msg e hsend
  · intro Q hQ
    rcases party_eq_or_eq_other Q P with rfl | rfl <;>
      simpa [SM.GameState.record, Party.other_ne] using hS.γPre_eq _ hQ

theorem Sync10ShiftedPaper.record_new_epoch {prng : PRFPRNG KR Sig I K} {Δ_off l t : ℕ}
    {esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T} {esP : EStateP Γ T Sig SS RS M E K}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp) (P : Party) (bad : Bool)
    (γP' : Γ) (Tm : T) (Im : I) (v' : SS) (m_msg : M) (e : E)
    (sc' : CKA.GameState Γ T) (sp' : PRFPRNG.GameState Sig I K)
    (hsend : P.sendsIn (esS.g.epoch P + 1) = true)
    (hb_sc' : sc'.b = true) (hb_sp' : sp'.b = false)
    (hcka' : localCKA ⟨true, some (l - 1), t⟩ 1 (esS.g.epoch P) = false →
      sc'.st P = γP' ∧ sc'.epoch P = esS.g.epoch P + 1 ∧
      sc'.st P.other = (esP.g.st P.other).γ ∧ sc'.epoch P.other = esS.g.epoch P ∧
      sc'.lastMsg = some Tm)
    (hprng_before : esS.g.epoch P + 1 < t →
      ((some (l - 1)).isSome && decide (esS.g.epoch P + 1 < (⟨true, some (l - 1), t⟩ : Mode).tH)) =
        true →
      sp'.σ = (prng.up (esS.g.st P).root Im).1 ∧
      sp'.corr = true ∧ sp'.prng = false ∧ sp'.prf = false)
    (hprng_after : esS.g.epoch P + 1 < t →
      ((some (l - 1)).isSome && decide (esS.g.epoch P + 1 < (⟨true, some (l - 1), t⟩ : Mode).tH)) =
        false →
      sp'.σ = (prng.up (esS.g.st P).root Im).1 ∧
      sp'.corr = false ∧ sp'.prng = false ∧
      (esS.g.epoch P + 1 + 1 < t → sp'.prf = false))
    (hprng_at : esS.g.epoch P + 1 = t →
      ((some (l - 1)).isSome && decide (t = (⟨true, some (l - 1), t⟩ : Mode).tH)) = false →
      sp'.σ = (esS.g.st P).root ∧ sp'.corr = false ∧ sp'.prng = false) :
    let m := esS.g.epoch P + 1
    let p := prng.up (esS.g.st P).root Im
    let σP' := if knownRoot ⟨true, some (l - 1), t⟩ m then some p.1 else none
    let stC' : VP (Option Γ) T Sig SS RS :=
      { esS.g.st P with
        tcur := m
        γ := if localCKA ⟨true, some (l - 1), t⟩ 1 m then some γP' else none
        curCkaMsg := some Tm, root := p.1, vS := some v' }
    let stP' : VP Γ T (Option Sig) SS RS :=
      { esP.g.st P with
        tcur := m, γ := γP', curCkaMsg := some Tm, root := σP', vS := some v' }
    let c : Header T × E := ((m, some Tm), e)
    let rcd : SM.Record M (Header T × E) := ⟨⟨P, m, 1⟩, m_msg, c⟩
    let gC₁ := epMgmtNew esS.g (2 + Δ_off) P bad
    let gP₁ := epMgmtNew esP.g (2 + Δ_off) P bad
    let h' : CKAStateShifted Γ T I :=
      { base := { cache := Function.update esS.h.base.cache m (some (Tm, Im)) }
        γPre := if m + 1 ≤ l then Function.update esS.h.γPre P (some γP') else esS.h.γPre }
    Sync10ShiftedPaper prng Δ_off l t
      { esS with g := gC₁.record (2 + Δ_off) P stC' rcd false, h := h' } sc'
      { esP with
        g := gP₁.record (2 + Δ_off) P stP' rcd false
        h := { cache := Function.update esP.h.cache m (some (Tm, σP', p.2)) } } sp' := by
  intro m p σP' stC' stP' c rcd gC₁ gP₁ h'
  have hbaseC : toBaseCS { esS with g := gC₁.record (2 + Δ_off) P stC' rcd false, h := h' } =
      { toBaseCS esS with
        g := (epMgmtNew (toBaseCS esS).g (2 + 1) P false).record (2 + 1) P stC' rcd false
        h := { cache := Function.update esS.h.base.cache m (some (Tm, Im)) } } := by
    simp [toBaseCS, gC₁, h']
  have hbaseP : toBasePS
      { esP with
        g := gP₁.record (2 + Δ_off) P stP' rcd false
        h := { cache := Function.update esP.h.cache m (some (Tm, σP', p.2)) } } =
      { toBasePS esP with
        g := (epMgmtNew (toBasePS esP).g (2 + 1) P false).record (2 + 1) P stP' rcd false
        h := { cache := Function.update esP.h.cache m (some (Tm, σP', p.2)) } } := by
    simp [toBasePS, gP₁]
  refine ⟨hS.hl, ?_,
    eraseSt_record (eraseSt_epMgmtNew hS.g_eq (2 + Δ_off) P bad) (2 + Δ_off) P stP' stC' rcd false,
    comp_inv_record gC₁ (2 + Δ_off) P stC' rcd false (by simp [gC₁, rcd, epMgmtNew_epoch, m])
      (comp_inv_epMgmtNew esS.g (2 + Δ_off) P bad hS.comp_inv), ?_⟩
  · rw [hbaseC, hbaseP]
    exact hS.baseSync.record_new_epoch P false γP' Tm Im v' m_msg e sc' sp'
      hsend hb_sc' hb_sp' hcka' hprng_before hprng_after hprng_at
  · intro Q hQ
    dsimp only [gC₁, SM.GameState.record] at hQ ⊢
    rw [epMgmtNew_epoch] at hQ
    rcases party_eq_or_eq_other Q P with rfl | rfl
    · simp only [Function.update_self] at hQ
      have hm_le : m + 1 ≤ l := hQ
      simp [h', hm_le, gP₁, stP']
    · simp only [Function.update_of_ne (Party.other_ne P)] at hQ
      simp only [h', gP₁, epMgmtNew_st, Function.update_of_ne (Party.other_ne P)]
      split
      · rw [Function.update_of_ne (Party.other_ne P)]
        exact hS.γPre_eq P.other hQ
      · exact hS.γPre_eq P.other hQ
omit [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType I] [SampleableType K] in
theorem Sync10ShiftedPaper.afterCorrShifted {prng : PRFPRNG KR Sig I K} {Δ_off l t : ℕ}
    {esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T} {esP : EStateP Γ T Sig SS RS M E K}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp) (P : Party) :
    Sync10ShiftedPaper prng Δ_off l t { esS with g := DeliverForge.afterCorrShifted l esS.g P } sc
      { esP with g := DeliverForge.afterCorrShifted l esP.g P } sp := by
  have hbaseC : toBaseCS { esS with g := DeliverForge.afterCorrShifted l esS.g P } =
      toBaseCS esS := by simp [toBaseCS]
  have hbaseP : toBasePS { esP with g := DeliverForge.afterCorrShifted l esP.g P } =
      toBasePS esP := by simp [toBasePS]
  refine ⟨hS.hl, ?_, eraseSt_afterCorrShifted hS.g_eq l P,
    comp_inv_afterCorrShifted esS.g l (2 + Δ_off) (by omega) P
      (fun r hr => (hS.baseSync.trans_inv r hr).2.2.1) hS.comp_inv,
    fun Q hQ => hS.γPre_eq Q hQ⟩
  rw [hbaseC, hbaseP]
  exact hS.baseSync

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem knownRoot_of_not_doom_shifted_paper {l t : ℕ} (hl : 1 ≤ l)
    {g : SM.GameState (PartyState (Option Γ) T Sig SS RS) M (Header T × E)} {P : Party}
    (hld : (⟨true, some (l - 1), t⟩ : Mode).policy.leakDoom g (afterCorrShifted l g P) = false)
    (hcd : (⟨true, some (l - 1), t⟩ : Mode).policy.corrDoom g P = false) :
    knownRoot ⟨true, some (l - 1), t⟩ (g.epoch P) = true := by
  by_cases hle : g.epoch P + 1 ≤ l
  · have hlt : g.epoch P < (⟨true, some (l - 1), t⟩ : Mode).tH := by
      simp only [Mode.tH, healEpoch]
      omega
    simp [knownRoot, hlt]
  · have hafter : afterCorrShifted l g P = g.afterCorr P :=
      afterCorrShifted_eq_afterCorr_of_not l g P (fun h => hle h.2)
    rw [hafter] at hld
    exact knownRoot_of_not_doom ⟨true, some (l - 1), t⟩ rfl g P hld hcd

open AuthL10Shifted

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem stepCDFShiftedPaper_coinsE (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δ_off : ℕ) (b_auth : Bool) (qep l t : ℕ)
    (n : unifSpec.Domain)
    (esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I))
    (sc : CKA.GameState Γ T) :
    stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t (.inl n) esS sc =
      (fun u => ((u, esS), sc)) <$> (query (spec := unifSpec) n : ProbComp (Fin (n + 1))) := by
  simp [stepCDFShiftedPaper, implEDFG, coinsE, cImpl, map_eq_bind_pure_comp,
    simulateQ_bind, simulateQ_query, bind_assoc]

theorem step_coinsE_DFShiftedPaper_le (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δ_off : ℕ) (b_auth : Bool) (qep l t : ℕ)
    (n : unifSpec.Domain)
    (esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I))
    (sc : CKA.GameState Γ T) (esP : EStateP Γ T Sig SS RS M E K)
    (sp : PRFPRNG.GameState Sig I K)
    (k : (SMSpecDF Γ T Sig SS RS M CCoins E).Range (.inl n) →
      SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (ih : ∀ r esS' sc' esP' sp',
      Sync10ShiftedPaper prng Δ_off l t esS' sc' esP' sp' →
      𝒟[runRDFShiftedPaper cka prng fs Δ_off b_auth qep l t (k r) esS' sc'] {true} ≤
        𝒟[runRDFShifted10Paper cka prng fs Δ_off b_auth qep l t (k r) esP' sp'] {true})
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp) :
    𝒟[stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t (.inl n) esS sc >>= fun r =>
      runRDFShiftedPaper cka prng fs Δ_off b_auth qep l t (k r.1.1) r.1.2 r.2] {true} ≤
    𝒟[stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t (.inl n) esP sp >>= fun r =>
      runRDFShifted10Paper cka prng fs Δ_off b_auth qep l t (k r.1.1) r.1.2 r.2] {true} := by
  have hP : stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t (.inl n) esP sp =
      stepP cka prng fs Δ_off qep ⟨true, some (l - 1), t⟩ (.inl n) esP sp := rfl
  rw [stepCDFShiftedPaper_coinsE, hP, stepP_coinsE, bind_map_left, bind_map_left]
  exact OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
    fun u _ => ih u esS sc esP sp hS

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem stepCDFShiftedPaper_challE (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δ_off : ℕ) (b_auth : Bool) (qep l t : ℕ)
    (q : Party × M × M × Option CCoins)
    (esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I))
    (sc : CKA.GameState Γ T) :
    stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
        (.inr (.inl (.inl (.inl (.inl (.inr q)))))) esS sc =
      pure ((none, esS), sc) := by
  rcases q with ⟨P, m₀, m₁, r⟩
  simp only [stepCDFShiftedPaper, implEDFG, QueryImpl.add_apply, challE,
    SM.Config.auth, Bool.not_false, Bool.or_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
    pure_bind]
  split
  · simp
  · split <;> simp

theorem step_challE_DFShiftedPaper_le (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δ_off : ℕ) (b_auth : Bool) (qep l t : ℕ)
    (q : Party × M × M × Option CCoins)
    (esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I))
    (sc : CKA.GameState Γ T) (esP : EStateP Γ T Sig SS RS M E K)
    (sp : PRFPRNG.GameState Sig I K)
    (k : Option (Header T × E) → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (ih : ∀ r esS' sc' esP' sp',
      Sync10ShiftedPaper prng Δ_off l t esS' sc' esP' sp' →
      𝒟[runRDFShiftedPaper cka prng fs Δ_off b_auth qep l t (k r) esS' sc'] {true} ≤
        𝒟[runRDFShifted10Paper cka prng fs Δ_off b_auth qep l t (k r) esP' sp'] {true})
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp) :
    𝒟[stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
      (.inr (.inl (.inl (.inl (.inl (.inr q)))))) esS sc >>= fun r =>
      runRDFShiftedPaper cka prng fs Δ_off b_auth qep l t (k r.1.1) r.1.2 r.2] {true} ≤
    𝒟[stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
      (.inr (.inl (.inl (.inl (.inl (.inr q)))))) esP sp >>= fun r =>
      runRDFShifted10Paper cka prng fs Δ_off b_auth qep l t (k r.1.1) r.1.2 r.2] {true} := by
  have hP : stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
      (.inr (.inl (.inl (.inl (.inl (.inr q)))))) esP sp =
      stepP cka prng fs Δ_off qep ⟨true, some (l - 1), t⟩
        (.inr (.inl (.inl (.inl (.inr q))))) esP sp := rfl
  rw [stepCDFShiftedPaper_challE, hP,
    stepP_challE cka prng fs Δ_off qep ⟨true, some (l - 1), t⟩ rfl, pure_bind, pure_bind]
  exact ih none esS sc esP sp hS

omit [SampleableType KR] [SampleableType KC] in
theorem step_corrEShiftedPaper_DF_le (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δ_off : ℕ) (b_auth : Bool) (qep l t : ℕ) (P : Party)
    (esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I))
    (sc : CKA.GameState Γ T) (esP : EStateP Γ T Sig SS RS M E K)
    (sp : PRFPRNG.GameState Sig I K)
    (k : Option (PartyState Γ T Sig SS RS) → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (ih : ∀ r esS' sc' esP' sp',
      Sync10ShiftedPaper prng Δ_off l t esS' sc' esP' sp' →
      𝒟[runRDFShiftedPaper cka prng fs Δ_off b_auth qep l t (k r) esS' sc'] {true} ≤
        𝒟[runRDFShifted10Paper cka prng fs Δ_off b_auth qep l t (k r) esP' sp'] {true})
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp) :
    𝒟[stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t (.inr (.inl (.inr P))) esS sc >>=
      fun r => runRDFShiftedPaper cka prng fs Δ_off b_auth qep l t (k r.1.1) r.1.2 r.2] {true} ≤
    𝒟[stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
      (.inr (.inl (.inr P))) esP sp >>= fun r =>
      runRDFShifted10Paper cka prng fs Δ_off b_auth qep l t (k r.1.1) r.1.2 r.2] {true} := by
  let mo : Mode := ⟨true, some (l - 1), t⟩
  have habC : esS.abort = false := hS.abort_C
  have habP : esP.abort = false := hS.abort_P
  have hwin : esP.g.win = esS.g.win := eraseSt_win hS.g_eq
  have hca : esP.g.corrAllowedPaper P = esS.g.corrAllowedPaper P :=
    AuthL11.eraseSt_corrAllowedPaper hS.g_eq P
  by_cases hguard : esS.g.win || !esS.g.corrAllowedPaper P
  · simp only [Bool.or_eq_true, Bool.not_eq_true'] at hguard
    have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t (.inr (.inl (.inr P))) esS sc =
        pure ((none, esS), sc) := by
      simp [stepCDFShiftedPaper, implEDFG, corrEShiftedPaper, habC, hguard,
        StateT.run_pure]
    have hP :
        stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t (.inr (.inl (.inr P))) esP sp =
        pure ((none, esP), sp) := by
      simp [stepPDFShiftedPaperGen, implEDFG, corrEShiftedPaper, habP, hwin, hca,
        hguard, StateT.run_pure]
    rw [hC, hP, pure_bind, pure_bind]; exact ih none esS sc esP sp hS
  · simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Bool.not_eq_false'] at hguard
    have hld_eq : mo.policy.leakDoom esP.g (afterCorrShifted l esP.g P) =
        mo.policy.leakDoom esS.g (afterCorrShifted l esS.g P) :=
      eraseSt_leakDoom hS.g_eq (eraseSt_afterCorrShifted hS.g_eq l P) mo.policy
    have hcd_eq : mo.policy.corrDoom esP.g P = mo.policy.corrDoom esS.g P :=
      eraseSt_corrDoom hS.g_eq mo.policy P
    by_cases hdoom :
        mo.policy.leakDoom esS.g (afterCorrShifted l esS.g P) || mo.policy.corrDoom esS.g P
    · simp only [Bool.or_eq_true] at hdoom
      dsimp only [mo, Mode.policy] at hdoom
      have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t (.inr (.inl (.inr P))) esS sc =
          pure ((none, { esS with abort := true }), sc) := by
        simp [stepCDFShiftedPaper, implEDFG, corrEShiftedPaper, abortE, habC, hguard,
          hdoom, StateT.run_modify]
      rw [hC, pure_bind]
      exact runRDFShiftedPaper_abort_apply_true_le cka prng fs Δ_off b_auth qep l t (k none) rfl _
    · simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at hdoom
      have hkr : knownRoot mo (esS.g.epoch P) = true :=
        knownRoot_of_not_doom_shifted_paper hS.hl hdoom.1 hdoom.2
      dsimp only [mo, Mode.policy] at hld_eq hcd_eq hdoom
      have hrootP : (esP.g.st P).root = some (esS.g.st P).root := by
        rw [hS.root_P P, hkr]; rfl
      have hP :
          stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t (.inr (.inl (.inr P))) esP sp =
          pure ((some (realParty (esS.g.st P) (esP.g.st P).γ (esS.g.st P).root
            (esS.g.st P).vS (esS.g.st P).vR),
            { esP with g := afterCorrShifted l esP.g P }), sp) := by
        simp [stepPDFShiftedPaperGen, implEDFG, corrEShiftedPaper, hooksPRNG,
          habP, hwin, hca, hguard, hld_eq, hcd_eq, hdoom.1, hdoom.2, hrootP,
          StateT.run_modify, realParty, hS.id_C P, hS.id_P P, hS.vS_eq P, hS.vR_eq P,
          hS.Tcur_eq P, hS.tcur_C P, hS.tcur_P P]
      rw [hP, pure_bind]
      by_cases hloc : localCKA mo 1 (esS.g.epoch P)
      · have hγC : (esS.g.st P).γ = some (esP.g.st P).γ := by rw [hS.γ_C P, hloc]; rfl
        have hC :
            stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t (.inr (.inl (.inr P))) esS sc =
            pure ((some (realParty (esS.g.st P) (esP.g.st P).γ (esS.g.st P).root
              (esS.g.st P).vS (esS.g.st P).vR),
              { esS with g := afterCorrShifted l esS.g P }), sc) := by
          simp [stepCDFShiftedPaper, implEDFG, corrEShiftedPaper, hooksCKAShifted,
            habC, hguard, hdoom.1, hdoom.2, hγC, StateT.run_modify]
        rw [hC, pure_bind]; exact ih _ _ _ _ _ (hS.afterCorrShifted P)
      · simp only [Bool.not_eq_true] at hloc
        have hγC : (esS.g.st P).γ = none := by rw [hS.γ_C P, hloc]; rfl
        by_cases hle : (esS.g.st P).tcur < l
        · have htcur : (esS.g.st P).tcur = esS.g.epoch P := hS.tcur_C P
          have hγPre : esS.h.γPre P = some (esP.g.st P).γ := hS.γPre_eq P (htcur ▸ hle)
          have hC :
              stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t (.inr (.inl (.inr P))) esS sc =
              pure ((some (realParty (esS.g.st P) (esP.g.st P).γ (esS.g.st P).root
                (esS.g.st P).vS (esS.g.st P).vR),
                { esS with g := afterCorrShifted l esS.g P }), sc) := by
            simp [stepCDFShiftedPaper, implEDFG, corrEShiftedPaper, hooksCKAShifted,
              habC, hguard, hdoom.1, hdoom.2, hγC, hle, hγPre, StateT.run_bind, StateT.run_get,
              StateT.run_pure, StateT.run_modify, simulateQ_pure]
          rw [hC, pure_bind]; exact ih _ _ _ _ _ (hS.afterCorrShifted P)
        · have hst_sc : sc.st P = (esP.g.st P).γ := (hS.cka_st P (Or.inl hloc)).1
          by_cases hcorr : sc.allowCorr (l + 1) || sc.finished 1 (l + 1) P
          · simp only [Bool.or_eq_true] at hcorr
            have hC :
                stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t (.inr (.inl (.inr P))) esS sc =
                pure ((some (realParty (esS.g.st P) (esP.g.st P).γ (esS.g.st P).root
                  (esS.g.st P).vS (esS.g.st P).vR),
                  { esS with g := afterCorrShifted l esS.g P }), sc) := by
              simp [stepCDFShiftedPaper, implEDFG, corrEShiftedPaper, hooksCKAShifted,
                liftCShifted, CKA.corrQuery, cImpl, CKA.oracleImpl, CKA.corrImpl,
                habC, hguard, hdoom.1, hdoom.2, hγC, hle, hcorr, hst_sc,
                StateT.run_bind, StateT.run_pure, StateT.run_modify,
                simulateQ_bind, simulateQ_query, simulateQ_pure, map_eq_bind_pure_comp]
            rw [hC, pure_bind]; exact ih _ _ _ _ _ (hS.afterCorrShifted P)
          · simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at hcorr
            have hC :
                stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t (.inr (.inl (.inr P))) esS sc =
                pure ((none, { esS with abort := true }), sc) := by
              simp [stepCDFShiftedPaper, implEDFG, corrEShiftedPaper, abortE,
                hooksCKAShifted, liftCShifted, CKA.corrQuery, cImpl, CKA.oracleImpl, CKA.corrImpl,
                habC, hguard, hdoom.1, hdoom.2, hγC, hle, hcorr,
                StateT.run_bind, simulateQ_bind, simulateQ_query, simulateQ_pure,
                map_eq_bind_pure_comp]
            rw [hC, pure_bind]
            exact runRDFShiftedPaper_abort_apply_true_le cka prng fs Δ_off b_auth qep l t (k none)
              rfl _

theorem step_injectE_new_epoch_DFShiftedPaper_le (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δ_off : ℕ) (b_auth : Bool) (qep l t : ℕ)
    (P : Party) (c : Header T × E)
    (esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I))
    (sc : CKA.GameState Γ T) (esP : EStateP Γ T Sig SS RS M E K)
    (sp : PRFPRNG.GameState Sig I K)
    (k : Option (SM.RecvResult M) → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (ih : ∀ r esS' sc' esP' sp',
      Sync10ShiftedPaper prng Δ_off l t esS' sc' esP' sp' →
      𝒟[runRDFShiftedPaper cka prng fs Δ_off b_auth qep l t (k r) esS' sc'] {true} ≤
        𝒟[runRDFShifted10Paper cka prng fs Δ_off b_auth qep l t (k r) esP' sp'] {true})
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp)
    (hwin0 : esS.g.win = false)
    (htrans0 : (esS.g.inTransit P.other c).isSome = false)
    (hsafe0 : esS.g.safeInj (2 + Δ_off) = true)
    (hsend0 : P.sendsIn c.1.1 = false)
    (hnew : c.1.1 = esS.g.epoch P + 1) :
    𝒟[stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t (.inr (.inl (.inl (.inr (P, c))))) esS sc
        >>= fun r =>
      runRDFShiftedPaper cka prng fs Δ_off b_auth qep l t (k r.1.1) r.1.2 r.2] {true} ≤
    𝒟[stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
        (.inr (.inl (.inl (.inr (P, c))))) esP sp >>= fun r =>
      runRDFShifted10Paper cka prng fs Δ_off b_auth qep l t (k r.1.1) r.1.2 r.2] {true} := by
  let mo : Mode := ⟨true, some (l - 1), t⟩
  have hwin : esP.g.win = esS.g.win := eraseSt_win hS.g_eq
  have htrans : esP.g.inTransit P.other c = esS.g.inTransit P.other c :=
    eraseSt_inTransit hS.g_eq P.other c
  have hsafe : esP.g.safeInj (2 + Δ_off) = esS.g.safeInj (2 + Δ_off) :=
    eraseSt_safeInj hS.g_eq (2 + Δ_off)
  have hesS_eq := estate_mk_abort_false hS.abort_C
  have hesP_eq := estate_mk_abort_false hS.abort_P
  have hsend0' : P.sendsIn (esS.g.epoch P + 1) = false := hnew ▸ hsend0
  have htriv_false :
      ∀ i', trivHook b_auth Δ_off t esS.g ⟨P.other, esS.g.epoch P + 1, i'⟩ = false := fun i' => by
    rw [trivHook_eq_trivial_of_new_epoch]
    exact trivial_false_of_safeInj esS.g (2 + Δ_off) P i' hsafe0 hS.comp_inv
  have htrivP_false :
      ∀ i', trivHook b_auth Δ_off t esP.g ⟨P.other, esS.g.epoch P + 1, i'⟩ = false := fun i' => by
    rw [eraseSt_trivHook hS.g_eq]; exact htriv_false i'
  cases hTn : c.1.2 with
  | none =>
    have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
        (.inr (.inl (.inl (.inr (P, c))))) esS sc =
        pure ((some .rejected, esS), sc) := by
      simp [stepCDFShiftedPaper, implEDFG, injectEG, vRecv, hS.abort_C,
        hwin0, htrans0, hsafe0, hS.id_C P, hS.tcur_C P, hsend0', hnew, hTn, StateT.run_pure,
        hesS_eq]
    have hP : stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
        (.inr (.inl (.inl (.inr (P, c))))) esP sp =
        pure ((some .rejected, esP), sp) := by
      simp [stepPDFShiftedPaperGen, implEDFG, injectEG, vRecv,
        hS.abort_P, hwin, htrans, hsafe, hwin0, htrans0, hsafe0, hS.id_P P, hS.tcur_P P, hsend0',
        hnew, hTn, StateT.run_pure, hesP_eq]
    rw [hC, hP, pure_bind, pure_bind]; exact ih (some .rejected) esS sc esP sp hS
  | some Tn =>
    have hafter : ∀ (γC' : Option Γ) (σC' : Sig) (γP' : Γ) (σP' : Option Sig) (rs : RS)
        (sp' : PRFPRNG.GameState Sig I K)
        (hsp' : sp'.prf = sp.prf ∨
          (sp.corr = false ∧ max (esS.g.epoch .A) (esS.g.epoch .B) + 1 ≥ t))
        (hsp_eq : sp' = { sp with prf := sp'.prf })
        (hsC : ((hooksCKAShifted cka prng fs l (tStarHook b_auth t)).startRecv esS.g P
          (esS.g.epoch P + 1) (esS.g.st P).γ (esS.g.st P).root Tn).run esS.h =
          pure (some (some (γC', σC', rs)), esS.h))
        (hsP : (simulateQ (pImpl prng)
          (((hooksPRNG cka prng fs (moHook b_auth l t)).startRecv esP.g P (esS.g.epoch P + 1)
            (esP.g.st P).γ (esP.g.st P).root Tn).run esP.h)).run sp =
          pure ((some (some (γP', σP', rs)), esP.h), sp')),
        𝒟[stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
            (.inr (.inl (.inl (.inr (P, c))))) esS sc >>= fun r =>
          runRDFShiftedPaper cka prng fs Δ_off b_auth qep l t (k r.1.1) r.1.2 r.2] {true} ≤
        𝒟[stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
            (.inr (.inl (.inl (.inr (P, c))))) esP sp >>= fun r =>
          runRDFShifted10Paper cka prng fs Δ_off b_auth qep l t (k r.1.1) r.1.2 r.2] {true} := by
      intro γC' σC' γP' σP' rs sp' hsp' hsp_eq hsC hsP
      have hS' : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp' := by
        rw [hsp_eq]; exact hS.set_prf sp'.prf hsp'
      rcases hfs : fs.receive rs c.1 c.2 with _ | ⟨v', i', m'⟩
      · have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
            (.inr (.inl (.inl (.inr (P, c))))) esS sc =
            pure ((some .rejected, esS), sc) := by
          simp [stepCDFShiftedPaper, implEDFG, injectEG, vRecv,
            hS.abort_C, hwin0, htrans0, hsafe0, hS.id_C P, hS.tcur_C P, hsend0', hnew, hTn, hsC,
            hfs, StateT.run_bind, StateT.run_pure, simulateQ_pure, hesS_eq]
        have hP : stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
            (.inr (.inl (.inl (.inr (P, c))))) esP sp =
            pure ((some .rejected, esP), sp') := by
          simp [stepPDFShiftedPaperGen, implEDFG, injectEG, vRecv,
            hS.abort_P, hwin, htrans, hsafe, hwin0, htrans0, hsafe0, hS.id_P P, hS.tcur_P P,
            hsend0', hnew, hTn, StateT.run_bind, simulateQ_bind, hsP, hfs, StateT.run_pure,
            simulateQ_pure, hesP_eq]
        rw [hC, hP, pure_bind, pure_bind]; exact ih (some .rejected) esS sc esP sp' hS'
      · by_cases hqep : qep + 1 < esS.g.epoch P + 1
        · have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
              (.inr (.inl (.inl (.inr (P, c))))) esS sc =
              pure ((some .rejected, esS), sc) := by
            simp [stepCDFShiftedPaper, implEDFG, injectEG, vRecv,
              hS.abort_C, hwin0, htrans0, hsafe0, hS.id_C P, hS.tcur_C P, hsend0', hnew, hTn, hsC,
              hfs, hqep, StateT.run_bind, StateT.run_pure, simulateQ_pure, hesS_eq]
          have hP : stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
              (.inr (.inl (.inl (.inr (P, c))))) esP sp =
              pure ((some .rejected, esP), sp') := by
            simp [stepPDFShiftedPaperGen, implEDFG, injectEG, vRecv,
              hS.abort_P, hwin, htrans, hsafe, hwin0, htrans0, hsafe0, hS.id_P P, hS.tcur_P P,
              hsend0', hnew, hTn, StateT.run_bind, simulateQ_bind, hsP, hfs, hqep, StateT.run_pure,
              simulateQ_pure, hesP_eq]
          rw [hC, hP, pure_bind, pure_bind]; exact ih (some .rejected) esS sc esP sp' hS'
        · have htrivC := htriv_false i'
          have htrivP := htrivP_false i'
          by_cases hinj : (SM.Config.auth (Msg := M) t).injectFull (esS.g.epoch P + 1)
          · have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
                (.inr (.inl (.inl (.inr (P, c))))) esS sc =
                pure ((some .rejected, { esS with g := { esS.g with win := true } }), sc) := by
              simp [stepCDFShiftedPaper, implEDFG, injectEG, vRecv,
                hS.abort_C, hwin0, htrans0, hsafe0, hS.id_C P, hS.tcur_C P, hsend0', hnew, hTn,
                hsC, hfs, hqep, htrivC, hinj, StateT.run_bind, StateT.run_pure, StateT.run_modify,
                simulateQ_pure]
            have hP : stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
                (.inr (.inl (.inl (.inr (P, c))))) esP sp =
                pure ((some .rejected, { esP with g := { esP.g with win := true } }), sp') := by
              simp [stepPDFShiftedPaperGen, implEDFG, injectEG, vRecv,
                hS.abort_P, hwin, htrans, hsafe, hwin0, htrans0, hsafe0, hS.id_P P, hS.tcur_P P,
                hsend0', hnew, hTn, StateT.run_bind, simulateQ_bind, hsP, hfs, hqep, htrivP, hinj,
                StateT.run_pure, StateT.run_modify, simulateQ_pure]
            rw [hC, hP, pure_bind, pure_bind, hsp_eq]
            exact ih (some .rejected) _ _ _ _ (hS.set_win_prf true sp'.prf hsp')
          · simp only [Bool.not_eq_true] at hinj
            have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
                (.inr (.inl (.inl (.inr (P, c))))) esS sc =
                pure ((some .rejected, esS), sc) := by
              simp [stepCDFShiftedPaper, implEDFG, injectEG, vRecv,
                hS.abort_C, hwin0, htrans0, hsafe0, hS.id_C P, hS.tcur_C P, hsend0', hnew, hTn,
                hsC, hfs, hqep, htrivC, hinj, StateT.run_bind, StateT.run_pure, simulateQ_pure,
                hesS_eq]
            have hP : stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
                (.inr (.inl (.inl (.inr (P, c))))) esP sp =
                pure ((some .rejected, esP), sp') := by
              simp [stepPDFShiftedPaperGen, implEDFG, injectEG, vRecv,
                hS.abort_P, hwin, htrans, hsafe, hwin0, htrans0, hsafe0, hS.id_P P, hS.tcur_P P,
                hsend0', hnew, hTn, StateT.run_bind, simulateQ_bind, hsP, hfs, hqep, htrivP, hinj,
                StateT.run_pure, simulateQ_pure, hesP_eq]
            rw [hC, hP, pure_bind, pure_bind]; exact ih (some .rejected) esS sc esP sp' hS'
    have hcache := hS.cache_at_succ P c.1.1 hnew
    have hnone :
        (∀ Im, esS.h.base.cache (esS.g.epoch P + 1) ≠ some (Tn, Im)) →
        (∀ σc k, esP.h.cache (esS.g.epoch P + 1) ≠ some (Tn, σc, k)) →
        𝒟[stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
            (.inr (.inl (.inl (.inr (P, c))))) esS sc >>= fun r =>
          runRDFShiftedPaper cka prng fs Δ_off b_auth qep l t (k r.1.1) r.1.2 r.2] {true} ≤
        𝒟[stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
            (.inr (.inl (.inl (.inr (P, c))))) esP sp >>= fun r =>
          runRDFShifted10Paper cka prng fs Δ_off b_auth qep l t (k r.1.1) r.1.2 r.2] {true} := by
      intro hcC_none hcP_none
      have hsC_un := startRecv_CKAShifted_unhonest cka prng fs l (tStarHook b_auth t) esS.g P
        (esS.g.epoch P + 1) (esS.g.st P).γ (esS.g.st P).root Tn esS.h hcC_none
      have hsP_un := startRecv_PRNG_unhonest cka prng fs (moHook b_auth l t) esP.g P
        (esS.g.epoch P + 1) (esP.g.st P).γ (esP.g.st P).root Tn esP.h hcP_none
      by_cases htStar : b_auth = true ∧ esS.g.epoch P + 1 = t
      · rcases htStar with ⟨rfl, htStar⟩
        by_cases hloc : localCKA mo 1 (esS.g.epoch P)
        · have hγC : (esS.g.st P).γ = some (esP.g.st P).γ := by
            rw [hS.γ_C P]; simp [mo, hloc]
          obtain ⟨hσ, hcorr0, hprng0⟩ := hS.sp_at_recv_tStar P htStar hloc
          have hm_ge : max (esS.g.epoch .A) (esS.g.epoch .B) + 1 ≥ t := by
            have : esS.g.epoch P ≤ max (esS.g.epoch .A) (esS.g.epoch .B) := by cases P <;> simp
            omega
          let kk := cka.receive (esP.g.st P).γ Tn
          let p := prng.up (esS.g.st P).root kk.2
          refine hafter (some kk.1) p.1 kk.1 (some p.1) (fs.initReceiver p.2)
            { sp with prf := true } (Or.inr ⟨hcorr0, hm_ge⟩) rfl ?_ ?_
          · rw [hsC_un]; simp [tStarHook, htStar, hγC, kk, p]
          · rw [hsP_un]
            simp [htStar, liftP, PRFPRNG.challPrfQuery, pImpl,
              PRFPRNG.oracleImpl, PRFPRNG.challPrfImpl, hcorr0, hprng0, hS.b_P, hσ, kk, p,
              simulateQ_bind, simulateQ_query, map_eq_bind_pure_comp,
              StateT.run_bind, StateT.run_get, StateT.run_pure, StateT.run_set]
        · simp only [Bool.not_eq_true] at hloc
          have hγC : (esS.g.st P).γ = none := by rw [hS.γ_C P]; simp [mo, hloc]
          have hsC_abort : ((hooksCKAShifted cka prng fs l (tStarHook true t)).startRecv esS.g P
              (esS.g.epoch P + 1) (esS.g.st P).γ (esS.g.st P).root Tn).run esS.h =
              pure (none, esS.h) := by
            rw [hsC_un]; simp [tStarHook, htStar, hγC]
          have hC : stepCDFShiftedPaper cka prng fs Δ_off true qep l t
              (.inr (.inl (.inl (.inr (P, c))))) esS sc =
              pure ((none, { esS with abort := true }), sc) := by
            simp [stepCDFShiftedPaper, implEDFG, injectEG, abortE,
              vRecv, hS.abort_C, hwin0, htrans0, hsafe0, hS.id_C P,
              hS.tcur_C P, hsend0', hnew, hTn, hsC_abort,
              StateT.run_bind, StateT.run_pure, StateT.run_modify, simulateQ_pure]
          rw [hC, pure_bind]
          exact runRDFShiftedPaper_abort_apply_true_le cka prng fs Δ_off true qep l t (k none) rfl _
      · have htStarC : esS.g.epoch P + 1 ≠ tStarHook b_auth t := by
          cases b_auth
          · simp [tStarHook]
          · simpa [tStarHook] using htStar
        have htStarP : ¬((moHook b_auth l t).auth = true ∧
            esS.g.epoch P + 1 = (moHook b_auth l t).tStar) := by simpa [moHook] using htStar
        have hsC_rej : ((hooksCKAShifted cka prng fs l (tStarHook b_auth t)).startRecv esS.g P
            (esS.g.epoch P + 1) (esS.g.st P).γ (esS.g.st P).root Tn).run esS.h =
            pure (some none, esS.h) := by rw [hsC_un]; simp [htStarC]
        have hsP_rej : ((hooksPRNG cka prng fs (moHook b_auth l t)).startRecv esP.g P
            (esS.g.epoch P + 1) (esP.g.st P).γ (esP.g.st P).root Tn).run esP.h =
            pure (some none, esP.h) := by rw [hsP_un]; simp [htStarP]
        have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
            (.inr (.inl (.inl (.inr (P, c))))) esS sc =
            pure ((some .rejected, esS), sc) := by
          simp [stepCDFShiftedPaper, implEDFG, injectEG, vRecv,
            hS.abort_C, hwin0, htrans0, hsafe0, hS.id_C P, hS.tcur_C P, hsend0', hnew, hTn,
            hsC_rej, StateT.run_bind, StateT.run_pure, simulateQ_pure, hesS_eq]
        have hP : stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
            (.inr (.inl (.inl (.inr (P, c))))) esP sp =
            pure ((some .rejected, esP), sp) := by
          simp [stepPDFShiftedPaperGen, implEDFG, injectEG, vRecv,
            hS.abort_P, hwin, htrans, hsafe, hwin0, htrans0, hsafe0, hS.id_P P, hS.tcur_P P,
            hsend0', hnew, hTn, hsP_rej, StateT.run_bind, StateT.run_pure, simulateQ_pure, hesP_eq]
        rw [hC, hP, pure_bind, pure_bind]; exact ih (some .rejected) esS sc esP sp hS
    rcases hcache with ⟨hcC, hcP⟩ | ⟨Tm, Im, hcC, hcP⟩
    · rw [hnew] at hcC hcP
      exact hnone (by simp [hcC]) (by simp [hcP])
    · rw [hnew] at hcC hcP
      have hcC' : esS.h.base.cache (esS.g.epoch P + 1) = some (Tm, Im) := hcC
      by_cases hTm : Tm = Tn
      · subst hTm
        let p := prng.up (esS.g.st P).root Im
        refine hafter ((esS.g.st P).γ.map fun γ => (cka.receive γ Tm).1) p.1
          (cka.receive (esP.g.st P).γ Tm).1
          (esP.g.st (Party.senderOf (esS.g.epoch P + 1))).root
          (fs.initReceiver p.2) sp (Or.inl rfl) rfl ?_ ?_
        · simp [hooksCKAShifted, hcC', p, StateT.run_bind, StateT.run_get, StateT.run_pure]
        · simp [hooksPRNG, hcP, p, StateT.run_bind, StateT.run_get, StateT.run_pure,
            simulateQ_pure]
      · exact hnone (by simp [hcC', hTm]) (by simp [hcP, hTm])

theorem step_injectE_DFShiftedPaper_le (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δ_off : ℕ) (b_auth : Bool) (qep l t : ℕ)
    (q : Party × (Header T × E))
    (esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I))
    (sc : CKA.GameState Γ T) (esP : EStateP Γ T Sig SS RS M E K)
    (sp : PRFPRNG.GameState Sig I K)
    (k : Option (SM.RecvResult M) → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (ih : ∀ r esS' sc' esP' sp',
      Sync10ShiftedPaper prng Δ_off l t esS' sc' esP' sp' →
      𝒟[runRDFShiftedPaper cka prng fs Δ_off b_auth qep l t (k r) esS' sc'] {true} ≤
        𝒟[runRDFShifted10Paper cka prng fs Δ_off b_auth qep l t (k r) esP' sp'] {true})
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp) :
    𝒟[stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t (.inr (.inl (.inl (.inr q)))) esS sc
        >>= fun r =>
      runRDFShiftedPaper cka prng fs Δ_off b_auth qep l t (k r.1.1) r.1.2 r.2] {true} ≤
    𝒟[stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
        (.inr (.inl (.inl (.inr q)))) esP sp >>= fun r =>
      runRDFShifted10Paper cka prng fs Δ_off b_auth qep l t (k r.1.1) r.1.2 r.2] {true} := by
  rcases q with ⟨P, c⟩
  have hwin : esP.g.win = esS.g.win := eraseSt_win hS.g_eq
  have htrans : esP.g.inTransit P.other c = esS.g.inTransit P.other c :=
    eraseSt_inTransit hS.g_eq P.other c
  have hsafe : esP.g.safeInj (2 + Δ_off) = esS.g.safeInj (2 + Δ_off) :=
    eraseSt_safeInj hS.g_eq (2 + Δ_off)
  have hesS_eq := estate_mk_abort_false hS.abort_C
  have hesP_eq := estate_mk_abort_false hS.abort_P
  by_cases hguard : esS.g.win || (esS.g.inTransit P.other c).isSome || !esS.g.safeInj (2 + Δ_off)
  · simp only [Bool.or_eq_true, Bool.not_eq_true'] at hguard
    have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
        (.inr (.inl (.inl (.inr (P, c))))) esS sc =
        pure ((none, esS), sc) := by
      simp [stepCDFShiftedPaper, implEDFG, injectEG, hS.abort_C,
        hguard, StateT.run_pure]
    have hP : stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
        (.inr (.inl (.inl (.inr (P, c))))) esP sp =
        pure ((none, esP), sp) := by
      simp [stepPDFShiftedPaperGen, implEDFG, injectEG, hS.abort_P,
        hwin, htrans, hsafe, hguard, StateT.run_pure]
    rw [hC, hP, pure_bind, pure_bind]; exact ih none esS sc esP sp hS
  · simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Bool.not_eq_false'] at hguard
    rcases hguard with ⟨⟨hwin0, htrans0⟩, hsafe0⟩
    by_cases hsend : P.sendsIn c.1.1 || decide (esS.g.epoch P + 1 < c.1.1)
    · simp only [Bool.or_eq_true, decide_eq_true_eq] at hsend
      have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
          (.inr (.inl (.inl (.inr (P, c))))) esS sc =
          pure ((some .rejected, esS), sc) := by
        simp [stepCDFShiftedPaper, implEDFG, injectEG, vRecv,
          hS.abort_C, hwin0, htrans0, hsafe0, hS.id_C P, hS.tcur_C P, hsend, StateT.run_pure,
          hesS_eq]
      have hP : stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
          (.inr (.inl (.inl (.inr (P, c))))) esP sp =
          pure ((some .rejected, esP), sp) := by
        simp [stepPDFShiftedPaperGen, implEDFG, injectEG, vRecv,
          hS.abort_P, hwin, htrans, hsafe, hwin0, htrans0, hsafe0, hS.id_P P, hS.tcur_P P, hsend,
          StateT.run_pure, hesP_eq]
      rw [hC, hP, pure_bind, pure_bind]; exact ih (some .rejected) esS sc esP sp hS
    · simp only [Bool.not_eq_true, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hsend
      rcases hsend with ⟨hsend0, hle⟩
      by_cases hnew : c.1.1 = esS.g.epoch P + 1
      · exact step_injectE_new_epoch_DFShiftedPaper_le cka prng fs Δ_off b_auth qep l t P c
          esS sc esP sp k ih hS hwin0 htrans0 hsafe0 hsend0 hnew
      · have hle_ep : c.1.1 ≤ esS.g.epoch P := by omega
        have hvRP : (esP.g.st P).vR c.1.1 = (esS.g.st P).vR c.1.1 := by rw [hS.vR_eq P]
        cases hvR : (esS.g.st P).vR c.1.1 with
        | none =>
          have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
              (.inr (.inl (.inl (.inr (P, c))))) esS sc =
              pure ((some .rejected, esS), sc) := by
            simp [stepCDFShiftedPaper, implEDFG, injectEG, vRecv,
              hS.abort_C, hwin0, htrans0, hsafe0, hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR,
              StateT.run_pure, hesS_eq]
          have hP : stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
              (.inr (.inl (.inl (.inr (P, c))))) esP sp =
              pure ((some .rejected, esP), sp) := by
            simp [stepPDFShiftedPaperGen, implEDFG, injectEG, vRecv,
              hS.abort_P, hwin, htrans, hsafe, hwin0, htrans0, hsafe0, hS.id_P P, hS.tcur_P P,
              hsend0, hle, hnew, hvRP, hvR, StateT.run_pure, hesP_eq]
          rw [hC, hP, pure_bind, pure_bind]; exact ih (some .rejected) esS sc esP sp hS
        | some v =>
          rcases hfs : fs.receive v c.1 c.2 with _ | ⟨v', i', m'⟩
          · have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
                (.inr (.inl (.inl (.inr (P, c))))) esS sc =
                pure ((some .rejected, esS), sc) := by
              simp [stepCDFShiftedPaper, implEDFG, injectEG, vRecv,
                hS.abort_C, hwin0, htrans0, hsafe0, hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR,
                hfs, StateT.run_pure, hesS_eq]
            have hP : stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
                (.inr (.inl (.inl (.inr (P, c))))) esP sp =
                pure ((some .rejected, esP), sp) := by
              simp [stepPDFShiftedPaperGen, implEDFG, injectEG, vRecv,
                hS.abort_P, hwin, htrans, hsafe, hwin0, htrans0, hsafe0, hS.id_P P, hS.tcur_P P,
                hsend0, hle, hnew, hvRP, hvR, hfs, StateT.run_pure, hesP_eq]
            rw [hC, hP, pure_bind, pure_bind]; exact ih (some .rejected) esS sc esP sp hS
          · by_cases hqep : qep + 1 < c.1.1
            · have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
                  (.inr (.inl (.inl (.inr (P, c))))) esS sc =
                  pure ((some .rejected, esS), sc) := by
                simp [stepCDFShiftedPaper, implEDFG, injectEG, vRecv,
                  hS.abort_C, hwin0, htrans0, hsafe0, hS.id_C P, hS.tcur_C P, hsend0, hle, hnew,
                  hvR, hfs, hqep, StateT.run_pure, hesS_eq]
              have hP : stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
                  (.inr (.inl (.inl (.inr (P, c))))) esP sp =
                  pure ((some .rejected, esP), sp) := by
                simp [stepPDFShiftedPaperGen, implEDFG, injectEG, vRecv,
                  hS.abort_P, hwin, htrans, hsafe, hwin0, htrans0, hsafe0, hS.id_P P, hS.tcur_P P,
                  hsend0, hle, hnew, hvRP, hvR, hfs, hqep, StateT.run_pure, hesP_eq]
              rw [hC, hP, pure_bind, pure_bind]; exact ih (some .rejected) esS sc esP sp hS
            · let pos : SM.Pos := ⟨P.other, c.1.1, i'⟩
              have htriv_eq : trivHook b_auth Δ_off t esP.g pos =
                  trivHook b_auth Δ_off t esS.g pos :=
                eraseSt_trivHook hS.g_eq b_auth Δ_off t pos
              by_cases htriv : trivHook b_auth Δ_off t esS.g pos
              · let vR' := Function.update (esS.g.st P).vR c.1.1 (some v')
                have hvR'_eq : Function.update (esP.g.st P).vR c.1.1 (some v') = vR' := by
                  simp [vR', hS.vR_eq P]
                have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
                    (.inr (.inl (.inl (.inr (P, c))))) esS sc =
                    pure ((some (.accepted c.1.1 i' (some m')),
                      { esS with g := esS.g.accept P { esS.g.st P with vR := vR' } pos }), sc) := by
                  simp [stepCDFShiftedPaper, implEDFG, injectEG, vRecv,
                    commitE, hS.abort_C, hwin0, htrans0, hsafe0, hS.id_C P,
                    hS.tcur_C P, hsend0, hle, hnew, hvR, hfs, hqep, htriv, pos, vR',
                    StateT.run_pure, StateT.run_modify]
                have hP : stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
                    (.inr (.inl (.inl (.inr (P, c))))) esP sp =
                    pure ((some (.accepted c.1.1 i' (some m')),
                      { esP with g := esP.g.accept P { esP.g.st P with vR := vR' } pos }), sp) := by
                  simp [stepPDFShiftedPaperGen, implEDFG, injectEG,
                    vRecv, commitE, hS.abort_P, hwin, htrans, hsafe, hwin0, htrans0, hsafe0,
                    hS.id_P P, hS.tcur_P P, hsend0, hle, hnew, hvRP, hvR, hfs, hqep, htriv_eq,
                    htriv, pos, hvR'_eq, StateT.run_pure, StateT.run_modify]
                rw [hC, hP, pure_bind, pure_bind]
                exact ih _ _ _ _ _ (hS.accept_old P vR' pos hle_ep)
              · simp only [Bool.not_eq_true] at htriv
                by_cases hinj : (SM.Config.auth (Msg := M) t).injectFull c.1.1
                · have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
                      (.inr (.inl (.inl (.inr (P, c))))) esS sc =
                      pure ((some .rejected, { esS with g := { esS.g with win := true } }),
                        sc) := by
                    simp [stepCDFShiftedPaper, implEDFG, injectEG,
                      vRecv, hS.abort_C, hwin0, htrans0, hsafe0, hS.id_C P,
                      hS.tcur_C P, hsend0, hle, hnew, hvR, hfs, hqep, htriv, hinj, pos,
                      StateT.run_pure, StateT.run_modify]
                  have hP : stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
                      (.inr (.inl (.inl (.inr (P, c))))) esP sp =
                      pure ((some .rejected, { esP with g := { esP.g with win := true } }),
                        sp) := by
                    simp [stepPDFShiftedPaperGen, implEDFG, injectEG,
                      vRecv, hS.abort_P, hwin, htrans, hsafe, hwin0, htrans0, hsafe0,
                      hS.id_P P, hS.tcur_P P, hsend0, hle, hnew, hvRP, hvR, hfs,
                      hqep, htriv_eq, htriv, hinj, pos, StateT.run_pure, StateT.run_modify]
                  rw [hC, hP, pure_bind, pure_bind]
                  exact ih (some .rejected) _ _ _ _ (hS.set_win_prf true sp.prf (Or.inl rfl))
                · simp only [Bool.not_eq_true] at hinj
                  have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
                      (.inr (.inl (.inl (.inr (P, c))))) esS sc =
                      pure ((some .rejected, esS), sc) := by
                    simp [stepCDFShiftedPaper, implEDFG, injectEG,
                      vRecv, hS.abort_C, hwin0, htrans0, hsafe0, hS.id_C P,
                      hS.tcur_C P, hsend0, hle, hnew, hvR, hfs, hqep, htriv, hinj, pos,
                      StateT.run_pure, hesS_eq]
                  have hP : stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
                      (.inr (.inl (.inl (.inr (P, c))))) esP sp =
                      pure ((some .rejected, esP), sp) := by
                    simp [stepPDFShiftedPaperGen, implEDFG, injectEG,
                      vRecv, hS.abort_P, hwin, htrans, hsafe, hwin0, htrans0, hsafe0,
                      hS.id_P P, hS.tcur_P P, hsend0, hle, hnew, hvRP, hvR, hfs,
                      hqep, htriv_eq, htriv, hinj, pos, StateT.run_pure, hesP_eq]
                  rw [hC, hP, pure_bind, pure_bind]
                  exact ih (some .rejected) esS sc esP sp hS

end AuthL10ShiftedPaper

end CryptoGames.SM.Construction.DeliverForge

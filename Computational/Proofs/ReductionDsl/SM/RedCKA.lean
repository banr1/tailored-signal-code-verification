/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.SM.Engine
public import Computational.Proofs.ReductionDsl.Size
import Computational.Proofs.ReductionDsl.Notation

/-!
# Costed CKA reductions for SM authenticity and privacy

Implements the `ReductionDsl.CostedReduction` CKA reductions for SM authenticity and privacy
(`redCKAAuthProg`, `redCKAAuthBucketProg`, `redCKAPrivProg`, `redCKAPrivUProg`) over `ckaSig` and
`ckaIface`, and proves simulation evaluation agreement, static query bounds, and static cost
characterizations.
-/

@[expose] public section

open ReductionDsl OracleSpec OracleComp

namespace CryptoGames.SM.Engine

open Construction CKA

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}

local notation "S" => ckaSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrTy" => ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrCtTy" => ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "psTy" => ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "rrTy" => ckaRrTy KC Γ CCoins T I KR RSt K SS RS M E

/-! ## Multi-step simulation agreement for `implEC` -/

theorem epMgmt_b_eq {St Msg C : Type} {Δ qep : ℕ} {s s₁ : GameState St Msg C}
    {P : Party} {bad : Bool} (h : s.epMgmt Δ qep P bad = some s₁) :
    s₁.b = s.b := by
  unfold GameState.epMgmt at h
  by_cases h1 : P.sendsIn (s.epoch P + 1)
  · by_cases h2 : qep < s.epoch P + 1
    · simp [h1, h2] at h
    · simp only [h1, h2, ↓reduceIte, Option.some.injEq] at h
      subst h
      by_cases h3 : (bad && !(s.safeCh Δ P)) = true <;> simp [h3, GameState.leak]
  · by_cases h2 : qep < s.epoch P
    · simp [h1, h2] at h
    · simp only [h1, Bool.false_eq_true, h2, ↓reduceIte, Option.some.injEq] at h
      subst h; rfl

theorem commitE_b_eq {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (s : Ctx γV T σV ssV rsV M E) (P : Party)
    (old new : VP γV T σV ssV rsV) (pos : Pos) :
    ∀ res ∈ support ((commitE hk s P old new pos).run es),
      res.2.g.b = es.g.b ∧ (∀ s₁, res.1 = some s₁ → s₁.b = s.b) := by
  intro ⟨cmRes, es'⟩ hmem
  unfold commitE abortE at hmem
  rw [run_liftH_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨ans, h'⟩, _, hmem⟩ := hmem
  rcases ans with _ | new'
  · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact ⟨rfl, fun _ h => by cases h⟩
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    refine ⟨rfl, fun s₁ hs₁ => ?_⟩
    cases hs₁; rfl

theorem transmitE_b_eq [Inhabited E] {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {Δ qep : ℕ} (π : Policy)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (arg : Party × M × Option CCoins) :
    ∀ res ∈ support ((transmitE hk Δ qep π arg).run es), res.2.g.b = es.g.b := by
  rcases arg with ⟨P, m, r⟩
  intro ⟨out, es'⟩ hmem
  unfold transmitE abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases hab : (es.abort || es.g.win)
  · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; rfl
  · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
    rcases hep : es.g.epMgmt Δ qep P r.isSome with _ | s₁
    · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; rfl
    · simp only [hep] at hmem
      by_cases hdoom : π.leakDoom es.g s₁
      · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; rfl
      · simp only [hdoom, Bool.false_eq_true, ↓reduceIte] at hmem
        rw [run_liftH_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨vsRes, h'⟩, _, hmem⟩ := hmem
        rcases vsRes with _ | ⟨st', c⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; rfl
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩
          dsimp [GameState.record]
          exact epMgmt_b_eq hep

theorem challE_b_eq [Inhabited E] {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {Δ qep : ℕ} (cfg : Config M) (π : Policy)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (arg : Party × M × M × Option CCoins) :
    ∀ res ∈ support ((challE hk Δ qep cfg π arg).run es), res.2.g.b = es.g.b := by
  rcases arg with ⟨P, m₀, m₁, r⟩
  intro ⟨out, es'⟩ hmem
  unfold challE abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases hab : (es.abort || es.g.win)
  · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; rfl
  · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
    rcases hep : es.g.epMgmt Δ qep P r.isSome with _ | s₁
    · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; rfl
    · simp only [hep] at hmem
      by_cases hch : (!(s₁.safeCh Δ P) || !(cfg.challAllowedIn (s₁.epoch P)))
      · simp only [hch, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; rfl
      · simp only [hch, Bool.false_eq_true, ↓reduceIte] at hmem
        by_cases hdoom : π.leakDoom es.g s₁
        · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; rfl
        · simp only [hdoom, Bool.false_eq_true, ↓reduceIte] at hmem
          rw [run_liftH_bind, mem_support_bind_iff] at hmem
          obtain ⟨⟨vsRes, h'⟩, _, hmem⟩ := hmem
          rcases vsRes with _ | ⟨st', c⟩
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; rfl
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩
            dsimp [GameState.record]
            exact epMgmt_b_eq hep

theorem deliverE_b_eq [DecidableEq T] [DecidableEq M] [DecidableEq E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {maxSkip : ℕ} (cfg : Config M)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (arg : Party × (Header T × E)) :
    ∀ res ∈ support ((deliverE hk maxSkip cfg arg).run es), res.2.g.b = es.g.b := by
  rcases arg with ⟨P, c⟩
  intro ⟨out, es'⟩ hmem
  unfold deliverE abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases hab : (es.abort || es.g.win)
  · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; rfl
  · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
    rcases htr : es.g.inTransit P.other c with _ | r
    · simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; rfl
    · simp only [htr] at hmem
      rw [run_liftH_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨vrRes, h'⟩, _, hmem⟩ := hmem
      rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; rfl
      · by_cases hmust : (cfg.deliverWin && es.g.mustBeCorrect maxSkip P r)
        · simp only [hmust, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; rfl
        · simp only [hmust, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; rfl
      · simp only [StateT.run_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨cmRes, es''⟩, hcm, hmem⟩ := hmem
        have ⟨hEs'', hAcc⟩ := commitE_b_eq hk { es with h := h' } es.g P (es.g.st P) st' r.pos
          (cmRes, es'') hcm
        rcases cmRes with _ | s₁
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hEs''
        · have hs₁ : s₁.b = es.g.b := hAcc s₁ rfl
          simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩
          split_ifs <;> exact hs₁

theorem injectE_b_eq [DecidableEq T] [DecidableEq E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {Δ qep : ℕ} (cfg : Config M)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (arg : Party × (Header T × E)) :
    ∀ res ∈ support ((injectE hk Δ qep cfg arg).run es), res.2.g.b = es.g.b := by
  rcases arg with ⟨P, c⟩
  intro ⟨out, es'⟩ hmem
  unfold injectE abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases href : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj Δ))
  · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; rfl
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hmem
    rw [run_liftH_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨vrRes, h'⟩, _, hmem⟩ := hmem
    rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
    · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; rfl
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; rfl
    · by_cases hqep : qep + 1 < t'
      · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; rfl
      · simp only [hqep, ↓reduceIte] at hmem
        by_cases htriv : es.g.trivial Δ ⟨P.other, t', i'⟩
        · simp only [htriv, ↓reduceIte, StateT.run_bind, mem_support_bind_iff] at hmem
          obtain ⟨⟨cmRes, es''⟩, hcm, hmem⟩ := hmem
          have ⟨hEs'', hAcc⟩ := commitE_b_eq hk { es with h := h' } es.g P (es.g.st P) st'
            ⟨P.other, t', i'⟩ (cmRes, es'') hcm
          rcases cmRes with _ | s₁
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hEs''
          · have hs₁ : s₁.b = es.g.b := hAcc s₁ rfl
            simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hs₁
        · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
          by_cases hf : cfg.injectFull t'
          · simp only [hf, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; rfl
          · simp only [hf, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; rfl

theorem corrE_b_eq {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    (π : Policy)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (P : Party) :
    ∀ res ∈ support ((corrE hk π P).run es), res.2.g.b = es.g.b := by
  intro ⟨out, es'⟩ hmem
  unfold corrE abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases href : (es.abort || es.g.win || !(es.g.corrAllowed P))
  · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; rfl
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hmem
    by_cases hdoom : (π.leakDoom es.g (es.g.afterCorr P) || π.corrDoom es.g P)
    · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
        pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; rfl
    · simp only [hdoom, Bool.false_eq_true, ↓reduceIte] at hmem
      rw [run_liftH_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨revRes, h'⟩, _, hmem⟩ := hmem
      rcases revRes with _ | st
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; rfl
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; rfl

theorem implE_b_eq [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {Δ qep maxSkip : ℕ} (cfg : Config M) (π : Policy)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (t : (SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain) :
    ∀ res ∈ support ((implE hk Δ qep maxSkip cfg π (.inr t)).run es),
      res.2.g.b = es.g.b := by
  rcases t with (((arg | arg) | arg) | arg) | P
  · exact transmitE_b_eq hk π es arg
  · exact challE_b_eq hk cfg π es arg
  · exact deliverE_b_eq hk cfg es arg
  · exact injectE_b_eq hk cfg es arg
  · exact corrE_b_eq hk π es P

theorem liftP_eq_liftM {S' : Sig} {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    (I' : Iface S' (unifSpec + TSpec))
    (hU : ∀ n, I'.fwdU n = query (spec := unifSpec + TSpec) (.inl n))
    {α : Type} (p : ProbComp α) :
    I'.liftP p = (liftM p : TComp TSpec α) := by
  simp only [Iface.liftP, funext hU, ← liftComp_eq_liftM, liftComp_def]
  rfl

variable
  {ckaInitA : KC → Γ}
  {ckaInitB : KC → Γ}
  {ckaSend : Γ → CCoins → Γ × T × I}
  {ckaReceive : Γ → T → Γ × I}
  {prngInit : KR → RSt}
  {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS}
  {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E}
  {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool}
  {eqI : I → I → Bool}
  {eqM : M → M → Bool}
  {eqE : E → E → Bool}
  {lam : I}
  {defaultE : E}

local notation "OO" =>
  ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

/-- Multi-step simulation agreement between `handlerImpl (implEC ...)` and `Engine.implE`. -/
theorem simulateQ_implEC_vr_eq {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S} {HS : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hDefaultE : defaultE = default)
    (hU : ∀ n, I'.fwdU n = query (spec := unifSpec + TSpec) (.inl n))
    (hsEncFn : HS → hsT.denote) (HBounded : HS → Prop) {HBoundedPost : HS → Prop}
    {VROkStep : ℕ → rsvT.denote → Prop}
    (hkC : HooksC OO I' γvT svT ssvT rsvT hsT)
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins
      γvT.denote svT.denote ssvT.denote rsvT.denote)
    (L B Δ qep maxSkip : ℕ)
    (hHk : HooksCAgrees hsEncFn HBounded (HBoundedPost := HBoundedPost)
      (VROk := VROkStep B) hkC hk)
    (hVRHk : HooksVRInv VROkStep hk)
    (cfgC : ConfigEC OO) (cfg : Config M)
    (hCfg : ConfigECAgrees cfgC cfg)
    (heqT : eqT = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    (π : Policy)
    (hHbStep : ∀ (t : (SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
      (es : EState (VP γvT.denote T svT.denote ssvT.denote rsvT.denote) M (Header T × E) HS),
      HBounded es.h → SMStateBoundedEngine L es.g →
      ∀ res ∈ support ((implE hk Δ qep maxSkip cfg π (.inr t)).run es), HBounded res.2.h) :
    ∀ {α : Type}
      {oa : OracleComp (unifSpec + SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) α}
      {qAdv : ℕ},
      oa.IsQueryBoundP
        (isGameQuery (G := SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv →
      ∀ (es : EState (VP γvT.denote T svT.denote ssvT.denote rsvT.denote) M (Header T × E) HS),
        HBounded es.h → SMEngineInv L B qAdv es.g → SMVRInv VROkStep B qAdv es.g →
        (simulateQ
          (handlerImpl (C := ckaSMCodec KC Γ CCoins T I KR RSt K SS RS M E)
            (implEC hkC L Δ qep maxSkip cfgC π .v0 .v1)) oa).run
          (esEnc vpTblEnc hsEncFn es) =
          (Prod.map id (esEnc vpTblEnc hsEncFn) <$>
            (simulateQ (implE hk Δ qep maxSkip cfg π) oa).run es) ∧
        ∀ res ∈ support ((simulateQ (implE hk Δ qep maxSkip cfg π) oa).run es),
          HBounded res.2.h ∧ SMEngineInv L B 0 res.2.g ∧ res.2.g.b = es.g.b := by
  intro α oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro qAdv _ es hHB hInv _
    refine ⟨by simp [simulateQ_pure, Prod.map], ?_⟩
    intro res hmem
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    exact ⟨hHB, hInv.mono (Nat.zero_le qAdv), rfl⟩
  | query_bind q mx ih =>
    intro qAdv hq es hHB hInv hVR
    rw [isQueryBoundP_query_bind_iff] at hq
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind]
    cases q with
    | inl n =>
      have hCoinL :
          ((handlerImpl (C := ckaSMCodec KC Γ CCoins T I KR RSt K SS RS M E)
            (implEC hkC L Δ qep maxSkip cfgC π .v0 .v1)) (.inl n)).run
            (esEnc vpTblEnc hsEncFn es) =
          (fun u => (u, esEnc vpTblEnc hsEncFn es)) <$>
            query (spec := unifSpec + TSpec) (.inl n) := by
        simp [handlerImpl, hU, StateT.run_lift, map_eq_bind_pure_comp]
      have hCoinR :
          (implE hk Δ qep maxSkip cfg π (.inl n)).run es =
          (fun u => (u, es)) <$> query (spec := unifSpec + TSpec) (.inl n) := by
        simp [implE, coinsE, StateT.run_lift, map_eq_bind_pure_comp]
      rw [hCoinL, hCoinR, bind_map_left, bind_map_left, map_bind]
      refine ⟨bind_congr fun u => (ih u (hq.2 u) es hHB hInv hVR).1, ?_⟩
      intro res hmem
      rw [mem_support_bind_iff] at hmem
      obtain ⟨u, _, hmem⟩ := hmem
      exact (ih u (hq.2 u) es hHB hInv hVR).2 res hmem
    | inr t =>
      have hpos : 0 < qAdv := hq.1.resolve_left (by simp [isGameQuery])
      obtain ⟨m, rfl⟩ : ∃ m, qAdv = m + 1 := ⟨qAdv - 1, by omega⟩
      have hqm : ∀ u, (mx u).IsQueryBoundP
          (isGameQuery (G := SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) m := by
        intro u; simpa [isGameQuery] using hq.2 u
      have hVRB : ∀ P t₀ v, (es.g.st P).vR t₀ = some v → VROkStep B v :=
        fun P t₀ v hv => hVRHk.mono (Nat.sub_le B (m + 1)) (hVR P t₀ v hv)
      have hStep :
          ((handlerImpl (C := ckaSMCodec KC Γ CCoins T I KR RSt K SS RS M E)
            (implEC hkC L Δ qep maxSkip cfgC π .v0 .v1)) (.inr t)).run
            (esEnc vpTblEnc hsEncFn es) =
          Prod.map id (esEnc vpTblEnc hsEncFn) <$>
            (implE hk Δ qep maxSkip cfg π (.inr t)).run es := by
        simp only [handlerImpl, StateT.run_mk,
          ← rdec_implEC_eval hDefaultE hsEncFn HBounded hkC hk hHk L Δ qep maxSkip
            cfgC cfg hCfg heqT heqM heqE π .v0 .v1
            (.cons (esEnc vpTblEnc hsEncFn es)
              (.cons ((ckaSMCodec KC Γ CCoins T I KR RSt K SS RS M E).qenc t) .nil))
            es t hHB hInv.toBoundedEngine hVRB rfl rfl,
          map_eq_bind_pure_comp, Function.comp_def]
      rw [hStep, bind_map_left, map_bind]
      refine ⟨OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es₁⟩ hmem => ?_, ?_⟩
      · have hHB₁ := hHbStep t es hHB hInv.toBoundedEngine (u, es₁) hmem
        have hInv₁ := implE_inv hk cfg π es t hInv (u, es₁) hmem
        have hVR₁ := implE_vrInv hk hVRHk cfg π es t hInv hVR (u, es₁) hmem
        exact (ih u (hqm u) es₁ hHB₁ hInv₁ hVR₁).1
      · intro res hmem
        rw [mem_support_bind_iff] at hmem
        obtain ⟨⟨u, es₁⟩, hmem₁, hmem₂⟩ := hmem
        have hHB₁ := hHbStep t es hHB hInv.toBoundedEngine (u, es₁) hmem₁
        have hInv₁ := implE_inv hk cfg π es t hInv (u, es₁) hmem₁
        have hVR₁ := implE_vrInv hk hVRHk cfg π es t hInv hVR (u, es₁) hmem₁
        have hb₁ := implE_b_eq hk cfg π es t (u, es₁) hmem₁
        obtain ⟨hHB₂, hInv₂, hb₂⟩ := (ih u (hqm u) es₁ hHB₁ hInv₁ hVR₁).2 res hmem₂
        exact ⟨hHB₂, hInv₂, hb₂.trans hb₁⟩

end CryptoGames.SM.Engine

namespace CryptoGames.SM.Construction

open Engine CKA
open scoped Computational.Proofs.ReductionDsl.Notation

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}

local notation "S" => ckaSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrTy" => ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrCtTy" => ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "psTy" => ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "rrTy" => ckaRrTy KC Γ CCoins T I KR RSt K SS RS M E

/-! ## `CKAState` representation and `hooksCKAC` -/

/-- Type of `CKAState T I` in `ckaSig`: a table `ℕ → Option (T × I)`. -/
@[reducible] def ckaHsTy : Ty S :=
  .tbl (.opt (.prod (.base .t) (.base .i)))

def ckaHsEnc (s : CKAState T I) :
    (@ckaHsTy KC Γ CCoins T I KR RSt K SS RS M E).denote :=
  s.cache

@[reducible] def ckaVpTy : Ty S :=
  @vpTblTy KC Γ CCoins T I KR RSt K SS RS M E
    (.opt (.base .γ)) (.base .sig) (.base .ss) (.base .rs)

@[reducible] def ckaVpEnc (p : VP (Option Γ) T RSt SS RS) :
    (@ckaVpTy KC Γ CCoins T I KR RSt K SS RS M E).denote :=
  vpTblEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (RSt := RSt)
    (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
    (γvT := .opt (.base .γ)) (svT := .base .sig) (ssvT := .base .ss) (rsvT := .base .rs) p

@[reducible] def ckaEsTy : Ty S :=
  esTy ckaVpTy ckaHsTy

section HooksCKAC

variable
  {ckaInitA : KC → Γ}
  {ckaInitB : KC → Γ}
  {ckaSend : Γ → CCoins → Γ × T × I}
  {ckaReceive : Γ → T → Γ × I}
  {prngInit : KR → RSt}
  {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS}
  {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E}
  {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool}
  {eqI : I → I → Bool}
  {eqM : M → M → Bool}
  {eqE : E → E → Bool}
  {lam : I}
  {defaultE : E}
  {sampKR : ProbComp KR}
  {sampKC : ProbComp KC}
  {sampCCoins : ProbComp CCoins}
  {sampI : ProbComp I}
  {sampK : ProbComp K}

local notation "OO" =>
  ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

local notation "II" =>
  ckaIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK

def ckaStartSendC (Δcka : ℕ) (mo : Mode) {Γ'}
    (hE : Expr OO Γ' ckaHsTy)
    (_ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat)
    (γvE : Expr OO Γ' (.opt (.base .γ)))
    (σE : Expr OO Γ' (.base .sig))
    (rE : Expr OO Γ' (.opt (.base .ccoins))) :
    Comp OO II Γ'
      (.prod (.opt (.prod (.opt (.base .γ)) (.prod (.base .t) (.prod (.base .sig) (.base .ss)))))
        ckaHsTy) :=
  rdsl do
    (h0, p0, t0, γv0, σ0, r0) ← return (hE, pE, tE, γvE, σE, rE)
    match γv0 with
    | none =>
      tiOpt ←
        match r0 with
        | none =>
          if t0 == nat mo.tH then
            query (O := OO) (I := II) CKATag.chall p0
          else
            query (O := OO) (I := II) CKATag.send p0
        | some coins =>
          query (O := OO) (I := II) CKATag.sendBad (p0, coins)
      match tiOpt with
      | none => return (none, h0)
      | some (tMsg, ik) =>
        let h1 := tset h0 t0 (some (tMsg, ik))
        let pOut := Expr.op (O := OO) CKAOp.prngUp (σ0, ik)
        let ss := Expr.op (O := OO) CKAOp.fsInitSender pOut.2
        if leN (nat (mo.tH + Δcka)) t0 then
          γOpt ← query (I := II) CKATag.corr p0
          match γOpt with
          | none => return (none, h1)
          | some γ' =>
            return (some (some γ', tMsg, pOut.1, ss), h1)
        else
          return (some (none, tMsg, pOut.1, ss), h1)
    | some γ =>
      coins ←
        match r0 with
        | none => sample (O := OO) (I := II) CKASamp.ccoins ()
        | some c => return c
      let cOut := Expr.op (O := OO) CKAOp.ckaSend (γ, coins)
      let tMsg := cOut.2.1
      let ik := cOut.2.2
      let h1 := tset h0 t0 (some (tMsg, ik))
      let pOut := Expr.op (O := OO) CKAOp.prngUp (σ0, ik)
      let ss := Expr.op (O := OO) CKAOp.fsInitSender pOut.2
      return (some (some cOut.1, tMsg, pOut.1, ss), h1)

def ckaStartRecvAnsE (mo : Mode) {Γ'}
    (hE : Expr OO Γ' ckaHsTy)
    (tE : Expr OO Γ' .nat)
    (γvE : Expr OO Γ' (.opt (.base .γ)))
    (σE : Expr OO Γ' (.base .sig))
    (tnE : Expr OO Γ' (.base .t)) :
    Expr OO Γ'
      (.opt (.opt (.prod (.opt (.base .γ)) (.prod (.base .sig) (.base .rs))))) :=
  rdslExpr =>
    letE (hE, tE, γvE, σE, tnE) fun (h0, t0, γv0, σ0, tn0) =>
      let honest :=
        match tget h0 t0 with
        | none => none
        | some (tCached, ikCached) =>
          if Expr.op (O := OO) CKAOp.eqT (tCached, tn0) then some ikCached else none
      match honest with
      | none =>
        if bool mo.auth && (t0 == nat mo.tStar) then
          match γv0 with
          | none => none
          | some γ =>
            let kOut := Expr.op (O := OO) CKAOp.ckaReceive (γ, tn0)
            let pOut := Expr.op (O := OO) CKAOp.prngUp (σ0, kOut.2)
            let rs := Expr.op (O := OO) CKAOp.fsInitReceiver pOut.2
            some (some (some kOut.1, pOut.1, rs))
        else
          some none
      | some ik =>
        let pOut := Expr.op (O := OO) CKAOp.prngUp (σ0, ik)
        let rs := Expr.op (O := OO) CKAOp.fsInitReceiver pOut.2
        let γv' :=
          match γv0 with
          | none => none
          | some γ => some (Expr.op (O := OO) CKAOp.ckaReceive (γ, tn0)).1
        some (some (γv', pOut.1, rs))

def ckaStartRecvC (mo : Mode) {Γ'}
    (hE : Expr OO Γ' ckaHsTy)
    (_ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (_pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat)
    (γvE : Expr OO Γ' (.opt (.base .γ)))
    (σE : Expr OO Γ' (.base .sig))
    (tnE : Expr OO Γ' (.base .t)) :
    Comp OO II Γ'
      (.prod (.opt (.opt (.prod (.opt (.base .γ)) (.prod (.base .sig) (.base .rs)))))
        ckaHsTy) :=
  rdsl do
    return (ckaStartRecvAnsE mo hE tE γvE σE tnE, hE)

def ckaFsSendC {Γ'}
    (hE : Expr OO Γ' ckaHsTy)
    (_ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (_pE : Expr OO Γ' .bool)
    (_tE : Expr OO Γ' .nat)
    (ssE : Expr OO Γ' (.base .ss))
    (hdrE : Expr OO Γ' hdrTy)
    (mE : Expr OO Γ' (.base .msg))
    (_pairE : Expr OO Γ' (.opt (.prod (.base .msg) (.base .msg)))) :
    Comp OO II Γ' (.prod (.opt (.prod (.base .ss) (.base .ct))) ckaHsTy) :=
  rdsl do
    return (some (Expr.op (O := OO) CKAOp.fsSend (ssE, hdrE, mE)), hE)

def ckaFsRecvC (B : ℕ) {Γ'}
    (hE : Expr OO Γ' ckaHsTy)
    (_ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (_pE : Expr OO Γ' .bool)
    (_tE : Expr OO Γ' .nat)
    (rsE : Expr OO Γ' (.base .rs))
    (hdrE : Expr OO Γ' hdrTy)
    (eE : Expr OO Γ' (.base .ct))
    (_recE : Expr OO Γ' (.opt cRecTy)) :
    Comp OO II Γ'
      (.prod (.opt (.opt (.prod (.base .rs) (.prod .nat (.base .msg))))) ckaHsTy) :=
  rdsl do
    return (some (Expr.op (O := OO) (CKAOp.fsReceive B) (rsE, hdrE, eE)), hE)

def ckaCommitC (Δcka : ℕ) (mo : Mode) {Γ'}
    (hE : Expr OO Γ' ckaHsTy)
    (_ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool)
    (oldE newE : Expr OO Γ' ckaVpTy) :
    Comp OO II Γ' (.prod (.opt ckaVpTy) ckaHsTy) :=
  rdsl do
    (h0, p0, old0, new0) ← return (hE, pE, oldE, newE)
    if (vpTcurNat old0 < vpTcurNat new0) && !(isSomeE (vpΓ old0)) then
      rOpt ← query (I := II) CKATag.receive p0
      match rOpt with
      | none => return (none, h0)
      | some _ =>
        if leN (nat (mo.tH + Δcka)) (vpTcurNat new0) then
          γOpt ← query (I := II) CKATag.corr p0
          match γOpt with
          | none => return (none, h0)
          | some γ' => return (some (vpSetΓ new0 (some γ')), h0)
        else
          return (some new0, h0)
    else
      return (some new0, h0)

def ckaRevealC {Γ'}
    (hE : Expr OO Γ' ckaHsTy)
    (_ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool)
    (vpE : Expr OO Γ' ckaVpTy) :
    Comp OO II Γ' (.prod (.opt psTy) ckaHsTy) :=
  rdsl do
    (h0, p0, vp0) ← return (hE, pE, vpE)
    match vpΓ vp0 with
    | none =>
      γOpt ← query (I := II) CKATag.corr p0
      match γOpt with
      | none => return (none, h0)
      | some γ =>
        return (some (realPartyE vp0 γ (vpRoot vp0) (vpVS vp0) (vpVR vp0)), h0)
    | some γ =>
      return (some (realPartyE vp0 γ (vpRoot vp0) (vpVS vp0) (vpVR vp0)), h0)

/-- Costed `HooksC` bundle for `redCKA`. -/
def hooksCKAC (B Δcka : ℕ) (mo : Mode) :
    HooksC OO II (.opt (.base .γ)) (.base .sig) (.base .ss) (.base .rs) ckaHsTy where
  startSend := ckaStartSendC Δcka mo
  startRecv := ckaStartRecvC mo
  fsSend := ckaFsSendC
  fsRecv := ckaFsRecvC B
  commit := ckaCommitC Δcka mo
  reveal := ckaRevealC

/-! ## Hook evaluation agreement -/

@[simp] theorem query_send_eval {Γ'} (pE : Expr OO Γ' .bool) (ρ : Env Γ') (P : Party)
    (hp : pE.eval ρ = partyEnc P) :
    (Comp.query (I := II) CKATag.send pE).eval ρ = CKA.sendQuery P := by
  unfold Comp.eval; dsimp only; rw [hp]; cases P <;> rfl

@[simp] theorem query_sendBad_eval {Γ'} (e : Expr OO Γ' (.prod .bool (.base .ccoins)))
    (ρ : Env Γ') (P : Party) (c : CCoins) (he : e.eval ρ = (partyEnc P, c)) :
    (Comp.query (I := II) CKATag.sendBad e).eval ρ = CKA.sendWithAdversaryCoinsQuery P c := by
  unfold Comp.eval; dsimp only; rw [he]; cases P <;> rfl

@[simp] theorem query_chall_eval {Γ'} (pE : Expr OO Γ' .bool) (ρ : Env Γ') (P : Party)
    (hp : pE.eval ρ = partyEnc P) :
    (Comp.query (I := II) CKATag.chall pE).eval ρ = CKA.challQuery P := by
  unfold Comp.eval; dsimp only; rw [hp]; cases P <;> rfl

@[simp] theorem query_receive_eval {Γ'} (pE : Expr OO Γ' .bool) (ρ : Env Γ') (P : Party)
    (hp : pE.eval ρ = partyEnc P) :
    (Comp.query (I := II) CKATag.receive pE).eval ρ = CKA.receiveQuery P := by
  unfold Comp.eval; dsimp only; rw [hp]; cases P <;> rfl

@[simp] theorem query_corr_eval {Γ'} (pE : Expr OO Γ' .bool) (ρ : Env Γ') (P : Party)
    (hp : pE.eval ρ = partyEnc P) :
    (Comp.query (I := II) CKATag.corr pE).eval ρ = CKA.corrQuery P := by
  unfold Comp.eval; dsimp only; rw [hp]; cases P <;> rfl

@[simp] theorem run_liftC_bind {α β : Type}
    (x : CKA.AdversaryComp Γ CCoins T I α)
    (k : α → HM (CKA.spec Γ CCoins T I) (CKAState T I) β)
    (h : CKAState T I) :
    (liftC x >>= k).run h = x >>= fun a => (k a).run h := by
  simp [liftC, StateT.run_bind, StateT.run_lift, bind_map_left]

@[simp] theorem run_lift_bind {α β : Type}
    (x : CKA.AdversaryComp Γ CCoins T I α)
    (k : α → HM (CKA.spec Γ CCoins T I) (CKAState T I) β)
    (h : CKAState T I) :
    (StateT.lift x >>= k).run h = x >>= fun a => (k a).run h :=
  run_liftC_bind x k h

private theorem caseOpt_eval {S' : Sig} {O' : Ops S'} {Γ' : List (Ty S')} {a b : Ty S'}
    (e : Expr O' Γ' (.opt a)) (n : Expr O' Γ' b) (s : Expr O' (a :: Γ') b) (ρ : Env Γ') :
    (Expr.caseOpt e n s).eval ρ =
      match e.eval ρ with
      | none => n.eval ρ
      | some x => s.eval (.cons x ρ) := rfl

@[simp] private theorem v0_eval_cons {S' : Sig} {O' : Ops S'} {Γ' : List (Ty S')} {a : Ty S'}
    (x : a.denote) (ρ : Env Γ') :
    (Expr.v0 (O := O')).eval (Env.cons x ρ) = x := rfl

theorem ckaStartSendC_eval [DecidableEq T] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hSend : ckaSend = cka.send)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (Δcka : ℕ) (mo : Mode)
    {Γ'} (hE : Expr OO Γ' ckaHsTy) (ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γvE : Expr OO Γ' (.opt (.base .γ))) (σE : Expr OO Γ' (.base .sig))
    (rE : Expr OO Γ' (.opt (.base .ccoins))) (ρ : Env Γ')
    (h : CKAState T I) (ctx : Ctx (Option Γ) T RSt SS RS M E) (P : Party)
    (hh : hE.eval ρ = ckaHsEnc h) (hp : pE.eval ρ = partyEnc P) :
    (ckaStartSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) Δcka mo hE ctxE pE tE γvE σE rE).eval ρ =
      Prod.map id ckaHsEnc <$>
        ((hooksCKA cka prng fs Δcka mo).startSend ctx P
          (tE.eval ρ) (γvE.eval ρ) (σE.eval ρ) (rE.eval ρ)).run h := by
  dsimp only [ckaStartSendC, hooksCKA]
  rw [eval_bind_ret]
  set t := tE.eval ρ
  set γv := γvE.eval ρ
  set σ := σE.eval ρ
  set r := rE.eval ρ
  have h0 : (Expr.pair hE (.pair pE (.pair tE (.pair γvE (.pair σE rE))))).eval ρ =
      (ckaHsEnc h, partyEnc P, t, γv, σ, r) := by
    simp [Expr.eval, hh, hp, t, γv, σ, r]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod ckaHsTy (.prod .bool (.prod .nat
      (.prod (.opt (.base CKASort.γ)) (.prod (.base CKASort.sig) (.opt (.base CKASort.ccoins)))))))
    (ckaHsEnc h, partyEnc P, t, γv, σ, r) ρ
  rw [eval_caseOpt]
  have hγv : (Expr.fst (.snd (.snd (.snd (Expr.v0 (O := OO)))))).eval ρ₁ = γv := rfl
  rw [hγv]
  rcases γv with _ | γ
  ·
    dsimp only
    have hCont (ans : Option (T × I)) :
        (Comp.caseOpt (O := OO) (I := II) .v0
          (.ret (.pair .none (.fst .v1)))
          (let T' : Expr OO _ (.base .t) := .fst .v0
           let Ik : Expr OO _ (.base .i) := .snd .v0
           let h_2 : Expr OO _ ckaHsTy := .fst .v2
           let p_2 : Expr OO _ .bool := .fst (.snd .v2)
           let t_2 : Expr OO _ .nat := .fst (.snd (.snd .v2))
           let h1 : Expr OO _ ckaHsTy := .tset h_2 t_2 (.some (.pair T' Ik))
           .ite (leN (.nat (mo.tH + Δcka)) t_2)
             (.bind (Comp.query (I := II) CKATag.corr p_2)
               (.caseOpt .v0
                 (.ret (.pair .none (.tset (.fst .v3) (.fst (.snd (.snd .v3)))
                   (.some (.pair (.fst .v1) (.snd .v1))))))
                 (let γ' : Expr OO _ (.base .γ) := .v0
                  let T'_2 : Expr OO _ (.base .t) := .fst .v2
                  let Ik_2 : Expr OO _ (.base .i) := .snd .v2
                  let h_4 : Expr OO _ ckaHsTy := .fst .v4
                  let t_4 : Expr OO _ .nat := .fst (.snd (.snd .v4))
                  let σ_4 : Expr OO _ (.base .sig) := .fst (.snd (.snd (.snd (.snd .v4))))
                  let h1_4 : Expr OO _ ckaHsTy := .tset h_4 t_4 (.some (.pair T'_2 Ik_2))
                  let pOut : Expr OO _ (.prod (.base .sig) (.base .k)) :=
                    Expr.op (O := OO) CKAOp.prngUp (.pair σ_4 Ik_2)
                  let ss : Expr OO _ (.base .ss) :=
                    Expr.op (O := OO) CKAOp.fsInitSender (.snd pOut)
                  .ret (.pair
                    (.some (.pair (.some γ') (.pair T'_2 (.pair (.fst pOut) ss))))
                    h1_4))))
             (let σ_2 : Expr OO _ (.base .sig) := .fst (.snd (.snd (.snd (.snd .v2))))
              let pOut : Expr OO _ (.prod (.base .sig) (.base .k)) :=
                Expr.op (O := OO) CKAOp.prngUp (.pair σ_2 Ik)
              let ss : Expr OO _ (.base .ss) :=
                Expr.op (O := OO) CKAOp.fsInitSender (.snd pOut)
              .ret (.pair
                (.some (.pair .none (.pair T' (.pair (.fst pOut) ss))))
                h1)))).eval
          (Env.cons (t := .opt (.prod (.base CKASort.t) (.base CKASort.i))) ans ρ₁) =
        Prod.map id ckaHsEnc <$>
          (match ans with
          | none => pure none
          | some (T', Ik) => do
            cacheC t (T', Ik)
            let p := prng.up σ Ik
            if mo.tH + Δcka ≤ t then do
              let γ? : Option Γ ← liftC (CKA.corrQuery P)
              match γ? with
              | none => pure none
              | some γ => pure (some (some γ, T', p.1, fs.initSender p.2))
            else pure (some (none, T', p.1, fs.initSender p.2))).run h := by
      dsimp only
      rcases ans with _ | ⟨T', Ik⟩
      · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v1]
      · simp only [eval_caseOpt, cacheC, StateT.run_bind, StateT.run_modify, pure_bind]
        set ρ₂ := Env.cons (t := .prod (.base CKASort.t) (.base CKASort.i)) (T', Ik)
          (Env.cons (t := .opt (.prod (.base CKASort.t) (.base CKASort.i))) (some (T', Ik)) ρ₁)
        change (Comp.ite _ _ _).eval ρ₂ = _
        rw [eval_ite]
        have hle : (leN (.nat (mo.tH + Δcka)) (.fst (.snd (.snd (Expr.v2 (O := OO)))))).eval ρ₂ =
            decide (mo.tH + Δcka ≤ t) := by
          rw [leN_eval]; rfl
        rw [hle]
        by_cases hfin : mo.tH + Δcka ≤ t
        · simp only [hfin, decide_true, ↓reduceIte, eval_bind, run_liftC_bind, map_bind]
          have hp2 : (Expr.fst (.snd (Expr.v2 (O := OO)))).eval ρ₂ = partyEnc P := rfl
          rw [query_corr_eval _ ρ₂ P hp2]
          refine bind_congr fun γ? => ?_
          rcases γ? with _ | γ'
          · simp only [eval_caseOpt, v0_eval_cons, eval_ret, pair_eval,
              StateT.run_pure, map_pure, Prod.map, id_eq]
            congr 2
            exact tset_eval_eq_update (.fst .v3) (.fst (.snd (.snd .v3)))
              (.some (.pair (.fst .v1) (.snd .v1)))
              (Env.cons (t := .opt (.base CKASort.γ)) none ρ₂)
          · simp only [eval_caseOpt, v0_eval_cons, eval_ret,
              StateT.run_pure, map_pure, Prod.map, id_eq]
            set ρ₃ := Env.cons (t := .base CKASort.γ) γ'
              (Env.cons (t := .opt (.base CKASort.γ)) (some γ') ρ₂)
            have hTset := tset_eval_eq_update (O' := OO) (.fst .v4) (.fst (.snd (.snd .v4)))
              (.some (.pair (.fst .v2) (.snd .v2))) ρ₃
            simp only [pair_eval, some_eval, hTset]
            simp [ρ₃, ρ₂, ρ₁, ckaOps, hPrngUp, hFsInitS, ckaHsEnc,
              Expr.eval, Expr.v0, Expr.v2, Expr.v4]
        · simp only [hfin, decide_false, Bool.false_eq_true, ↓reduceIte,
            eval_ret, StateT.run_pure, map_pure, Prod.map, id_eq]
          have hTset := tset_eval_eq_update (O' := OO) (.fst .v2) (.fst (.snd (.snd .v2)))
            (.some (.pair (.fst .v0) (.snd .v0))) ρ₂
          simp only [pair_eval, some_eval, hTset]
          simp [ρ₂, ρ₁, ckaOps, hPrngUp, hFsInitS, ckaHsEnc,
            Expr.eval, Expr.v0, Expr.v2]
    have hp1 : (Expr.fst (.snd (Expr.v0 (O := OO)))).eval ρ₁ = partyEnc P := rfl
    have hr : (Expr.snd (.snd (.snd (.snd (.snd (Expr.v0 (O := OO))))))).eval ρ₁ = r := rfl
    rw [eval_bind, eval_caseOpt, hr]
    rcases r with _ | c
    · rw [eval_ite]
      have htH : (Expr.eqN (.fst (.snd (.snd (Expr.v0 (O := OO))))) (.nat mo.tH)).eval ρ₁ =
          decide (t = mo.tH) := rfl
      rw [htH]
      by_cases hteq : t = mo.tH
      · rw [ite_eq_left (decide_eq_true hteq), ite_eq_left hteq]
        simp only [query_chall_eval _ ρ₁ P hp1, run_liftC_bind, map_bind]
        exact bind_congr hCont
      · rw [ite_eq_right (by simp [hteq]), ite_eq_right hteq]
        simp only [query_send_eval _ ρ₁ P hp1, run_liftC_bind, map_bind]
        exact bind_congr hCont
    · have hbad : (Expr.pair (.fst (.snd (Expr.v1 (O := OO)))) .v0).eval
          (Env.cons (t := .base CKASort.ccoins) c ρ₁) = (partyEnc P, c) := rfl
      simp only [query_sendBad_eval _ _ P c hbad, run_liftC_bind, map_bind]
      exact bind_congr hCont
  ·
    dsimp only
    set ρ₂ := Env.cons (t := .base CKASort.γ) γ ρ₁
    have hCoinsCont (coins : CCoins) :
        (Comp.ret (O := OO) (I := II)
          (.pair
            (.some (.pair (.some (.fst (Expr.op (O := OO) CKAOp.ckaSend (.pair .v1 .v0))))
              (.pair (.fst (.snd (Expr.op (O := OO) CKAOp.ckaSend (.pair .v1 .v0))))
                (.pair
                  (.fst (Expr.op (O := OO) CKAOp.prngUp
                    (.pair (.fst (.snd (.snd (.snd (.snd .v2)))))
                      (.snd (.snd (Expr.op (O := OO) CKAOp.ckaSend (.pair .v1 .v0)))))))
                  (Expr.op (O := OO) CKAOp.fsInitSender
                    (.snd (Expr.op (O := OO) CKAOp.prngUp
                      (.pair (.fst (.snd (.snd (.snd (.snd .v2)))))
                        (.snd (.snd (Expr.op (O := OO) CKAOp.ckaSend (.pair .v1 .v0))))))))))))
            (.tset (.fst .v2) (.fst (.snd (.snd .v2)))
              (.some (.pair
                (.fst (.snd (Expr.op (O := OO) CKAOp.ckaSend (.pair .v1 .v0))))
                (.snd (.snd (Expr.op (O := OO) CKAOp.ckaSend (.pair .v1 .v0))))))))).eval
          (Env.cons (t := .base CKASort.ccoins) coins ρ₂) =
        Prod.map id ckaHsEnc <$>
          (do
            let c := cka.send γ coins
            cacheC t (c.2.1, c.2.2)
            let p := prng.up σ c.2.2
            pure (some (some c.1, c.2.1, p.1, fs.initSender p.2))).run h := by
      dsimp only
      simp only [cacheC, StateT.run_bind, StateT.run_modify, StateT.run_pure,
        pure_bind, map_pure, Prod.map, id_eq]
      set ρ₃ := Env.cons (t := .base CKASort.ccoins) coins ρ₂
      change (Comp.ret _).eval ρ₃ = _
      have hTset := tset_eval_eq_update (O' := OO) (.fst .v2) (.fst (.snd (.snd .v2)))
        (.some (.pair (.fst (.snd (Expr.op (O := OO) CKAOp.ckaSend (.pair .v1 .v0))))
          (.snd (.snd (Expr.op (O := OO) CKAOp.ckaSend (.pair .v1 .v0)))))) ρ₃
      simp only [eval_ret, pair_eval, some_eval, hTset]
      simp [ρ₃, ρ₂, ρ₁, ckaOps, hSend, hPrngUp, hFsInitS, ckaHsEnc,
        Expr.eval, Expr.v0, Expr.v1, Expr.v2]
    have hr2 : (Expr.snd (.snd (.snd (.snd (.snd (Expr.v1 (O := OO))))))).eval ρ₂ = r := rfl
    rw [eval_bind, eval_caseOpt, hr2]
    rcases r with _ | c
    · have hSamp : (Comp.sample (O := OO) (I := II) CKASamp.ccoins .unit).eval ρ₂ =
          sampleT CCoins := by
        simp only [Comp.eval, ckaIface, ckaSamplers, hSampCCoins, sampleT]
        exact liftP_eq_liftM II (fun _ => rfl) ($ᵗ CCoins)
      simp only [hSamp, run_lift_bind, map_bind]
      exact bind_congr hCoinsCont
    · simp only [eval_ret, v0_eval_cons, pure_bind]
      exact hCoinsCont c

theorem ckaStartRecvC_eval [DecidableEq T] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hRecv : ckaReceive = cka.receive)
    (hPrngUp : prngUp = prng.up)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (heqT : eqT = (· == ·))
    (Δcka : ℕ) (mo : Mode)
    {Γ'} (hE : Expr OO Γ' ckaHsTy) (ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γvE : Expr OO Γ' (.opt (.base .γ))) (σE : Expr OO Γ' (.base .sig))
    (tnE : Expr OO Γ' (.base .t)) (ρ : Env Γ')
    (h : CKAState T I) (ctx : Ctx (Option Γ) T RSt SS RS M E) (P : Party)
    (hh : hE.eval ρ = ckaHsEnc h) :
    (ckaStartRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) mo hE ctxE pE tE γvE σE tnE).eval ρ =
      Prod.map id ckaHsEnc <$>
        ((hooksCKA cka prng fs Δcka mo).startRecv ctx P
          (tE.eval ρ) (γvE.eval ρ) (σE.eval ρ) (tnE.eval ρ)).run h := by
  dsimp only [ckaStartRecvC, ckaStartRecvAnsE, hooksCKA]
  simp only [eval_ret, pair_eval, letE_eval, hh, StateT.run_bind, StateT.run_get, pure_bind]
  set t : ℕ := tE.eval ρ
  set γv : Option Γ := γvE.eval ρ
  set σ : RSt := σE.eval ρ
  set Tn : T := tnE.eval ρ
  set ρ₁ := Env.cons
    (t := .prod ckaHsTy (.prod .nat (.prod (.opt (.base CKASort.γ))
      (.prod (.base CKASort.sig) (.base CKASort.t)))))
    (ckaHsEnc h, t, γv, σ, Tn) ρ
  change (pure ((Expr.caseOpt _ _ _).eval ρ₁, ckaHsEnc h) :
      TComp (CKA.spec Γ CCoins T I) _) = _
  have hHonest :
      (Expr.caseOpt (.tget (.fst (Expr.v0 (O := OO))) (.fst (.snd .v0))) .none
        (.ite (Expr.op (O := OO) CKAOp.eqT (.pair (.fst .v0) (.snd (.snd (.snd (.snd .v1))))))
          (.some (.snd .v0)) .none)).eval ρ₁ =
      (match h.cache t with
        | some (Tc, Ik) => if Tc = Tn then some Ik else none
        | none => none) := by
    have hGet : (Expr.tget (.fst (Expr.v0 (O := OO))) (.fst (.snd .v0))).eval ρ₁ = h.cache t := rfl
    rw [caseOpt_eval, hGet]
    rcases h.cache t with _ | ⟨Tc, Ik⟩
    · rfl
    · simp only [ρ₁, ckaOps, heqT, Expr.eval, Expr.v0, Expr.v1, BEq.beq]
      by_cases hEq : Tc = Tn <;> simp [hEq]
  rw [caseOpt_eval, hHonest]
  rcases h.cache t with _ | ⟨Tc, Ik⟩
  · dsimp only
    rw [ite_eval]
    have hCond :
        (Expr.and (.bool mo.auth)
          (.eqN (.fst (.snd (Expr.v0 (O := OO)))) (.nat mo.tStar))).eval ρ₁ =
        (mo.auth && decide (t = mo.tStar)) := rfl
    rw [hCond]
    by_cases hAuthB : (mo.auth && decide (t = mo.tStar)) = true
    · simp only [hAuthB, ↓reduceIte]
      rcases γv with _ | γ
      · simp only [StateT.run_pure, map_pure]; rfl
      · simp only [StateT.run_pure, map_pure, Prod.map, id_eq]
        congr 1; congr 1
        simp [ρ₁, ckaOps, hRecv, hPrngUp, hFsInitR, Expr.eval, Expr.v0, Expr.v1]
    · simp only [hAuthB]; rfl
  · dsimp only
    by_cases hEq : Tc = Tn
    · simp only [hEq, ↓reduceIte]
      rcases γv with _ | γ <;>
      · simp only [StateT.run_pure, map_pure, Prod.map, id_eq]
        congr 1; congr 1
        simp [ρ₁, ckaOps, hRecv, hPrngUp, hFsInitR, Expr.eval, Expr.v0, Expr.v1, Expr.v2]
    · simp only [hEq, ↓reduceIte]
      rw [ite_eval]
      have hCond :
          (Expr.and (.bool mo.auth)
            (.eqN (.fst (.snd (Expr.v0 (O := OO)))) (.nat mo.tStar))).eval ρ₁ =
          (mo.auth && decide (t = mo.tStar)) := rfl
      rw [hCond]
      by_cases hAuthB : (mo.auth && decide (t = mo.tStar)) = true
      · simp only [hAuthB, ↓reduceIte]
        rcases γv with _ | γ
        · simp only [StateT.run_pure, map_pure]; rfl
        · simp only [StateT.run_pure, map_pure, Prod.map, id_eq]
          congr 1; congr 1
          simp [ρ₁, ckaOps, hRecv, hPrngUp, hFsInitR, Expr.eval, Expr.v0, Expr.v1]
      · simp only [hAuthB]; rfl

theorem ckaCommitC_eval [DecidableEq T] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (mo : Mode)
    {Γ'} (hE : Expr OO Γ' ckaHsTy) (ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool) (oldE newE : Expr OO Γ' ckaVpTy) (ρ : Env Γ')
    (h : CKAState T I) (ctx : Ctx (Option Γ) T RSt SS RS M E) (P : Party)
    (old new : VP (Option Γ) T RSt SS RS)
    (hh : hE.eval ρ = ckaHsEnc h) (hp : pE.eval ρ = partyEnc P)
    (hold : oldE.eval ρ = ckaVpEnc old) (hnew : newE.eval ρ = ckaVpEnc new) :
    (ckaCommitC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) Δcka mo hE ctxE pE oldE newE).eval ρ =
      Prod.map (Option.map ckaVpEnc) ckaHsEnc <$>
        ((hooksCKA cka prng fs Δcka mo).commit ctx P old new).run h := by
  unfold ckaCommitC hooksCKA
  dsimp only
  rw [eval_bind_ret]
  have h0 : (Expr.pair hE (.pair pE (.pair oldE newE))).eval ρ =
      (ckaHsEnc h, partyEnc P, ckaVpEnc old, ckaVpEnc new) := by
    simp [Expr.eval, hh, hp, hold, hnew]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod ckaHsTy (.prod .bool (.prod ckaVpTy ckaVpTy)))
    (ckaHsEnc h, partyEnc P, ckaVpEnc old, ckaVpEnc new) ρ
  rw [eval_ite]
  have hCond :
      (Expr.and (.lt (vpTcurNat (.fst (.snd (.snd (Expr.v0 (O := OO))))))
          (vpTcurNat (.snd (.snd (.snd .v0)))))
        (.not (isSomeE (vpΓ (.fst (.snd (.snd .v0))))))).eval ρ₁ =
      (decide (old.tcur < new.tcur) && old.γ.isNone) := by
    rcases old with ⟨id_o, root_o, vS_o, vR_o, _ | γ_o, Tcur_o, tcur_o⟩ <;>
      simp [ρ₁, isSomeE, vpTcurNat, vpΓ, ckaVpEnc, vpTblEnc, vpEnc, Expr.eval, Expr.v0]
  rw [hCond]
  by_cases hc : (decide (old.tcur < new.tcur) && old.γ.isNone) = true
  · simp only [hc, ↓reduceIte, eval_bind, run_liftC_bind, map_bind]
    rw [query_receive_eval _ ρ₁ P rfl]
    refine bind_congr fun rcvRes => ?_
    rcases rcvRes with _ | ⟨⟩
    · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v1]
    · simp only [eval_caseOpt]
      set ρ₂ := Env.cons (t := .unit) ()
        (Env.cons (t := .opt .unit) (some ()) ρ₁)
      change (Comp.ite _ _ _).eval ρ₂ = _
      rw [eval_ite]
      have hle : (leN (.nat (mo.tH + Δcka))
          (vpTcurNat (.snd (.snd (.snd (Expr.v2 (O := OO))))))).eval ρ₂ =
          decide (mo.tH + Δcka ≤ new.tcur) := by
        rw [leN_eval]; rfl
      rw [hle]
      by_cases hfin : mo.tH + Δcka ≤ new.tcur
      · simp only [hfin, decide_true, ↓reduceIte, eval_bind, run_liftC_bind, map_bind]
        rw [query_corr_eval _ ρ₂ P rfl]
        refine bind_congr fun γ? => ?_
        rcases γ? with _ | γ'
        · simp [ρ₂, ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v3]
        · simp only [eval_caseOpt, v0_eval_cons, eval_ret,
            StateT.run_pure, map_pure, Prod.map, Option.map_some]
          set ρ₃ := Env.cons (t := .base CKASort.γ) γ'
            (Env.cons (t := .opt (.base CKASort.γ)) (some γ') ρ₂)
          have hSetΓ := vpSetΓ_eval (O' := OO)
            (.snd (.snd (.snd (Expr.v4 (O := OO))))) (.some .v0) ρ₃ new rfl
          simp only [pair_eval, some_eval, hSetΓ]
          rfl
      · simp [ρ₂, ρ₁, hfin, eval_ret, StateT.run_pure, Prod.map, Expr.eval, Expr.v2]
  · simp [ρ₁, hc, eval_ret, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]

theorem ckaRevealC_eval [DecidableEq T] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (mo : Mode)
    {Γ'} (hE : Expr OO Γ' ckaHsTy) (ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool) (vpE : Expr OO Γ' ckaVpTy) (ρ : Env Γ')
    (h : CKAState T I) (ctx : Ctx (Option Γ) T RSt SS RS M E) (P : Party)
    (vp : VP (Option Γ) T RSt SS RS)
    (hh : hE.eval ρ = ckaHsEnc h) (hp : pE.eval ρ = partyEnc P)
    (hvp : vpE.eval ρ = ckaVpEnc vp) :
    (ckaRevealC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) hE ctxE pE vpE).eval ρ =
      Prod.map (Option.map ckaPsEnc) ckaHsEnc <$>
        ((hooksCKA cka prng fs Δcka mo).reveal ctx P vp).run h := by
  unfold ckaRevealC hooksCKA
  dsimp only
  rw [eval_bind_ret]
  have h0 : (Expr.pair hE (.pair pE vpE)).eval ρ =
      (ckaHsEnc h, partyEnc P, ckaVpEnc vp) := by
    simp [Expr.eval, hh, hp, hvp]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod ckaHsTy (.prod .bool ckaVpTy))
    (ckaHsEnc h, partyEnc P, ckaVpEnc vp) ρ
  rw [eval_caseOpt]
  have hγ : (vpΓ (.snd (.snd (Expr.v0 (O := OO))))).eval ρ₁ = vp.γ := rfl
  rw [hγ]
  rcases vp.γ with _ | γ
  · simp only [eval_bind, run_liftC_bind, map_bind]
    rw [query_corr_eval _ ρ₁ P rfl]
    refine bind_congr fun γ? => ?_
    rcases γ? with _ | γ'
    · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v1]
    · simp only [eval_caseOpt, v0_eval_cons, eval_ret,
        StateT.run_pure, map_pure, Prod.map, Option.map_some]
      set ρ₂ := Env.cons (t := .base CKASort.γ) γ'
        (Env.cons (t := .opt (.base CKASort.γ)) (some γ') ρ₁)
      have hReal := realPartyE_eval (O' := OO)
        (.snd (.snd .v2)) .v0 (vpRoot (.snd (.snd .v2)))
        (vpVS (.snd (.snd .v2))) (vpVR (.snd (.snd .v2))) ρ₂ vp rfl
      simp only [pair_eval, some_eval, hReal]
      rfl
  · simp only [pure_bind, StateT.run_pure, map_pure, Prod.map, Option.map_some]
    set ρ₂ := Env.cons (t := .base CKASort.γ) γ ρ₁
    change (Comp.ret _).eval ρ₂ = _
    have hReal := realPartyE_eval (O' := OO)
      (.snd (.snd .v1)) .v0 (vpRoot (.snd (.snd .v1)))
      (vpVS (.snd (.snd .v1))) (vpVR (.snd (.snd .v1))) ρ₂ vp rfl
    simp only [eval_ret, pair_eval, some_eval, hReal]
    rfl

/-! ## Costed CKA reductions -/

def initCKAEStateC (mo : Mode) {Γ'} (bE : Expr OO Γ' .bool) : Comp OO II Γ' ckaEsTy :=
  rdsl do
    b0 ← return bE
    kr ← sample (I := II) CKASamp.kr ()
    (γA, γB) ←
      if bool mo.tL.isNone then
        kc ← sample (I := II) CKASamp.kc ()
        return (some (Expr.op (O := OO) CKAOp.ckaInitA kc),
                some (Expr.op (O := OO) CKAOp.ckaInitB kc))
      else
        return (none, none)
    let out :=
      Expr.op (O := OO) CKAOp.prngUp
        (Expr.op (O := OO) CKAOp.prngInit kr, Expr.op (O := OO) CKAOp.lamI ())
    let parties :=
      mkPartiesE γA γB out.1
        (Expr.op (O := OO) CKAOp.fsInitSender out.2)
        (Expr.op (O := OO) CKAOp.fsInitReceiver out.2)
    let g0 := cGsInitE parties.1 parties.2 b0
    let h0 := tconst none
    return (esMk g0 h0 false)

def initCKARaw [SampleableType KR] [SampleableType KC]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (mo : Mode) (b : Bool) :
    CKA.AdversaryComp Γ CCoins T I
      (EState (VP (Option Γ) T RSt SS RS) M (Header T × E) (CKAState T I)) :=
  sampleT KR >>= fun kr =>
  (match mo.tL with
    | none => (fun kc => (some (cka.initA kc), some (cka.initB kc))) <$> sampleT KC
    | some _ => pure (none, none)) >>= fun γAB =>
  let out := prng.up (prng.init kr) lam
  let (vA, vB) := mkParties (T := T) γAB.1 γAB.2 out.1 (fs.initSender out.2) (fs.initReceiver out.2)
  pure { g := { st := fun | .A => vA | .B => vB, b := b }, h := {} }

theorem initCKAEStateC_eval [SampleableType KR] [SampleableType KC]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hInitA : ckaInitA = cka.initA)
    (hInitB : ckaInitB = cka.initB)
    (hPrngInit : prngInit = prng.init)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hSampKR : sampKR = ($ᵗ KR : ProbComp KR))
    (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (mo : Mode) {Γ'} (bE : Expr OO Γ' .bool) (ρ : Env Γ') :
    (initCKAEStateC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) mo bE).eval ρ =
      esEnc ckaVpEnc ckaHsEnc <$> initCKARaw cka prng fs lam mo (bE.eval ρ) := by
  unfold initCKAEStateC initCKARaw
  rw [eval_bind_ret]
  set b := bE.eval ρ
  set ρ₁ := Env.cons (t := .bool) b ρ
  rw [eval_bind, map_bind]
  have hKR : (Comp.sample (O := OO) (I := II) CKASamp.kr .unit).eval ρ₁ = sampleT KR := by
    simp only [Comp.eval, ckaIface, ckaSamplers, hSampKR, sampleT]
    exact liftP_eq_liftM II (fun _ => rfl) ($ᵗ KR)
  rw [hKR]
  refine bind_congr fun kr => ?_
  set ρ₂ := Env.cons (t := .base CKASort.kr) kr ρ₁
  rw [eval_bind, eval_ite, map_bind]
  have hBranch :
      (if (Expr.bool (O := OO) mo.tL.isNone).eval ρ₂ then
        (Comp.bind (Comp.sample (O := OO) (I := II) CKASamp.kc .unit)
          (.ret (.pair
            (.some (Expr.op (O := OO) CKAOp.ckaInitA .v0))
            (.some (Expr.op (O := OO) CKAOp.ckaInitB .v0))))).eval ρ₂
       else (Comp.ret (O := OO) (I := II) (.pair .none .none)).eval ρ₂) =
      (match mo.tL with
        | none => (fun kc => (some (cka.initA kc), some (cka.initB kc))) <$> sampleT KC
        | some _ => pure (none, none)) := by
    rcases mo.tL with _ | l
    · simp only [Option.isNone, ↓reduceIte, eval_bind, eval_ret, Expr.eval, ckaOps, hInitA, hInitB,
        map_eq_bind_pure_comp, Function.comp_def]
      have hKC : (Comp.sample (O := OO) (I := II) CKASamp.kc .unit).eval ρ₂ = sampleT KC := by
        simp only [Comp.eval, ckaIface, ckaSamplers, hSampKC, sampleT]
        exact liftP_eq_liftM II (fun _ => rfl) ($ᵗ KC)
      rw [hKC]; rfl
    · rfl
  rw [hBranch]
  refine bind_congr fun ⟨γA, γB⟩ => ?_
  set ρ₃ := Env.cons (t := .prod (.opt (.base CKASort.γ)) (.opt (.base CKASort.γ))) (γA, γB) ρ₂
  change (Comp.ret _).eval ρ₃ = _
  rw [eval_ret, map_pure]
  have hMkP := mkPartiesE_eval (O' := OO)
    (.fst .v0) (.snd .v0)
    (.fst (Expr.op (O := OO) CKAOp.prngUp
      (.pair (Expr.op (O := OO) CKAOp.prngInit .v1) (Expr.op (O := OO) CKAOp.lamI .unit))))
    (Expr.op (O := OO) CKAOp.fsInitSender
      (.snd (Expr.op (O := OO) CKAOp.prngUp
        (.pair (Expr.op (O := OO) CKAOp.prngInit .v1) (Expr.op (O := OO) CKAOp.lamI .unit)))))
    (Expr.op (O := OO) CKAOp.fsInitReceiver
      (.snd (Expr.op (O := OO) CKAOp.prngUp
        (.pair (Expr.op (O := OO) CKAOp.prngInit .v1) (Expr.op (O := OO) CKAOp.lamI .unit)))))
    ρ₃
  set out := prng.up (prng.init kr) lam
  set pAB := mkParties (T := T) γA γB out.1 (fs.initSender out.2) (fs.initReceiver out.2)
  have hMkP' :
      (mkPartiesE (O' := OO) (.fst .v0) (.snd .v0)
        (.fst (Expr.op (O := OO) CKAOp.prngUp
          (.pair (Expr.op (O := OO) CKAOp.prngInit .v1) (Expr.op (O := OO) CKAOp.lamI .unit))))
        (Expr.op (O := OO) CKAOp.fsInitSender
          (.snd (Expr.op (O := OO) CKAOp.prngUp
            (.pair (Expr.op (O := OO) CKAOp.prngInit .v1) (Expr.op (O := OO) CKAOp.lamI .unit)))))
        (Expr.op (O := OO) CKAOp.fsInitReceiver
          (.snd (Expr.op (O := OO) CKAOp.prngUp
            (.pair (Expr.op (O := OO) CKAOp.prngInit .v1)
              (Expr.op (O := OO) CKAOp.lamI .unit)))))).eval
        ρ₃ = (ckaVpEnc pAB.1, ckaVpEnc pAB.2) := by
    simpa [ρ₃, ρ₂, ρ₁, ckaOps, hPrngInit, hPrngUp, hFsInitS, hFsInitR, out, pAB, Prod.map,
      Expr.eval, Expr.v0, Expr.v1] using hMkP
  have hGs := cGsInitE_eval ckaVpEnc (O' := OO)
    (.fst (mkPartiesE (.fst .v0) (.snd .v0)
      (.fst (Expr.op (O := OO) CKAOp.prngUp
        (.pair (Expr.op (O := OO) CKAOp.prngInit .v1) (Expr.op (O := OO) CKAOp.lamI .unit))))
      (Expr.op (O := OO) CKAOp.fsInitSender
        (.snd (Expr.op (O := OO) CKAOp.prngUp
          (.pair (Expr.op (O := OO) CKAOp.prngInit .v1) (Expr.op (O := OO) CKAOp.lamI .unit)))))
      (Expr.op (O := OO) CKAOp.fsInitReceiver
        (.snd (Expr.op (O := OO) CKAOp.prngUp
          (.pair (Expr.op (O := OO) CKAOp.prngInit .v1) (Expr.op (O := OO) CKAOp.lamI .unit)))))))
    (.snd (mkPartiesE (.fst .v0) (.snd .v0)
      (.fst (Expr.op (O := OO) CKAOp.prngUp
        (.pair (Expr.op (O := OO) CKAOp.prngInit .v1) (Expr.op (O := OO) CKAOp.lamI .unit))))
      (Expr.op (O := OO) CKAOp.fsInitSender
        (.snd (Expr.op (O := OO) CKAOp.prngUp
          (.pair (Expr.op (O := OO) CKAOp.prngInit .v1) (Expr.op (O := OO) CKAOp.lamI .unit)))))
      (Expr.op (O := OO) CKAOp.fsInitReceiver
        (.snd (Expr.op (O := OO) CKAOp.prngUp
          (.pair (Expr.op (O := OO) CKAOp.prngInit .v1) (Expr.op (O := OO) CKAOp.lamI .unit)))))))
    .v2 ρ₃ pAB.1 pAB.2
    (by simp [Expr.eval, hMkP']) (by simp [Expr.eval, hMkP'])
  simp only [esMk, pair_eval, hGs]
  rfl

theorem initCKARaw_inv [SampleableType KR] [SampleableType KC]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (mo : Mode) (b : Bool)
    {L B qAdv : ℕ} (hqB : qAdv ≤ B) (hB1 : B + 1 ≤ L) (hBB : B * B ≤ L * L) :
    ∀ es₀ ∈ support (initCKARaw cka prng fs lam mo b),
      SMEngineInv L B qAdv es₀.g ∧ es₀.g.b = b := by
  intro es₀ hmem
  unfold initCKARaw at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨kr, _, hmem⟩ := hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨⟨γA, γB⟩, _, hmem⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff] at hmem
  subst hmem
  exact ⟨(SMEngineInv.init _ b hB1 hBB).mono hqB, rfl⟩

theorem runCKA_eq_bind_initCKARaw
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (Δcka qep : ℕ) (mo : Mode) (b : Bool)
    (A : SchemeAdversary Γ T RSt SS RS M CCoins E) :
    runCKA cka prng fs lam Δcka qep mo b A =
      (do
        let es₀ ← initCKARaw cka prng fs lam mo b
        let res ←
          (simulateQ
            (implE (hooksCKA cka prng fs Δcka mo) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy)
            A).run es₀
        return some res) := by
  unfold runCKA engRun initCKA initCKARaw
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  refine bind_congr fun kr => ?_
  rcases mo.tL with _ | l
  · simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind,
      bind_map_left]; rfl
  · simp only [StateT.run_pure, pure_bind]; rfl

/-- Costed `redCKAAuth` reduction (ACD19 Lemma 9) over `ckaOps`, `ckaIface`, and `ckaSMCodec`. -/
def redCKAAuthProg (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (t : ℕ) :
    CostedReduction OO II
      (SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (ckaSMCodec KC Γ CCoins T I KR RSt K SS RS M E)
      .unit .unit .bool .bool where
  σ := ckaEsTy
  init := rdsl [_] do
    es ← initCKAEStateC (raw ⟨true, tL, t⟩) false
    return ((), es)
  handle := rdsl [es, q] do
    implEC (raw (hooksCKAC B Δcka ⟨true, tL, t⟩)) L (raw (2 + Δcka)) qep maxSkip
      (raw (modeCfgEC OO ⟨true, tL, t⟩)) (raw (⟨true, tL, t⟩ : Mode).policy) es q
  finish := rdsl [es, _] do
    return (authOutE L (raw (2 + Δcka)) (raw (⟨true, tL, t⟩ : Mode).policy) es)

def ckaStartRecvBucketAnsE (Δcka : ℕ) (tL : Option ℕ) {Γ'}
    (hE : Expr OO Γ' ckaHsTy)
    (tE : Expr OO Γ' .nat)
    (γvE : Expr OO Γ' (.opt (.base .γ)))
    (σE : Expr OO Γ' (.base .sig))
    (tnE : Expr OO Γ' (.base .t)) :
    Expr OO Γ'
      (.opt (.opt (.prod (.opt (.base .γ)) (.prod (.base .sig) (.base .rs))))) :=
  rdslExpr =>
    letE (hE, tE, γvE, σE, tnE) fun (h0, t0, γv0, σ0, tn0) =>
      let honest :=
        match tget h0 t0 with
        | none => none
        | some (tCached, ikCached) =>
          if Expr.op (O := OO) CKAOp.eqT (tCached, tn0) then some ikCached else none
      match honest with
      | none =>
        if validGuessE (raw (2 + Δcka)) (optNatLit (raw tL)) t0 then
          match γv0 with
          | none => none
          | some γ =>
            let kOut := Expr.op (O := OO) CKAOp.ckaReceive (γ, tn0)
            let pOut := Expr.op (O := OO) CKAOp.prngUp (σ0, kOut.2)
            let rs := Expr.op (O := OO) CKAOp.fsInitReceiver pOut.2
            some (some (some kOut.1, pOut.1, rs))
        else
          some none
      | some ik =>
        let pOut := Expr.op (O := OO) CKAOp.prngUp (σ0, ik)
        let rs := Expr.op (O := OO) CKAOp.fsInitReceiver pOut.2
        let γv' :=
          match γv0 with
          | none => none
          | some γ => some (Expr.op (O := OO) CKAOp.ckaReceive (γ, tn0)).1
        some (some (γv', pOut.1, rs))

def hooksCKABucketC (B Δcka : ℕ) (tL : Option ℕ) :
    HooksC OO II (.opt (.base .γ)) (.base .sig) (.base .ss) (.base .rs) ckaHsTy where
  startSend := ckaStartSendC Δcka ⟨true, tL, 0⟩
  startRecv hE _ctxE _pE tE γvE σE tnE := rdsl do
    return (ckaStartRecvBucketAnsE Δcka tL hE tE γvE σE tnE, hE)
  fsSend := ckaFsSendC
  fsRecv := ckaFsRecvC B
  commit := ckaCommitC Δcka ⟨true, tL, 0⟩
  reveal := ckaRevealC

def bucketAuthCfgEC (Δcka : ℕ) (tL : Option ℕ) : ConfigEC OO where
  deliverWin := false
  injectFullE {_} t' := validGuessE (2 + Δcka) (optNatLit tL) t'
  challOKE {_} _ := .bool false
  challMsgE {_} _ b m0 m1 := .ite b m1 m0

@[reducible] def ckaBucketEsTy : Ty S := .prod ckaEsTy (.opt .nat)

/-- Stage-2 `canon`-bucket `redCKAAuth` reduction at leak-epoch bucket `tL`. -/
def redCKAAuthBucketProg (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) :
    CostedReduction OO II
      (SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (ckaSMCodec KC Γ CCoins T I KR RSt K SS RS M E)
      .unit .unit .bool .bool where
  σ := ckaBucketEsTy
  init := rdsl [_] do
    es ← initCKAEStateC (raw ⟨true, tL, 0⟩) false
    return ((), (es, none))
  handle := rdsl [st, q] do
    (es0, winEp0, q0) ← return (st.1, st.2, q)
    match q0 with
    | .inl (.inl (.inl (.inl x))) =>
      (p0, m0, r0) ← return x
      if orE (esAbort es0) (cGsWin (esG es0)) then
        return (inl (inl (inl (inl none))), (es0, winEp0))
      else
        match cEpMgmtE (raw (2 + Δcka)) (raw qep) (esG es0) p0 (isSomeE r0) with
        | none => return (inl (inl (inl (inl none))), (es0, winEp0))
        | some s1 =>
          (res, h') ← vSendC (raw (hooksCKABucketC B Δcka tL)) (esH es0) s1 p0 (pGet (cGsSt s1) p0) m0 none r0
          match res with
          | none => return (inl (inl (inl (inl none))), (esMk (esG es0) h' true, winEp0))
          | some (st', ct) =>
            let recE := ((p0, pGet (cGsEpoch s1) p0, pGet (cGsIdx s1) p0 + 1), m0, ct)
            let g' := cRecordE (raw L) (raw (2 + Δcka)) s1 p0 st' recE false
            return (inl (inl (inl (inl (some ct)))), (esMk g' h' (esAbort es0), winEp0))
    | .inl (.inl (.inl (.inr _))) =>
      return (inl (inl (inl (inr none))), (es0, winEp0))
    | .inl (.inl (.inr x)) =>
      (out, es') ← deliverEC (raw (hooksCKABucketC B Δcka tL)) L maxSkip
        (raw (bucketAuthCfgEC Δcka tL)) es0 x
      return (inl (inl (inr out)), (es', winEp0))
    | .inl (.inr x) =>
      let wasWin := cGsWin (esG es0)
      (out, es') ← injectEC (raw (hooksCKABucketC B Δcka tL)) L (raw (2 + Δcka)) qep
        (raw (bucketAuthCfgEC Δcka tL)) es0 x
      let winEp' := if !wasWin && cGsWin (esG es') then some x.2.1.1 else winEp0
      return (inl (inr out), (es', winEp'))
    | .inr p0 =>
      let s0 := esG es0
      if orE (esAbort es0) (orE (cGsWin s0) (!(cCorrAllowedE (raw L) s0 p0))) then
        return (inr none, (es0, winEp0))
      else
        let s1 := cAfterCorrE (raw L) s0 p0
        (res, h') ← ckaRevealC (esH es0) s0 p0 (pGet (cGsSt s0) p0)
        match res with
        | none => return (inr none, (esMk s0 h' true, winEp0))
        | some stOut =>
          return (inr (some stOut), (esMk s1 h' (esAbort es0), winEp0))
  finish := rdsl [st, _] do
    (es0, winEp0) ← return (st.1, st.2)
    match winEp0 with
    | none => return false
    | some tWin =>
      return ((!(esAbort es0) && cGsWin (esG es0)) &&
        cAuthOKE (raw L) (raw (2 + Δcka)) (optNatLit (raw tL)) tWin (esG es0))

/-- Costed `redCKAPriv` reduction (ACD19 Lemma 13) over `ckaOps`, `ckaIface`, and `ckaSMCodec`. -/
def redCKAPrivProg (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (t : ℕ) :
    CostedReduction OO II
      (SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (ckaSMCodec KC Γ CCoins T I KR RSt K SS RS M E)
      .unit .unit .bool .bool where
  σ := ckaEsTy
  init := rdsl [_] do
    b ← sample (I := II) CKASamp.bit ()
    es ← initCKAEStateC (raw ⟨false, tL, t⟩) b
    return ((), es)
  handle := rdsl [es, q] do
    implEC (raw (hooksCKAC B Δcka ⟨false, tL, t⟩)) L (raw (2 + Δcka)) qep maxSkip
      (raw (modeCfgEC OO ⟨false, tL, t⟩)) (raw (⟨false, tL, t⟩ : Mode).policy) es q
  finish := rdsl [es, guess] do
    privOutC L (raw (2 + Δcka)) (raw (⟨false, tL, t⟩ : Mode).policy)
      (raw (rdsl do sample (I := II) CKASamp.bit ())) (cGsB (esG es)) guess es

@[reducible] def ckaUHsTy : Ty S := .prod ckaHsTy (.opt (.base .k))

@[reducible] def ckaUEsTy : Ty S := esTy ckaVpTy ckaUHsTy

def ckaStartSendUC (Δcka : ℕ) (mo : Mode) {Γ'}
    (hE : Expr OO Γ' ckaUHsTy)
    (_ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat)
    (γvE : Expr OO Γ' (.opt (.base .γ)))
    (σE : Expr OO Γ' (.base .sig))
    (rE : Expr OO Γ' (.opt (.base .ccoins))) :
    Comp OO II Γ'
      (.prod (.opt (.prod (.opt (.base .γ)) (.prod (.base .t) (.prod (.base .sig) (.base .ss)))))
        ckaUHsTy) :=
  rdsl do
    (hPair, p0, t0, γv0, σ0, r0) ← return (hE, pE, tE, γvE, σE, rE)
    let h0 := hPair.1
    let kOpt0 := hPair.2
    match γv0 with
    | none =>
      tiOpt ←
        match r0 with
        | none =>
          if t0 == nat mo.tH then
            query (O := OO) (I := II) CKATag.chall p0
          else
            query (O := OO) (I := II) CKATag.send p0
        | some coins =>
          query (O := OO) (I := II) CKATag.sendBad (p0, coins)
      match tiOpt with
      | none => return (none, (h0, kOpt0))
      | some (tMsg, ik) =>
        let h1 := tset h0 t0 (some (tMsg, ik))
        let pOut := Expr.op (O := OO) CKAOp.prngUp (σ0, ik)
        (kEpoch, kOpt1) ←
          if t0 == nat mo.tStar then
            kU ← sample (O := OO) (I := II) CKASamp.k ()
            return (kU, some kU)
          else
            return (pOut.2, kOpt0)
        let ss := Expr.op (O := OO) CKAOp.fsInitSender kEpoch
        if leN (nat (mo.tH + Δcka)) t0 then
          γOpt ← query (I := II) CKATag.corr p0
          match γOpt with
          | none => return (none, (h1, kOpt1))
          | some γ' =>
            return (some (some γ', tMsg, pOut.1, ss), (h1, kOpt1))
        else
          return (some (none, tMsg, pOut.1, ss), (h1, kOpt1))
    | some γ =>
      coins ←
        match r0 with
        | none => sample (O := OO) (I := II) CKASamp.ccoins ()
        | some c => return c
      let cOut := Expr.op (O := OO) CKAOp.ckaSend (γ, coins)
      let tMsg := cOut.2.1
      let ik := cOut.2.2
      let h1 := tset h0 t0 (some (tMsg, ik))
      let pOut := Expr.op (O := OO) CKAOp.prngUp (σ0, ik)
      (kEpoch, kOpt1) ←
        if t0 == nat mo.tStar then
          kU ← sample (O := OO) (I := II) CKASamp.k ()
          return (kU, some kU)
        else
          return (pOut.2, kOpt0)
      let ss := Expr.op (O := OO) CKAOp.fsInitSender kEpoch
      return (some (some cOut.1, tMsg, pOut.1, ss), (h1, kOpt1))

def ckaStartRecvUAnsE (mo : Mode) {Γ'}
    (hE : Expr OO Γ' ckaUHsTy)
    (tE : Expr OO Γ' .nat)
    (γvE : Expr OO Γ' (.opt (.base .γ)))
    (σE : Expr OO Γ' (.base .sig))
    (tnE : Expr OO Γ' (.base .t)) :
    Expr OO Γ'
      (.opt (.opt (.prod (.opt (.base .γ)) (.prod (.base .sig) (.base .rs))))) :=
  rdslExpr =>
    letE (hE, tE, γvE, σE, tnE) fun (hPair, t0, γv0, σ0, tn0) =>
      let h0 := hPair.1
      let kOpt0 := hPair.2
      let honest :=
        match tget h0 t0 with
        | none => none
        | some (tCached, ikCached) =>
          if Expr.op (O := OO) CKAOp.eqT (tCached, tn0) then some ikCached else none
      match honest with
      | none =>
        if bool mo.auth && (t0 == nat mo.tStar) then
          match γv0 with
          | none => none
          | some γ =>
            let kOut := Expr.op (O := OO) CKAOp.ckaReceive (γ, tn0)
            let pOut := Expr.op (O := OO) CKAOp.prngUp (σ0, kOut.2)
            let rs := Expr.op (O := OO) CKAOp.fsInitReceiver pOut.2
            some (some (some kOut.1, pOut.1, rs))
        else
          some none
      | some ik =>
        let pOut := Expr.op (O := OO) CKAOp.prngUp (σ0, ik)
        let kEpoch :=
          if t0 == nat mo.tStar then
            match kOpt0 with
            | none => pOut.2
            | some kU => kU
          else
            pOut.2
        let rs := Expr.op (O := OO) CKAOp.fsInitReceiver kEpoch
        let γv' :=
          match γv0 with
          | none => none
          | some γ => some (Expr.op (O := OO) CKAOp.ckaReceive (γ, tn0)).1
        some (some (γv', pOut.1, rs))

def hooksCKAUC (B Δcka : ℕ) (mo : Mode) :
    HooksC OO II (.opt (.base .γ)) (.base .sig) (.base .ss) (.base .rs) ckaUHsTy where
  startSend := ckaStartSendUC Δcka mo
  startRecv hE _ctxE _pE tE γvE σE tnE := rdsl do
    return (ckaStartRecvUAnsE mo hE tE γvE σE tnE, hE)
  fsSend hE _ctxE _pE _tE ssE hdrE mE _pairE := rdsl do
    return (some (Expr.op (O := OO) CKAOp.fsSend (ssE, hdrE, mE)), hE)
  fsRecv hE _ctxE _pE _tE rsE hdrE eE _recE := rdsl do
    return (some (Expr.op (O := OO) (CKAOp.fsReceive B) (rsE, hdrE, eE)), hE)
  commit hE _ctxE pE oldE newE := rdsl do
    (hPair, p0, old0, new0) ← return (hE, pE, oldE, newE)
    if (vpTcurNat old0 < vpTcurNat new0) && !(isSomeE (vpΓ old0)) then
      rOpt ← query (I := II) CKATag.receive p0
      match rOpt with
      | none => return (none, hPair)
      | some _ =>
        if leN (nat (mo.tH + Δcka)) (vpTcurNat new0) then
          γOpt ← query (I := II) CKATag.corr p0
          match γOpt with
          | none => return (none, hPair)
          | some γ' => return (some (vpSetΓ new0 (some γ')), hPair)
        else
          return (some new0, hPair)
    else
      return (some new0, hPair)
  reveal hE _ctxE pE vpE := rdsl do
    (hPair, p0, vp0) ← return (hE, pE, vpE)
    match vpΓ vp0 with
    | none =>
      γOpt ← query (I := II) CKATag.corr p0
      match γOpt with
      | none => return (none, hPair)
      | some γ =>
        return (some (realPartyE vp0 γ (vpRoot vp0) (vpVS vp0) (vpVR vp0)), hPair)
    | some γ =>
      return (some (realPartyE vp0 γ (vpRoot vp0) (vpVS vp0) (vpVR vp0)), hPair)

/-- Stage-2 switch-back privacy CKA reduction keeping challenge epoch `i`'s honest FS-AEAD key uniform. -/
def redCKAPrivUProg (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (i : ℕ) :
    CostedReduction OO II
      (SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (ckaSMCodec KC Γ CCoins T I KR RSt K SS RS M E)
      .unit .unit .bool .bool where
  σ := ckaUEsTy
  init := rdsl [_] do
    b ← sample (I := II) CKASamp.bit ()
    es0 ← initCKAEStateC (raw ⟨false, tL, i⟩) b
    return ((), (esG es0, (esH es0, none), esAbort es0))
  handle := rdsl [es, q] do
    implEC (raw (hooksCKAUC B Δcka ⟨false, tL, i⟩)) L (raw (2 + Δcka)) qep maxSkip
      (raw (modeCfgEC OO ⟨false, tL, i⟩)) (raw (⟨false, tL, i⟩ : Mode).policy) es q
  finish := rdsl [es, guess] do
    privOutC L (raw (2 + Δcka)) (raw (⟨false, tL, i⟩ : Mode).policy)
      (raw (rdsl do sample (I := II) CKASamp.bit ())) (cGsB (esG es)) guess es

private theorem ckaVpEnc_eq_vpTblEnc :
    @ckaVpEnc KC Γ CCoins T I KR RSt K SS RS M E =
      vpTblEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (RSt := RSt)
        (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
        (γvT := .opt (.base .γ)) (svT := .base .sig) (ssvT := .base .ss) (rsvT := .base .rs) := rfl

@[simp] private theorem eval_v0_cons {Γ' : List (Ty S)} {t : Ty S} (x : t.denote) (ρ : Env Γ') :
    (Expr.v0 (O := OO)).eval (Env.cons x ρ) = x := rfl

@[simp] private theorem eval_bool_env {Γ' : List (Ty S)} (b : Bool) (ρ : Env Γ') :
    (Expr.bool (O := OO) b).eval ρ = b := rfl

@[simp] private theorem eval_ret_pair_unit_v0 {Γ' : List (Ty S)} {t : Ty S}
    (x : t.denote) (ρ : Env Γ') :
    (Comp.ret (O := OO) (I := II) (.pair .unit .v0)).eval (Env.cons x ρ) = pure ((), x) := rfl

/-! ## Static query bounds -/

@[simp] theorem ckaStartSendC_queries (Δcka : ℕ) (mo : Mode) {Γ'}
    (hE : Expr OO Γ' ckaHsTy) (ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γvE : Expr OO Γ' (.opt (.base .γ))) (σE : Expr OO Γ' (.base .sig))
    (rE : Expr OO Γ' (.opt (.base .ccoins))) :
    (ckaStartSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) Δcka mo hE ctxE pE tE γvE σE rE).queries
      (fun _ => 1) (fun _ => 0) = 2 := by
  simp [ckaStartSendC, Comp.queries]

@[simp] theorem ckaStartRecvC_queries (mo : Mode) {Γ'}
    (hE : Expr OO Γ' ckaHsTy) (ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γvE : Expr OO Γ' (.opt (.base .γ))) (σE : Expr OO Γ' (.base .sig))
    (tnE : Expr OO Γ' (.base .t)) :
    (ckaStartRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) mo hE ctxE pE tE γvE σE tnE).queries
      (fun _ => 1) (fun _ => 0) = 0 := by
  simp [ckaStartRecvC, Comp.queries]

@[simp] theorem ckaFsSendC_queries {Γ'}
    (hE : Expr OO Γ' ckaHsTy) (ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (ssE : Expr OO Γ' (.base .ss)) (hdrE : Expr OO Γ' hdrTy)
    (mE : Expr OO Γ' (.base .msg)) (pairE : Expr OO Γ' (.opt (.prod (.base .msg) (.base .msg)))) :
    (ckaFsSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) hE ctxE pE tE ssE hdrE mE pairE).queries
      (fun _ => 1) (fun _ => 0) = 0 := by
  simp [ckaFsSendC, Comp.queries]

@[simp] theorem ckaFsRecvC_queries (B : ℕ) {Γ'}
    (hE : Expr OO Γ' ckaHsTy) (ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (rsE : Expr OO Γ' (.base .rs)) (hdrE : Expr OO Γ' hdrTy)
    (eE : Expr OO Γ' (.base .ct)) (recE : Expr OO Γ' (.opt cRecTy)) :
    (ckaFsRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B hE ctxE pE tE rsE hdrE eE recE).queries
      (fun _ => 1) (fun _ => 0) = 0 := by
  simp [ckaFsRecvC, Comp.queries]

@[simp] theorem ckaCommitC_queries (Δcka : ℕ) (mo : Mode) {Γ'}
    (hE : Expr OO Γ' ckaHsTy) (ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool) (oldE newE : Expr OO Γ' ckaVpTy) :
    (ckaCommitC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) Δcka mo hE ctxE pE oldE newE).queries
      (fun _ => 1) (fun _ => 0) = 2 := by
  simp [ckaCommitC, Comp.queries]

@[simp] theorem ckaRevealC_queries {Γ'}
    (hE : Expr OO Γ' ckaHsTy) (ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool) (vpE : Expr OO Γ' ckaVpTy) :
    (ckaRevealC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) hE ctxE pE vpE).queries
      (fun _ => 1) (fun _ => 0) = 1 := by
  simp [ckaRevealC, Comp.queries]

@[simp] theorem implEC_hooksCKAC_queries (L B Δcka qep maxSkip : ℕ) (mo : Mode) {Γ'}
    (es : Expr OO Γ' ckaEsTy)
    (q : Expr OO Γ' (ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E)) :
    (implEC (hooksCKAC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B Δcka mo)
      L (2 + Δcka) qep maxSkip (modeCfgEC OO mo) mo.policy es q).queries
      (fun _ => 1) (fun _ => 0) = 2 := by
  simp [implEC, transmitEC, challEC, deliverEC, injectEC, corrEC,
    vSendC, vSendStep1C, vRecvC, vRecvStep1C, commitEC, hooksCKAC, Comp.queries]

@[simp] theorem initCKAEStateC_queries (mo : Mode) {Γ'} (bE : Expr OO Γ' .bool) :
    (initCKAEStateC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) mo bE).queries (fun _ => 1) (fun _ => 0) = 0 := by
  simp [initCKAEStateC, Comp.queries]

@[simp] theorem redCKAAuthProg_totalQueries (L B Δcka qep maxSkip : ℕ)
    (tL : Option ℕ) (t q : ℕ) :
    (redCKAAuthProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip tL t).totalQueries (fun _ => 1) (fun _ => 0) q = q * 2 := by
  simp [CostedReduction.totalQueries, redCKAAuthProg, Comp.queries]

@[simp] theorem redCKAPrivProg_totalQueries (L B Δcka qep maxSkip : ℕ)
    (tL : Option ℕ) (t q : ℕ) :
    (redCKAPrivProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip tL t).totalQueries (fun _ => 1) (fun _ => 0) q = q * 2 := by
  simp [CostedReduction.totalQueries, redCKAPrivProg, privOutC, Comp.queries]

/-! ## Static cost characterizations -/

private theorem bits_zero : bits 0 = 1 := rfl

theorem initCKAEStateC_cost (mo : Mode) {Γ'} (bE : Expr OO Γ' .bool) :
    (initCKAEStateC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) mo bE).cost = bE.cost + 484 := by
  simp [initCKAEStateC, esMk, cGsInitE, cGsMk, mkPartiesE, vpMk, partyEnc,
    ckaIface, ckaSamplers, ckaOps, Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, bits_zero]

theorem redCKAAuthProg_totalCost (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (t q : ℕ) :
    (redCKAAuthProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip tL t).totalCost q =
      491 +
        q * ((implEC (Γ' := [ckaEsTy, ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E])
          (hooksCKAC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
            (sampI := sampI) (sampK := sampK) B Δcka ⟨true, tL, t⟩)
          L (2 + Δcka) qep maxSkip (modeCfgEC OO ⟨true, tL, t⟩)
          (⟨true, tL, t⟩ : Mode).policy .v0 .v1).cost + 12) +
        (authOutE (O' := OO) L (2 + Δcka) (⟨true, tL, t⟩ : Mode).policy
          (Expr.v0 : Expr OO [ckaEsTy, .bool] ckaEsTy)).cost := by
  simp only [CostedReduction.totalCost, redCKAAuthProg, ckaSMCodec, ckaIface, Comp.cost,
    initCKAEStateC_cost, Expr.cost, Expr.v0]
  rw [max_eq_right (by omega)]
  omega

theorem redCKAPrivProg_totalCost (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (t q : ℕ) :
    (redCKAPrivProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip tL t).totalCost q =
      493 +
        q * ((implEC (Γ' := [ckaEsTy, ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E])
          (hooksCKAC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
            (sampI := sampI) (sampK := sampK) B Δcka ⟨false, tL, t⟩)
          L (2 + Δcka) qep maxSkip (modeCfgEC OO ⟨false, tL, t⟩)
          (⟨false, tL, t⟩ : Mode).policy .v0 .v1).cost + 12) +
        (privOutC (O' := OO) L (2 + Δcka) (⟨false, tL, t⟩ : Mode).policy
          (Comp.sample (O := OO) (I := II) CKASamp.bit .unit) (cGsB (esG .v0)) .v1
          (Expr.v0 : Expr OO [ckaEsTy, .bool] ckaEsTy)).cost := by
  simp only [CostedReduction.totalCost, redCKAPrivProg, ckaSMCodec, ckaIface, ckaSamplers, Comp.cost,
    initCKAEStateC_cost, Expr.cost, Expr.v0]
  rw [max_eq_right (by omega)]

/-! ## Receiver-state invariants and evaluation bridges -/

theorem hooksCKA_startRecv_rs [DecidableEq T] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (mo : Mode)
    {VROk : RS → Prop} (hInitR : ∀ k, VROk (fs.initReceiver k))
    (ctx : Ctx (Option Γ) T RSt SS RS M E) (P : Party) (t : ℕ)
    (γv : Option Γ) (σ : RSt) (Tn : T) (h : CKAState T I) :
    ∀ res ∈ support (((hooksCKA cka prng fs Δcka mo).startRecv ctx P t γv σ Tn).run h),
      ∀ γ' σ' rs, res.1 = some (some (γ', σ', rs)) → VROk rs := by
  intro ⟨ans, h'⟩ hmem γ' σ' rs hEq
  subst hEq
  unfold hooksCKA at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  revert hmem
  rcases h.cache t with _ | ⟨Tc, Ik⟩
  · intro hmem
    split_ifs at hmem
    · rcases γv with _ | γ
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨h, _⟩; cases h
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq, Option.some.injEq] at hmem
        rcases hmem with ⟨⟨rfl, rfl, rfl⟩, rfl⟩; exact hInitR _
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, Option.some.injEq] at hmem
      rcases hmem with ⟨h, _⟩; cases h
  · intro hmem
    by_cases hEq : Tc = Tn
    · simp only [hEq, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, Option.some.injEq] at hmem
      rcases hmem with ⟨⟨rfl, rfl, rfl⟩, rfl⟩; exact hInitR _
    · simp only [hEq, ↓reduceIte] at hmem
      split_ifs at hmem
      · rcases γv with _ | γ
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨h, _⟩; cases h
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq, Option.some.injEq] at hmem
          rcases hmem with ⟨⟨rfl, rfl, rfl⟩, rfl⟩; exact hInitR _
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq, Option.some.injEq] at hmem
        rcases hmem with ⟨h, _⟩; cases h

theorem hooksCKA_commit_vR [DecidableEq T] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (mo : Mode)
    (ctx : Ctx (Option Γ) T RSt SS RS M E) (P : Party)
    (old new : VP (Option Γ) T RSt SS RS) (h : CKAState T I) :
    ∀ res ∈ support (((hooksCKA cka prng fs Δcka mo).commit ctx P old new).run h),
      ∀ new', res.1 = some new' → new'.vR = new.vR := by
  intro ⟨ans, h'⟩ hmem new' hEq
  subst hEq
  dsimp only [hooksCKA] at hmem
  by_cases h1 : (decide (old.tcur < new.tcur) && old.γ.isNone) = true
  · simp only [h1, ↓reduceIte, run_liftC_bind, mem_support_bind_iff] at hmem
    obtain ⟨rcvRes, _, hmem⟩ := hmem
    rcases rcvRes with _ | ⟨⟩
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨h, _⟩; cases h
    · dsimp only at hmem
      by_cases h2 : mo.tH + Δcka ≤ new.tcur
      · simp only [h2, ↓reduceIte, run_liftC_bind, mem_support_bind_iff] at hmem
        obtain ⟨γ?, _, hmem⟩ := hmem
        rcases γ? with _ | γ'
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨h, _⟩; cases h
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq, Option.some.injEq] at hmem
          rcases hmem with ⟨rfl, rfl⟩; rfl
      · simp only [h2, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq, Option.some.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩; rfl
  · simp only [h1, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩; rfl

theorem hooksCKAC_agrees_vr [DecidableEq T] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (B Δcka : ℕ) (mo : Mode)
    {VROk : RS → Prop}
    (hSend : ckaSend = cka.send)
    (hRecv : ckaReceive = cka.receive)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send)
    (hFsRecv : fsReceive = fs.receive)
    (heqT : eqT = (· == ·))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hInitR : ∀ k, VROk (fs.initReceiver k))
    (hFsB : ∀ rs hdr e rs' i m, VROk rs → fs.receive rs hdr e = some (rs', i, m) → i ≤ B) :
    HooksCAgrees (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      ckaHsEnc (fun _ => True) (HBoundedPost := fun _ => True) (VROk := VROk)
      (hooksCKAC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B Δcka mo)
      (hooksCKA cka prng fs Δcka mo) where
  hBounded_post _ _ := trivial
  startSend_eval hE ctxE pE tE γE σE rE ρ h ctx P _ hh _ hp :=
    ckaStartSendC_eval cka prng fs hSend hPrngUp hFsInitS hSampCCoins Δcka mo
      hE ctxE pE tE γE σE rE ρ h ctx P hh hp
  startSend_bounded _ _ _ _ _ _ _ _ _ _ := trivial
  startRecv_eval hE ctxE pE tE γE σE tnE ρ h ctx P _ hh _ _ :=
    ckaStartRecvC_eval cka prng fs hRecv hPrngUp hFsInitR heqT Δcka mo
      hE ctxE pE tE γE σE tnE ρ h ctx P hh
  startRecv_bounded _ _ _ _ _ _ _ _ _ _ := trivial
  startRecv_vrOk ctx P t γ σ Tn h _ :=
    hooksCKA_startRecv_rs cka prng fs Δcka mo hInitR ctx P t γ σ Tn h
  fsSend_eval hE _ _ _ ssE hdrE mE _ ρ h _ _ _ hh _ _ := by
    simp [hooksCKAC, ckaFsSendC, hooksCKA, ckaOps, hFsSend, hh,
      StateT.run_pure, Prod.map, Expr.eval]
  fsRecv_eval hE _ _ _ rsE hdrE eE _ ρ h _ _ _ _ hVR hh _ _ _ := by
    simp only [hooksCKAC, ckaFsRecvC, hooksCKA, eval_ret,
      ckaOps, hFsRecv, hh, StateT.run_pure, map_pure, Prod.map, id_eq, Expr.eval]
    congr 2
    rcases hrc : fs.receive (rsE.eval ρ) (hdrE.eval ρ) (eE.eval ρ) with _ | ⟨rs', i, m⟩
    · rfl
    · simp [Nat.min_eq_left (hFsB _ _ _ _ _ _ hVR hrc)]
  fsRecv_bounded _ _ _ _ _ _ _ _ _ _ _ := trivial
  commit_eval hE ctxE pE oldE newE ρ h ctx P old new _ hh _ hp hold hnew :=
    ckaCommitC_eval cka prng fs Δcka mo hE ctxE pE oldE newE ρ h ctx P old new hh hp hold hnew
  reveal_eval hE ctxE pE vpE ρ h ctx P vp _ hh _ hp hvp :=
    ckaRevealC_eval cka prng fs Δcka mo hE ctxE pE vpE ρ h ctx P vp hh hp hvp

theorem initCKARaw_vrInv [SampleableType KR] [SampleableType KC]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (mo : Mode) (b : Bool)
    {VROkStep : ℕ → RS → Prop} {B qAdv : ℕ}
    (hInitR : ∀ k, VROkStep (B - qAdv) (fs.initReceiver k)) :
    ∀ es₀ ∈ support (initCKARaw cka prng fs lam mo b),
      SMVRInv VROkStep B qAdv es₀.g := by
  intro es₀ hmem P t v hv
  unfold initCKARaw at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨kr, _, hmem⟩ := hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨⟨γA, γB⟩, _, hmem⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff] at hmem
  subst hmem
  cases P <;> simp only [mkParties] at hv
  · split_ifs at hv with ht0
    · cases hv; exact hInitR _
  · cases hv

theorem redCKAAuthProg_eval_vr
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    {VROkStep : ℕ → RS → Prop}
    (hInitA : ckaInitA = cka.initA)
    (hInitB : ckaInitB = cka.initB)
    (hSend : ckaSend = cka.send)
    (hRecv : ckaReceive = cka.receive)
    (hPrngInit : prngInit = prng.init)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send)
    (hFsRecv : fsReceive = fs.receive)
    (heqT : eqT = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    (hDefaultE : defaultE = default)
    (hSampKR : sampKR = ($ᵗ KR : ProbComp KR))
    (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hVRHk : HooksVRInv VROkStep (hooksCKA cka prng fs Δcka ⟨true, tL, t⟩))
    (hInitR : ∀ k, VROkStep 0 (fs.initReceiver k))
    (hFsB : ∀ rs hdr e rs' i m, VROkStep B_q rs → fs.receive rs hdr e = some (rs', i, m) → i ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : SchemeAdversary Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q) :
    (redCKAAuthProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka qep fs.maxSkip tL t).eval (fun _ => A) () =
      redCKAAuth cka prng fs lam Δcka qep tL t A := by
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv := by
    refine hA.of_imp (fun x hx => ?_)
    rcases x with _ | _ <;> simp_all [isGameQuery]
  have hHk := hooksCKAC_agrees_vr (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (prngInit := prngInit) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    cka prng fs B Δcka ⟨true, tL, t⟩ hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend hFsRecv
    heqT hSampCCoins (fun k => hVRHk.mono (Nat.zero_le B_q) (hInitR k)) hFsB
  have hInit := initCKAEStateC_eval
    (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    cka prng fs hInitA hInitB hPrngInit hPrngUp hFsInitS hFsInitR hSampKR hSampKC
    ⟨true, tL, t⟩ (Expr.bool (O := OO) false) (Env.cons (t := .unit) () .nil)
  unfold redCKAAuthProg CostedReduction.eval CostedReduction.impl redCKAAuth
  dsimp only
  rw [eval_bind, hInit, ckaVpEnc_eq_vpTblEnc, runCKA_eq_bind_initCKARaw]
  simp only [bind_map_left, eval_bool_env, eval_ret_pair_unit_v0, bind_assoc, pure_bind]
  refine OracleComp.bind_congr_of_forall_mem_support
    (initCKARaw cka prng fs lam ⟨true, tL, t⟩ false) fun es₀ hes₀ => ?_
  have ⟨hInv₀, _⟩ := initCKARaw_inv cka prng fs lam ⟨true, tL, t⟩ false hqB hB1 hBB es₀ hes₀
  have hVR₀ := initCKARaw_vrInv (B := B_q) (qAdv := qAdv) cka prng fs lam ⟨true, tL, t⟩ false
    (fun k => hVRHk.mono (Nat.zero_le _) (hInitR k)) es₀ hes₀
  have ⟨hSim, hSimInv⟩ := simulateQ_implEC_vr_eq hDefaultE (fun _ => rfl) ckaHsEnc (fun _ => True)
    (hooksCKAC B Δcka ⟨true, tL, t⟩) (hooksCKA cka prng fs Δcka ⟨true, tL, t⟩)
    L B_q (2 + Δcka) qep fs.maxSkip hHk hVRHk
    (modeCfgEC OO ⟨true, tL, t⟩) (⟨true, tL, t⟩ : Mode).cfg
    (modeCfgEC_agrees ⟨true, tL, t⟩) heqT heqM heqE (⟨true, tL, t⟩ : Mode).policy
    (fun _ _ _ _ _ _ => trivial) hA' es₀ trivial hInv₀ hVR₀
  rw [hSim, bind_map_left]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨b', es'⟩ hes' => ?_
  obtain ⟨_, hInv', _⟩ := hSimInv (b', es') hes'
  have hBnd' := hInv'.toBoundedEngine
  have hOut := authOutE_eval vpTblEnc ckaHsEnc (O' := OO) L (2 + Δcka)
    (⟨true, tL, t⟩ : Mode).policy .v0
    (Env.cons (esEnc vpTblEnc ckaHsEnc es') (Env.cons (t := .bool) b' .nil))
    es' hBnd'.leaks_le hBnd'.corrs_le rfl
  simp only [eval_ret, Prod.map_apply, id_eq, hOut]
  rfl

theorem redCKAPrivProg_eval_vr
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    {VROkStep : ℕ → RS → Prop}
    (hInitA : ckaInitA = cka.initA)
    (hInitB : ckaInitB = cka.initB)
    (hSend : ckaSend = cka.send)
    (hRecv : ckaReceive = cka.receive)
    (hPrngInit : prngInit = prng.init)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send)
    (hFsRecv : fsReceive = fs.receive)
    (heqT : eqT = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    (hDefaultE : defaultE = default)
    (hSampKR : sampKR = ($ᵗ KR : ProbComp KR))
    (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hVRHk : HooksVRInv VROkStep (hooksCKA cka prng fs Δcka ⟨false, tL, t⟩))
    (hInitR : ∀ k, VROkStep 0 (fs.initReceiver k))
    (hFsB : ∀ rs hdr e rs' i m, VROkStep B_q rs → fs.receive rs hdr e = some (rs', i, m) → i ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : SchemeAdversary Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q) :
    (redCKAPrivProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka qep fs.maxSkip tL t).eval (fun _ => A) () =
      redCKAPriv cka prng fs lam Δcka qep tL t A := by
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv := by
    refine hA.of_imp (fun x hx => ?_)
    rcases x with _ | _ <;> simp_all [isGameQuery]
  have hHk := hooksCKAC_agrees_vr (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (prngInit := prngInit) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    cka prng fs B Δcka ⟨false, tL, t⟩ hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend hFsRecv
    heqT hSampCCoins (fun k => hVRHk.mono (Nat.zero_le B_q) (hInitR k)) hFsB
  have hBit : ∀ {Γ'} (ρ' : Env Γ'),
      (Comp.sample (O := OO) (I := II) CKASamp.bit .unit).eval ρ' = sampleT Bool := by
    intro Γ' ρ'
    simp only [Comp.eval, ckaIface, ckaSamplers, sampleT]
    exact liftP_eq_liftM II (fun _ => rfl) ($ᵗ Bool)
  unfold redCKAPrivProg CostedReduction.eval CostedReduction.impl redCKAPriv
  dsimp only
  rw [eval_bind, hBit, bind_assoc]
  refine bind_congr fun b => ?_
  have hInit := initCKAEStateC_eval
    (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    cka prng fs hInitA hInitB hPrngInit hPrngUp hFsInitS hFsInitR hSampKR hSampKC
    ⟨false, tL, t⟩ (Expr.v0 (O := OO)) (Env.cons (t := .bool) b (Env.cons (t := .unit) () .nil))
  rw [eval_bind, hInit, ckaVpEnc_eq_vpTblEnc, runCKA_eq_bind_initCKARaw]
  simp only [bind_map_left, eval_v0_cons, eval_ret_pair_unit_v0, bind_assoc, pure_bind]
  refine OracleComp.bind_congr_of_forall_mem_support
    (initCKARaw cka prng fs lam ⟨false, tL, t⟩ b) fun es₀ hes₀ => ?_
  have ⟨hInv₀, hb₀⟩ := initCKARaw_inv cka prng fs lam ⟨false, tL, t⟩ b hqB hB1 hBB es₀ hes₀
  have hVR₀ := initCKARaw_vrInv (B := B_q) (qAdv := qAdv) cka prng fs lam ⟨false, tL, t⟩ b
    (fun k => hVRHk.mono (Nat.zero_le _) (hInitR k)) es₀ hes₀
  have ⟨hSim, hSimInv⟩ := simulateQ_implEC_vr_eq hDefaultE (fun _ => rfl) ckaHsEnc (fun _ => True)
    (hooksCKAC B Δcka ⟨false, tL, t⟩) (hooksCKA cka prng fs Δcka ⟨false, tL, t⟩)
    L B_q (2 + Δcka) qep fs.maxSkip hHk hVRHk
    (modeCfgEC OO ⟨false, tL, t⟩) (⟨false, tL, t⟩ : Mode).cfg
    (modeCfgEC_agrees ⟨false, tL, t⟩) heqT heqM heqE (⟨false, tL, t⟩ : Mode).policy
    (fun _ _ _ _ _ _ => trivial) hA' es₀ trivial hInv₀ hVR₀
  rw [hSim, bind_map_left]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨b', es'⟩ hes' => ?_
  obtain ⟨_, hInv', hb'⟩ := hSimInv (b', es') hes'
  have hBnd' := hInv'.toBoundedEngine
  have hbEq : (cGsB (esG (Expr.v0 (O := OO)))).eval
      (Env.cons (esEnc vpTblEnc ckaHsEnc es') (Env.cons (t := .bool) b' .nil)) = b := by
    change es'.g.b = b
    exact hb'.trans hb₀
  exact privOutC_eval ckaHsEnc L (2 + Δcka) (⟨false, tL, t⟩ : Mode).policy
    (Comp.sample (I := II) CKASamp.bit .unit) hBit
    (cGsB (esG .v0)) .v1 .v0
    (Env.cons (esEnc vpTblEnc ckaHsEnc es') (Env.cons (t := .bool) b' .nil))
    b b' es' hBnd'.leaks_le hbEq rfl rfl

end HooksCKAC

section FromAEADPRG

variable {MK C : Type}

theorem hooksCKA_vrInv_fromAEADPRG [DecidableEq T] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip Δcka : ℕ) (mo : Mode) :
    HooksVRInv (RSReach maxSkip)
      (hooksCKA cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo) where
  mono hle hv := hv.mono hle
  startRecv_step ctx P t γ σ Tn h :=
    hooksCKA_startRecv_rs cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo
      (RSReach.init ae G maxSkip) ctx P t γ σ Tn h
  fsRecv_step _ _ _ rs hdr e _ h res hVR hmem v' i' m' hEq := by
    rcases res with ⟨ans, h'⟩
    dsimp only at hEq
    subst hEq
    dsimp only [hooksCKA] at hmem
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, Option.some.injEq] at hmem
    rcases hmem with ⟨hrec, _⟩
    exact (RSReach.receive ae G maxSkip _ hVR hrec.symm).2
  commit_vR := hooksCKA_commit_vR cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo

end FromAEADPRG

end CryptoGames.SM.Construction

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
# Costed `redPRNGAuth` and `redPRNGPriv` Reductions

Defines the ACD19 `B2` reductions (`redPRNGAuthProg`, `redPRNGPrivProg`, and
`redPRNGAuthStage2Prog`) from Fig. 8 SM authenticity and privacy to PRF-PRNG security as
`ReductionDsl.CostedReduction` programs, with evaluation agreement, query bounds, and cost bounds.
-/

@[expose] public section

open ReductionDsl OracleSpec OracleComp

namespace CryptoGames.SM.Engine.RedPRNG

open Construction CKA PRFPRNG

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}

local notation "S" => prngSig KC Γ CCoins T I KR RSt K SS RS M E

/-! ## Simulation agreement for `implEC` -/

theorem epMgmt_b_eq {St Msg C : Type} {Δ qep : ℕ} {s s₁ : SM.GameState St Msg C}
    {P : Party} {bad : Bool} (h : s.epMgmt Δ qep P bad = some s₁) :
    s₁.b = s.b := by
  unfold SM.GameState.epMgmt at h
  by_cases h1 : P.sendsIn (s.epoch P + 1)
  · by_cases h2 : qep < s.epoch P + 1
    · simp [h1, h2] at h
    · simp only [h1, h2, ↓reduceIte, Option.some.injEq] at h
      subst h
      by_cases h3 : (bad && !(s.safeCh Δ P)) = true <;> simp [h3, SM.GameState.leak]
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
          dsimp [SM.GameState.record]
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
            dsimp [SM.GameState.record]
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
  prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

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
    (hHk : HooksCAgrees hsEncFn HBounded (HBoundedPost := HBoundedPost) (VROk := VROkStep B) hkC hk)
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
          (handlerImpl (C := prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E)
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
          ((handlerImpl (C := prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E)
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
          ((handlerImpl (C := prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E)
            (implEC hkC L Δ qep maxSkip cfgC π .v0 .v1)) (.inr t)).run
            (esEnc vpTblEnc hsEncFn es) =
          Prod.map id (esEnc vpTblEnc hsEncFn) <$>
            (implE hk Δ qep maxSkip cfg π (.inr t)).run es := by
        simp only [handlerImpl, StateT.run_mk, prngSMCodec,
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

end CryptoGames.SM.Engine.RedPRNG

namespace CryptoGames.SM.Construction

open Engine Engine.RedPRNG CKA PRFPRNG
open scoped Computational.Proofs.ReductionDsl.Notation

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}

local notation "S" => prngSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrTy" => ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrCtTy" => ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "psTy" => ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "rrTy" => ckaRrTy KC Γ CCoins T I KR RSt K SS RS M E

/-! ## `PRNGState` representation and `hooksPRNGC` -/

@[reducible] def prngHsTy : Ty S :=
  .tbl (.opt (.prod (.base .t) (.prod (.opt (.base .sig)) (.base .k))))

def prngHsEnc (s : PRNGState T RSt K) :
    (@prngHsTy KC Γ CCoins T I KR RSt K SS RS M E).denote :=
  s.cache

@[reducible] def prngVpTy : Ty S :=
  @vpTblTy KC Γ CCoins T I KR RSt K SS RS M E
    (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs)

@[reducible] def prngVpEnc (p : VP Γ T (Option RSt) SS RS) :
    (@prngVpTy KC Γ CCoins T I KR RSt K SS RS M E).denote :=
  vpTblEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (RSt := RSt)
    (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
    (γvT := .base .γ) (svT := .opt (.base .sig)) (ssvT := .base .ss) (rsvT := .base .rs) p

@[reducible] def prngEsTy : Ty S :=
  esTy prngVpTy prngHsTy

section HooksPRNGC

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
  prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

local notation "II" =>
  prngIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK

def prngProcessCorrC {Γ'} (ikOptE : Expr OO Γ' (.opt (.base .i))) :
    Comp OO II Γ' (.opt (.prod (.opt (.base .sig)) (.base .k))) :=
  rdsl do
    kOpt ← query (O := OO) (I := II) PRNGTag.process ikOptE
    match kOpt with
    | none => return none
    | some kOut =>
      σOpt ← query (O := OO) (I := II) PRNGTag.corr ()
      match σOpt with
      | none => return none
      | some σOut => return (some (some σOut, kOut))

def rootPRNGC (mo : Mode) {Γ'}
    (tE : Expr OO Γ' .nat)
    (ikE : Expr OO Γ' (.base .i))
    (σvE : Expr OO Γ' (.opt (.base .sig))) :
    Comp OO II Γ' (.opt (.prod (.opt (.base .sig)) (.base .k))) :=
  rdsl do
    (t0, ik0, σv0) ← return (tE, ikE, σvE)
    if nat mo.tStar < t0 then
      match σv0 with
      | none => return none
      | some σ =>
        let p := Expr.op (O := OO) CKAOp.prngUp (σ, ik0)
        return (some (some p.1, p.2))
    else if t0 == nat mo.tStar then
      if bool mo.tL.isSome && (t0 == nat mo.tH) then
        kOpt ← query (O := OO) (I := II) PRNGTag.challPrng none
        match kOpt with
        | none => return none
        | some kOut =>
          σOpt ← query (O := OO) (I := II) PRNGTag.corr ()
          match σOpt with
          | none => return none
          | some σOut => return (some (some σOut, kOut))
      else
        skOpt ← query (O := OO) (I := II) PRNGTag.challPrf ik0
        match skOpt with
        | none => return none
        | some (σOut, kOut) => return (some (some σOut, kOut))
    else if bool mo.tL.isSome && (t0 == nat mo.tH) then
      kOpt ← query (O := OO) (I := II) PRNGTag.process none
      match kOpt with
      | none => return none
      | some kOut => return (some (none, kOut))
    else if bool mo.tL.isSome && (t0 < nat mo.tH) then
      prngProcessCorrC (some ik0)
    else
      kOpt ← query (O := OO) (I := II) PRNGTag.process (some ik0)
      match kOpt with
      | none => return none
      | some kOut => return (some (none, kOut))

def prngStartSendC (mo : Mode) {Γ'}
    (hE : Expr OO Γ' prngHsTy)
    (_ctxE : Expr OO Γ' (cGsTy prngVpTy))
    (_pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ))
    (σvE : Expr OO Γ' (.opt (.base .sig)))
    (rE : Expr OO Γ' (.opt (.base .ccoins))) :
    Comp OO II Γ'
      (.prod (.opt (.prod (.base .γ) (.prod (.base .t) (.prod (.opt (.base .sig)) (.base .ss)))))
        prngHsTy) :=
  rdsl do
    (h0, t0, γ0, σv0, r0) ← return (hE, tE, γE, σvE, rE)
    coins ←
      match r0 with
      | none => sample (O := OO) (I := II) CKASamp.ccoins ()
      | some c => return c
    let cOut := Expr.op (O := OO) CKAOp.ckaSend (γ0, coins)
    stepOpt ← rootPRNGC mo t0 cOut.2.2 σv0
    match stepOpt with
    | none => return (none, h0)
    | some (σ', kVal) =>
      let tMsg := cOut.2.1
      let h1 := tset h0 t0 (some (tMsg, σ', kVal))
      let ss := Expr.op (O := OO) CKAOp.fsInitSender kVal
      return (some (cOut.1, tMsg, σ', ss), h1)

def prngStartRecvC (mo : Mode) {Γ'}
    (hE : Expr OO Γ' prngHsTy)
    (_ctxE : Expr OO Γ' (cGsTy prngVpTy))
    (_pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ))
    (_σvE : Expr OO Γ' (.opt (.base .sig)))
    (tnE : Expr OO Γ' (.base .t)) :
    Comp OO II Γ'
      (.prod (.opt (.opt (.prod (.base .γ) (.prod (.opt (.base .sig)) (.base .rs)))))
        prngHsTy) :=
  rdsl do
    (h0, t0, γ0, tn0) ← return (hE, tE, γE, tnE)
    let honest :=
      match tget h0 t0 with
      | none => none
      | some (tCached, entry) =>
        if Expr.op (O := OO) CKAOp.eqT (tCached, tn0) then some entry else none
    match honest with
    | none =>
      if bool mo.auth && (t0 == nat mo.tStar) then
        let kk := Expr.op (O := OO) CKAOp.ckaReceive (γ0, tn0)
        skOpt ← query (O := OO) (I := II) PRNGTag.challPrf kk.2
        match skOpt with
        | none => return (none, h0)
        | some (σOut, kOut) =>
          let rs := Expr.op (O := OO) CKAOp.fsInitReceiver kOut
          return (some (some (kk.1, some σOut, rs)), h0)
      else
        return (some none, h0)
    | some (σc, kVal) =>
      let γ' := (Expr.op (O := OO) CKAOp.ckaReceive (γ0, tn0)).1
      let rs := Expr.op (O := OO) CKAOp.fsInitReceiver kVal
      return (some (some (γ', σc, rs)), h0)

def prngFsSendC {Γ'}
    (hE : Expr OO Γ' prngHsTy)
    (_ctxE : Expr OO Γ' (cGsTy prngVpTy))
    (_pE : Expr OO Γ' .bool)
    (_tE : Expr OO Γ' .nat)
    (ssE : Expr OO Γ' (.base .ss))
    (hdrE : Expr OO Γ' hdrTy)
    (mE : Expr OO Γ' (.base .msg))
    (_pairE : Expr OO Γ' (.opt (.prod (.base .msg) (.base .msg)))) :
    Comp OO II Γ' (.prod (.opt (.prod (.base .ss) (.base .ct))) prngHsTy) :=
  rdsl do
    return (some (Expr.op (O := OO) CKAOp.fsSend (ssE, hdrE, mE)), hE)

def prngFsRecvC (B : ℕ) {Γ'}
    (hE : Expr OO Γ' prngHsTy)
    (_ctxE : Expr OO Γ' (cGsTy prngVpTy))
    (_pE : Expr OO Γ' .bool)
    (_tE : Expr OO Γ' .nat)
    (rsE : Expr OO Γ' (.base .rs))
    (hdrE : Expr OO Γ' hdrTy)
    (eE : Expr OO Γ' (.base .ct))
    (_recE : Expr OO Γ' (.opt cRecTy)) :
    Comp OO II Γ'
      (.prod (.opt (.opt (.prod (.base .rs) (.prod .nat (.base .msg))))) prngHsTy) :=
  rdsl do
    return (some (Expr.op (O := OO) (CKAOp.fsReceive B) (rsE, hdrE, eE)), hE)

def prngCommitC {Γ'}
    (hE : Expr OO Γ' prngHsTy)
    (_ctxE : Expr OO Γ' (cGsTy prngVpTy))
    (_pE : Expr OO Γ' .bool)
    (_oldE newE : Expr OO Γ' prngVpTy) :
    Comp OO II Γ' (.prod (.opt prngVpTy) prngHsTy) :=
  rdsl do
    return (some newE, hE)

def prngRevealC {Γ'}
    (hE : Expr OO Γ' prngHsTy)
    (_ctxE : Expr OO Γ' (cGsTy prngVpTy))
    (_pE : Expr OO Γ' .bool)
    (vpE : Expr OO Γ' prngVpTy) :
    Comp OO II Γ' (.prod (.opt psTy) prngHsTy) :=
  rdsl do
    (h0, vp0) ← return (hE, vpE)
    match vpRoot vp0 with
    | none => return (none, h0)
    | some σ =>
      return (some (realPartyE vp0 (vpΓ vp0) σ (vpVS vp0) (vpVR vp0)), h0)

def hooksPRNGC (B : ℕ) (mo : Mode) :
    HooksC OO II (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs) prngHsTy where
  startSend := prngStartSendC mo
  startRecv := prngStartRecvC mo
  fsSend := prngFsSendC
  fsRecv := prngFsRecvC B
  commit := prngCommitC
  reveal := prngRevealC

/-! ## Hook-level evaluation agreement -/

@[simp] theorem query_process_eval {Γ'} (ikOptE : Expr OO Γ' (.opt (.base .i))) (ρ : Env Γ') :
    (@Comp.query _ _ _ OO II _ PRNGTag.process ikOptE).eval ρ =
      PRFPRNG.processQuery (State := RSt) (Output := K) (ikOptE.eval ρ) := rfl

@[simp] theorem query_challPrng_eval {Γ'} (ikOptE : Expr OO Γ' (.opt (.base .i))) (ρ : Env Γ') :
    (@Comp.query _ _ _ OO II _ PRNGTag.challPrng ikOptE).eval ρ =
      PRFPRNG.challPrngQuery (State := RSt) (Output := K) (ikOptE.eval ρ) := rfl

@[simp] theorem query_challPrf_eval {Γ'} (ikE : Expr OO Γ' (.base .i)) (ρ : Env Γ') :
    (@Comp.query _ _ _ OO II _ PRNGTag.challPrf ikE).eval ρ =
      PRFPRNG.challPrfQuery (State := RSt) (Output := K) (ikE.eval ρ) := rfl

@[simp] theorem query_prngCorr_eval {Γ'} (uE : Expr OO Γ' .unit) (ρ : Env Γ') :
    (@Comp.query _ _ _ OO II _ PRNGTag.corr uE).eval ρ =
      PRFPRNG.corrQuery (State := RSt) (Input := I) (Output := K) := rfl

theorem prngProcessCorrC_eval {Γ'} (ikOptE : Expr OO Γ' (.opt (.base .i))) (ρ : Env Γ')
    (ikOpt : Option I) (hik : ikOptE.eval ρ = ikOpt)
    (h : PRNGState T RSt K) :
    ((processCorr (T := T) (Sig := RSt) (K := K) ikOpt).run h) =
      (fun ans => (ans, h)) <$>
        (prngProcessCorrC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) ikOptE).eval ρ := by
  unfold processCorr prngProcessCorrC liftP
  simp only [eval_bind, query_process_eval, hik, StateT.run_bind, StateT.run_lift,
    bind_assoc, pure_bind, map_bind]
  refine bind_congr fun k? => ?_
  rcases k? with _ | k
  · simp [Comp.eval, StateT.run_pure, Expr.eval, Expr.v0]
  · simp only [eval_caseOpt, Expr.eval, Expr.v0, Env.get_cons_zero, eval_bind,
      query_prngCorr_eval, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]
    refine bind_congr fun σ? => ?_
    rcases σ? with _ | σ'
    · simp [Comp.eval, StateT.run_pure, Expr.eval]
    · simp [Comp.eval, StateT.run_pure, Expr.eval, Expr.v2]

theorem rootPRNGC_eval
    (prng : PRFPRNG KR RSt I K)
    (hPrngUp : prngUp = prng.up)
    (mo : Mode) {Γ'}
    (tE : Expr OO Γ' .nat)
    (ikE : Expr OO Γ' (.base .i))
    (σvE : Expr OO Γ' (.opt (.base .sig)))
    (ρ : Env Γ') (h : PRNGState T RSt K) :
    ((rootPRNG (T := T) prng mo (tE.eval ρ) (ikE.eval ρ) (σvE.eval ρ)).run h) =
      (fun ans => (ans, h)) <$>
        (rootPRNGC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) mo tE ikE σvE).eval ρ := by
  unfold rootPRNG rootPRNGC
  rw [eval_bind_ret]
  set t : ℕ := tE.eval ρ
  set Ik : I := ikE.eval ρ
  set σv : Option RSt := σvE.eval ρ
  have h0 : (Expr.pair tE (.pair ikE σvE)).eval ρ = (t, Ik, σv) := rfl
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := (.prod .nat (.prod (.base .i) (.opt (.base .sig))) : Ty S))
    (t, Ik, σv) ρ
  rw [eval_ite]
  have hlt1 : (Expr.lt (.nat mo.tStar) (.fst (Expr.v0 (O := OO)))).eval ρ₁ =
      decide (mo.tStar < t) := rfl
  rw [hlt1]
  by_cases hgt : mo.tStar < t
  · simp only [hgt, decide_true, ↓reduceIte]
    rcases σv with _ | σ <;>
      simp [ρ₁, Comp.eval, StateT.run_pure, hPrngUp, Expr.eval, Expr.v0, Expr.v1]
  · simp only [hgt, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [eval_ite]
    have heq1 : (Expr.eqN (.fst (Expr.v0 (O := OO))) (.nat mo.tStar)).eval ρ₁ =
        decide (t = mo.tStar) := rfl
    rw [heq1]
    by_cases hts : t = mo.tStar
    · have htsIf : (t = mo.tStar) ↔ True := by simp [hts]
      simp only [htsIf, decide_true, ↓reduceIte]
      rw [eval_ite]
      have hcond2 : (Expr.and (.bool mo.tL.isSome)
          (.eqN (.fst (Expr.v0 (O := OO))) (.nat mo.tH))).eval ρ₁ =
          (mo.tL.isSome && decide (t = mo.tH)) := rfl
      rw [hcond2]
      by_cases htH : (mo.tL.isSome && decide (t = mo.tH)) = true
      · simp only [htH, ↓reduceIte, eval_bind, query_challPrng_eval,
          liftP, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]
        refine bind_congr fun k? => ?_
        rcases k? with _ | k
        · simp [Comp.eval, StateT.run_pure, Expr.eval, Expr.v0]
        · simp only [eval_caseOpt, Expr.eval, Expr.v0, Env.get_cons_zero, eval_bind,
            query_prngCorr_eval, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]
          refine bind_congr fun σ? => ?_
          rcases σ? with _ | σ'
          · simp [Comp.eval, StateT.run_pure, Expr.eval]
          · simp [Comp.eval, StateT.run_pure, Expr.eval, Expr.v2]
      · simp only [htH, Bool.false_eq_true, ↓reduceIte, eval_bind, query_challPrf_eval,
          liftP, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]
        have hIk : (Expr.fst (.snd (Expr.v0 (O := OO)))).eval ρ₁ = Ik := rfl
        rw [hIk]
        refine bind_congr fun ans => ?_
        rcases ans with _ | ⟨σ', k⟩ <;>
          simp [ρ₁, Comp.eval, StateT.run_pure, Expr.eval, Expr.v0]
    · simp only [hts, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [eval_ite]
      have hcond3 : (Expr.and (.bool mo.tL.isSome)
          (.eqN (.fst (Expr.v0 (O := OO))) (.nat mo.tH))).eval ρ₁ =
          (mo.tL.isSome && decide (t = mo.tH)) := rfl
      rw [hcond3]
      by_cases htH : (mo.tL.isSome && decide (t = mo.tH)) = true
      · simp only [htH, ↓reduceIte, eval_bind, query_process_eval,
          liftP, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]
        have hNone : (Expr.none (O := OO) (t := .base .i)).eval ρ₁ = none := rfl
        rw [hNone]
        refine bind_congr fun k? => ?_
        rcases k? with _ | k <;>
          simp [Comp.eval, StateT.run_pure, Expr.eval, Expr.v0]
      · simp only [htH, Bool.false_eq_true, ↓reduceIte]
        rw [eval_ite]
        have hcond4 : (Expr.and (.bool mo.tL.isSome)
            (.lt (.fst (Expr.v0 (O := OO))) (.nat mo.tH))).eval ρ₁ =
            (mo.tL.isSome && decide (t < mo.tH)) := rfl
        rw [hcond4]
        by_cases hltH : (mo.tL.isSome && decide (t < mo.tH)) = true
        · simp only [hltH, ↓reduceIte]
          exact prngProcessCorrC_eval (.some (.fst (.snd .v0))) ρ₁ (some Ik) rfl h
        · simp only [hltH, Bool.false_eq_true, ↓reduceIte, eval_bind, query_process_eval,
            liftP, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]
          have hSomeIk : (Expr.some (.fst (.snd (Expr.v0 (O := OO))))).eval ρ₁ = some Ik := rfl
          rw [hSomeIk]
          refine bind_congr fun k? => ?_
          rcases k? with _ | k <;>
            simp [ρ₁, Comp.eval, StateT.run_pure, Expr.eval, Expr.v0]

theorem prngStartSendC_eval [DecidableEq T] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hSend : ckaSend = cka.send)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (mo : Mode)
    {Γ'} (hE : Expr OO Γ' prngHsTy) (ctxE : Expr OO Γ' (cGsTy prngVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ)) (σvE : Expr OO Γ' (.opt (.base .sig)))
    (rE : Expr OO Γ' (.opt (.base .ccoins))) (ρ : Env Γ')
    (h : PRNGState T RSt K) (ctx : Ctx Γ T (Option RSt) SS RS M E) (P : Party)
    (hh : hE.eval ρ = prngHsEnc h) :
    (prngStartSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) mo hE ctxE pE tE γE σvE rE).eval ρ =
      Prod.map id prngHsEnc <$>
        ((hooksPRNG cka prng fs mo).startSend ctx P
          (tE.eval ρ) (γE.eval ρ) (σvE.eval ρ) (rE.eval ρ)).run h := by
  unfold prngStartSendC
  rw [eval_bind_ret]
  set t : ℕ := tE.eval ρ
  set γ : Γ := γE.eval ρ
  set σv : Option RSt := σvE.eval ρ
  set r : Option CCoins := rE.eval ρ
  have h0 : (Expr.pair hE (.pair tE (.pair γE (.pair σvE rE)))).eval ρ =
      (prngHsEnc h, t, γ, σv, r) := by
    simp [Expr.eval, hh, t, γ, σv, r]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := (.prod prngHsTy (.prod .nat (.prod (.base .γ)
      (.prod (.opt (.base .sig)) (.opt (.base .ccoins))))) : Ty S))
    (prngHsEnc h, t, γ, σv, r) ρ
  have hStep1 :
      (Comp.caseOpt (O := OO) (I := II) (.snd (.snd (.snd (.snd .v0))))
        (@Comp.sample _ _ _ OO II _ CKASamp.ccoins .unit)
        (.ret .v0)).eval ρ₁ =
      (match r with
        | some c => pure c
        | none => (sampleT CCoins : TComp (PRFPRNG.spec RSt I K) CCoins)) := by
    rcases r with _ | c
    · simp only [ρ₁, Comp.eval, Expr.eval, Expr.v0, Env.get_cons_zero,
        prngIface, prngSamplers, ckaSamplers, hSampCCoins, sampleT]
      exact liftP_eq_liftM II (fun _ => rfl) ($ᵗ CCoins)
    · rfl
  have hRHS :
      ((hooksPRNG cka prng fs mo).startSend ctx P t γ σv r).run h =
      ((match r with
          | some c => pure c
          | none => (sampleT CCoins : TComp (PRFPRNG.spec RSt I K) CCoins)) >>= fun coins =>
        (do
          let x ← rootPRNG prng mo t (cka.send γ coins).2.2 σv
          match x with
          | none => return none
          | some (σ', k) =>
            modify fun (s : PRNGState T RSt K) =>
              { cache := Function.update s.cache t (some ((cka.send γ coins).2.1, σ', k)) }
            return some ((cka.send γ coins).1, (cka.send γ coins).2.1, σ',
              fs.initSender k)).run h) := by
    rcases r with _ | c
    · simp only [hooksPRNG, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]; rfl
    · simp only [hooksPRNG, StateT.run_bind, pure_bind]; rfl
  rw [eval_bind, hStep1, hRHS, map_bind]
  refine bind_congr fun coins => ?_
  set ρ₂ := Env.cons (t := (.base .ccoins : Ty S)) coins ρ₁
  rw [eval_bind]
  have hRoot := rootPRNGC_eval (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    prng hPrngUp mo (.fst (.snd .v1))
    (.snd (.snd (Expr.op (O := OO) CKAOp.ckaSend (.pair (.fst (.snd (.snd .v1))) .v0))))
    (.fst (.snd (.snd (.snd .v1)))) ρ₂ h
  have hRootArgs :
      ((Expr.fst (.snd (Expr.v1 (O := OO)))).eval ρ₂ = t) ∧
      ((Expr.snd (.snd (Expr.op (O := OO) CKAOp.ckaSend
        (.pair (.fst (.snd (.snd .v1))) .v0)))).eval ρ₂ = (cka.send γ coins).2.2) ∧
      ((Expr.fst (.snd (.snd (.snd (Expr.v1 (O := OO)))))).eval ρ₂ = σv) := by
    refine ⟨rfl, ?_, rfl⟩
    simp [ρ₂, ρ₁, hSend, Expr.eval, Expr.v0, Expr.v1]
  rw [hRootArgs.1, hRootArgs.2.1, hRootArgs.2.2] at hRoot
  rw [StateT.run_bind, hRoot, bind_map_left, map_bind]
  refine bind_congr fun step => ?_
  rcases step with _ | ⟨σ', k⟩
  · simp [ρ₂, ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v2]
  · simp only [eval_caseOpt, StateT.run_bind, StateT.run_modify, StateT.run_pure,
      pure_bind, map_pure, Prod.map, id_eq]
    set ρ₃ := Env.cons (t := (.prod (.opt (.base .sig)) (.base .k) : Ty S)) (σ', k)
      (Env.cons (t := (.opt (.prod (.opt (.base .sig)) (.base .k)) : Ty S)) (some (σ', k)) ρ₂)
    change (Comp.ret _).eval ρ₃ = _
    have hTset := tset_eval_eq_update (O' := OO)
      (.fst .v3) (.fst (.snd .v3))
      (.some (.pair
        (.fst (.snd (Expr.op (O := OO) CKAOp.ckaSend (.pair (.fst (.snd (.snd .v3))) .v2))))
        (.pair (.fst .v0) (.snd .v0)))) ρ₃
    simp only [eval_ret, pair_eval, some_eval, hTset]
    simp [ρ₃, ρ₂, ρ₁, hSend, hFsInitS, prngHsEnc,
      Expr.eval, Expr.v0, Expr.v2, Expr.v3]

theorem prngStartRecvC_eval [DecidableEq T] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hRecv : ckaReceive = cka.receive)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (heqT : eqT = (· == ·))
    (mo : Mode)
    {Γ'} (hE : Expr OO Γ' prngHsTy) (ctxE : Expr OO Γ' (cGsTy prngVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ)) (σvE : Expr OO Γ' (.opt (.base .sig)))
    (tnE : Expr OO Γ' (.base .t)) (ρ : Env Γ')
    (h : PRNGState T RSt K) (ctx : Ctx Γ T (Option RSt) SS RS M E) (P : Party)
    (hh : hE.eval ρ = prngHsEnc h) :
    (prngStartRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) mo hE ctxE pE tE γE σvE tnE).eval ρ =
      Prod.map id prngHsEnc <$>
        ((hooksPRNG cka prng fs mo).startRecv ctx P
          (tE.eval ρ) (γE.eval ρ) (σvE.eval ρ) (tnE.eval ρ)).run h := by
  unfold prngStartRecvC hooksPRNG
  dsimp only
  rw [eval_bind_ret]
  set t : ℕ := tE.eval ρ
  set γ : Γ := γE.eval ρ
  set Tn : T := tnE.eval ρ
  have h0 : (Expr.pair hE (.pair tE (.pair γE tnE))).eval ρ = (prngHsEnc h, t, γ, Tn) := by
    simp [Expr.eval, hh, t, γ, Tn]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := (.prod prngHsTy (.prod .nat (.prod (.base .γ) (.base .t))) : Ty S))
    (prngHsEnc h, t, γ, Tn) ρ
  rw [eval_caseOpt]
  have hHonest :
      (Expr.caseOpt (.tget (.fst (Expr.v0 (O := OO))) (.fst (.snd .v0))) .none
        (.ite (Expr.op (O := OO) CKAOp.eqT (.pair (.fst .v0) (.snd (.snd (.snd .v1)))))
          (.some (.snd .v0)) .none)).eval ρ₁ =
      (match h.cache t with
        | some (Tc, σc, k) => if Tc = Tn then some (σc, k) else none
        | none => none) := by
    simp only [ρ₁, prngHsEnc, heqT, Expr.eval, Expr.v0, Expr.v1,
      Env.get_cons_zero, Env.get_cons_succ, BEq.beq]
    rcases h.cache t with _ | ⟨Tc, σc, k⟩
    · rfl
    · by_cases hEq : Tc = Tn <;> simp [hEq]
  rw [hHonest]; clear hHonest
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  have hNoneBranch :
      (Comp.ite (I := II) (.and (.bool mo.auth) (.eqN (.fst (.snd .v0)) (.nat mo.tStar)))
        (.bind (@Comp.query _ _ _ OO II _ PRNGTag.challPrf
            (.snd (Expr.op (O := OO) CKAOp.ckaReceive
              (.pair (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))))))
          (.caseOpt .v0
            (.ret (.pair .none (.fst .v1)))
            (.ret (.pair
              (.some (.some (.pair
                (.fst (Expr.op (O := OO) CKAOp.ckaReceive
                  (.pair (.fst (.snd (.snd .v2))) (.snd (.snd (.snd .v2))))))
                (.pair (.some (.fst .v0))
                  (Expr.op (O := OO) CKAOp.fsInitReceiver (.snd .v0))))))
              (.fst .v2)))))
        (.ret (.pair (.some .none) (.fst .v0)))).eval ρ₁ =
      Prod.map id prngHsEnc <$>
        ((if mo.auth && t = mo.tStar then do
          let kk := cka.receive γ Tn
          match ← liftP (PRFPRNG.challPrfQuery kk.2) with
          | none => pure none
          | some (σ', k') => pure (some (some (kk.1, some σ', fs.initReceiver k')))
        else pure (some none) :
          HM (PRFPRNG.spec RSt I K) (PRNGState T RSt K)
            (Option (Option (Γ × Option RSt × RS)))).run h) := by
    rw [eval_ite]
    have hAuthCond :
        (Expr.and (.bool mo.auth) (.eqN (.fst (.snd (Expr.v0 (O := OO)))) (.nat mo.tStar))).eval
          ρ₁ = (mo.auth && decide (t = mo.tStar)) := rfl
    rw [hAuthCond]
    by_cases hAuth : (mo.auth && decide (t = mo.tStar)) = true
    · simp only [hAuth, ↓reduceIte, eval_bind, query_challPrf_eval,
        liftP, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]
      have hkk : (Expr.snd (Expr.op (O := OO) CKAOp.ckaReceive
          (.pair (.fst (.snd (.snd (Expr.v0 (O := OO))))) (.snd (.snd (.snd .v0)))))).eval ρ₁ =
          (cka.receive γ Tn).2 := by
        simp [ρ₁, hRecv, Expr.eval, Expr.v0]
      rw [hkk]
      refine bind_congr fun ans => ?_
      rcases ans with _ | ⟨σ', k'⟩ <;>
        simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, hRecv, hFsInitR,
          Expr.eval, Expr.v0, Expr.v1, Expr.v2]
    · simp [hAuth, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, ρ₁]
  rcases h.cache t with _ | ⟨Tc, σc, k⟩
  · dsimp only
    exact hNoneBranch
  · by_cases hEq : Tc = Tn
    · simp [hEq, ρ₁, Comp.eval, StateT.run_pure, Prod.map, hRecv, hFsInitR,
        Expr.eval, Expr.v0, Expr.v1]
    · simp only [hEq, ↓reduceIte]
      exact hNoneBranch

theorem prngRevealC_eval [DecidableEq T] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (mo : Mode)
    {Γ'} (hE : Expr OO Γ' prngHsTy) (ctxE : Expr OO Γ' (cGsTy prngVpTy))
    (pE : Expr OO Γ' .bool) (vpE : Expr OO Γ' prngVpTy) (ρ : Env Γ')
    (h : PRNGState T RSt K) (ctx : Ctx Γ T (Option RSt) SS RS M E) (P : Party)
    (vp : VP Γ T (Option RSt) SS RS)
    (hh : hE.eval ρ = prngHsEnc h) (hvp : vpE.eval ρ = prngVpEnc vp) :
    (prngRevealC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) hE ctxE pE vpE).eval ρ =
      Prod.map (Option.map ckaPsEnc) prngHsEnc <$>
        ((hooksPRNG cka prng fs mo).reveal ctx P vp).run h := by
  unfold prngRevealC hooksPRNG
  dsimp only
  rw [eval_bind_ret]
  have h0 : (Expr.pair hE vpE).eval ρ = (prngHsEnc h, prngVpEnc vp) := by
    simp [Expr.eval, hh, hvp]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := (.prod prngHsTy prngVpTy : Ty S)) (prngHsEnc h, prngVpEnc vp) ρ
  rw [eval_caseOpt]
  have hRoot : (vpRoot (.snd (Expr.v0 (O := OO)))).eval ρ₁ = vp.root := rfl
  rw [hRoot]
  rcases vp.root with _ | σ
  · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
  · simp only [StateT.run_pure, map_pure, Prod.map, Option.map_some]
    set ρ₂ := Env.cons (t := (.base .sig : Ty S)) σ ρ₁
    change (Comp.ret _).eval ρ₂ = _
    have hReal := realPartyE_eval (O' := OO)
      (.snd .v1) (vpΓ (.snd .v1)) .v0
      (vpVS (.snd .v1)) (vpVR (.snd .v1)) ρ₂ vp rfl
    simp only [eval_ret, pair_eval, some_eval, hReal]
    rfl

/-! ## Costed initialization and reduction programs -/

def abortedParties (γA γB : Γ) :
    VP Γ T (Option RSt) SS RS × VP Γ T (Option RSt) SS RS :=
  ({ id := .A, root := none, vS := none, vR := fun _ => none, γ := γA, curCkaMsg := none, tcur := 0 },
   { id := .B, root := none, vS := none, vR := fun _ => none, γ := γB, curCkaMsg := none, tcur := 0 })

def abortedPartiesE {Γ'} (γAE γBE : Expr OO Γ' (.base .γ)) :
    Expr OO Γ' (.prod prngVpTy prngVpTy) :=
  rdslExpr =>
    (vpMk (bool (partyEnc .A)) none none (tconst none) γAE none 0,
     vpMk (bool (partyEnc .B)) none none (tconst none) γBE none 0)

@[simp] theorem abortedPartiesE_eval {Γ'} (γAE γBE : Expr OO Γ' (.base .γ)) (ρ : Env Γ') :
    (abortedPartiesE γAE γBE).eval ρ =
      Prod.map prngVpEnc prngVpEnc
        (abortedParties (T := T) (RSt := RSt) (SS := SS) (RS := RS)
          (γAE.eval ρ) (γBE.eval ρ)) := by
  simp [abortedPartiesE, abortedParties, vpMk, prngVpEnc, vpTblEnc, vpEnc, Prod.map, Expr.eval]

def initPRNGRaw [SampleableType KC]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (mo : Mode) (b : Bool) :
    PRFPRNG.AdversaryComp RSt I K
      (EState (VP Γ T (Option RSt) SS RS) M (Header T × E) (PRNGState T RSt K)) := do
  let kc ← sampleT KC
  let (step, h₀) ← (rootPRNG prng mo 0 lam none).run {}
  match step with
  | none =>
    let (vA, vB) := abortedParties (T := T) (RSt := RSt) (SS := SS) (RS := RS)
      (cka.initA kc) (cka.initB kc)
    pure { g := { st := fun | .A => vA | .B => vB, b := b }, h := h₀, abort := true }
  | some (σv, k) =>
    let (vA, vB) := mkParties (T := T) (cka.initA kc) (cka.initB kc) σv
      (fs.initSender k) (fs.initReceiver k)
    pure { g := { st := fun | .A => vA | .B => vB, b := b }, h := h₀, abort := false }

def initPRNGEStateC (mo : Mode) {Γ'} (bE : Expr OO Γ' .bool) : Comp OO II Γ' prngEsTy :=
  rdsl do
    b0 ← return bE
    kc ← sample (O := OO) (I := II) CKASamp.kc ()
    stepOpt ← rootPRNGC mo 0 (Expr.op (O := OO) CKAOp.lamI ()) none
    match stepOpt with
    | none =>
      let parties :=
        abortedPartiesE
          (Expr.op (O := OO) CKAOp.ckaInitA kc)
          (Expr.op (O := OO) CKAOp.ckaInitB kc)
      let g0 := cGsInitE parties.1 parties.2 b0
      return (esMk g0 (tconst none) true)
    | some (σv, kVal) =>
      let parties :=
        mkPartiesE
          (Expr.op (O := OO) CKAOp.ckaInitA kc)
          (Expr.op (O := OO) CKAOp.ckaInitB kc) σv
          (Expr.op (O := OO) CKAOp.fsInitSender kVal)
          (Expr.op (O := OO) CKAOp.fsInitReceiver kVal)
      let g0 := cGsInitE parties.1 parties.2 b0
      return (esMk g0 (tconst none) false)

theorem initPRNGEStateC_eval [SampleableType KC]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hInitA : ckaInitA = cka.initA)
    (hInitB : ckaInitB = cka.initB)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (mo : Mode) {Γ'} (bE : Expr OO Γ' .bool) (ρ : Env Γ') :
    (initPRNGEStateC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) mo bE).eval ρ =
      esEnc prngVpEnc prngHsEnc <$> initPRNGRaw cka prng fs lam mo (bE.eval ρ) := by
  unfold initPRNGEStateC initPRNGRaw
  rw [eval_bind_ret]
  set b := bE.eval ρ
  set ρ₁ := Env.cons (t := (.bool : Ty S)) b ρ
  rw [eval_bind, map_bind]
  have hKC : (@Comp.sample _ _ _ OO II _ CKASamp.kc .unit).eval ρ₁ = sampleT KC := by
    simp only [Comp.eval, prngIface, prngSamplers, ckaSamplers, hSampKC, sampleT]
    exact liftP_eq_liftM II (fun _ => rfl) ($ᵗ KC)
  rw [hKC]
  refine bind_congr fun kc => ?_
  set ρ₂ := Env.cons (t := (.base .kc : Ty S)) kc ρ₁
  rw [eval_bind, map_bind]
  have hRoot := rootPRNGC_eval (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    prng hPrngUp mo (.nat 0) (Expr.op (O := OO) CKAOp.lamI .unit) .none ρ₂ ({} : PRNGState T RSt K)
  simp only [Expr.eval] at hRoot
  rw [hRoot, bind_map_left]
  refine bind_congr fun step => ?_
  rcases step with _ | ⟨σv, k⟩
  · simp only [eval_caseOpt, map_pure]
    set ρ₃ := Env.cons (t := (.opt (.prod (.opt (.base .sig)) (.base .k)) : Ty S)) none ρ₂
    change (Comp.ret _).eval ρ₃ = _
    rw [eval_ret]
    set pAB := abortedParties (T := T) (RSt := RSt) (SS := SS) (RS := RS)
      (cka.initA kc) (cka.initB kc)
    have hAbP := abortedPartiesE_eval
      (Expr.op (O := OO) CKAOp.ckaInitA .v1) (Expr.op (O := OO) CKAOp.ckaInitB .v1) ρ₃
    have hAbP' :
        (abortedPartiesE
          (Expr.op (O := OO) CKAOp.ckaInitA .v1)
          (Expr.op (O := OO) CKAOp.ckaInitB .v1)).eval ρ₃ =
          (prngVpEnc pAB.1, prngVpEnc pAB.2) := by
      rw [hAbP]
      simp [ρ₃, ρ₂, ρ₁, hInitA, hInitB, pAB, Prod.map, Expr.eval, Expr.v1]
    have hGs := cGsInitE_eval prngVpEnc (O' := OO)
      (.fst (abortedPartiesE
        (Expr.op (O := OO) CKAOp.ckaInitA .v1) (Expr.op (O := OO) CKAOp.ckaInitB .v1)))
      (.snd (abortedPartiesE
        (Expr.op (O := OO) CKAOp.ckaInitA .v1) (Expr.op (O := OO) CKAOp.ckaInitB .v1)))
      .v2 ρ₃ pAB.1 pAB.2
      (by simp [Expr.eval, hAbP']) (by simp [Expr.eval, hAbP'])
    simp only [esMk, pair_eval, hGs]
    rfl
  · simp only [eval_caseOpt, map_pure]
    set ρ₃ := Env.cons (t := (.prod (.opt (.base .sig)) (.base .k) : Ty S)) (σv, k)
      (Env.cons (t := (.opt (.prod (.opt (.base .sig)) (.base .k)) : Ty S)) (some (σv, k)) ρ₂)
    change (Comp.ret _).eval ρ₃ = _
    rw [eval_ret]
    set pAB := mkParties (T := T) (cka.initA kc) (cka.initB kc) σv
      (fs.initSender k) (fs.initReceiver k)
    have hMkP := mkPartiesE_eval (O' := OO)
      (Expr.op (O := OO) CKAOp.ckaInitA .v2) (Expr.op (O := OO) CKAOp.ckaInitB .v2)
      (.fst .v0)
      (Expr.op (O := OO) CKAOp.fsInitSender (.snd .v0))
      (Expr.op (O := OO) CKAOp.fsInitReceiver (.snd .v0)) ρ₃
    have hMkP' :
        (mkPartiesE (O' := OO)
          (Expr.op (O := OO) CKAOp.ckaInitA .v2)
          (Expr.op (O := OO) CKAOp.ckaInitB .v2)
          (.fst .v0)
          (Expr.op (O := OO) CKAOp.fsInitSender (.snd .v0))
          (Expr.op (O := OO) CKAOp.fsInitReceiver (.snd .v0))).eval ρ₃ =
          (prngVpEnc pAB.1, prngVpEnc pAB.2) := by
      rw [hMkP]
      simp [ρ₃, ρ₂, ρ₁, hInitA, hInitB, hFsInitS, hFsInitR, pAB, Prod.map,
        Expr.eval, Expr.v0, Expr.v2]
    have hGs := cGsInitE_eval prngVpEnc (O' := OO)
      (.fst (mkPartiesE
        (Expr.op (O := OO) CKAOp.ckaInitA .v2)
        (Expr.op (O := OO) CKAOp.ckaInitB .v2)
        (.fst .v0)
        (Expr.op (O := OO) CKAOp.fsInitSender (.snd .v0))
        (Expr.op (O := OO) CKAOp.fsInitReceiver (.snd .v0))))
      (.snd (mkPartiesE
        (Expr.op (O := OO) CKAOp.ckaInitA .v2)
        (Expr.op (O := OO) CKAOp.ckaInitB .v2)
        (.fst .v0)
        (Expr.op (O := OO) CKAOp.fsInitSender (.snd .v0))
        (Expr.op (O := OO) CKAOp.fsInitReceiver (.snd .v0))))
      .v3 ρ₃ pAB.1 pAB.2
      (by simp [Expr.eval, hMkP']) (by simp [Expr.eval, hMkP'])
    simp only [esMk, pair_eval, hGs]
    rfl

theorem SMEngineInv.aborted {γA γB : Γ} (b : Bool) {L B : ℕ}
    (hB1 : B + 1 ≤ L) (hBB : B * B ≤ L * L) :
    SMEngineInv L B B
      ({ st := fun
           | .A => (abortedParties (T := T) (RSt := RSt) (SS := SS) (RS := RS) γA γB).1
           | .B => (abortedParties (T := T) (RSt := RSt) (SS := SS) (RS := RS) γA γB).2
         b := b } : Ctx Γ T (Option RSt) SS RS M E) :=
  SMEngineInv.init _ b hB1 hBB

theorem initPRNGRaw_inv [SampleableType KC]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (mo : Mode) (b : Bool)
    {L B qAdv : ℕ} (hqB : qAdv ≤ B) (hB1 : B + 1 ≤ L) (hBB : B * B ≤ L * L) :
    ∀ es₀ ∈ support (initPRNGRaw cka prng fs lam mo b),
      SMEngineInv L B qAdv es₀.g ∧ es₀.g.b = b := by
  intro es₀ hmem
  unfold initPRNGRaw at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨kc, _, hmem⟩ := hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨⟨step, h₀⟩, _, hmem⟩ := hmem
  rcases step with _ | ⟨σv, k⟩
  · simp only [support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    exact ⟨(SMEngineInv.aborted b hB1 hBB).mono hqB, rfl⟩
  · simp only [support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    exact ⟨(SMEngineInv.init _ b hB1 hBB).mono hqB, rfl⟩

/-- Costed `redPRNGAuth` reduction (`B2` for authenticity, ACD19 Lemma 10). -/
def redPRNGAuthProg (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (t : ℕ) :
    CostedReduction OO II
      (SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E)
      .unit .unit .bool .bool where
  σ := prngEsTy
  init := rdsl [_] do
    es ← initPRNGEStateC (raw ⟨true, tL, t⟩) false
    return ((), es)
  handle := rdsl [es, q] do
    implEC (raw (hooksPRNGC B ⟨true, tL, t⟩)) L (raw (2 + Δcka)) qep maxSkip
      (raw (modeCfgEC OO ⟨true, tL, t⟩)) (raw (⟨true, tL, t⟩ : Mode).policy) es q
  finish := rdsl [es, _] do
    return (authOutE L (raw (2 + Δcka)) (raw (⟨true, tL, t⟩ : Mode).policy) es)

/-- Costed `redPRNGPriv` reduction (`B2` for privacy, ACD19 Lemma 14). -/
def redPRNGPrivProg (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (t : ℕ) :
    CostedReduction OO II
      (SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E)
      .unit .unit .bool .bool where
  σ := prngEsTy
  init := rdsl [_] do
    b ← sample (O := OO) (I := II) CKASamp.bit ()
    es ← initPRNGEStateC (raw ⟨false, tL, t⟩) b
    return ((), es)
  handle := rdsl [es, q] do
    implEC (raw (hooksPRNGC B ⟨false, tL, t⟩)) L (raw (2 + Δcka)) qep maxSkip
      (raw (modeCfgEC OO ⟨false, tL, t⟩)) (raw (⟨false, tL, t⟩ : Mode).policy) es q
  finish := rdsl [es, guess] do
    privOutC L (raw (2 + Δcka)) (raw (⟨false, tL, t⟩ : Mode).policy)
      (raw (fun {Γ''} => rdsl do sample (O := OO) (I := II) (Γ := Γ'') CKASamp.bit ()))
      (cGsB (esG es)) guess es

def prngStartRecvMainC {Γ'}
    (hE : Expr OO Γ' prngHsTy)
    (_ctxE : Expr OO Γ' (cGsTy prngVpTy))
    (_pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ))
    (_σvE : Expr OO Γ' (.opt (.base .sig)))
    (tnE : Expr OO Γ' (.base .t)) :
    Comp OO II Γ'
      (.prod (.opt (.opt (.prod (.base .γ) (.prod (.opt (.base .sig)) (.base .rs)))))
        prngHsTy) :=
  rdsl do
    (h0, t0, γ0, tn0) ← return (hE, tE, γE, tnE)
    let honest :=
      match tget h0 t0 with
      | none => none
      | some (tCached, entry) =>
        if Expr.op (O := OO) CKAOp.eqT (tCached, tn0) then some entry else none
    match honest with
    | none => return (some none, h0)
    | some (σc, kVal) =>
      let γ' := (Expr.op (O := OO) CKAOp.ckaReceive (γ0, tn0)).1
      let rs := Expr.op (O := OO) CKAOp.fsInitReceiver kVal
      return (some (some (γ', σc, rs)), h0)

def hooksPRNGMainC (B : ℕ) (mo : Mode) :
    HooksC OO II (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs) prngHsTy where
  startSend := prngStartSendC mo
  startRecv := prngStartRecvMainC
  fsSend := prngFsSendC
  fsRecv := prngFsRecvC B
  commit := prngCommitC
  reveal := prngRevealC

def isHonestHdrPRNGE {Γ'} (hE : Expr OO Γ' prngHsTy) (hdrE : Expr OO Γ' hdrTy) : Expr OO Γ' .bool :=
  rdslExpr =>
    letE (hE, hdrE) fun (h0, hdr0) =>
      match tget h0 hdr0.1 with
      | none => false
      | some (tCached, _) =>
        match hdr0.2 with
        | none => false
        | some tn0 => Expr.op (O := OO) CKAOp.eqT (tCached, tn0)

@[reducible] def prngStage2EsTy : Ty S := .prod prngEsTy .bool

/-- Stage-2 coin-averaged (`main` / `forgedHdr`) `redPRNGAuth` reduction at `(tL, t)`. -/
def redPRNGAuthStage2Prog (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (t : ℕ) :
    CostedReduction OO II
      (SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E)
      .unit .unit .bool .bool where
  σ := prngStage2EsTy
  init := rdsl [_] do
    forgedMode ← sample (O := OO) (I := II) CKASamp.bit ()
    es ← initPRNGEStateC (raw ⟨true, tL, t⟩) false
    return ((), (es, forgedMode))
  handle := rdsl [st, q] do
    (es0, forgedMode, q0) ← return (st.1, st.2, q)
    if forgedMode then
      let wasWin := cGsWin (esG es0)
      (out, es') ← implEC (raw (hooksPRNGC B ⟨true, tL, t⟩)) L (raw (2 + Δcka)) qep maxSkip
        (raw (modeCfgEC OO ⟨true, tL, t⟩)) (raw (⟨true, tL, t⟩ : Mode).policy) es0 q0
      let suppressHonestWin :=
        match q0 with
        | .inl qL =>
          match qL with
          | .inl _ => false
          | .inr x => isHonestHdrPRNGE (esH es0) x.2.1
        | .inr _ => false
      let esFinal :=
        if !wasWin && cGsWin (esG es') && suppressHonestWin then
          esSetG es' (cGsSetWin (esG es') false)
        else es'
      return (out, (esFinal, forgedMode))
    else
      (out, es') ← implEC (raw (hooksPRNGMainC B ⟨true, tL, t⟩)) L (raw (2 + Δcka)) qep maxSkip
        (raw (modeCfgEC OO ⟨true, tL, t⟩)) (raw (⟨true, tL, t⟩ : Mode).policy) es0 q0
      return (out, (es', forgedMode))
  finish := rdsl [st, _] do
    return (authOutE L (raw (2 + Δcka)) (raw (⟨true, tL, t⟩ : Mode).policy) st.1)

/-! ## Evaluation bridge theorems -/

private theorem simulateQ_liftM_unif {ι : Type} {tspec : OracleSpec.{0, 0} ι} {St α : Type}
    (impl : QueryImpl tspec (StateT St ProbComp)) (mx : ProbComp α) :
    simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl)
      (liftM mx : TComp tspec α) =
    StateT.lift mx := by
  ext st
  change (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl)
    (liftM mx : TComp tspec α)).run st = (mx >>= fun a => pure (a, st))
  rw [← liftComp_eq_liftM]
  induction mx using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t r ih =>
    rw [liftComp_bind, liftComp_liftM_query]
    have hq : (liftM (OracleSpec.query t) : TComp tspec _) =
        (liftM (OracleSpec.query (spec := unifSpec + tspec) (.inl t)) : TComp tspec _) := rfl
    have hrun :
        ((liftM ((QueryImpl.liftTarget (StateT St ProbComp)
          (QueryImpl.ofLift unifSpec ProbComp) + impl)
          (.inl t)) : StateT St ProbComp (unifSpec.Range t))).run st =
        ((liftM (OracleSpec.query t) : ProbComp _) >>= fun u => pure (u, st)) := rfl
    rw [hq, simulateQ_query_bind]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, StateT.run_bind]
    rw [hrun]
    simp only [bind_assoc, pure_bind, ih]

private theorem simulateQ_sampleT_run {ι : Type} {tspec : OracleSpec.{0, 0} ι} {St α : Type}
    [SampleableType α] (impl : QueryImpl tspec (StateT St ProbComp)) (st : St) :
    (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl)
      (sampleT α)).run st =
    (($ᵗ α : ProbComp α) >>= fun a => pure (a, st)) := by
  unfold sampleT
  rw [simulateQ_liftM_unif]
  rfl

theorem rootPRNG_zero_support_some [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR RSt I K) (mo : Mode) (lam : I) (kr : KR) (b_prng : Bool)
    (step : Option (Option RSt × K)) (h₀ : PRNGState T RSt K)
    (sp : PRFPRNG.GameState RSt I K)
    (hmem : ((step, h₀), sp) ∈ support
      ((simulateQ
        ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (PRFPRNG.GameState RSt I K) ProbComp) + PRFPRNG.oracleImpl prng)
        ((rootPRNG (T := T) prng mo 0 lam none).run {})).run
        { σ := prng.init kr, b := b_prng })) :
    ∃ σv k, step = some (σv, k) ∧ h₀ = {} := by
  unfold rootPRNG processCorr liftP at hmem
  have h0_lt : ¬(mo.tStar < 0) := by omega
  have h0_tH : ∀ (hSome : mo.tL.isSome = true), 0 ≠ mo.tH ∧ 0 < mo.tH := by
    intro hSome
    rcases htL : mo.tL with _ | l
    · simp [htL] at hSome
    · simp [Mode.tH, healEpoch, htL]
  simp only [h0_lt, ↓reduceIte] at hmem
  by_cases hts : 0 = mo.tStar
  · have htsIf : (0 = mo.tStar) ↔ True := by simp [hts]
    have hcond' : (mo.tL.isSome && decide (0 = mo.tH)) = false := by
      cases hs : mo.tL.isSome
      · rfl
      · simp [(h0_tH hs).1]
    simp only [htsIf, hcond', Bool.false_eq_true, ↓reduceIte] at hmem
    cases b_prng
    · simp [PRFPRNG.challPrfQuery, PRFPRNG.oracleImpl, PRFPRNG.challPrfImpl,
        StateT.run_bind, StateT.run_pure, StateT.run_get, StateT.run_set, StateT.run_lift,
        simulateQ_bind, simulateQ_query, simulateQ_pure,
        map_eq_bind_pure_comp, bind_assoc] at hmem
      rcases hmem with ⟨⟨rfl, rfl⟩, _⟩
      exact ⟨_, _, rfl, rfl⟩
    · simp [PRFPRNG.challPrfQuery, PRFPRNG.oracleImpl, PRFPRNG.challPrfImpl, List.lookup,
        StateT.run_bind, StateT.run_pure, StateT.run_get, StateT.run_set, StateT.run_lift,
        StateT.run_modify, StateT.run_monadLift, monadLift_self,
        simulateQ_bind, simulateQ_query, simulateQ_pure,
        map_eq_bind_pure_comp, bind_assoc] at hmem
      rcases hmem with ⟨R', ⟨rfl, rfl⟩, _⟩
      exact ⟨_, _, rfl, rfl⟩
  · simp only [hts, ↓reduceIte] at hmem
    by_cases hs : mo.tL.isSome = true
    · have ⟨hne, hlt⟩ := h0_tH hs
      have hcond1 : (mo.tL.isSome && decide (0 = mo.tH)) = false := by simp [hs, hne]
      have hcond2 : (mo.tL.isSome && decide (0 < mo.tH)) = true := by simp [hs, hlt]
      simp only [hcond1, hcond2, Bool.false_eq_true, ↓reduceIte] at hmem
      simp [PRFPRNG.processQuery, PRFPRNG.corrQuery, PRFPRNG.oracleImpl, PRFPRNG.processImpl,
        PRFPRNG.corrImpl, PRFPRNG.samIfNec, StateT.run_bind, StateT.run_pure, StateT.run_lift,
        StateT.run_get, StateT.run_set, simulateQ_bind, simulateQ_query, simulateQ_pure,
        map_eq_bind_pure_comp, bind_assoc] at hmem
      rcases hmem with ⟨⟨rfl, rfl⟩, _⟩
      exact ⟨_, _, rfl, rfl⟩
    · have hcond1 : (mo.tL.isSome && decide (0 = mo.tH)) = false := by simp [hs]
      have hcond2 : (mo.tL.isSome && decide (0 < mo.tH)) = false := by simp [hs]
      simp only [hcond1, hcond2, Bool.false_eq_true, ↓reduceIte] at hmem
      simp [PRFPRNG.processQuery, PRFPRNG.oracleImpl, PRFPRNG.processImpl, PRFPRNG.samIfNec,
        StateT.run_bind, StateT.run_pure, StateT.run_lift, StateT.run_get, StateT.run_set,
        simulateQ_bind, simulateQ_query, simulateQ_pure, map_eq_bind_pure_comp, bind_assoc] at hmem
      rcases hmem with ⟨⟨rfl, rfl⟩, _⟩
      exact ⟨_, _, rfl, rfl⟩

/-! ## Query and cost bounds -/

@[simp] theorem prngProcessCorrC_queries {Γ'} (ikOptE : Expr OO Γ' (.opt (.base .i))) :
    (prngProcessCorrC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) ikOptE).queries
      (fun _ => 1) (fun _ => 0) = 2 := by
  simp [prngProcessCorrC, Comp.queries]

@[simp] theorem rootPRNGC_queries (mo : Mode) {Γ'}
    (tE : Expr OO Γ' .nat) (ikE : Expr OO Γ' (.base .i))
    (σvE : Expr OO Γ' (.opt (.base .sig))) :
    (rootPRNGC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) mo tE ikE σvE).queries
      (fun _ => 1) (fun _ => 0) = 2 := by
  simp [rootPRNGC, Comp.queries]

@[simp] theorem prngStartSendC_queries (mo : Mode) {Γ'}
    (hE : Expr OO Γ' prngHsTy) (ctxE : Expr OO Γ' (cGsTy prngVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ)) (σvE : Expr OO Γ' (.opt (.base .sig)))
    (rE : Expr OO Γ' (.opt (.base .ccoins))) :
    (prngStartSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) mo hE ctxE pE tE γE σvE rE).queries
      (fun _ => 1) (fun _ => 0) = 2 := by
  simp [prngStartSendC, Comp.queries]

@[simp] theorem prngStartRecvC_queries (mo : Mode) {Γ'}
    (hE : Expr OO Γ' prngHsTy) (ctxE : Expr OO Γ' (cGsTy prngVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ)) (σvE : Expr OO Γ' (.opt (.base .sig)))
    (tnE : Expr OO Γ' (.base .t)) :
    (prngStartRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) mo hE ctxE pE tE γE σvE tnE).queries
      (fun _ => 1) (fun _ => 0) = 1 := by
  simp [prngStartRecvC, Comp.queries]

@[simp] theorem prngFsSendC_queries {Γ'}
    (hE : Expr OO Γ' prngHsTy) (ctxE : Expr OO Γ' (cGsTy prngVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (ssE : Expr OO Γ' (.base .ss)) (hdrE : Expr OO Γ' hdrTy)
    (mE : Expr OO Γ' (.base .msg)) (pairE : Expr OO Γ' (.opt (.prod (.base .msg) (.base .msg)))) :
    (prngFsSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) hE ctxE pE tE ssE hdrE mE pairE).queries
      (fun _ => 1) (fun _ => 0) = 0 := by
  simp [prngFsSendC, Comp.queries]

@[simp] theorem prngFsRecvC_queries (B : ℕ) {Γ'}
    (hE : Expr OO Γ' prngHsTy) (ctxE : Expr OO Γ' (cGsTy prngVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (rsE : Expr OO Γ' (.base .rs)) (hdrE : Expr OO Γ' hdrTy)
    (eE : Expr OO Γ' (.base .ct)) (recE : Expr OO Γ' (.opt cRecTy)) :
    (prngFsRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B hE ctxE pE tE rsE hdrE eE recE).queries
      (fun _ => 1) (fun _ => 0) = 0 := by
  simp [prngFsRecvC, Comp.queries]

@[simp] theorem prngCommitC_queries {Γ'}
    (hE : Expr OO Γ' prngHsTy) (ctxE : Expr OO Γ' (cGsTy prngVpTy))
    (pE : Expr OO Γ' .bool) (oldE newE : Expr OO Γ' prngVpTy) :
    (prngCommitC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) hE ctxE pE oldE newE).queries
      (fun _ => 1) (fun _ => 0) = 0 := by
  simp [prngCommitC, Comp.queries]

@[simp] theorem prngRevealC_queries {Γ'}
    (hE : Expr OO Γ' prngHsTy) (ctxE : Expr OO Γ' (cGsTy prngVpTy))
    (pE : Expr OO Γ' .bool) (vpE : Expr OO Γ' prngVpTy) :
    (prngRevealC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) hE ctxE pE vpE).queries
      (fun _ => 1) (fun _ => 0) = 0 := by
  simp [prngRevealC, Comp.queries]

@[simp] theorem implEC_hooksPRNGC_queries (L B Δcka qep maxSkip : ℕ) (mo : Mode) {Γ'}
    (es : Expr OO Γ' prngEsTy)
    (q : Expr OO Γ' (ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E)) :
    (implEC (hooksPRNGC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B mo)
      L (2 + Δcka) qep maxSkip (modeCfgEC OO mo) mo.policy es q).queries
      (fun _ => 1) (fun _ => 0) = 2 := by
  simp [implEC, transmitEC, challEC, deliverEC, injectEC, corrEC,
    vSendC, vSendStep1C, vRecvC, vRecvStep1C, commitEC, hooksPRNGC, Comp.queries]

@[simp] theorem initPRNGEStateC_queries (mo : Mode) {Γ'} (bE : Expr OO Γ' .bool) :
    (initPRNGEStateC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) mo bE).queries (fun _ => 1) (fun _ => 0) = 2 := by
  simp [initPRNGEStateC, Comp.queries]

@[simp] theorem redPRNGAuthProg_totalQueries (L B Δcka qep maxSkip : ℕ)
    (tL : Option ℕ) (t q : ℕ) :
    (redPRNGAuthProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip tL t).totalQueries (fun _ => 1) (fun _ => 0) q = 2 + q * 2 := by
  simp [CostedReduction.totalQueries, redPRNGAuthProg, Comp.queries]

@[simp] theorem redPRNGPrivProg_totalQueries (L B Δcka qep maxSkip : ℕ)
    (tL : Option ℕ) (t q : ℕ) :
    (redPRNGPrivProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip tL t).totalQueries (fun _ => 1) (fun _ => 0) q = 2 + q * 2 := by
  simp [CostedReduction.totalQueries, redPRNGPrivProg, privOutC, Comp.queries]

theorem redPRNGAuthProg_totalCost (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (t q : ℕ) :
    (redPRNGAuthProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip tL t).totalCost q =
      (initPRNGEStateC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        ⟨true, tL, t⟩ (.bool false : Expr OO [.unit] .bool)).cost + 6 +
        q * ((implEC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
          (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (I' := II)
          (Γ' := [prngEsTy, ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E])
          (hooksPRNGC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
            (sampI := sampI) (sampK := sampK) B ⟨true, tL, t⟩)
          L (2 + Δcka) qep maxSkip (modeCfgEC OO ⟨true, tL, t⟩)
          (⟨true, tL, t⟩ : Mode).policy .v0 .v1).cost + 12) +
        (authOutE (O' := OO) L (2 + Δcka) (⟨true, tL, t⟩ : Mode).policy
          (Expr.v0 : Expr OO [prngEsTy, .bool] prngEsTy)).cost := by
  simp only [CostedReduction.totalCost, redPRNGAuthProg, prngSMCodec, ckaSMCodec, prngIface, Comp.cost,
    Expr.cost]
  have hV0 : (Expr.v0 : Expr OO [prngEsTy, .unit] prngEsTy).cost = 1 := rfl
  rw [hV0, max_eq_right (by omega)]
  omega

theorem redPRNGPrivProg_totalCost (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (t q : ℕ) :
    (redPRNGPrivProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip tL t).totalCost q =
      (initPRNGEStateC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        ⟨false, tL, t⟩ (Expr.v0 : Expr OO [.bool, .unit] .bool)).cost + 8 +
        q * ((implEC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
          (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (I' := II)
          (Γ' := [prngEsTy, ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E])
          (hooksPRNGC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
            (sampI := sampI) (sampK := sampK) B ⟨false, tL, t⟩)
          L (2 + Δcka) qep maxSkip (modeCfgEC OO ⟨false, tL, t⟩)
          (⟨false, tL, t⟩ : Mode).policy .v0 .v1).cost + 12) +
        (privOutC (O' := OO) (I' := II) (Γ' := [prngEsTy, .bool]) L (2 + Δcka)
          (⟨false, tL, t⟩ : Mode).policy
          (fun {Γ''} => @Comp.sample _ _ _ OO II Γ'' CKASamp.bit .unit)
          (cGsB (esG .v0)) .v1 .v0).cost := by
  simp only [CostedReduction.totalCost, redPRNGPrivProg, prngSMCodec, ckaSMCodec, prngIface, prngSamplers,
    ckaSamplers, Comp.cost, Expr.cost]
  have hV0 : (Expr.v0 : Expr OO [prngEsTy, .bool, .unit] prngEsTy).cost = 1 := rfl
  rw [hV0, max_eq_right (by omega)]
  omega

/-! ## Evaluation bridges for `FSAEAD.fromAEADPRG` -/

theorem hooksPRNG_startRecv_rs [DecidableEq T] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (mo : Mode)
    {VROk : RS → Prop} (hInitR : ∀ k, VROk (fs.initReceiver k))
    (ctx : Ctx Γ T (Option RSt) SS RS M E) (P : Party) (t : ℕ)
    (γ : Γ) (σv : Option RSt) (Tn : T) (h : PRNGState T RSt K) :
    ∀ res ∈ support (((hooksPRNG cka prng fs mo).startRecv ctx P t γ σv Tn).run h),
      ∀ γ' σ' rs, res.1 = some (some (γ', σ', rs)) → VROk rs := by
  intro ⟨ans, h'⟩ hmem γ' σ' rs hEq
  subst hEq
  unfold hooksPRNG at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  revert hmem
  rcases h.cache t with _ | ⟨Tc, σc, k⟩
  · intro hmem
    split_ifs at hmem
    · simp only [liftP, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨qres, _, hmem⟩ := hmem
      rcases qres with _ | ⟨σ', k'⟩
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
      · simp only [liftP, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
          mem_support_bind_iff] at hmem
        obtain ⟨qres, _, hmem⟩ := hmem
        rcases qres with _ | ⟨σ', k'⟩
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨h, _⟩; cases h
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq, Option.some.injEq] at hmem
          rcases hmem with ⟨⟨rfl, rfl, rfl⟩, rfl⟩; exact hInitR _
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq, Option.some.injEq] at hmem
        rcases hmem with ⟨h, _⟩; cases h

theorem hooksPRNG_commit_vR [DecidableEq T] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (mo : Mode)
    (ctx : Ctx Γ T (Option RSt) SS RS M E) (P : Party)
    (old new : VP Γ T (Option RSt) SS RS) (h : PRNGState T RSt K) :
    ∀ res ∈ support (((hooksPRNG cka prng fs mo).commit ctx P old new).run h),
      ∀ new', res.1 = some new' → new'.vR = new.vR := by
  intro ⟨ans, h'⟩ hmem new' hEq
  subst hEq
  dsimp only [hooksPRNG] at hmem
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
    Prod.mk.injEq, Option.some.injEq] at hmem
  rcases hmem with ⟨rfl, rfl⟩; rfl

theorem hooksPRNGC_agrees_vr [DecidableEq T] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (B : ℕ) (mo : Mode)
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
      prngHsEnc (fun _ => True) (HBoundedPost := fun _ => True) (VROk := VROk)
      (hooksPRNGC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B mo)
      (hooksPRNG cka prng fs mo) where
  hBounded_post _ _ := trivial
  startSend_eval hE ctxE pE tE γE σE rE ρ h ctx P _ hh _ _ :=
    prngStartSendC_eval cka prng fs hSend hPrngUp hFsInitS hSampCCoins mo
      hE ctxE pE tE γE σE rE ρ h ctx P hh
  startSend_bounded _ _ _ _ _ _ _ _ _ _ := trivial
  startRecv_eval hE ctxE pE tE γE σE tnE ρ h ctx P _ hh _ _ :=
    prngStartRecvC_eval cka prng fs hRecv hFsInitR heqT mo
      hE ctxE pE tE γE σE tnE ρ h ctx P hh
  startRecv_bounded _ _ _ _ _ _ _ _ _ _ := trivial
  startRecv_vrOk ctx P t γ σv Tn h _ :=
    hooksPRNG_startRecv_rs cka prng fs mo hInitR ctx P t γ σv Tn h
  fsSend_eval hE _ _ _ ssE hdrE mE _ ρ h _ _ _ hh _ _ := by
    simp [hooksPRNGC, prngFsSendC, hooksPRNG, ckaOps, hFsSend, hh,
      StateT.run_pure, Prod.map, Expr.eval]
  fsRecv_eval hE _ _ _ rsE hdrE eE _ ρ h _ _ _ _ hVR hh _ _ _ := by
    simp only [hooksPRNGC, prngFsRecvC, hooksPRNG, eval_ret,
      ckaOps, hFsRecv, hh, StateT.run_pure, map_pure, Prod.map, id_eq, Expr.eval]
    congr 2
    rcases hrc : fs.receive (rsE.eval ρ) (hdrE.eval ρ) (eE.eval ρ) with _ | ⟨rs', i, m⟩
    · rfl
    · simp [Nat.min_eq_left (hFsB _ _ _ _ _ _ hVR hrc)]
  fsRecv_bounded _ _ _ _ _ _ _ _ _ _ _ := trivial
  commit_eval hE _ _ _ newE ρ h _ _ _ new _ hh _ _ _ hnew := by
    simp [hooksPRNGC, prngCommitC, hooksPRNG, hh, hnew, StateT.run_pure, Prod.map, Expr.eval]
  reveal_eval hE ctxE pE vpE ρ h ctx P vp _ hh _ _ hvp :=
    prngRevealC_eval cka prng fs mo hE ctxE pE vpE ρ h ctx P vp hh hvp

theorem initPRNGRaw_vrInv [SampleableType KC]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (mo : Mode) (b : Bool)
    {VROkStep : ℕ → RS → Prop} {B qAdv : ℕ}
    (hInitR : ∀ k, VROkStep (B - qAdv) (fs.initReceiver k)) :
    ∀ es₀ ∈ support (initPRNGRaw cka prng fs lam mo b),
      SMVRInv VROkStep B qAdv es₀.g := by
  intro es₀ hmem P t v hv
  unfold initPRNGRaw at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨kc, _, hmem⟩ := hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨⟨step, h₀⟩, _, hmem⟩ := hmem
  rcases step with _ | ⟨σv, k⟩
  · simp only [support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    cases P <;> simp [abortedParties] at hv
  · simp only [support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    cases P <;> simp only [mkParties] at hv
    · split_ifs at hv with ht0
      · cases hv; exact hInitR _
    · cases hv

theorem redPRNGAuthProg_eval_eq_bind_initPRNGRaw_vr
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
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send)
    (hFsRecv : fsReceive = fs.receive)
    (heqT : eqT = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    (hDefaultE : defaultE = default)
    (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hVRHk : HooksVRInv VROkStep (hooksPRNG cka prng fs ⟨true, tL, t⟩))
    (hInitR : ∀ k, VROkStep 0 (fs.initReceiver k))
    (hFsB : ∀ rs hdr e rs' i m, VROkStep B_q rs → fs.receive rs hdr e = some (rs', i, m) → i ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : SchemeAdversary Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q) :
    (redPRNGAuthProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka qep fs.maxSkip tL t).eval (fun _ => A) () =
      (do
        let es₀ ← initPRNGRaw cka prng fs lam ⟨true, tL, t⟩ false
        let (_, es') ←
          (simulateQ
            (implE (hooksPRNG cka prng fs ⟨true, tL, t⟩)
              (2 + Δcka) qep fs.maxSkip (⟨true, tL, t⟩ : Mode).cfg (⟨true, tL, t⟩ : Mode).policy)
            A).run es₀
        pure (authOut (2 + Δcka) (⟨true, tL, t⟩ : Mode).policy es')) := by
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv := by
    refine hA.of_imp (fun x hx => ?_)
    rcases x with _ | _ <;> simp_all [isGameQuery]
  have hHk := hooksPRNGC_agrees_vr
    (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (prngInit := prngInit)
    (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    cka prng fs B ⟨true, tL, t⟩ hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend hFsRecv
    heqT hSampCCoins (fun k => hVRHk.mono (Nat.zero_le B_q) (hInitR k)) hFsB
  have hInit := initPRNGEStateC_eval (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (prngInit := prngInit) (fsSend := fsSend) (fsReceive := fsReceive)
    (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    cka prng fs hInitA hInitB hPrngUp hFsInitS hFsInitR hSampKC
    ⟨true, tL, t⟩ (.bool false) (Env.cons (t := (.unit : Ty S)) () .nil)
  unfold CostedReduction.eval redPRNGAuthProg CostedReduction.impl
  dsimp only
  rw [eval_bind, hInit]
  let vpE := vpTblEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
    (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
    (γvT := .base .γ) (svT := .opt (.base .sig)) (ssvT := .base .ss) (rsvT := .base .rs)
  let esT := @prngEsTy KC Γ CCoins T I KR RSt K SS RS M E
  have hVp : prngVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K) =
      vpE := rfl
  rw [hVp]
  simp only [bind_map_left, eval_ret, Expr.eval, Expr.v0, Env.get_cons_zero,
    bind_assoc, pure_bind]
  refine OracleComp.bind_congr_of_forall_mem_support
    (initPRNGRaw cka prng fs lam ⟨true, tL, t⟩ false)
    fun es₀ hes₀ => ?_
  have ⟨hInv₀, _⟩ := initPRNGRaw_inv cka prng fs lam ⟨true, tL, t⟩ false hqB hB1 hBB es₀ hes₀
  have hVR₀ := initPRNGRaw_vrInv (B := B_q) (qAdv := qAdv) cka prng fs lam ⟨true, tL, t⟩ false
    (fun k => hVRHk.mono (Nat.zero_le _) (hInitR k)) es₀ hes₀
  have ⟨hSim, hSimInv⟩ := simulateQ_implEC_vr_eq hDefaultE (fun _ => rfl) prngHsEnc (fun _ => True)
    (hooksPRNGC B ⟨true, tL, t⟩) (hooksPRNG cka prng fs ⟨true, tL, t⟩)
    L B_q (2 + Δcka) qep fs.maxSkip hHk hVRHk
    (modeCfgEC OO ⟨true, tL, t⟩) (⟨true, tL, t⟩ : Mode).cfg
    (modeCfgEC_agrees ⟨true, tL, t⟩)
    heqT heqM heqE (⟨true, tL, t⟩ : Mode).policy (fun _ _ _ _ _ _ => trivial) hA' es₀ trivial hInv₀
    hVR₀
  dsimp only [Expr.v0] at hSim
  rw [hSim, bind_map_left]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨b', es'⟩ hes' => ?_
  obtain ⟨_, hInv', _⟩ := hSimInv (b', es') hes'
  have hBnd' := hInv'.toBoundedEngine
  have hOut := authOutE_eval vpE prngHsEnc (O' := OO) L (2 + Δcka)
    (⟨true, tL, t⟩ : Mode).policy .v0
    (Env.cons (t := esT) (esEnc vpE prngHsEnc es')
      (Env.cons (t := (.bool : Ty S)) b' .nil))
    es' hBnd'.leaks_le hBnd'.corrs_le rfl
  dsimp only [Prod.map, id, Expr.v0, vpE, Mode.policy] at hOut ⊢
  rw [hOut]

theorem redPRNGPrivProg_eval_eq_bind_initPRNGRaw_vr
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
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send)
    (hFsRecv : fsReceive = fs.receive)
    (heqT : eqT = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    (hDefaultE : defaultE = default)
    (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hVRHk : HooksVRInv VROkStep (hooksPRNG cka prng fs ⟨false, tL, t⟩))
    (hInitR : ∀ k, VROkStep 0 (fs.initReceiver k))
    (hFsB : ∀ rs hdr e rs' i m, VROkStep B_q rs → fs.receive rs hdr e = some (rs', i, m) → i ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : SchemeAdversary Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q) :
    (redPRNGPrivProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka qep fs.maxSkip tL t).eval (fun _ => A) () =
      (do
        let b ← sampleT Bool
        let es₀ ← initPRNGRaw cka prng fs lam ⟨false, tL, t⟩ b
        let (b', es') ←
          (simulateQ
            (implE (hooksPRNG cka prng fs ⟨false, tL, t⟩)
              (2 + Δcka) qep fs.maxSkip (⟨false, tL, t⟩ : Mode).cfg (⟨false, tL, t⟩ : Mode).policy)
            A).run es₀
        privOut (2 + Δcka) (⟨false, tL, t⟩ : Mode).policy b b' es') := by
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv := by
    refine hA.of_imp (fun x hx => ?_)
    rcases x with _ | _ <;> simp_all [isGameQuery]
  have hHk := hooksPRNGC_agrees_vr
    (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (prngInit := prngInit)
    (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    cka prng fs B ⟨false, tL, t⟩ hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend hFsRecv
    heqT hSampCCoins (fun k => hVRHk.mono (Nat.zero_le B_q) (hInitR k)) hFsB
  have hBit : ∀ {Γ'} (ρ' : Env Γ'),
      (@Comp.sample _ _ _ OO II _ CKASamp.bit .unit).eval ρ' = sampleT Bool := by
    intro Γ' ρ'
    simp only [Comp.eval, prngIface, prngSamplers, ckaSamplers, sampleT]
    exact liftP_eq_liftM II (fun _ => rfl) ($ᵗ Bool)
  unfold CostedReduction.eval redPRNGPrivProg CostedReduction.impl
  dsimp only
  rw [eval_bind, hBit, bind_assoc]
  refine bind_congr fun b => ?_
  have hInit := initPRNGEStateC_eval (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (prngInit := prngInit) (fsSend := fsSend) (fsReceive := fsReceive)
    (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    cka prng fs hInitA hInitB hPrngUp hFsInitS hFsInitR hSampKC
    ⟨false, tL, t⟩ .v0 (Env.cons (t := (.bool : Ty S)) b (Env.cons (t := (.unit : Ty S)) () .nil))
  rw [eval_bind, hInit]
  let vpE := vpTblEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
    (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
    (γvT := .base .γ) (svT := .opt (.base .sig)) (ssvT := .base .ss) (rsvT := .base .rs)
  let esT := @prngEsTy KC Γ CCoins T I KR RSt K SS RS M E
  have hVp : prngVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K) =
      vpE := rfl
  rw [hVp]
  simp only [bind_map_left, eval_ret, Expr.eval, Expr.v0, Env.get_cons_zero,
    bind_assoc, pure_bind]
  refine OracleComp.bind_congr_of_forall_mem_support (initPRNGRaw cka prng fs lam ⟨false, tL, t⟩ b)
    fun es₀ hes₀ => ?_
  have ⟨hInv₀, hb₀⟩ := initPRNGRaw_inv cka prng fs lam ⟨false, tL, t⟩ b hqB hB1 hBB es₀ hes₀
  have hVR₀ := initPRNGRaw_vrInv (B := B_q) (qAdv := qAdv) cka prng fs lam ⟨false, tL, t⟩ b
    (fun k => hVRHk.mono (Nat.zero_le _) (hInitR k)) es₀ hes₀
  have ⟨hSim, hSimInv⟩ := simulateQ_implEC_vr_eq hDefaultE (fun _ => rfl) prngHsEnc (fun _ => True)
    (hooksPRNGC B ⟨false, tL, t⟩) (hooksPRNG cka prng fs ⟨false, tL, t⟩)
    L B_q (2 + Δcka) qep fs.maxSkip hHk hVRHk
    (modeCfgEC OO ⟨false, tL, t⟩) (⟨false, tL, t⟩ : Mode).cfg
    (modeCfgEC_agrees ⟨false, tL, t⟩)
    heqT heqM heqE (⟨false, tL, t⟩ : Mode).policy (fun _ _ _ _ _ _ => trivial) hA' es₀ trivial hInv₀
    hVR₀
  dsimp only [Expr.v0] at hSim
  rw [hSim, bind_map_left]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨b', es'⟩ hes' => ?_
  obtain ⟨_, hInv', hb'⟩ := hSimInv (b', es') hes'
  have hBnd' := hInv'.toBoundedEngine
  have hbEq : (cGsB (esG (Expr.v0 (O := OO)))).eval
      (Env.cons (t := esT) (esEnc vpE prngHsEnc es')
        (Env.cons (t := (.bool : Ty S)) b' .nil)) = b := by
    change es'.g.b = b
    exact hb'.trans hb₀
  exact privOutC_eval prngHsEnc L (2 + Δcka) (⟨false, tL, t⟩ : Mode).policy
    (fun {Γ''} => @Comp.sample _ _ _ OO II Γ'' CKASamp.bit .unit) hBit
    (cGsB (esG .v0)) .v1 .v0
    (Env.cons (t := esT) (esEnc vpE prngHsEnc es')
      (Env.cons (t := (.bool : Ty S)) b' .nil))
    b b' es' hBnd'.leaks_le hbEq rfl rfl

theorem redPRNGAuthProg_branch_eval_vr
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
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send)
    (hFsRecv : fsReceive = fs.receive)
    (heqT : eqT = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    (hDefaultE : defaultE = default)
    (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hVRHk : HooksVRInv VROkStep (hooksPRNG cka prng fs ⟨true, tL, t⟩))
    (hInitR : ∀ k, VROkStep 0 (fs.initReceiver k))
    (hFsB : ∀ rs hdr e rs' i m, VROkStep B_q rs → fs.receive rs hdr e = some (rs', i, m) → i ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : SchemeAdversary Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q)
    (b_prng : Bool) :
    PRFPRNG.branch prng b_prng
      ((redPRNGAuthProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
          (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK)
          L B Δcka qep fs.maxSkip tL t).eval (fun _ => A) ()) =
      PRFPRNG.branch prng b_prng (redPRNGAuth cka prng fs lam Δcka qep tL t A) := by
  rw [redPRNGAuthProg_eval_eq_bind_initPRNGRaw_vr cka prng fs L B B_q Δcka qep tL t
    hInitA hInitB hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend hFsRecv
    heqT heqM heqE hDefaultE hSampKC hSampCCoins hVRHk hInitR hFsB hB1 hBB A qAdv hA hqB]
  unfold PRFPRNG.branch redPRNGAuth runPRNG engRun initPRNG initPRNGRaw
  refine bind_congr fun kr => ?_
  rw [StateT.run'_eq, StateT.run'_eq]
  refine congrArg (Prod.fst <$> ·) ?_
  simp only [StateT.run_bind, StateT.run_lift, simulateQ_bind, simulateQ_sampleT_run,
    bind_assoc, pure_bind]
  refine bind_congr fun kc => ?_
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨step, h₀⟩, sp⟩ hmem => ?_
  obtain ⟨σv, k, rfl, rfl⟩ := rootPRNG_zero_support_some (T := T) prng ⟨true, tL, t⟩ lam kr b_prng
    step h₀ sp hmem
  simp [StateT.run_pure, simulateQ_pure, Mode.policy]
  rfl

theorem redPRNGAuthProg_eval_vr
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
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send)
    (hFsRecv : fsReceive = fs.receive)
    (heqT : eqT = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    (hDefaultE : defaultE = default)
    (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hVRHk : HooksVRInv VROkStep (hooksPRNG cka prng fs ⟨true, tL, t⟩))
    (hInitR : ∀ k, VROkStep 0 (fs.initReceiver k))
    (hFsB : ∀ rs hdr e rs' i m, VROkStep B_q rs → fs.receive rs hdr e = some (rs', i, m) → i ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : SchemeAdversary Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q) :
    PRFPRNG.game prng
      ((redPRNGAuthProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
          (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK)
          L B Δcka qep fs.maxSkip tL t).eval (fun _ => A) ()) =
      PRFPRNG.game prng (redPRNGAuth cka prng fs lam Δcka qep tL t A) := by
  unfold PRFPRNG.game
  refine bind_congr fun b_prng => ?_
  have hBr := redPRNGAuthProg_branch_eval_vr (prngInit := prngInit) (eqI := eqI) (lam := lam)
    (sampKR := sampKR) (sampI := sampI) (sampK := sampK)
    cka prng fs L B B_q Δcka qep tL t hInitA hInitB hSend hRecv hPrngUp
    hFsInitS hFsInitR hFsSend hFsRecv heqT heqM heqE hDefaultE hSampKC hSampCCoins
    hVRHk hInitR hFsB hB1 hBB A qAdv hA hqB b_prng
  unfold PRFPRNG.branch at hBr
  simp only [← bind_assoc]
  exact congrArg (· >>= fun b' => pure (b_prng == b')) hBr

theorem redPRNGAuthProg_advantage_vr
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
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send)
    (hFsRecv : fsReceive = fs.receive)
    (heqT : eqT = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    (hDefaultE : defaultE = default)
    (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hVRHk : HooksVRInv VROkStep (hooksPRNG cka prng fs ⟨true, tL, t⟩))
    (hInitR : ∀ k, VROkStep 0 (fs.initReceiver k))
    (hFsB : ∀ rs hdr e rs' i m, VROkStep B_q rs → fs.receive rs hdr e = some (rs', i, m) → i ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : SchemeAdversary Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q) :
    PRFPRNG.advantage prng
      ((redPRNGAuthProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
          (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK)
          L B Δcka qep fs.maxSkip tL t).eval (fun _ => A) ()) =
      PRFPRNG.advantage prng (redPRNGAuth cka prng fs lam Δcka qep tL t A) := by
  unfold PRFPRNG.advantage
  rw [redPRNGAuthProg_eval_vr cka prng fs L B B_q Δcka qep tL t
    hInitA hInitB hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend hFsRecv
    heqT heqM heqE hDefaultE hSampKC hSampCCoins hVRHk hInitR hFsB hB1 hBB A qAdv hA hqB]

theorem redPRNGPrivProg_branch_eval_vr
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
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send)
    (hFsRecv : fsReceive = fs.receive)
    (heqT : eqT = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    (hDefaultE : defaultE = default)
    (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hVRHk : HooksVRInv VROkStep (hooksPRNG cka prng fs ⟨false, tL, t⟩))
    (hInitR : ∀ k, VROkStep 0 (fs.initReceiver k))
    (hFsB : ∀ rs hdr e rs' i m, VROkStep B_q rs → fs.receive rs hdr e = some (rs', i, m) → i ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : SchemeAdversary Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q)
    (b_prng : Bool) :
    PRFPRNG.branch prng b_prng
      ((redPRNGPrivProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
          (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK)
          L B Δcka qep fs.maxSkip tL t).eval (fun _ => A) ()) =
      PRFPRNG.branch prng b_prng (redPRNGPriv cka prng fs lam Δcka qep tL t A) := by
  rw [redPRNGPrivProg_eval_eq_bind_initPRNGRaw_vr cka prng fs L B B_q Δcka qep tL t
    hInitA hInitB hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend hFsRecv
    heqT heqM heqE hDefaultE hSampKC hSampCCoins hVRHk hInitR hFsB hB1 hBB A qAdv hA hqB]
  unfold PRFPRNG.branch redPRNGPriv runPRNG engRun initPRNG initPRNGRaw
  refine bind_congr fun kr => ?_
  rw [StateT.run'_eq, StateT.run'_eq]
  refine congrArg (Prod.fst <$> ·) ?_
  simp only [StateT.run_bind, StateT.run_lift, simulateQ_bind, simulateQ_sampleT_run,
    bind_assoc, pure_bind]
  refine bind_congr fun b => ?_
  refine bind_congr fun kc => ?_
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨step, h₀⟩, sp⟩ hmem => ?_
  obtain ⟨σv, k, rfl, rfl⟩ := rootPRNG_zero_support_some (T := T) prng ⟨false, tL, t⟩ lam kr b_prng
    step h₀ sp hmem
  simp [StateT.run_pure, simulateQ_pure, Mode.policy]
  rfl

theorem redPRNGPrivProg_eval_vr
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
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send)
    (hFsRecv : fsReceive = fs.receive)
    (heqT : eqT = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    (hDefaultE : defaultE = default)
    (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hVRHk : HooksVRInv VROkStep (hooksPRNG cka prng fs ⟨false, tL, t⟩))
    (hInitR : ∀ k, VROkStep 0 (fs.initReceiver k))
    (hFsB : ∀ rs hdr e rs' i m, VROkStep B_q rs → fs.receive rs hdr e = some (rs', i, m) → i ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : SchemeAdversary Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q) :
    PRFPRNG.game prng
      ((redPRNGPrivProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
          (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK)
          L B Δcka qep fs.maxSkip tL t).eval (fun _ => A) ()) =
      PRFPRNG.game prng (redPRNGPriv cka prng fs lam Δcka qep tL t A) := by
  unfold PRFPRNG.game
  refine bind_congr fun b_prng => ?_
  have hBr := redPRNGPrivProg_branch_eval_vr (prngInit := prngInit) (eqI := eqI) (lam := lam)
    (sampKR := sampKR) (sampI := sampI) (sampK := sampK)
    cka prng fs L B B_q Δcka qep tL t hInitA hInitB hSend hRecv hPrngUp
    hFsInitS hFsInitR hFsSend hFsRecv heqT heqM heqE hDefaultE hSampKC hSampCCoins
    hVRHk hInitR hFsB hB1 hBB A qAdv hA hqB b_prng
  unfold PRFPRNG.branch at hBr
  simp only [← bind_assoc]
  exact congrArg (· >>= fun b' => pure (b_prng == b')) hBr

theorem redPRNGPrivProg_advantage_vr
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
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send)
    (hFsRecv : fsReceive = fs.receive)
    (heqT : eqT = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    (hDefaultE : defaultE = default)
    (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hVRHk : HooksVRInv VROkStep (hooksPRNG cka prng fs ⟨false, tL, t⟩))
    (hInitR : ∀ k, VROkStep 0 (fs.initReceiver k))
    (hFsB : ∀ rs hdr e rs' i m, VROkStep B_q rs → fs.receive rs hdr e = some (rs', i, m) → i ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : SchemeAdversary Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q) :
    PRFPRNG.advantage prng
      ((redPRNGPrivProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
          (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK)
          L B Δcka qep fs.maxSkip tL t).eval (fun _ => A) ()) =
      PRFPRNG.advantage prng (redPRNGPriv cka prng fs lam Δcka qep tL t A) := by
  unfold PRFPRNG.advantage
  rw [redPRNGPrivProg_eval_vr cka prng fs L B B_q Δcka qep tL t
    hInitA hInitB hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend hFsRecv
    heqT heqM heqE hDefaultE hSampKC hSampCCoins hVRHk hInitR hFsB hB1 hBB A qAdv hA hqB]

end HooksPRNGC

section FromAEADPRG

variable {MK C : Type}

theorem hooksPRNG_vrInv_fromAEADPRG [DecidableEq T] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip : ℕ) (mo : Mode) :
    HooksVRInv (RSReach maxSkip)
      (hooksPRNG cka prng (FSAEAD.fromAEADPRG ae G maxSkip) mo) where
  mono hle hv := hv.mono hle
  startRecv_step ctx P t γ σv Tn h :=
    hooksPRNG_startRecv_rs cka prng (FSAEAD.fromAEADPRG ae G maxSkip) mo
      (RSReach.init ae G maxSkip) ctx P t γ σv Tn h
  fsRecv_step _ _ _ rs hdr e _ h res hVR hmem v' i' m' hEq := by
    rcases res with ⟨ans, h'⟩
    dsimp only at hEq
    subst hEq
    dsimp only [hooksPRNG] at hmem
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, Option.some.injEq] at hmem
    rcases hmem with ⟨hrec, _⟩
    exact (RSReach.receive ae G maxSkip _ hVR hrec.symm).2
  commit_vR := hooksPRNG_commit_vR cka prng (FSAEAD.fromAEADPRG ae G maxSkip) mo

end FromAEADPRG

end CryptoGames.SM.Construction

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Session.StatementComposed -- shake: keep
public import Computational.Proofs.E2E.ComposedKeyIndHop
public import Computational.Proofs.GameHop.GlobalHybrid
import Computational.Proofs.GameHop.Advantage
import Computational.Proofs.GameHop.StateSim
import VCVio.EvalDist.Monad.Basic

/-!
# Measure combinators and SM state helpers for `ComposedPrefixSlot`

**Checked by Lean.**

Provides `ProbComp` monotonicity and decomposition lemmas, challenge-bit preservation for
`SM.oracleImplR`, and oracle simulation helpers (`implExt`, `kioFullImpl`) for the prefix-slot
hybrid.
-/

@[expose] public section

open scoped ENNReal
open OracleComp OracleSpec MeasureTheory
open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme WireAEAD FSAEAD
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.E2E.Prefix

namespace CryptoVerification.E2E

@[simp]
private theorem stateT_run_lift {M : Type → Type} [Monad M] {σ α : Type}
    (mx : M α) (s : σ) :
    (StateT.lift mx : StateT σ M α).run s = (mx >>= fun x => pure (x, s)) := rfl

@[simp]
private theorem stateT_run_liftM {M : Type → Type} [Monad M] {σ α : Type}
    (mx : M α) (s : σ) :
    (liftM mx : StateT σ M α).run s = (mx >>= fun x => pure (x, s)) := rfl

section MeasureCombinators

theorem boolDist_le_iSup_flip_of_beq_not_le (c₁ c₂ : ProbComp Bool) (adv : Bool → ℝ≥0∞)
    (h : ∀ flip : Bool,
      𝒟[(· == !flip) <$> c₁] {true} ≤ 𝒟[(· == !flip) <$> c₂] {true} + adv flip) :
    𝒟[c₁].boolDist 𝒟[c₂] ≤ ⨆ flip : Bool, adv flip :=
  Computational.Proofs.GameHop.Advantage.boolDist_le_iSup_flip_of_beq_not_le c₁ c₂ adv h

theorem evalDist_bind_mono_prob {α : Type} (c : ProbComp α) (F G : α → ProbComp Bool)
    (h : ∀ a, 𝒟[F a] {true} ≤ 𝒟[G a] {true}) :
    𝒟[c >>= F] {true} ≤ 𝒟[c >>= G] {true} :=
  Computational.Proofs.GameHop.Advantage.evalDist_bind_mono_prob c F G
    (measurableSet_singleton true) h

theorem evalDist_bind_mono_prob_of_support {α : Type} (c : ProbComp α) (F G : α → ProbComp Bool)
    (h : ∀ a ∈ support c, 𝒟[F a] {true} ≤ 𝒟[G a] {true}) :
    𝒟[c >>= F] {true} ≤ 𝒟[c >>= G] {true} :=
  Computational.Proofs.GameHop.Advantage.evalDist_bind_mono_prob_of_support c F G
    (measurableSet_singleton true) h

theorem evalDist_bind_mono_of_imp {α : Type} (c : ProbComp α) (f g : α → Bool)
    (h : ∀ a, f a ≤ g a) :
    𝒟[c >>= fun a => pure (f a)] {true} ≤ 𝒟[c >>= fun a => pure (g a)] {true} := by
  refine evalDist_bind_mono_prob c (fun a => pure (f a)) (fun a => pure (g a)) fun a => ?_
  have ha := h a
  revert ha
  cases f a <;> cases g a <;> simp

theorem evalDist_bind_fst_or_not_fst (c : ProbComp (Bool × Bool)) (flip : Bool) :
    𝒟[c >>= fun p => pure (p.2 == !flip)] {true} =
      𝒟[c >>= fun p => pure (p.1 && (p.2 == !flip))] {true} +
        𝒟[c >>= fun p => pure (!p.1 && (p.2 == !flip))] {true} := by
  induction c using OracleComp.inductionOn with
  | pure p =>
    rcases p with ⟨E, Y⟩
    cases E <;> cases Y <;> cases flip <;> simp
  | query_bind t k ih =>
    simp only [bind_assoc]
    rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete, evalDist_bind_of_discrete,
      Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable,
      Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable,
      Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable,
      ← lintegral_add_left Measurable.of_discrete]
    exact lintegral_congr ih

theorem evalDist_bind_congr_prob_of_support {α : Type}
    (c : ProbComp α) (F G : α → ProbComp Bool)
    (h : ∀ a ∈ support c, 𝒟[F a] {true} = 𝒟[G a] {true}) :
    𝒟[c >>= F] {true} = 𝒟[c >>= G] {true} :=
  le_antisymm
    (evalDist_bind_mono_prob_of_support c F G (fun a ha => le_of_eq (h a ha)))
    (evalDist_bind_mono_prob_of_support c G F (fun a ha => le_of_eq (h a ha).symm))

theorem prob_bind_congr_of_support {α γ : Type} (mx : ProbComp α) (f g : α → ProbComp γ)
    (h : ∀ a ∈ support mx, f a = g a) : (mx >>= f) = (mx >>= g) :=
  Computational.Proofs.GameHop.StateSim.AllSupport.bind_congr h f g (fun _ ha => ha)

export Computational.Proofs.GameHop.GlobalHybrid
  (slotStepOut slotStepY1 slotStepY0 slotStepWRed slotStep_bool_le_true slotStep_bool_le_false)

end MeasureCombinators

namespace Signed

theorem evalDist_bind_apply_lintegral {α : Type} (oa : ProbComp α) (f : α → ProbComp Bool)
    (v : Bool) :
    letI : MeasurableSpace α := ⊤
    𝒟[oa >>= f] {v} = ∫⁻ a, 𝒟[f a] {v} ∂𝒟[oa] := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  rw [evalDist_bind_of_discrete,
    Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]

theorem evalDist_bind_apply_eq_add {α : Type} (oa : ProbComp α) (f g h : α → ProbComp Bool)
    (v : Bool) (H : ∀ a, 𝒟[f a] {v} = 𝒟[g a] {v} + 𝒟[h a] {v}) :
    𝒟[oa >>= f] {v} = 𝒟[oa >>= g] {v} + 𝒟[oa >>= h] {v} := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  rw [evalDist_bind_apply_lintegral, evalDist_bind_apply_lintegral,
    evalDist_bind_apply_lintegral, ← lintegral_add_left Measurable.of_discrete]
  exact lintegral_congr fun a => H a

theorem boolBias_mix_gameR_eq {α Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
    [SampleableType RCoins] (oa : ProbComp α) (sm : α → SMSchemeR Key St Msg Coins RCoins C)
    (Δ qep : ℕ) (cfg : SM.ConfigR St Msg C) (R : α → SM.Adversary St Msg Coins C) :
    𝒟[oa >>= fun o => SM.gameR (sm o) Δ qep cfg (R o)].boolBias =
      𝒟[oa >>= fun o => SM.runR (sm o) Δ qep cfg true (R o) >>=
          fun p => pure (p.1 || p.2.win)].boolDist
        𝒟[oa >>= fun o => SM.runR (sm o) Δ qep cfg false (R o) >>=
          fun p => pure (p.1 && !p.2.win)] := by
  have hg : ∀ o, SM.gameR (sm o) Δ qep cfg (R o) = (do
      let b ← ($ᵗ Bool : ProbComp Bool)
      let z ← if b then
          (SM.runR (sm o) Δ qep cfg true (R o) >>= fun p => pure (p.1 || p.2.win))
        else
          (SM.runR (sm o) Δ qep cfg false (R o) >>= fun p => pure (p.1 && !p.2.win))
      return (b == z)) := by
    intro o
    unfold SM.gameR
    refine bind_congr fun b => ?_
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
      refine bind_congr fun ⟨w, gs⟩ => ?_
      cases w <;> cases gs.win <;> rfl
    · simp only [↓reduceIte, bind_assoc, pure_bind]
      refine bind_congr fun ⟨w, gs⟩ => ?_
      cases w <;> cases gs.win <;> rfl
  simp only [hg]
  rw [OracleComp.evalDist_bind_bind_swap oa ($ᵗ Bool), ← evalDist_boolBias_bind_uniformBool]
  congr 2
  refine bind_congr fun b => ?_
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc]

end Signed

abbrev ExtState (ℓ : ℕ) :=
  SM.GameState (GhostState Bytes) (Plain ℓ) Bytes

theorem epMgmt_b {St Msg C : Type} (s s₁ : GameState St Msg C) (Δ qep : ℕ)
    (P : Party) (bad : Bool) (h : s.epMgmt Δ qep P bad = some s₁) : s₁.b = s.b := by
  unfold GameState.epMgmt at h
  split_ifs at h <;> cases h <;> rfl

theorem oracleImplR_preserves_b {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (q : (SM.spec St Msg Coins C).Domain) (gs : GameState St Msg C)
    {p : (SM.spec St Msg Coins C).Range q × GameState St Msg C}
    (hp : p ∈ support ((SM.oracleImplR sm Δ qep cfg q).run gs)) :
    p.2.b = gs.b := by
  rcases q with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · change p ∈ support ((SM.transmitR sm Δ qep cfg (P, m, r)).run gs) at hp
    unfold SM.transmitR SM.transmitImpl at hp
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hp
    cases h1 : cfg.sendOK gs P
    · simp only [h1, Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hp
      subst hp; rfl
    · simp only [h1, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        StateT.run_bind, StateT.run_get, pure_bind] at hp
      cases h2 : gs.win
      · simp only [h2, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_run_liftM,
          bind_assoc, pure_bind, support_bind, Set.mem_iUnion] at hp
        rcases hp with ⟨⟨coins, bad⟩, _, hp⟩
        cases hep : gs.epMgmt Δ qep P bad with
        | none =>
          simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
          subst hp; rfl
        | some s₁ =>
          simp only [hep, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hp
          subst hp
          exact epMgmt_b gs s₁ Δ qep P bad hep
      · simp only [h2, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
        subst hp; rfl
  · change p ∈ support ((SM.challR sm Δ qep cfg (P, m₀, m₁, r)).run gs) at hp
    unfold SM.challR SM.challImpl at hp
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hp
    cases h1 : cfg.sendOK gs P
    · simp only [h1, Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hp
      subst hp; rfl
    · simp only [h1, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        StateT.run_bind, StateT.run_get, pure_bind] at hp
      cases h2 : gs.win
      · simp only [h2, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_run_liftM,
          bind_assoc, pure_bind, support_bind, Set.mem_iUnion] at hp
        rcases hp with ⟨⟨coins, bad⟩, _, hp⟩
        cases hep : gs.epMgmt Δ qep P bad with
        | none =>
          simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
          subst hp; rfl
        | some s₁ =>
          simp only [hep] at hp
          cases h3 : (!(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P)))
          · simp only [h3, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
              StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hp
            subst hp
            exact epMgmt_b gs s₁ Δ qep P bad hep
          · simp only [h3, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
            subst hp; rfl
      · simp only [h2, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
        subst hp; rfl
  · change p ∈ support ((SM.deliverR sm cfg (P, c)).run gs) at hp
    unfold SM.deliverR at hp
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hp
    cases h1 : gs.win
    · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hp
      cases htr : gs.inTransit P.other c with
      | none =>
        simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
        subst hp; rfl
      | some r =>
        simp only [htr, StateT.run_bind, stateT_run_liftM, bind_assoc, pure_bind,
          support_bind, Set.mem_iUnion] at hp
        rcases hp with ⟨rc, _, hp⟩
        cases hrcv : sm.receive (gs.st P) c rc with
        | none =>
          simp only [hrcv] at hp
          split_ifs at hp <;>
            simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff] at hp <;>
            (subst hp; rfl)
        | some res =>
          rcases res with ⟨st', t', i', m'⟩
          simp only [hrcv] at hp
          split_ifs at hp <;>
            simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff] at hp <;>
            (subst hp; rfl)
    · simp only [h1, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp; rfl
  · change p ∈ support ((SM.injectR sm Δ qep cfg (P, c)).run gs) at hp
    unfold SM.injectR at hp
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hp
    cases h1 : (gs.win || (gs.inTransit P.other c).isSome || !(gs.safeInj Δ) || !(cfg.injOK c))
    · simp only [h1, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_run_liftM,
        bind_assoc, pure_bind, support_bind, Set.mem_iUnion] at hp
      rcases hp with ⟨rc, _, hp⟩
      cases hrcv : sm.receive (gs.st P) c rc with
      | none =>
        simp only [hrcv, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
        subst hp; rfl
      | some res =>
        rcases res with ⟨st', t', i', m'⟩
        simp only [hrcv] at hp
        split_ifs at hp <;>
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hp <;>
          (subst hp; rfl)
    · simp only [h1, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp; rfl
  · change p ∈ support ((SM.corrR cfg P).run gs) at hp
    unfold SM.corrR at hp
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hp
    split_ifs at hp <;>
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hp <;>
      (subst hp; rfl)

abbrev implExt {Pt PQC : Type} [SampleableType PQC]
    (Z : Crypto) (spqr : Spqr Bytes PQC) (ℓ qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (idA idB : IdentityKey) (s : BitVec 256) :
    QueryImpl (unifSpec + smSpecWithSpqr ℓ PQC) (StateT (ExtState ℓ) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (ExtState ℓ) ProbComp) +
    SM.oracleImplR (sessionSchemeSpkWithSpqr (paramsIdsWithSpqr Z spqr idA idB) ℓ s) (2 + 1) qep
      (configRefuseEarlyBobCorr decT encT)

@[simp]
private theorem liftM_unif_sm_query_bind {ℓ : ℕ} {PQC α : Type}
    (q : unifSpec.Domain) (k : unifSpec.Range q → ProbComp α) :
    (liftM (liftM (OracleSpec.query q) >>= k) :
      OracleComp (unifSpec + smSpecWithSpqr ℓ PQC) α) =
      (liftM (OracleSpec.query (spec := unifSpec + smSpecWithSpqr ℓ PQC) (Sum.inl q)) >>=
        fun u => (liftM (k u) : OracleComp (unifSpec + smSpecWithSpqr ℓ PQC) α)) := rfl

@[simp]
theorem simulateQ_pure_run_run {ι : Type} {spec : OracleSpec.{0, 0} ι} {σ₁ σ₂ α : Type}
    (impl : QueryImpl spec (StateT σ₁ (StateT σ₂ ProbComp)))
    (x : α) (s₁ : σ₁) (s₂ : σ₂) :
    ((simulateQ impl (pure x)).run s₁).run s₂ = pure ((x, s₁), s₂) := rfl

abbrev kioFullImpl {S : SignalPqxdh.Setup} {St : Type}
    (kioImpl : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT St ProbComp)) :
    QueryImpl (unifSpec + SignalPqxdh.keyIndSpec S) (StateT St ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + kioImpl

@[simp]
theorem simulateQ_kioFullImpl_kioKind {S : SignalPqxdh.Setup} {St : Type}
    (kioImpl : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT St ProbComp))
    (q : SignalPqxdh.KeyIndQuery S) :
    simulateQ (kioFullImpl kioImpl) (kioKind S q) = kioImpl q :=
  QueryImpl.simulateQ_add_query_right _ _ q

private theorem liftM_unif_query_bind' {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (q : unifSpec.Domain) (k : unifSpec.Range q → ProbComp α) :
    (liftM (liftM (OracleSpec.query q) >>= k) : OracleComp (unifSpec + spec) α) =
      (liftM (OracleSpec.query (spec := unifSpec + spec) (Sum.inl q)) >>=
        fun u => (liftM (k u) : OracleComp (unifSpec + spec) α)) := rfl

theorem simulateQ_kioFullImpl_liftM_run {S : SignalPqxdh.Setup} {St α : Type}
    (kioImpl : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT St ProbComp))
    (mx : ProbComp α) (st : St) :
    (simulateQ (kioFullImpl kioImpl)
      (liftM mx : OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) α)).run st =
    (StateT.lift mx : StateT St ProbComp α).run st := by
  induction mx using OracleComp.inductionOn generalizing st with
  | pure x => rfl
  | query_bind t m ih =>
    rw [liftM_unif_query_bind', simulateQ_query_bind, StateT.run_bind]
    show (((liftM (OracleSpec.query t) : ProbComp _) >>= fun u => pure (u, st)) >>= fun y =>
        (simulateQ (kioFullImpl kioImpl) (liftM (m y.1))).run y.2) =
      ((liftM (OracleSpec.query t) : ProbComp _) >>= fun u => (StateT.lift (m u)).run st)
    simp only [bind_assoc, pure_bind, ih]

end CryptoVerification.E2E

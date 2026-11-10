/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.PureAuxMacroLift
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.SessionShort
public import Computational.Proofs.E2E.SignedPrims

/-!
# Structural Game-Query Subsumption Across Coin Re-encoding

Defines `QuerySubsumes oa₁ oa₂` on `OracleComp (unifSpec + G) α` to relate computations making
identical game queries on matching response paths across coin re-encodings, and shows that
`compilePureAuxRed` preserves structural query bounds. Also provides `CoinSimEquiv` congruence
lemmas for `advAvg` mixtures.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

open OracleComp OracleSpec
open CryptoGames (CKAScheme PRFPRNG FSAEADScheme)
open CryptoGames.CKA (DHFun)
open CryptoGames.LibsignalSession (Crypto PublicKey)
open CryptoVerification.E2E.Signed (advAvg)
open _root_.ReductionDsl (Sig Ty Ops Iface Env Expr Comp GameCodec CostedReduction
  handlerImpl iterM findML anyML mapML consumeFirstML foldML
  atomicSig atomicFig8Ops BV128)
open Computational.Proofs.ReductionDsl.MacroLift (mapTy toVal mapEnvAux callMacroAux_eval)
open Computational.Proofs.ReductionDsl.PureAuxMacroLift (CoinSimEquiv
  ckaAdvantage_congr prngAdvantage_congr fsaeadGame_evalDistEq_of_coinSimEquiv
  PureAuxBundle PureAuxAdapters sampleBoolFig8Comp
  callAdaptR_eval compilePureAuxExpr_eval compilePureAuxComp compilePureAuxRed)

namespace Computational.Proofs.SessionCostedFig8.QuerySubsumes

/-- Every coin-resolved path of `oa₁` matches some coin-resolved path of `oa₂` with identical game queries and continuations. -/
inductive QuerySubsumes {κ : Type} {G : OracleSpec.{0, 0} κ} {α : Type} :
    OracleComp (unifSpec + G) α → OracleComp (unifSpec + G) α → Prop where
  | ret (a : α) : QuerySubsumes (pure a) (pure a)
  | coin_l (n : ℕ) (k : Fin (n + 1) → OracleComp (unifSpec + G) α)
      (oa₂ : OracleComp (unifSpec + G) α) :
      (∀ u, QuerySubsumes (k u) oa₂) →
      QuerySubsumes (liftM (OracleSpec.query (spec := unifSpec + G) (.inl n)) >>= k) oa₂
  | coin_r (oa₁ : OracleComp (unifSpec + G) α) (n : ℕ)
      (k : Fin (n + 1) → OracleComp (unifSpec + G) α) (u : Fin (n + 1)) :
      QuerySubsumes oa₁ (k u) →
      QuerySubsumes oa₁ (liftM (OracleSpec.query (spec := unifSpec + G) (.inl n)) >>= k)
  | game (g : κ) (k₁ k₂ : G.Range g → OracleComp (unifSpec + G) α) :
      (∀ r, QuerySubsumes (k₁ r) (k₂ r)) →
      QuerySubsumes
        (liftM (OracleSpec.query (spec := unifSpec + G) (.inr g)) >>= k₁)
        (liftM (OracleSpec.query (spec := unifSpec + G) (.inr g)) >>= k₂)

namespace QuerySubsumes

section Basic

variable {κ : Type} {G : OracleSpec.{0, 0} κ}

theorem refl {α : Type} (oa : OracleComp (unifSpec + G) α) : QuerySubsumes oa oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact .ret a
  | query_bind t mx ih =>
    rcases t with n | g
    · exact .coin_l n mx _ fun u => .coin_r _ n mx u (ih u)
    · exact .game g mx mx ih

theorem of_eq {α : Type} {oa₁ oa₂ : OracleComp (unifSpec + G) α} (h : oa₁ = oa₂) :
    QuerySubsumes oa₁ oa₂ :=
  h ▸ refl oa₁

private theorem pure_ne_query_bind {α : Type} (a : α) (t : (unifSpec + G).Domain)
    (k : (unifSpec + G).Range t → OracleComp (unifSpec + G) α) :
    (pure a : OracleComp (unifSpec + G) α) ≠
      liftM (OracleSpec.query (spec := unifSpec + G) t) >>= k := by
  intro h
  have hd := congrArg (OracleComp.isPure (spec := unifSpec + G)) h
  simp at hd

private def headQuery {α : Type} (oa : OracleComp (unifSpec + G) α) :
    Option (Sigma fun t : (unifSpec + G).Domain =>
      (unifSpec + G).Range t → OracleComp (unifSpec + G) α) :=
  OracleComp.construct (fun _ => none) (fun t mx _ => some ⟨t, mx⟩) oa

private theorem query_bind_inj {α : Type} {t₁ t₂ : (unifSpec + G).Domain}
    {k₁ : (unifSpec + G).Range t₁ → OracleComp (unifSpec + G) α}
    {k₂ : (unifSpec + G).Range t₂ → OracleComp (unifSpec + G) α}
    (h : (liftM (OracleSpec.query (spec := unifSpec + G) t₁) >>= k₁) =
         (liftM (OracleSpec.query (spec := unifSpec + G) t₂) >>= k₂)) :
    ∃ ht : t₁ = t₂, ht ▸ k₁ = k₂ := by
  have hd := congrArg headQuery h
  simp only [headQuery, OracleComp.construct_query_bind, Option.some.injEq] at hd
  rcases hd with ⟨rfl, rfl⟩
  exact ⟨rfl, rfl⟩

private theorem trans_pure {α : Type} {a : α} {oa₂ oa₃ : OracleComp (unifSpec + G) α}
    (h₂₃ : QuerySubsumes oa₂ oa₃) (heq : oa₂ = pure a) :
    QuerySubsumes (pure a) oa₃ := by
  induction h₂₃ with
  | ret b =>
    have hab := (OracleComp.pure_inj b a).mp heq
    subst hab
    exact .ret b
  | coin_l n k _ _ _ => exact False.elim (pure_ne_query_bind a (.inl n) k heq.symm)
  | coin_r _ n k u _ ih => exact .coin_r (pure a) n k u (ih heq)
  | game g k₁ k₂ _ _ => exact False.elim (pure_ne_query_bind a (.inr g) k₁ heq.symm)

private theorem trans_coin_r {α : Type} {oa₁ : OracleComp (unifSpec + G) α}
    {n : ℕ} {k : Fin (n + 1) → OracleComp (unifSpec + G) α} {u : Fin (n + 1)}
    (ih_u : ∀ {oa₃}, QuerySubsumes (k u) oa₃ → QuerySubsumes oa₁ oa₃)
    {oa₂ oa₃ : OracleComp (unifSpec + G) α}
    (h₂₃ : QuerySubsumes oa₂ oa₃)
    (heq : oa₂ = liftM (OracleSpec.query (spec := unifSpec + G) (.inl n)) >>= k) :
    QuerySubsumes oa₁ oa₃ := by
  induction h₂₃ with
  | ret b => exact False.elim (pure_ne_query_bind b (.inl n) k heq)
  | coin_l n' k' _ hk' _ =>
    obtain ⟨ht, hk_eq⟩ := query_bind_inj heq.symm
    cases ht
    subst hk_eq
    exact ih_u (hk' u)
  | coin_r _ m km v _ ih => exact .coin_r oa₁ m km v (ih heq)
  | game g k₁ k₂ _ _ =>
    obtain ⟨ht, _⟩ := query_bind_inj heq
    cases ht

private theorem trans_game {α : Type} {g : κ}
    {k₁ k₂ : G.Range g → OracleComp (unifSpec + G) α}
    (ih_r : ∀ r {oa₃}, QuerySubsumes (k₂ r) oa₃ → QuerySubsumes (k₁ r) oa₃)
    {oa₂ oa₃ : OracleComp (unifSpec + G) α}
    (h₂₃ : QuerySubsumes oa₂ oa₃)
    (heq : oa₂ = liftM (OracleSpec.query (spec := unifSpec + G) (.inr g)) >>= k₂) :
    QuerySubsumes (liftM (OracleSpec.query (spec := unifSpec + G) (.inr g)) >>= k₁) oa₃ := by
  induction h₂₃ with
  | ret b => exact False.elim (pure_ne_query_bind b (.inr g) k₂ heq)
  | coin_l n k _ _ _ =>
    obtain ⟨ht, _⟩ := query_bind_inj heq
    cases ht
  | coin_r _ m km v _ ih => exact .coin_r _ m km v (ih heq)
  | game g' k₂' k₃ hk' _ =>
    obtain ⟨ht, hk_eq⟩ := query_bind_inj heq.symm
    cases ht
    subst hk_eq
    exact .game g k₁ k₃ fun r => ih_r r (hk' r)

theorem trans {α : Type} {oa₁ oa₂ oa₃ : OracleComp (unifSpec + G) α}
    (h₁₂ : QuerySubsumes oa₁ oa₂) (h₂₃ : QuerySubsumes oa₂ oa₃) :
    QuerySubsumes oa₁ oa₃ := by
  induction h₁₂ generalizing oa₃ with
  | ret a => exact trans_pure h₂₃ rfl
  | coin_l n k _ _ ih => exact .coin_l n k oa₃ fun u => ih u h₂₃
  | coin_r oa₁ n k u _ ih => exact trans_coin_r (fun {_} h => ih h) h₂₃ rfl
  | game g k₁ k₂ _ ih => exact trans_game (fun r {_} h => ih r h) h₂₃ rfl

theorem bind {α β : Type} {oa₁ oa₂ : OracleComp (unifSpec + G) α}
    {f₁ f₂ : α → OracleComp (unifSpec + G) β}
    (h : QuerySubsumes oa₁ oa₂) (hf : ∀ a, QuerySubsumes (f₁ a) (f₂ a)) :
    QuerySubsumes (oa₁ >>= f₁) (oa₂ >>= f₂) := by
  induction h with
  | ret a => simp only [pure_bind]; exact hf a
  | coin_l n k _ _ ih => rw [bind_assoc]; exact .coin_l n _ _ ih
  | coin_r _ n k u _ ih => rw [bind_assoc]; exact .coin_r _ n _ u ih
  | game g k₁ k₂ _ ih => rw [bind_assoc, bind_assoc]; exact .game g _ _ ih

theorem map {α β : Type} {oa₁ oa₂ : OracleComp (unifSpec + G) α}
    (f : α → β) (h : QuerySubsumes oa₁ oa₂) :
    QuerySubsumes (f <$> oa₁) (f <$> oa₂) := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  exact h.bind fun a => .ret (f a)

theorem isQueryBound {B : Type*} {α : Type} {oa₁ oa₂ : OracleComp (unifSpec + G) α}
    {b : B} {canQuery : (unifSpec + G).Domain → B → Prop}
    {cost : (unifSpec + G).Domain → B → B}
    (h : QuerySubsumes oa₁ oa₂)
    (hcan : ∀ n b', canQuery (.inl n) b')
    (hcost : ∀ n b', cost (.inl n) b' = b')
    (hb : IsQueryBound oa₂ b canQuery cost) :
    IsQueryBound oa₁ b canQuery cost := by
  induction h generalizing b with
  | ret _ => trivial
  | coin_l n k _ _ ih =>
    rw [isQueryBound_query_bind_iff]
    refine ⟨hcan n b, fun u => ?_⟩
    rw [hcost n b]
    exact ih u hb
  | coin_r _ n k u _ ih =>
    rw [isQueryBound_query_bind_iff] at hb
    have hbu := hb.2 u
    rw [hcost n b] at hbu
    exact ih hbu
  | game g k₁ k₂ _ ih =>
    rw [isQueryBound_query_bind_iff] at hb ⊢
    exact ⟨hb.1, fun r => ih r (hb.2 r)⟩

theorem isQueryBoundP {α : Type} {oa₁ oa₂ : OracleComp (unifSpec + G) α}
    {p : (unifSpec + G).Domain → Prop} [DecidablePred p] {n : ℕ}
    (h : QuerySubsumes oa₁ oa₂)
    (hp : ∀ u, ¬ p (.inl u))
    (hb : oa₂.IsQueryBoundP p n) :
    oa₁.IsQueryBoundP p n := by
  induction h generalizing n with
  | ret _ => trivial
  | coin_l m k _ _ ih =>
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl (hp m), fun u => ?_⟩
    simp only [hp m, ↓reduceIte]
    exact ih u hb
  | coin_r _ m k u _ ih =>
    rw [isQueryBoundP_query_bind_iff] at hb
    have hbu := hb.2 u
    simp only [hp m, ↓reduceIte] at hbu
    exact ih hbu
  | game g k₁ k₂ _ ih =>
    rw [isQueryBoundP_query_bind_iff] at hb ⊢
    exact ⟨hb.1, fun r => ih r (hb.2 r)⟩

theorem allQueriesSatisfy {α : Type} {oa₁ oa₂ : OracleComp (unifSpec + G) α}
    {P : (unifSpec + G).Domain → Prop}
    (h : QuerySubsumes oa₁ oa₂)
    (hP : ∀ u, P (.inl u))
    (hb : AllQueriesSatisfy oa₂ P) :
    AllQueriesSatisfy oa₁ P := by
  rw [allQueriesSatisfy_def] at hb ⊢
  exact h.isQueryBound (fun u _ => hP u) (fun _ _ => rfl) hb

end Basic

/-! ## Coin lifting -/

section LiftP

variable {κ : Type} {G : OracleSpec.{0, 0} κ}

theorem pure_liftP_of_mem_support {S : Sig} (I : Iface S (unifSpec + G))
    (hFwdU : ∀ n, I.fwdU n = query (spec := unifSpec + G) (.inl n))
    {α : Type} (c : ProbComp α) {a : α} (ha : a ∈ support c) :
    QuerySubsumes (pure a) (I.liftP c) := by
  induction c using OracleComp.inductionOn with
  | pure x =>
    rw [support_pure, Set.mem_singleton_iff] at ha
    subst ha
    exact .ret a
  | query_bind n mx ih =>
    rw [mem_support_bind_iff] at ha
    obtain ⟨u, _, hmu⟩ := ha
    have hstep :
        I.liftP (liftM (OracleSpec.query (spec := unifSpec) n) >>= mx) =
          liftM (OracleSpec.query (spec := unifSpec + G) (.inl n)) >>=
            fun v => I.liftP (mx v) := by
      dsimp only [Iface.liftP]
      rw [simulateQ_query_bind]
      change (I.fwdU n >>= fun v => I.liftP (mx v)) = _
      rw [hFwdU n]
      rfl
    rw [hstep]
    exact .coin_r (pure a) n (fun v => I.liftP (mx v)) u (ih u hmu)

theorem liftP_bind_left {S : Sig} (I : Iface S (unifSpec + G))
    (hFwdU : ∀ n, I.fwdU n = query (spec := unifSpec + G) (.inl n))
    {α β : Type} (c : ProbComp α) (k : α → OracleComp (unifSpec + G) β)
    (oa₂ : OracleComp (unifSpec + G) β)
    (hk : ∀ a, QuerySubsumes (k a) oa₂) :
    QuerySubsumes (I.liftP c >>= k) oa₂ := by
  induction c using OracleComp.inductionOn with
  | pure a =>
    have hp : I.liftP (pure a) = pure a := simulateQ_pure _ a
    rw [hp, pure_bind]
    exact hk a
  | query_bind n mx ih =>
    have hstep :
        (I.liftP (liftM (OracleSpec.query (spec := unifSpec) n) >>= mx) >>= k) =
          liftM (OracleSpec.query (spec := unifSpec + G) (.inl n)) >>=
            fun u => I.liftP (mx u) >>= k := by
      dsimp only [Iface.liftP]
      rw [simulateQ_query_bind, bind_assoc]
      change (I.fwdU n >>= fun u => I.liftP (mx u) >>= k) = _
      rw [hFwdU n]
      rfl
    rw [hstep]
    exact .coin_l n _ oa₂ fun u => ih u

theorem liftP_map_uniformSample {S₁ S₂ : Sig}
    (I₁ : Iface S₁ (unifSpec + G)) (I₂ : Iface S₂ (unifSpec + G))
    (hFwdU₁ : ∀ n, I₁.fwdU n = query (spec := unifSpec + G) (.inl n))
    (hFwdU₂ : ∀ n, I₂.fwdU n = query (spec := unifSpec + G) (.inl n))
    {α β : Type} [SampleableType β] (c : ProbComp α) (f : α → β) :
    QuerySubsumes (I₂.liftP c >>= fun x => pure (f x)) (I₁.liftP ($ᵗ β)) :=
  liftP_bind_left I₂ hFwdU₂ c _ _ fun _ =>
    pure_liftP_of_mem_support I₁ hFwdU₁ ($ᵗ β) (mem_support_uniformSample (α := β))

theorem sampleBoolFig8Comp_querySubsumes (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (lam : Pt)
    {S₁ : Sig} (I₁ : Iface S₁ (unifSpec + G))
    (I₂ : Iface (atomicSig ℓ Pt) (unifSpec + G))
    (hFwdU₁ : ∀ n, I₁.fwdU n = query (spec := unifSpec + G) (.inl n))
    (hFwdU₂ : ∀ n, I₂.fwdU n = query (spec := unifSpec + G) (.inl n))
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (sampBv128 : Comp (atomicFig8Ops ℓ Pt C Dh encPt encT lam) I₂ Γ BV128)
    (ρ : Env Γ)
    (hSamp : sampBv128.eval ρ = I₂.liftP ($ᵗ (BitVec 128) : ProbComp (BitVec 128))) :
    QuerySubsumes
      ((sampleBoolFig8Comp ℓ Pt C Dh encPt encT lam sampBv128).eval ρ)
      (I₁.liftP ($ᵗ Bool : ProbComp Bool)) := by
  simp only [sampleBoolFig8Comp, Comp.eval, hSamp]
  exact liftP_map_uniformSample I₁ I₂ hFwdU₁ hFwdU₂ ($ᵗ (BitVec 128)) _

end LiftP

/-! ## Compiler preservation -/

section Compiler

variable {κ : Type} {G : OracleSpec.{0, 0} κ}

private theorem iterM_querySubsumes_hom
    {α β : Type} (g : α → β)
    (f₁ : α → OracleComp (unifSpec + G) α) (f₂ : β → OracleComp (unifSpec + G) β)
    (hf : ∀ a, QuerySubsumes (f₂ (g a)) (g <$> f₁ a)) :
    ∀ (n : ℕ) (a : α), QuerySubsumes (iterM f₂ n (g a)) (g <$> iterM f₁ n a)
  | 0, _ => of_eq (by simp [iterM])
  | n + 1, a => by
    dsimp only [iterM]
    refine ((hf a).bind fun _ => .refl _).trans ?_
    rw [bind_map_left, map_bind]
    exact (QuerySubsumes.refl (f₁ a)).bind fun a' => iterM_querySubsumes_hom g f₁ f₂ hf n a'

private theorem findML_querySubsumes_hom
    {α β : Type} (g : α → β)
    (p₁ : α → OracleComp (unifSpec + G) Bool) (p₂ : β → OracleComp (unifSpec + G) Bool)
    (hp : ∀ x, QuerySubsumes (p₂ (g x)) (p₁ x)) :
    ∀ xs : List α, QuerySubsumes (findML p₂ (xs.map g)) (Option.map g <$> findML p₁ xs)
  | [] => of_eq (by simp [findML])
  | x :: xs => by
    dsimp only [List.map_cons, findML]
    rw [map_bind]
    refine (hp x).bind fun b => match b with
      | true => of_eq (by simp)
      | false => findML_querySubsumes_hom g p₁ p₂ hp xs

private theorem anyML_querySubsumes_hom
    {α β : Type} (g : α → β)
    (p₁ : α → OracleComp (unifSpec + G) Bool) (p₂ : β → OracleComp (unifSpec + G) Bool)
    (hp : ∀ x, QuerySubsumes (p₂ (g x)) (p₁ x)) :
    ∀ xs : List α, QuerySubsumes (anyML p₂ (xs.map g)) (anyML p₁ xs)
  | [] => .refl _
  | x :: xs => by
    dsimp only [List.map_cons, anyML]
    exact (hp x).bind fun b => match b with
      | true => .refl _
      | false => anyML_querySubsumes_hom g p₁ p₂ hp xs

private theorem mapML_querySubsumes_hom
    {α₁ α₂ β₁ β₂ : Type} (g : α₁ → α₂) (h : β₁ → β₂)
    (f₁ : α₁ → OracleComp (unifSpec + G) β₁) (f₂ : α₂ → OracleComp (unifSpec + G) β₂)
    (hf : ∀ x, QuerySubsumes (f₂ (g x)) (h <$> f₁ x)) :
    ∀ xs : List α₁, QuerySubsumes (mapML f₂ (xs.map g)) (List.map h <$> mapML f₁ xs)
  | [] => of_eq (by simp [mapML])
  | x :: xs => by
    dsimp only [List.map_cons, mapML]
    refine ((hf x).bind fun _ => .refl _).trans ?_
    rw [bind_map_left, map_bind]
    refine (QuerySubsumes.refl (f₁ x)).bind fun y => ?_
    rw [map_bind]
    refine ((mapML_querySubsumes_hom g h f₁ f₂ hf xs).bind fun _ => .refl _).trans ?_
    rw [bind_map_left]
    exact of_eq (by simp)

private theorem consumeFirstML_querySubsumes_hom
    {α β : Type} (g : α → β)
    (p₁ : α → OracleComp (unifSpec + G) Bool) (p₂ : β → OracleComp (unifSpec + G) Bool)
    (mk₁ : α → α) (mk₂ : β → β)
    (hp : ∀ x, QuerySubsumes (p₂ (g x)) (p₁ x))
    (hmk : ∀ x, mk₂ (g x) = g (mk₁ x)) :
    ∀ xs : List α,
      QuerySubsumes (consumeFirstML p₂ mk₂ (xs.map g))
        (Prod.map id (List.map g) <$> consumeFirstML p₁ mk₁ xs)
  | [] => of_eq (by simp [consumeFirstML])
  | x :: xs => by
    dsimp only [List.map_cons, consumeFirstML]
    rw [map_bind]
    refine (hp x).bind fun b => ?_
    cases b with
    | true => exact of_eq (by simp [hmk x])
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [map_bind]
      refine ((consumeFirstML_querySubsumes_hom g p₁ p₂ mk₁ mk₂ hp hmk xs).bind
        fun _ => .refl _).trans ?_
      rw [bind_map_left]
      exact of_eq (by simp)

private theorem foldML_querySubsumes_hom
    {α₁ α₂ β₁ β₂ : Type} (g : α₁ → α₂) (h : β₁ → β₂)
    (f₁ : α₁ → β₁ → OracleComp (unifSpec + G) β₁)
    (f₂ : α₂ → β₂ → OracleComp (unifSpec + G) β₂)
    (hf : ∀ x b, QuerySubsumes (f₂ (g x) (h b)) (h <$> f₁ x b)) :
    ∀ (b : β₁) (xs : List α₁),
      QuerySubsumes (foldML f₂ (h b) (xs.map g)) (h <$> foldML f₁ b xs)
  | _, [] => of_eq (by simp [foldML])
  | b, x :: xs => by
    dsimp only [List.map_cons, foldML]
    refine ((hf x b).bind fun _ => .refl _).trans ?_
    rw [bind_map_left, map_bind]
    exact (QuerySubsumes.refl (f₁ x b)).bind fun b' =>
      foldML_querySubsumes_hom g h f₁ f₂ hf b' xs

theorem simulateQ_congr_querySubsumes {ι : Type} {H : OracleSpec.{0, 0} ι} {σ α : Type}
    (impl : QueryImpl (unifSpec + H) (StateT σ (OracleComp (unifSpec + G))))
    (hCoin : ∀ n s,
      (impl (.inl n)).run s =
        (liftM (OracleSpec.query (spec := unifSpec + G) (.inl n)) >>= fun u => pure (u, s)))
    {oa₁ oa₂ : OracleComp (unifSpec + H) α}
    (h : QuerySubsumes oa₁ oa₂) (s : σ) :
    QuerySubsumes ((simulateQ impl oa₁).run s) ((simulateQ impl oa₂).run s) := by
  induction h generalizing s with
  | ret a => exact .ret (a, s)
  | coin_l n k oa₂ _ ih =>
    rw [simulateQ_query_bind, StateT.run_bind]
    change QuerySubsumes
      ((impl (.inl n)).run s >>= fun p => (simulateQ impl (k p.1)).run p.2)
      ((simulateQ impl oa₂).run s)
    rw [hCoin n s, bind_assoc]
    refine .coin_l n _ _ fun u => ?_
    rw [pure_bind]
    exact ih u s
  | coin_r oa₁ n k u _ ih =>
    rw [simulateQ_query_bind, StateT.run_bind]
    change QuerySubsumes ((simulateQ impl oa₁).run s)
      ((impl (.inl n)).run s >>= fun p => (simulateQ impl (k p.1)).run p.2)
    rw [hCoin n s, bind_assoc]
    refine .coin_r _ n _ u ?_
    rw [pure_bind]
    exact ih s
  | game g k₁ k₂ _ ih =>
    rw [simulateQ_query_bind, StateT.run_bind, simulateQ_query_bind, StateT.run_bind]
    change QuerySubsumes
      ((impl (.inr g)).run s >>= fun p => (simulateQ impl (k₁ p.1)).run p.2)
      ((impl (.inr g)).run s >>= fun p => (simulateQ impl (k₂ p.1)).run p.2)
    exact (QuerySubsumes.refl ((impl (.inr g)).run s)).bind fun p => ih p.1 p.2

theorem simulateQ_state_querySubsumes {ι : Type} {H : OracleSpec.{0, 0} ι}
    {σ₁ σ₂ α : Type} (mkSt : σ₁ → σ₂)
    {impl₁ : QueryImpl H (StateT σ₁ (OracleComp (unifSpec + G)))}
    {impl₂ : QueryImpl H (StateT σ₂ (OracleComp (unifSpec + G)))}
    (hStep : ∀ q s₁,
      QuerySubsumes ((impl₂ q).run (mkSt s₁)) (Prod.map id mkSt <$> (impl₁ q).run s₁))
    (oa : OracleComp H α) (s₁ : σ₁) :
    QuerySubsumes
      ((simulateQ impl₂ oa).run (mkSt s₁))
      (Prod.map id mkSt <$> (simulateQ impl₁ oa).run s₁) := by
  induction oa using OracleComp.inductionOn generalizing s₁ with
  | pure a => exact of_eq (by simp)
  | query_bind q k ih =>
    rw [simulateQ_query_bind, StateT.run_bind, simulateQ_query_bind, StateT.run_bind]
    change QuerySubsumes
      ((impl₂ q).run (mkSt s₁) >>= fun p => (simulateQ impl₂ (k p.1)).run p.2)
      (Prod.map id mkSt <$> ((impl₁ q).run s₁ >>= fun p => (simulateQ impl₁ (k p.1)).run p.2))
    rw [map_bind]
    refine ((hStep q s₁).bind fun _ => .refl _).trans ?_
    rw [bind_map_left]
    exact (QuerySubsumes.refl ((impl₁ q).run s₁)).bind fun ⟨r, s₁'⟩ => ih r s₁'

theorem compilePureAuxComp_querySubsumes {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {I₁ : Iface S₁ (unifSpec + G)} {I₂ : Iface S₂ (unifSpec + G)} {auxT : Ty S₂}
    (M : PureAuxBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    (toDen : (b : S₁.Base) → S₁.den b → (M.fSort b).denote) (aux : auxT.denote)
    (hOpE : ∀ o x,
      (M.opMacro o).eval (.cons (toVal M.fSort toDen (O₁.dom o) x) (.cons aux .nil)) =
        toVal M.fSort toDen (O₁.cod o) (O₁.eval o x))
    (hSampSub : ∀ s x,
      QuerySubsumes
        ((M.sampMacro s).eval (.cons (toVal M.fSort toDen (I₁.smp.sDom s) x) (.cons aux .nil)))
        (toVal M.fSort toDen (I₁.smp.sTy s) <$> I₁.liftP (I₁.smp.samp s x)))
    (hQuerySub : ∀ g x,
      QuerySubsumes
        ((M.queryMacro g).eval (.cons (toVal M.fSort toDen (I₁.dom g) x) (.cons aux .nil)))
        (toVal M.fSort toDen (I₁.cod g) <$>
          (I₁.dec g x <$> (liftM (OracleSpec.query (spec := unifSpec + G) (I₁.enc g x)) :
            OracleComp (unifSpec + G) _))))
    {Γ : List (Ty S₁)} {t : Ty S₁} (c : Comp O₁ I₁ Γ t) (ρ : Env Γ) :
    QuerySubsumes
      ((compilePureAuxComp M c).eval (mapEnvAux M.fSort toDen aux ρ))
      (toVal M.fSort toDen t <$> c.eval ρ) := by
  induction c with
  | ret e =>
    exact of_eq
      (by simp [compilePureAuxComp, Comp.eval, compilePureAuxExpr_eval M toDen aux hOpE e ρ])
  | bind c k ihc ihk =>
    dsimp only [compilePureAuxComp, Comp.eval]
    refine ((ihc ρ).bind fun _ => .refl _).trans ?_
    rw [bind_map_left, map_bind]
    exact (QuerySubsumes.refl (c.eval ρ)).bind fun x => ihk (.cons x ρ)
  | ite b c d ihc ihd =>
    dsimp only [compilePureAuxComp, Comp.eval]
    rw [compilePureAuxExpr_eval M toDen aux hOpE b ρ]
    dsimp only [toVal]
    cases b.eval ρ with
    | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact ihd ρ
    | true => simp only [↓reduceIte]; exact ihc ρ
  | caseOpt e n s ihn ihs =>
    dsimp only [compilePureAuxComp, Comp.eval]
    rw [compilePureAuxExpr_eval M toDen aux hOpE e ρ]
    dsimp only [toVal]
    cases e.eval ρ with
    | none => exact ihn ρ
    | some x => exact ihs (.cons x ρ)
  | caseSum e l r ihl ihr =>
    dsimp only [compilePureAuxComp, Comp.eval]
    rw [compilePureAuxExpr_eval M toDen aux hOpE e ρ]
    dsimp only [toVal]
    cases e.eval ρ with
    | inl x => exact ihl (.cons x ρ)
    | inr y => exact ihr (.cons y ρ)
  | sample s e =>
    dsimp only [compilePureAuxComp, Comp.eval]
    rw [pure_bind, compilePureAuxExpr_eval M toDen aux hOpE e ρ,
      callMacroAux_eval M.fSort toDen aux ρ]
    exact hSampSub s (e.eval ρ)
  | query g e =>
    dsimp only [compilePureAuxComp, Comp.eval]
    rw [pure_bind, compilePureAuxExpr_eval M toDen aux hOpE e ρ,
      callMacroAux_eval M.fSort toDen aux ρ]
    exact hQuerySub g (e.eval ρ)
  | iter n e body ihb =>
    dsimp only [compilePureAuxComp, Comp.eval]
    rw [compilePureAuxExpr_eval M toDen aux hOpE e ρ]
    exact iterM_querySubsumes_hom (toVal M.fSort toDen _)
      (fun a => body.eval (.cons a ρ)) _ (fun a => ihb (.cons a ρ)) n (e.eval ρ)
  | findM K l p ihp =>
    dsimp only [compilePureAuxComp, Comp.eval]
    rw [compilePureAuxExpr_eval M toDen aux hOpE l ρ]
    dsimp only [toVal]
    rw [← List.map_take]
    exact findML_querySubsumes_hom (toVal M.fSort toDen _)
      (fun x => p.eval (.cons x ρ)) _ (fun x => (ihp (.cons x ρ)).trans
        (of_eq (show id <$> p.eval (.cons x ρ) = _ from id_map _)))
      ((l.eval ρ).take K)
  | anyM K l p ihp =>
    dsimp only [compilePureAuxComp, Comp.eval]
    rw [compilePureAuxExpr_eval M toDen aux hOpE l ρ]
    dsimp only [toVal]
    rw [← List.map_take]
    refine (anyML_querySubsumes_hom (toVal M.fSort toDen _)
      (fun x => p.eval (.cons x ρ)) _ (fun x => (ihp (.cons x ρ)).trans
        (of_eq (show id <$> p.eval (.cons x ρ) = _ from id_map _)))
      ((l.eval ρ).take K)).trans ?_
    exact of_eq (show _ = id <$> _ from (id_map _).symm)
  | mapM K l f ihf =>
    dsimp only [compilePureAuxComp, Comp.eval]
    rw [compilePureAuxExpr_eval M toDen aux hOpE l ρ]
    dsimp only [toVal]
    rw [← List.map_take]
    exact mapML_querySubsumes_hom (toVal M.fSort toDen _) (toVal M.fSort toDen _)
      (fun x => f.eval (.cons x ρ)) _ (fun x => ihf (.cons x ρ)) ((l.eval ρ).take K)
  | consumeFirstM K l p mk ihp =>
    dsimp only [compilePureAuxComp, Comp.eval]
    rw [compilePureAuxExpr_eval M toDen aux hOpE l ρ]
    dsimp only [toVal]
    rw [← List.map_take]
    exact consumeFirstML_querySubsumes_hom (toVal M.fSort toDen _)
      (fun x => p.eval (.cons x ρ)) _ (fun x => mk.eval (.cons x ρ)) _
      (fun x => (ihp (.cons x ρ)).trans
        (of_eq (show id <$> p.eval (.cons x ρ) = _ from id_map _)))
      (fun x => compilePureAuxExpr_eval M toDen aux hOpE mk (.cons x ρ)) ((l.eval ρ).take K)
  | foldM K l z f ihf =>
    dsimp only [compilePureAuxComp, Comp.eval]
    rw [compilePureAuxExpr_eval M toDen aux hOpE l ρ,
      compilePureAuxExpr_eval M toDen aux hOpE z ρ]
    dsimp only [toVal]
    rw [← List.map_take]
    exact foldML_querySubsumes_hom (toVal M.fSort toDen _) (toVal M.fSort toDen _)
      (fun x acc => f.eval (.cons x (.cons acc ρ))) _
      (fun x acc => ihf (.cons x (.cons acc ρ))) (z.eval ρ) ((l.eval ρ).take K)

theorem compilePureAuxRed_querySubsumes {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι : Type} {H : OracleSpec.{0, 0} ι}
    {I₁ : Iface S₁ (unifSpec + G)} {I₂ : Iface S₂ (unifSpec + G)}
    {C₁ : GameCodec S₁ H} {C₂ : GameCodec S₂ H} {auxT : Ty S₂}
    (M : PureAuxBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    {rIn₁ aIn₁ aOut₁ out₁ : Ty S₁} {rIn₂ aIn₂ aOut₂ out₂ : Ty S₂}
    (Ad : PureAuxAdapters M.fSort O₂ C₁ C₂ auxT rIn₁ aIn₁ aOut₁ out₁ rIn₂ aIn₂ aOut₂ out₂)
    (R : CostedReduction O₁ I₁ H C₁ rIn₁ aIn₁ aOut₁ out₁)
    (toDen : (b : S₁.Base) → S₁.den b → (M.fSort b).denote)
    (x₁ : rIn₁.denote) (x₂ : rIn₂.denote) (aux : auxT.denote)
    (hSplit : Ad.splitIn.eval (.cons x₂ .nil) = (toVal M.fSort toDen rIn₁ x₁, aux))
    (hOpE : ∀ o x,
      (M.opMacro o).eval (.cons (toVal M.fSort toDen (O₁.dom o) x) (.cons aux .nil)) =
        toVal M.fSort toDen (O₁.cod o) (O₁.eval o x))
    (hSampSub : ∀ s x,
      QuerySubsumes
        ((M.sampMacro s).eval (.cons (toVal M.fSort toDen (I₁.smp.sDom s) x) (.cons aux .nil)))
        (toVal M.fSort toDen (I₁.smp.sTy s) <$> I₁.liftP (I₁.smp.samp s x)))
    (hQuerySub : ∀ g x,
      QuerySubsumes
        ((M.queryMacro g).eval (.cons (toVal M.fSort toDen (I₁.dom g) x) (.cons aux .nil)))
        (toVal M.fSort toDen (I₁.cod g) <$>
          (I₁.dec g x <$> (liftM (OracleSpec.query (spec := unifSpec + G) (I₁.enc g x)) :
            OracleComp (unifSpec + G) _))))
    (hFwdU₁ : ∀ n, I₁.fwdU n = query (spec := unifSpec + G) (.inl n))
    (hFwdU₂ : ∀ n, I₂.fwdU n = query (spec := unifSpec + G) (.inl n))
    (hQ : ∀ q : H.Domain,
      Ad.adaptQ.eval (.cons (C₂.qenc q) .nil) = toVal M.fSort toDen C₁.Q (C₁.qenc q))
    (hR : ∀ (q : H.Domain) (r₁ : C₁.R.denote),
      C₂.rdec q (Ad.adaptR.eval (.cons (toVal M.fSort toDen C₁.R r₁) (.cons (C₂.qenc q) .nil))) =
        C₁.rdec q r₁)
    (adv₁ : aIn₁.denote → OracleComp (unifSpec + H) aOut₁.denote)
    (adv₂ : aIn₂.denote → OracleComp (unifSpec + H) aOut₂.denote)
    (toOut : aOut₁.denote → aOut₂.denote)
    (hAdv : ∀ a₁ : aIn₁.denote,
      QuerySubsumes
        (adv₂ (Ad.adaptAIn.eval (.cons (toVal M.fSort toDen aIn₁ a₁) .nil)))
        (toOut <$> adv₁ a₁))
    (hAOut : ∀ b₁ : aOut₁.denote,
      Ad.adaptAOut.eval (.cons (toOut b₁) .nil) = toVal M.fSort toDen aOut₁ b₁)
    {outEq : out₁.denote → out₂.denote}
    (hOut : ∀ y₁ : out₁.denote,
      Ad.adaptOut.eval (.cons (toVal M.fSort toDen out₁ y₁) .nil) = outEq y₁) :
    QuerySubsumes
      ((compilePureAuxRed M Ad R).eval adv₂ x₂)
      (outEq <$> R.eval adv₁ x₁) := by
  let R₂ := compilePureAuxRed M Ad R
  let mkSt : R.σ.denote → R₂.σ.denote := fun s => (toVal M.fSort toDen R.σ s, aux)
  have hInit :
      QuerySubsumes
        (R₂.init.eval (.cons x₂ .nil))
        ((fun (p : (aIn₁.prod R.σ).denote) =>
          ((Ad.adaptAIn.eval (.cons (toVal M.fSort toDen aIn₁ p.1) .nil),
            mkSt p.2) : (aIn₂.prod R₂.σ).denote)) <$>
          R.init.eval (.cons x₁ .nil)) := by
    simp only [R₂, compilePureAuxRed, Comp.eval, pure_bind, Expr.eval, Env.get, hSplit]
    rw [Comp.wkTop2_eval]
    change QuerySubsumes
      (do
        let x ← (compilePureAuxComp M R.init).eval (mapEnvAux M.fSort toDen aux (.cons x₁ .nil))
        _)
      _
    rw [map_eq_bind_pure_comp, Function.comp_def]
    refine ((compilePureAuxComp_querySubsumes M toDen aux hOpE hSampSub hQuerySub R.init
      (.cons x₁ .nil)).bind fun _ => .refl _).trans ?_
    rw [bind_map_left]
    refine of_eq (bind_congr fun p => ?_)
    congr 1; congr 1
    dsimp only [toVal]
    exact Expr.wkTop1_eval Ad.adaptAIn _ _
  have hStep :
      ∀ (q : (unifSpec + H).Domain) (s₁ : R.σ.denote),
        QuerySubsumes
          ((R₂.impl q).run (mkSt s₁))
          (Prod.map id mkSt <$> (R.impl q).run s₁) := by
    intro q s₁
    rcases q with n | t
    · refine of_eq ?_
      change
        (StateT.lift (I₂.fwdU n)).run (mkSt s₁) =
          Prod.map id mkSt <$> (StateT.lift (I₁.fwdU n)).run s₁
      rw [StateT.run_lift, StateT.run_lift, hFwdU₂ n, hFwdU₁ n]
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, Prod.map, id_eq]
    · simp only [R₂, CostedReduction.impl, handlerImpl, StateT.run_mk,
        compilePureAuxRed, Comp.eval, pure_bind, Expr.eval, Env.get, mkSt]
      have hq' :
          (Expr.wkTop1 Ad.adaptQ).eval
            (Env.cons (C₂.qenc t)
              (Env.cons aux
                (Env.cons (t := .prod (mapTy M.fSort R.σ) auxT)
                  (toVal M.fSort toDen R.σ s₁, aux) (Env.cons (C₂.qenc t) Env.nil)))) =
            toVal M.fSort toDen C₁.Q (C₁.qenc t) := by
        rw [Expr.wkTop1_eval]; exact hQ t
      rw [hq', Comp.wkTop3_eval]
      have hm :
          Env.cons (toVal M.fSort toDen R.σ s₁)
            (Env.cons (toVal M.fSort toDen C₁.Q (C₁.qenc t)) (Env.cons aux Env.nil)) =
            mapEnvAux M.fSort toDen aux (.cons s₁ (.cons (C₁.qenc t) .nil)) := rfl
      dsimp only [compilePureAuxRed, Ty.denote]
      rw [hm, bind_assoc, map_bind]
      refine ((compilePureAuxComp_querySubsumes M toDen aux hOpE hSampSub hQuerySub R.handle
        (.cons s₁ (.cons (C₁.qenc t) .nil))).bind fun _ => .refl _).trans ?_
      rw [bind_map_left]
      refine of_eq (bind_congr fun p => ?_)
      simp only [pure_bind, map_pure, Prod.map, id_eq, toVal]
      congr 1; congr 1
      rw [callAdaptR_eval]
      exact hR t p.1
  have hCoinR₂ :
      ∀ (n : ℕ) (s₂ : R₂.σ.denote),
        (R₂.impl (.inl n)).run s₂ =
          (liftM (OracleSpec.query (spec := unifSpec + G) (.inl n)) >>= fun u => pure (u, s₂)) := by
    intro n s₂
    change (StateT.lift (I₂.fwdU n)).run s₂ = _
    rw [StateT.run_lift, hFwdU₂ n]
    rfl
  unfold CostedReduction.eval
  rw [map_bind]
  refine (hInit.bind fun _ => .refl _).trans ?_
  rw [bind_map_left]
  refine (QuerySubsumes.refl (R.init.eval (.cons x₁ .nil))).bind fun ⟨a₁, s₁⟩ => ?_
  dsimp only
  rw [map_bind]
  have hAdvStep :
      QuerySubsumes
        ((simulateQ R₂.impl
          (adv₂ (Ad.adaptAIn.eval (.cons (toVal M.fSort toDen aIn₁ a₁) .nil)))).run (mkSt s₁))
        (Prod.map toOut mkSt <$> (simulateQ R.impl (adv₁ a₁)).run s₁) := by
    refine (simulateQ_congr_querySubsumes R₂.impl hCoinR₂ (hAdv a₁) (mkSt s₁)).trans ?_
    rw [simulateQ_map, StateT.run_map]
    have hHom := (simulateQ_state_querySubsumes mkSt hStep (adv₁ a₁) s₁).map (Prod.map toOut id)
    rw [Functor.map_map] at hHom
    exact hHom
  refine (hAdvStep.bind fun _ => .refl _).trans ?_
  rw [bind_map_left]
  refine (QuerySubsumes.refl ((simulateQ R.impl (adv₁ a₁)).run s₁)).bind fun ⟨b₁, s₁'⟩ => ?_
  dsimp only [Prod.map, R₂]
  simp only [compilePureAuxRed, Comp.eval, pure_bind, Expr.eval, Env.get, mkSt]
  have hb' :
      (Expr.wkTop1 Ad.adaptAOut).eval
        (Env.cons (toOut b₁)
          (Env.cons aux
            (Env.cons (t := .prod (mapTy M.fSort R.σ) auxT)
              (toVal M.fSort toDen R.σ s₁', aux) (Env.cons (toOut b₁) Env.nil)))) =
        toVal M.fSort toDen aOut₁ b₁ := by
    rw [Expr.wkTop1_eval]; exact hAOut b₁
  rw [hb', Comp.wkTop3_eval]
  have hm' :
      Env.cons (toVal M.fSort toDen R.σ s₁')
        (Env.cons (toVal M.fSort toDen aOut₁ b₁) (Env.cons aux Env.nil)) =
        mapEnvAux M.fSort toDen aux (.cons s₁' (.cons b₁ .nil)) := rfl
  rw [hm']
  have hFinL :
      ((compilePureAuxComp M R.finish).eval
          (mapEnvAux M.fSort toDen aux (.cons s₁' (.cons b₁ .nil))) >>=
        fun z => pure ((Expr.wkTop1 Ad.adaptOut).eval
          (Env.cons z (Env.cons z (Env.cons (toVal M.fSort toDen R.σ s₁')
            (Env.cons (toVal M.fSort toDen aOut₁ b₁)
              (Env.cons aux (Env.cons (t := .prod (mapTy M.fSort R.σ) auxT)
                (toVal M.fSort toDen R.σ s₁', aux)
                (Env.cons (toOut b₁) Env.nil))))))))) =
      (fun z => Ad.adaptOut.eval (.cons z .nil)) <$>
        (compilePureAuxComp M R.finish).eval
          (mapEnvAux M.fSort toDen aux (.cons s₁' (.cons b₁ .nil))) := by
    rw [map_eq_bind_pure_comp, Function.comp_def]
    refine bind_congr fun z => ?_
    rw [Expr.wkTop1_eval]
  have hFinR :
      (fun z => Ad.adaptOut.eval (.cons z .nil)) <$>
        (toVal M.fSort toDen out₁ <$> R.finish.eval (.cons s₁' (.cons b₁ .nil))) =
      outEq <$> R.finish.eval (.cons s₁' (.cons b₁ .nil)) := by
    rw [Functor.map_map]
    congr 1
    funext y₁
    exact hOut y₁
  rw [hFinL, ← hFinR]
  exact (compilePureAuxComp_querySubsumes M toDen aux hOpE hSampSub hQuerySub R.finish
    (.cons s₁' (.cons b₁ .nil))).map (fun z => Ad.adaptOut.eval (.cons z .nil))

end Compiler

/-! ## Protocol query bounds -/

section ProtocolBounds

theorem smMakesAtMostQueries_of_querySubsumes {St Msg Coins C : Type}
    {A₁ A₂ : CryptoGames.SM.Adversary St Msg Coins C} {q : ℕ}
    (h : QuerySubsumes A₁ A₂) (hq : CryptoGames.SM.MakesAtMostQueries A₂ q) :
    CryptoGames.SM.MakesAtMostQueries A₁ q :=
  h.isQueryBoundP (fun _ => by simp) hq

theorem sendMsgsOk_of_querySubsumes {St Msg Coins C : Type} {ok : Msg → Bool}
    {A₁ A₂ : CryptoGames.SM.Adversary St Msg Coins C}
    (h : QuerySubsumes A₁ A₂)
    (hok : CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk ok A₂) :
    CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk ok A₁ :=
  h.isQueryBoundP (fun _ => by simp [CryptoGames.LibsignalSM.Proofs.SessionShort.badSendMsg]) hok

theorem smEqualPubChalls_of_querySubsumes {St Msg Coins C Pub : Type} [DecidableEq Pub]
    {pubOf : Msg → Pub} {A₁ A₂ : CryptoGames.SM.Adversary St Msg Coins C}
    (h : QuerySubsumes A₁ A₂) (heq : CryptoGames.SM.EqualPubChalls pubOf A₂) :
    CryptoGames.SM.EqualPubChalls pubOf A₁ :=
  h.isQueryBoundP (fun _ => by simp [CryptoGames.SM.unequalPubChall]) heq

theorem fsaeadMakesAtMostQueries_of_querySubsumes {SS RS AD Msg C : Type}
    {R₁ R₂ : CryptoGames.FSAEAD.Adversary SS RS AD Msg C} {q : ℕ}
    (h : QuerySubsumes R₁ R₂) (hq : CryptoGames.FSAEAD.MakesAtMostQueries R₂ q) :
    CryptoGames.FSAEAD.MakesAtMostQueries R₁ q :=
  h.isQueryBoundP (fun _ => by simp) hq

theorem fsaeadMakesAtMostDecQueries_of_querySubsumes {SS RS AD Msg C : Type}
    {R₁ R₂ : CryptoGames.FSAEAD.Adversary SS RS AD Msg C} {qd : ℕ}
    (h : QuerySubsumes R₁ R₂) (hqd : CryptoGames.FSAEAD.MakesAtMostDecQueries R₂ qd) :
    CryptoGames.FSAEAD.MakesAtMostDecQueries R₁ qd :=
  h.isQueryBoundP (fun _ => by simp [CryptoGames.FSAEAD.isDecQuery]) hqd

theorem fsaeadEqualPubChallenges_of_querySubsumes {SS RS AD Pub M C : Type} [DecidableEq Pub]
    {R₁ R₂ : CryptoGames.FSAEAD.Adversary SS RS AD (Pub × M) C}
    (h : QuerySubsumes R₁ R₂) (heq : CryptoGames.FSAEAD.EqualPubChallenges R₂) :
    CryptoGames.FSAEAD.EqualPubChallenges R₁ :=
  h.isQueryBoundP (fun _ => by simp [CryptoGames.FSAEAD.unequalPubChall]) heq

theorem fsaeadAllQueriesInOneADClass_of_querySubsumes {SS RS AD Msg C κ : Type} [DecidableEq κ]
    {cls : AD → κ} {R₁ R₂ : CryptoGames.FSAEAD.Adversary SS RS AD Msg C}
    (h : QuerySubsumes R₁ R₂) (hcls : CryptoGames.FSAEAD.AllQueriesInOneADClass cls R₂) :
    CryptoGames.FSAEAD.AllQueriesInOneADClass cls R₁ := by
  obtain ⟨k₀, hk₀⟩ := hcls
  exact ⟨k₀, h.isQueryBoundP (fun _ => by simp [CryptoGames.FSAEAD.queryADOutsideClass]) hk₀⟩

theorem fsaeadEncMsgsOk_of_querySubsumes {SS RS AD Msg C : Type} {ok : Msg → Bool}
    {R₁ R₂ : CryptoGames.FSAEAD.Adversary SS RS AD Msg C}
    (h : QuerySubsumes R₁ R₂) (hok : CryptoGames.FSAEAD.EncMsgsOk ok R₂) :
    CryptoGames.FSAEAD.EncMsgsOk ok R₁ :=
  h.isQueryBoundP (fun _ => by simp [CryptoGames.FSAEAD.encBadMsg]) hok

private theorem guardedSafePost_inv_query_bind {κ : Type} {G : OracleSpec.{0, 0} κ} {α : Type}
    {RespOk : (t : (unifSpec + G).Domain) → (unifSpec + G).Range t → Prop}
    {Q : (unifSpec + G).Domain → Prop} {P : α → Prop}
    {t : (unifSpec + G).Domain} {k : (unifSpec + G).Range t → OracleComp (unifSpec + G) α}
    (h : CryptoGames.GuardedSafe.GuardedSafePost RespOk Q P
      (liftM (OracleSpec.query (spec := unifSpec + G) t) >>= k)) :
    ¬ Q t ∧ ∀ u, RespOk t u → CryptoGames.GuardedSafe.GuardedSafePost RespOk Q P (k u) := by
  generalize heq : (liftM (OracleSpec.query (spec := unifSpec + G) t) >>= k) = oa at h
  cases h with
  | pure hp => exact False.elim (pure_ne_query_bind _ _ _ heq.symm)
  | query_bind hQt hcont =>
    obtain ⟨rfl, rfl⟩ := query_bind_inj heq
    exact ⟨hQt, hcont⟩

theorem guardedSafePost {κ : Type} {G : OracleSpec.{0, 0} κ} {α : Type}
    {RespOk : (t : (unifSpec + G).Domain) → (unifSpec + G).Range t → Prop}
    {Q : (unifSpec + G).Domain → Prop} {P : α → Prop}
    (hQu : ∀ n, ¬ Q (.inl n))
    (hRu : ∀ n (u : Fin (n + 1)), RespOk (.inl n) u)
    {oa₁ oa₂ : OracleComp (unifSpec + G) α}
    (hsub : QuerySubsumes oa₁ oa₂)
    (h₂ : CryptoGames.GuardedSafe.GuardedSafePost RespOk Q P oa₂) :
    CryptoGames.GuardedSafe.GuardedSafePost RespOk Q P oa₁ := by
  induction hsub with
  | ret _ => exact h₂
  | coin_l n _ _ _ ih =>
    exact CryptoGames.GuardedSafe.GuardedSafePost.query_bind (hQu n) fun u _ => ih u h₂
  | coin_r _ n _ u _ ih =>
    exact ih ((guardedSafePost_inv_query_bind h₂).2 u (hRu n u))
  | game _ _ _ _ ih =>
    obtain ⟨hQt, hcont⟩ := guardedSafePost_inv_query_bind h₂
    exact CryptoGames.GuardedSafe.GuardedSafePost.query_bind hQt fun r hr => ih r (hcont r hr)

theorem guardedFSInjectShort_of_querySubsumes {SS RS AD Msg : Type}
    {R₁ R₂ : CryptoGames.FSAEAD.Adversary SS RS AD Msg
      (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)}
    (h : QuerySubsumes R₁ R₂)
    (hg : CryptoGames.Ratchet.LibsignalInst.GuardedFSInjectShort R₂) :
    CryptoGames.Ratchet.LibsignalInst.GuardedFSInjectShort R₁ :=
  h.guardedSafePost (fun _ => not_false) (fun _ _ => trivial) hg

end ProtocolBounds

end QuerySubsumes

/-! ## Mixture congruence -/

section AdvAvg

theorem coinSimEquiv_advAvg {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    (oa : ProbComp α)
    {D₁ D₂ : α → OracleComp (unifSpec + spec) β}
    (hD : ∀ o,
      CoinSimEquiv (fun n => query (spec := unifSpec + spec) (.inl n)) (D₁ o) (D₂ o)) :
    CoinSimEquiv (fun n => query (spec := unifSpec + spec) (.inl n))
      (advAvg oa D₁) (advAvg oa D₂) :=
  (CoinSimEquiv.refl (liftM oa : OracleComp (unifSpec + spec) α)).bind hD

theorem ckaAdvantage_advAvg_congr {Key State Coins Msg CKey α : Type}
    [SampleableType Key] [SampleableType Coins] [SampleableType CKey]
    (cka : CKAScheme Key State Coins Msg CKey) (Δ tStar : ℕ) (oa : ProbComp α)
    {D₁ D₂ : α → CryptoGames.CKA.Adversary State Coins Msg CKey}
    (hD : ∀ o,
      CoinSimEquiv
        (fun n => query (spec := unifSpec + CryptoGames.CKA.spec State Coins Msg CKey) (.inl n))
        (D₁ o) (D₂ o)) :
    CryptoGames.CKA.advantage cka Δ tStar (advAvg oa D₁) =
      CryptoGames.CKA.advantage cka Δ tStar (advAvg oa D₂) :=
  ckaAdvantage_congr cka Δ tStar (coinSimEquiv_advAvg oa hD)

theorem prngAdvantage_advAvg_congr {Key State Input Output α : Type}
    [DecidableEq Input] [SampleableType Key] [SampleableType Input] [SampleableType Output]
    (P : PRFPRNG Key State Input Output) (oa : ProbComp α)
    {D₁ D₂ : α → CryptoGames.PRFPRNG.Adversary State Input Output}
    (hD : ∀ o,
      CoinSimEquiv
        (fun n => query (spec := unifSpec + CryptoGames.PRFPRNG.spec State Input Output) (.inl n))
        (D₁ o) (D₂ o)) :
    CryptoGames.PRFPRNG.advantage P (advAvg oa D₁) =
      CryptoGames.PRFPRNG.advantage P (advAvg oa D₂) :=
  prngAdvantage_congr P (coinSimEquiv_advAvg oa hD)

theorem fsaeadGame_mix_evalDistEq_of_coinSimEquiv {Key SS RS AD Msg C α : Type}
    [DecidableEq AD] [DecidableEq Msg] [DecidableEq C] [SampleableType Key]
    (fs : FSAEADScheme Key SS RS AD Msg C) (oa : ProbComp α)
    {D₁ D₂ : α → CryptoGames.FSAEAD.Adversary SS RS AD Msg C}
    (hD : ∀ o,
      CoinSimEquiv
        (fun n => query (spec := unifSpec + CryptoGames.FSAEAD.spec SS RS AD Msg C) (.inl n))
        (D₁ o) (D₂ o)) :
    (oa >>= fun o => CryptoGames.FSAEAD.game fs (D₁ o)) =ᵈ
      (oa >>= fun o => CryptoGames.FSAEAD.game fs (D₂ o)) :=
  EvalDistEq.rfl.bind fun o => fsaeadGame_evalDistEq_of_coinSimEquiv fs (hD o)

end AdvAvg

end Computational.Proofs.SessionCostedFig8.QuerySubsumes

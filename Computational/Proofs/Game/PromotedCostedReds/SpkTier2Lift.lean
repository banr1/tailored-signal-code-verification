/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Reductions.ReductionDsl.TargetCodecs
public import Computational.Proofs.ReductionDsl.Bridge -- proof-setup: allow-public-import
import Computational.Proofs.Game.PromotedCostedReds.AtomicOpsHonest

/-!
# Symmetric Relational Simulation Bridge

Provides `OracleCompRel` and `eval_eq_simulateQ_of_rel` for bridging `CostedReduction` witnesses
to shallow `StateT` reductions without a state decoder, along with `atomicSessionOps` constructors.
-/

public section

set_option autoImplicit false

open CryptoGames.CKA (DHFun)
open CryptoGames.LibsignalSession (Crypto PublicKey)
open CryptoVerification.E2E (Bytes)
open ReductionDsl (AtomicCurveCheckOp AtomicGroupOp AtomicPtDecOp AtomicPtEncOp AtomicPureOp
  AtomicSpqrKemOp AtomicSymOp Comp CostedReduction Env Expr GameCodec Iface Ops PK PtT Sig Ty Var
  atomicCurveCheckOps atomicPtDecOps atomicPtEncOps atomicSessionOps atomicSig handlerImpl
  isGameQuery)

namespace Computational.Proofs.Game.PromotedCostedReds.SpkTier2Lift

open OracleSpec OracleComp

/-! ## Relational simulation bridge -/

section RelationalBridge

/-- Inductive relational coupling between two `OracleComp T` computations issuing identical
oracle queries at every step and whose return values satisfy `P`. -/
inductive OracleCompRel {ι : Type} {T : OracleSpec ι} {α β : Type} (P : α → β → Prop) :
    OracleComp T α → OracleComp T β → Prop where
  | pureP {a : α} {b : β} (h : P a b) : OracleCompRel P (pure a) (pure b)
  | queryBind (t : ι) (k₁ : T t → OracleComp T α) (k₂ : T t → OracleComp T β)
      (hk : ∀ u, OracleCompRel P (k₁ u) (k₂ u)) :
      OracleCompRel P ((liftM (T.query t) : OracleComp T (T t)) >>= k₁)
        ((liftM (T.query t) : OracleComp T (T t)) >>= k₂)

theorem OracleCompRel.eq_of_eq {ι : Type} {T : OracleSpec ι} {α : Type}
    {oa ob : OracleComp T α} (h : OracleCompRel Eq oa ob) : oa = ob := by
  induction h with
  | pureP hp => exact congrArg Pure.pure hp
  | queryBind t k₁ k₂ _ ih => exact congrArg _ (funext ih)

theorem OracleCompRel.mono {ι : Type} {T : OracleSpec ι} {α β : Type}
    {P Q : α → β → Prop} (hPQ : ∀ a b, P a b → Q a b)
    {oa : OracleComp T α} {ob : OracleComp T β} (h : OracleCompRel P oa ob) :
    OracleCompRel Q oa ob := by
  induction h with
  | pureP hp => exact .pureP (hPQ _ _ hp)
  | queryBind t k₁ k₂ _ ih => exact .queryBind t k₁ k₂ ih

theorem OracleCompRel.bind {ι : Type} {T : OracleSpec ι} {α β γ δ : Type}
    {Q : γ → δ → Prop} {P : α → β → Prop}
    {oa : OracleComp T γ} {ob : OracleComp T δ}
    {ka : γ → OracleComp T α} {kb : δ → OracleComp T β}
    (hab : OracleCompRel Q oa ob)
    (hk : ∀ c d, Q c d → OracleCompRel P (ka c) (kb d)) :
    OracleCompRel P (oa >>= ka) (ob >>= kb) := by
  induction hab with
  | pureP hq =>
    rw [pure_bind, pure_bind]
    exact hk _ _ hq
  | queryBind t m₁ m₂ _ ih =>
    rw [bind_assoc, bind_assoc]
    exact .queryBind t _ _ fun u => ih u

theorem OracleCompRel.refl_mem_support {ι : Type} {T : OracleSpec ι} {α : Type}
    (oa : OracleComp T α) :
    OracleCompRel (fun x y => x ∈ support oa ∧ x = y) oa oa := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    exact .pureP ⟨by simp, rfl⟩
  | query_bind t mx ih =>
    refine .queryBind t mx mx fun u => (ih u).mono fun x y ⟨hx, hxy⟩ => ⟨?_, hxy⟩
    rw [mem_support_bind_iff]
    exact ⟨u, by simp, hx⟩

theorem OracleCompRel.of_eq {ι : Type} {T : OracleSpec ι} {α : Type}
    {oa ob : OracleComp T α} (h : oa = ob) : OracleCompRel Eq oa ob := by
  subst h
  exact (OracleCompRel.refl_mem_support oa).mono fun _ _ ⟨_, hxy⟩ => hxy

theorem OracleCompRel.bind_same {ι : Type} {T : OracleSpec ι} {α β γ : Type}
    {P : α → β → Prop} (oc : OracleComp T γ)
    (ka : γ → OracleComp T α) (kb : γ → OracleComp T β)
    (hk : ∀ c ∈ support oc, OracleCompRel P (ka c) (kb c)) :
    OracleCompRel P (oc >>= ka) (oc >>= kb) :=
  OracleCompRel.bind (OracleCompRel.refl_mem_support oc) fun c _ ⟨hc, hcd⟩ => by
    subst hcd; exact hk c hc

theorem OracleCompRel.map_same {ι : Type} {T : OracleSpec ι} {α β γ : Type}
    {P : α → β → Prop} (oc : OracleComp T γ) (f : γ → α) (g : γ → β)
    (hfg : ∀ c ∈ support oc, P (f c) (g c)) :
    OracleCompRel P (f <$> oc) (g <$> oc) := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  exact OracleCompRel.bind_same oc _ _ fun c hc => .pureP (hfg c hc)

theorem simulateQ_run_rel_of_bound {ι : Type} {T : OracleSpec ι}
    {κ : Type} {G : OracleSpec κ} {σ₁ σ₂ : Type}
    (so₁ : QueryImpl (unifSpec + G) (StateT σ₁ (OracleComp T)))
    (so₂ : QueryImpl (unifSpec + G) (StateT σ₂ (OracleComp T)))
    (Rel : ℕ → σ₁ → σ₂ → Prop)
    (hmono : ∀ {m n} {s₁ s₂}, m ≤ n → Rel n s₁ s₂ → Rel m s₁ s₂)
    (hU : ∀ q n s₁ s₂, Rel q s₁ s₂ →
      OracleCompRel (fun r₁ r₂ => r₁.1 = r₂.1 ∧ Rel q r₁.2 r₂.2)
        ((so₁ (.inl n)).run s₁) ((so₂ (.inl n)).run s₂))
    (hstep : ∀ m t s₁ s₂, Rel (m + 1) s₁ s₂ →
      OracleCompRel (fun r₁ r₂ => r₁.1 = r₂.1 ∧ Rel m r₁.2 r₂.2)
        ((so₁ (.inr t)).run s₁) ((so₂ (.inr t)).run s₂)) :
    ∀ {α : Type} {oa : OracleComp (unifSpec + G) α} {qAdv : ℕ},
      oa.IsQueryBoundP (isGameQuery (G := G)) qAdv →
      ∀ (s₁ : σ₁) (s₂ : σ₂), Rel qAdv s₁ s₂ →
        OracleCompRel (fun r₁ r₂ => r₁.1 = r₂.1 ∧ Rel 0 r₁.2 r₂.2)
          ((simulateQ so₁ oa).run s₁) ((simulateQ so₂ oa).run s₂) := by
  intro α oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro qAdv _ s₁ s₂ hs
    simp only [simulateQ_pure, StateT.run_pure]
    exact .pureP ⟨rfl, hmono (Nat.zero_le qAdv) hs⟩
  | query_bind q mx ih =>
    intro qAdv hb s₁ s₂ hs
    rw [isQueryBoundP_query_bind_iff] at hb
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind]
    cases q with
    | inl n =>
      refine OracleCompRel.bind (hU qAdv n s₁ s₂ hs) fun ⟨u₁, s₁'⟩ ⟨u₂, s₂'⟩ ⟨hu, hs'⟩ => ?_
      dsimp only at hu hs'
      subst hu
      exact ih u₁ (hb.2 u₁) s₁' s₂' hs'
    | inr t =>
      have hpos : 0 < qAdv := hb.1.resolve_left (by simp [isGameQuery])
      obtain ⟨m, rfl⟩ : ∃ m, qAdv = m + 1 := ⟨qAdv - 1, by omega⟩
      have hqm : ∀ u, (mx u).IsQueryBoundP (isGameQuery (G := G)) m := by
        intro u; simpa [isGameQuery] using hb.2 u
      refine OracleCompRel.bind (hstep m t s₁ s₂ hs) fun ⟨u₁, s₁'⟩ ⟨u₂, s₂'⟩ ⟨hu, hs'⟩ => ?_
      dsimp only at hu hs'
      subst hu
      exact ih u₁ (hqm u₁) s₁' s₂' hs'

/-- Symmetric relational bridge for `CostedReduction.eval` (requires no decoder `R.σ.denote → σ₂`). -/
theorem eval_eq_simulateQ_of_rel {S : Sig} {ι : Type} {T : OracleSpec ι}
    {O : Ops S} {I : Iface S T} {κ : Type} {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut out : Ty S}
    (R : CostedReduction O I G C rIn aIn aOut out) {σ₂ : Type}
    (Rel : ℕ → R.σ.denote → σ₂ → Prop)
    (initImpl : rIn.denote → OracleComp T (aIn.denote × σ₂))
    (so : QueryImpl (unifSpec + G) (StateT σ₂ (OracleComp T)))
    (finishImpl : σ₂ → aOut.denote → OracleComp T out.denote)
    (qAdv : ℕ) (x : rIn.denote)
    (hinit : OracleCompRel (fun r₁ r₂ => r₁.1 = r₂.1 ∧ Rel qAdv r₁.2 r₂.2)
      (R.init.eval (.cons x .nil)) (initImpl x))
    (hU : ∀ n s₂, (so (.inl n)).run s₂ = (StateT.lift (I.fwdU n)).run s₂)
    (hstep : ∀ m t s₁ s₂, Rel (m + 1) s₁ s₂ →
      OracleCompRel (fun r₁ r₂ => r₁.1 = r₂.1 ∧ Rel m r₁.2 r₂.2)
        ((R.impl (.inr t)).run s₁) ((so (.inr t)).run s₂))
    (hfin : ∀ s₁ s₂ b, Rel 0 s₁ s₂ →
      R.finish.eval (.cons s₁ (.cons b .nil)) = finishImpl s₂ b)
    (hmono : ∀ {m n} {s₁ s₂}, m ≤ n → Rel n s₁ s₂ → Rel m s₁ s₂)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote)
    (hb : ∀ a, (A a).IsQueryBoundP (isGameQuery (G := G)) qAdv) :
    R.eval A x = (do
      let (a, s₀) ← initImpl x
      let (b, s₁) ← (simulateQ so (A a)).run s₀
      finishImpl s₁ b) := by
  apply OracleCompRel.eq_of_eq
  unfold CostedReduction.eval
  have hU_rel : ∀ q n s₁ s₂, Rel q s₁ s₂ →
      OracleCompRel (fun r₁ r₂ => r₁.1 = r₂.1 ∧ Rel q r₁.2 r₂.2)
        ((R.impl (.inl n)).run s₁) ((so (.inl n)).run s₂) := by
    intro q n s₁ s₂ hs
    simp only [CostedReduction.impl, handlerImpl, hU, StateT.run_lift]
    exact OracleCompRel.bind_same (I.fwdU n) _ _ fun u _ => .pureP ⟨rfl, hs⟩
  refine OracleCompRel.bind hinit fun ⟨a₁, s₁⟩ ⟨a₂, s₂⟩ ⟨ha, hs⟩ => ?_
  dsimp only at ha hs
  subst ha
  refine OracleCompRel.bind
    (simulateQ_run_rel_of_bound R.impl so Rel hmono hU_rel hstep (hb a₁) s₁ s₂ hs)
    fun ⟨b₁, s₁'⟩ ⟨b₂, s₂'⟩ ⟨hb_eq, hs'⟩ => ?_
  dsimp only at hb_eq hs'
  subst hb_eq
  exact OracleCompRel.of_eq (hfin s₁' s₂' b₁ hs')

end RelationalBridge

/-! ## Operation constructors -/

section SessionOpConstructors

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
  {C : Crypto} {K : CryptoVerification.LibsignalSpqrV1.MlKem} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

@[expose, reducible] def tier2PureOp {Γ : List (Ty ASig)} (o : AtomicPureOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) : Expr AOps Γ (o.cod ℓ Pt) :=
  ReductionDsl.Expr.op (O := AOps) (Sum.inl (Sum.inl (Sum.inl (Sum.inl o)))) a

@[expose, reducible] def tier2PtEncOp {Γ : List (Ty ASig)} (o : AtomicPtEncOp)
    (a : Expr AOps Γ ((atomicPtEncOps ℓ encT).dom o)) :
    Expr AOps Γ ((atomicPtEncOps ℓ encT).cod o) :=
  ReductionDsl.Expr.op (O := AOps) (Sum.inl (Sum.inl (Sum.inl (Sum.inr (Sum.inl o))))) a

@[expose, reducible] def tier2SymOp {Γ : List (Ty ASig)} (o : AtomicSymOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) : Expr AOps Γ (o.cod ℓ Pt) :=
  ReductionDsl.Expr.op (O := AOps) (Sum.inl (Sum.inl (Sum.inl (Sum.inr (Sum.inr o))))) a

@[expose, reducible] def tier2GroupOp {Γ : List (Ty ASig)} (o : AtomicGroupOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) : Expr AOps Γ (o.cod ℓ Pt) :=
  ReductionDsl.Expr.op (O := AOps) (Sum.inl (Sum.inl (Sum.inr o))) a

@[expose, reducible] def tier2PtDecOp {Γ : List (Ty ASig)} (o : AtomicPtDecOp)
    (a : Expr AOps Γ ((atomicPtDecOps ℓ decT).dom o)) :
    Expr AOps Γ ((atomicPtDecOps ℓ decT).cod o) :=
  ReductionDsl.Expr.op (O := AOps) (Sum.inl (Sum.inr (Sum.inl o))) a

@[expose, reducible] def tier2CurveOp {Γ : List (Ty ASig)} (o : AtomicCurveCheckOp)
    (a : Expr AOps Γ ((atomicCurveCheckOps ℓ decT encT).dom o)) :
    Expr AOps Γ ((atomicCurveCheckOps ℓ decT encT).cod o) :=
  ReductionDsl.Expr.op (O := AOps) (Sum.inl (Sum.inr (Sum.inr o))) a

@[expose, reducible] def tier2SpqrKemOp {Γ : List (Ty ASig)} (o : AtomicSpqrKemOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) : Expr AOps Γ (o.cod ℓ Pt) :=
  ReductionDsl.Expr.op (O := AOps) (Sum.inr o) a

@[simp] theorem eval_tier2PureOp {Γ : List (Ty ASig)} (o : AtomicPureOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) (ρ : Env Γ) :
    (tier2PureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).eval ρ = o.eval ℓ Pt (a.eval ρ) := rfl

@[simp] theorem cost_tier2PureOp {Γ : List (Ty ASig)} (o : AtomicPureOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) :
    (tier2PureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).cost = a.cost + o.cost ℓ := rfl

@[simp] theorem eval_tier2PtEncOp {Γ : List (Ty ASig)}
    (a : Expr AOps Γ (PtT (ℓ := ℓ) (Pt := Pt))) (ρ : Env Γ) :
    (tier2PtEncOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) .ptEncPk a).eval ρ = encT (a.eval ρ) := rfl

@[simp] theorem cost_tier2PtEncOp {Γ : List (Ty ASig)}
    (a : Expr AOps Γ (PtT (ℓ := ℓ) (Pt := Pt))) :
    (tier2PtEncOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) .ptEncPk a).cost = a.cost + 4 := rfl

@[simp] theorem eval_tier2SymOp {Γ : List (Ty ASig)} (o : AtomicSymOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) (ρ : Env Γ) :
    (tier2SymOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).eval ρ = o.eval ℓ Pt C (a.eval ρ) := rfl

@[simp] theorem cost_tier2SymOp {Γ : List (Ty ASig)} (o : AtomicSymOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) :
    (tier2SymOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).cost = a.cost + o.cost ℓ := rfl

@[simp] theorem eval_tier2GroupOp {Γ : List (Ty ASig)} (o : AtomicGroupOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) (ρ : Env Γ) :
    (tier2GroupOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).eval ρ = o.eval ℓ Pt C Dh encPt lam (a.eval ρ) := rfl

@[simp] theorem cost_tier2GroupOp {Γ : List (Ty ASig)} (o : AtomicGroupOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) :
    (tier2GroupOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).cost = a.cost + o.cost := rfl

@[simp] theorem eval_tier2PtDecOp {Γ : List (Ty ASig)}
    (a : Expr AOps Γ (PK (ℓ := ℓ) (Pt := Pt))) (ρ : Env Γ) :
    (tier2PtDecOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) .ptDecPk a).eval ρ = decT (a.eval ρ) := rfl

@[simp] theorem cost_tier2PtDecOp {Γ : List (Ty ASig)}
    (a : Expr AOps Γ (PK (ℓ := ℓ) (Pt := Pt))) :
    (tier2PtDecOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) .ptDecPk a).cost = a.cost + 8 := rfl

@[simp] theorem eval_tier2CurveOp {Γ : List (Ty ASig)} (o : AtomicCurveCheckOp)
    (a : Expr AOps Γ ((atomicCurveCheckOps ℓ decT encT).dom o)) (ρ : Env Γ) :
    (tier2CurveOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).eval ρ =
      (atomicCurveCheckOps ℓ decT encT).eval o (a.eval ρ) := rfl

@[simp] theorem cost_tier2CurveOp {Γ : List (Ty ASig)} (o : AtomicCurveCheckOp)
    (a : Expr AOps Γ ((atomicCurveCheckOps ℓ decT encT).dom o)) :
    (tier2CurveOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).cost = a.cost + (atomicCurveCheckOps ℓ decT encT).cost o := rfl

@[simp] theorem eval_tier2SpqrKemOp {Γ : List (Ty ASig)} (o : AtomicSpqrKemOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) (ρ : Env Γ) :
    (tier2SpqrKemOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).eval ρ = o.eval ℓ Pt C K (a.eval ρ) := rfl

@[simp] theorem cost_tier2SpqrKemOp {Γ : List (Ty ASig)} (o : AtomicSpqrKemOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) :
    (tier2SpqrKemOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).cost = a.cost + o.cost := rfl

end SessionOpConstructors

end Computational.Proofs.Game.PromotedCostedReds.SpkTier2Lift

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.GameHop.StateSim
public import Computational.Specifications.Reductions.ReductionDsl.Core
public import Computational.Proofs.ReductionDsl.Soundness

/-!
# Support-Invariant Rules and Potential-Based Query Bounds for `ReductionDsl`

Propagates unary `AllSupport` invariants across `ReductionDsl` evaluators and runners, and tracks
state-potential query bounds (`PotOK`) across `handlerImpl` simulations.
-/

set_option autoImplicit false

@[expose] public section

namespace Computational.Proofs.GameHop.ReductionDsl.SupportWP

open OracleSpec OracleComp
open Computational.Proofs.GameHop.StateSim (AllSupport)
open _root_.ReductionDsl (Sig Ty Env Ops Iface Expr Comp GameCodec Mid TwoStageCostedReduction
  iterM findML anyML mapML consumeFirstML foldML handlerImpl runFuel)

section LoopSupport

variable {ι : Type} {T : OracleSpec.{0, 0} ι}

theorem allSupport_iterM {α : Type} {P : α → Prop} (f : α → OracleComp T α)
    (hf : ∀ a, P a → AllSupport P (f a)) :
    ∀ (n : ℕ) {a : α}, P a → AllSupport P (iterM f n a)
  | 0, _, ha => AllSupport.pure ha
  | n + 1, _, ha => (hf _ ha).bind fun _ ha' => allSupport_iterM f hf n ha'

theorem allSupport_findML {α : Type} {Q : α → Prop} (p : α → OracleComp T Bool) :
    ∀ (xs : List α), (∀ x ∈ xs, Q x) →
      AllSupport (fun o => ∀ x, o = some x → Q x) (findML p xs)
  | [], _ => AllSupport.pure fun _ h => by cases h
  | x :: xs, hxs => by
    simp only [findML]
    refine (AllSupport.of_forall (p x) fun _ => trivial).bind fun b _ => ?_
    cases b
    · exact allSupport_findML p xs fun y hy => hxs y (List.mem_cons_of_mem x hy)
    · exact AllSupport.pure fun y hy => by
        injection hy with hxy; subst hxy; exact hxs x List.mem_cons_self

theorem allSupport_mapML {α β : Type} {P : α → Prop} {Q : β → Prop}
    (f : α → OracleComp T β) (hf : ∀ x, P x → AllSupport Q (f x)) :
    ∀ (xs : List α), (∀ x ∈ xs, P x) →
      AllSupport (fun ys => ys.length = xs.length ∧ ∀ y ∈ ys, Q y) (mapML f xs)
  | [], _ => AllSupport.pure ⟨rfl, fun _ h => by cases h⟩
  | x :: xs, hxs => by
    simp only [mapML]
    refine (hf x (hxs x List.mem_cons_self)).bind fun y hy => ?_
    refine (allSupport_mapML f hf xs fun z hz => hxs z (List.mem_cons_of_mem x hz)).bind
      fun ys hys => ?_
    refine AllSupport.pure ⟨by simp [hys.1], fun z hz => ?_⟩
    rcases List.mem_cons.mp hz with rfl | hz'
    · exact hy
    · exact hys.2 z hz'

theorem allSupport_foldML {α β : Type} {P : α → Prop} {I : β → Prop}
    (f : α → β → OracleComp T β) (hf : ∀ x acc, P x → I acc → AllSupport I (f x acc)) :
    ∀ {acc : β} (xs : List α), I acc → (∀ x ∈ xs, P x) → AllSupport I (foldML f acc xs)
  | _, [], hacc, _ => AllSupport.pure hacc
  | acc, x :: xs, hacc, hxs => by
    simp only [foldML]
    exact (hf x acc (hxs x List.mem_cons_self) hacc).bind fun acc' hacc' =>
      allSupport_foldML f hf xs hacc' fun z hz => hxs z (List.mem_cons_of_mem x hz)

end LoopSupport

section CompSupport

variable {S : Sig} {ι : Type} {T : OracleSpec.{0, 0} ι} {O : Ops S} {I : Iface S T}

theorem allSupport_comp_ret {Γ : List (Ty S)} {t : Ty S} {P : t.denote → Prop}
    (e : Expr O Γ t) (ρ : Env Γ) (h : P (e.eval ρ)) :
    AllSupport P ((Comp.ret (I := I) e).eval ρ) :=
  AllSupport.pure h

theorem allSupport_comp_bind {Γ : List (Ty S)} {t u : Ty S}
    {P : t.denote → Prop} {Q : u.denote → Prop}
    (c : Comp O I Γ t) (k : Comp O I (t :: Γ) u) (ρ : Env Γ)
    (hc : AllSupport P (c.eval ρ))
    (hk : ∀ x, P x → AllSupport Q (k.eval (.cons x ρ))) :
    AllSupport Q ((Comp.bind c k).eval ρ) :=
  hc.bind hk

theorem allSupport_comp_ite {Γ : List (Ty S)} {t : Ty S} {P : t.denote → Prop}
    (b : Expr O Γ .bool) (c d : Comp O I Γ t) (ρ : Env Γ)
    (hc : b.eval ρ = true → AllSupport P (c.eval ρ))
    (hd : b.eval ρ = false → AllSupport P (d.eval ρ)) :
    AllSupport P ((Comp.ite b c d).eval ρ) := by
  simp only [Comp.eval]
  cases hb : b.eval ρ
  · exact hd hb
  · exact hc hb

theorem allSupport_comp_caseOpt {Γ : List (Ty S)} {t u : Ty S} {P : u.denote → Prop}
    (e : Expr O Γ (.opt t)) (n : Comp O I Γ u) (s : Comp O I (t :: Γ) u) (ρ : Env Γ)
    (hn : e.eval ρ = none → AllSupport P (n.eval ρ))
    (hs : ∀ x, e.eval ρ = some x → AllSupport P (s.eval (.cons x ρ))) :
    AllSupport P ((Comp.caseOpt e n s).eval ρ) := by
  simp only [Comp.eval]
  cases he : e.eval ρ
  · exact hn he
  · exact hs _ he

theorem allSupport_comp_caseSum {Γ : List (Ty S)} {t u v : Ty S} {P : v.denote → Prop}
    (e : Expr O Γ (.sum t u)) (l : Comp O I (t :: Γ) v) (r : Comp O I (u :: Γ) v) (ρ : Env Γ)
    (hl : ∀ a, e.eval ρ = .inl a → AllSupport P (l.eval (.cons a ρ)))
    (hr : ∀ b, e.eval ρ = .inr b → AllSupport P (r.eval (.cons b ρ))) :
    AllSupport P ((Comp.caseSum e l r).eval ρ) := by
  simp only [Comp.eval]
  cases he : e.eval ρ
  · exact hl _ he
  · exact hr _ he

theorem allSupport_simulateQ_handlerImpl {κ : Type} {G : OracleSpec.{0, 0} κ}
    {C : GameCodec S G} {σ : Ty S} {α : Type}
    (inv : σ.denote → Prop)
    (h : Comp O I [σ, C.Q] (.prod C.R σ))
    (hStep : ∀ gq s, inv s →
      AllSupport (fun p : C.R.denote × σ.denote => inv p.2)
        (h.eval (.cons s (.cons (C.qenc gq) .nil))))
    (oa : OracleComp (unifSpec + G) α) (s₀ : σ.denote) (hs₀ : inv s₀) :
    AllSupport (fun z : α × σ.denote => inv z.2)
      ((simulateQ (handlerImpl (C := C) h) oa).run s₀) := by
  refine AllSupport.simulateQ_run (handlerImpl (C := C) h) inv (fun q s hs => ?_) oa s₀ hs₀
  rcases q with uq | gq
  · intro z hz
    simp only [handlerImpl, StateT.run_lift, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨_, _, rfl⟩ := hz
    exact hs
  · intro z hz
    simp only [handlerImpl, StateT.run_mk, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    exact hStep gq s hs p hp

theorem allSupport_runFuel {κ : Type} {G : OracleSpec.{0, 0} κ}
    {C : GameCodec S G} {σ : Ty S} {α : Type}
    (inv : σ.denote → Prop)
    (h : Comp O I [σ, C.Q] (.prod C.R σ))
    (hStep : ∀ gq s, inv s →
      AllSupport (fun p : C.R.denote × σ.denote => inv p.2)
        (h.eval (.cons s (.cons (C.qenc gq) .nil))))
    (dflt : α) (oa : OracleComp (unifSpec + G) α) (fuel : ℕ) (s₀ : σ.denote) (hs₀ : inv s₀) :
    AllSupport (fun z : α × σ.denote => inv z.2) (runFuel (C := C) h dflt oa fuel s₀) := by
  induction oa using OracleComp.inductionOn generalizing fuel s₀ with
  | pure a =>
    exact AllSupport.pure hs₀
  | query_bind q k ih =>
    unfold runFuel
    rw [OracleComp.construct_query_bind]
    rcases q with uq | gq
    · dsimp only
      exact (AllSupport.of_forall (I.fwdU uq) fun _ => trivial).bind fun u _ => ih u fuel s₀ hs₀
    · rcases fuel with _ | fuel
      · exact AllSupport.pure hs₀
      · dsimp only
        exact (hStep gq s₀ hs₀).bind fun p hp => ih (C.rdec gq p.1) fuel p.2 hp

theorem allSupport_run1 {κ : Type} {G : OracleSpec.{0, 0} κ}
    {C : GameCodec S G} {rIn aIn aOut ch rIn2 out : Ty S} {α : Type}
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (inv : R.σ.denote → Prop)
    (pauseInv : R.π.denote → R.σ.denote → Prop)
    (hStep : ∀ gq s, inv s →
      AllSupport
        (fun res : (C.R.denote × R.σ.denote) ⊕ (ch.denote × R.π.denote × R.σ.denote) =>
          match res with
          | .inl (_, s') => inv s'
          | .inr (_, p, s') => pauseInv p s')
        (R.handlePre.eval (.cons s (.cons (C.qenc gq) .nil))))
    (dflt : α) (oa : OracleComp (unifSpec + G) α) (fuel : ℕ) (s₀ : R.σ.denote) (hs₀ : inv s₀) :
    AllSupport
      (fun m : Mid G α R.π.denote R.σ.denote ch.denote =>
        match m with
        | .done _ s => inv s
        | .paused _ _ p s _ => pauseInv p s)
      (R.run1 dflt oa fuel s₀) := by
  induction oa using OracleComp.inductionOn generalizing fuel s₀ with
  | pure a =>
    exact AllSupport.pure hs₀
  | query_bind q k ih =>
    unfold TwoStageCostedReduction.run1
    rw [OracleComp.construct_query_bind]
    rcases q with uq | gq
    · dsimp only
      exact (AllSupport.of_forall (I.fwdU uq) fun _ => trivial).bind fun u _ => ih u fuel s₀ hs₀
    · rcases fuel with _ | fuel
      · exact AllSupport.pure hs₀
      · dsimp only
        refine (hStep gq s₀ hs₀).bind fun res hres => ?_
        rcases res with ⟨v, s'⟩ | ⟨c, p, s'⟩
        · exact ih (C.rdec gq v) fuel s' hres
        · exact AllSupport.pure hres

end CompSupport

section PotOK

variable {S : Sig} {ι : Type} {T : OracleSpec.{0, 0} ι} {O : Ops S} {I : Iface S T}

/-- Continuation-passing potential bound requiring `oa >>= k` to satisfy `IsQueryBoundP P n`
whenever each continuation `k a` has query bound `B a`. -/
def PotOK {α : Type} (P : ι → Prop) [DecidablePred P]
    (B : α → ℕ) (oa : OracleComp T α) (n : ℕ) : Prop :=
  ∀ {β : Type} (k : α → OracleComp T β),
    (∀ a, (k a).IsQueryBoundP P (B a)) → (oa >>= k).IsQueryBoundP P n

theorem PotOK.pure' {α : Type} {P : ι → Prop} [DecidablePred P]
    {B : α → ℕ} {a : α} {n : ℕ} (h : B a ≤ n) :
    PotOK P B (pure a : OracleComp T α) n := by
  intro β k hk
  simpa using (hk a).mono h

theorem PotOK.bind' {α γ : Type} {P : ι → Prop} [DecidablePred P]
    {B : γ → ℕ} {oa : OracleComp T α} {f : α → OracleComp T γ} {m n r : ℕ}
    (hoa : oa.IsQueryBoundP P m)
    (hf : ∀ a, PotOK P B (f a) r) (hmn : m + r ≤ n) :
    PotOK P B (oa >>= f) n := by
  intro β k hk
  rw [bind_assoc]
  exact (isQueryBoundP_bind hoa (fun a _ => hf a k hk)).mono hmn

theorem PotOK.bindPot {α γ : Type} {P : ι → Prop} [DecidablePred P]
    {B₁ : α → ℕ} {B₂ : γ → ℕ} {oa : OracleComp T α}
    {f : α → OracleComp T γ} {n : ℕ}
    (hoa : PotOK P B₁ oa n) (hf : ∀ a, PotOK P B₂ (f a) (B₁ a)) :
    PotOK P B₂ (oa >>= f) n := by
  intro β k hk
  rw [bind_assoc]
  exact hoa (fun a => f a >>= k) (fun a => hf a k hk)

theorem PotOK.toQueryBound {α : Type} {P : ι → Prop} [DecidablePred P]
    {B : α → ℕ} {oa : OracleComp T α} {n : ℕ}
    (h : PotOK P B oa n) (hB : ∀ a, B a = 0) :
    oa.IsQueryBoundP P n := by
  have := h (fun a => (pure a : OracleComp T α))
    (fun a => by rw [hB a]; exact isQueryBoundP_pure P a 0)
  simpa using this

theorem potC_bind {P : ι → Prop} [DecidablePred P]
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (hw : ∀ g x, P (I.enc g x) → 1 ≤ w g)
    (hU : ∀ n, (I.fwdU n).IsQueryBoundP P 0)
    {Γ : List (Ty S)} {τ₁ τ₂ : Ty S} {B : τ₂.denote → ℕ}
    (m : Comp O I Γ τ₁) (k : Comp O I (τ₁ :: Γ) τ₂) (env : Env Γ) {r n : ℕ}
    (hk : ∀ x, PotOK P B (k.eval (.cons x env)) r)
    (hmn : m.queries w ws + r ≤ n) :
    PotOK P B ((Comp.bind m k).eval env) n := by
  simp only [Comp.eval]
  exact PotOK.bind' (Comp.queryBound_eval P w ws hw hU m env) hk hmn

theorem potC_caseSum {P : ι → Prop} [DecidablePred P]
    {Γ : List (Ty S)} {τ₁ τ₂ τ : Ty S} {B : τ.denote → ℕ}
    (s : Expr O Γ (.sum τ₁ τ₂))
    (kl : Comp O I (τ₁ :: Γ) τ) (kr : Comp O I (τ₂ :: Γ) τ)
    (env : Env Γ) {n : ℕ}
    (hl : ∀ a, s.eval env = .inl a → PotOK P B (kl.eval (.cons a env)) n)
    (hr : ∀ b, s.eval env = .inr b → PotOK P B (kr.eval (.cons b env)) n) :
    PotOK P B ((Comp.caseSum s kl kr).eval env) n := by
  simp only [Comp.eval]
  split
  · next a h => exact hl a h
  · next b h => exact hr b h

theorem potC_caseOpt {P : ι → Prop} [DecidablePred P]
    {Γ : List (Ty S)} {τ₁ τ : Ty S} {B : τ.denote → ℕ}
    (o : Expr O Γ (.opt τ₁))
    (kn : Comp O I Γ τ) (ks : Comp O I (τ₁ :: Γ) τ)
    (env : Env Γ) {n : ℕ}
    (hn : o.eval env = none → PotOK P B (kn.eval env) n)
    (hs : ∀ a, o.eval env = some a → PotOK P B (ks.eval (.cons a env)) n) :
    PotOK P B ((Comp.caseOpt o kn ks).eval env) n := by
  simp only [Comp.eval]
  split
  · next h => exact hn h
  · next a h => exact hs a h

theorem potC_ite {P : ι → Prop} [DecidablePred P]
    {Γ : List (Ty S)} {τ : Ty S} {B : τ.denote → ℕ}
    (c : Expr O Γ .bool) (t e : Comp O I Γ τ) (env : Env Γ) {n : ℕ}
    (ht : c.eval env = true → PotOK P B (t.eval env) n)
    (he : c.eval env = false → PotOK P B (e.eval env) n) :
    PotOK P B ((Comp.ite c t e).eval env) n := by
  simp only [Comp.eval]
  cases h : c.eval env
  · simp only [Bool.false_eq_true, ↓reduceIte]; exact he h
  · simp only [↓reduceIte]; exact ht h

theorem potC_ret {P : ι → Prop} [DecidablePred P]
    {Γ : List (Ty S)} {τ : Ty S} {B : τ.denote → ℕ}
    (e : Expr O Γ τ) (env : Env Γ) {n : ℕ} (h : B (e.eval env) ≤ n) :
    PotOK P B ((Comp.ret e : Comp O I Γ τ).eval env) n := by
  simp only [Comp.eval]
  exact PotOK.pure' h

/-- Potential-based query bound for `simulateQ (handlerImpl h)`: if every step respects the state
potential `B`, the whole simulation respects `B`. -/
theorem potOK_simulateQ_handlerImpl {κ : Type} {G : OracleSpec.{0, 0} κ}
    {C : GameCodec S G} {σ : Ty S} {α : Type}
    {P : ι → Prop} [DecidablePred P]
    (B : σ.denote → ℕ)
    (hU : ∀ n, (I.fwdU n).IsQueryBoundP P 0)
    (h : Comp O I [σ, C.Q] (.prod C.R σ))
    (hStep : ∀ q s, PotOK P (fun x : C.R.denote × σ.denote => B x.2)
      (h.eval (.cons s (.cons q .nil))) (B s))
    (mx : OracleComp (unifSpec + G) α) (st : σ.denote) :
    PotOK P (fun x : α × σ.denote => B x.2)
      ((simulateQ (handlerImpl (C := C) h) mx).run st) (B st) := by
  induction mx using OracleComp.inductionOn generalizing st with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure]
    exact PotOK.pure' le_rfl
  | query_bind q k ih =>
    rw [simulateQ_query_bind, StateT.run_bind]
    rcases q with uq | gq
    · change PotOK P _
        ((do let u ← I.fwdU uq; return (u, st)) >>=
          fun x => (simulateQ (handlerImpl (C := C) h) (k x.1)).run x.2)
        (B st)
      rw [bind_assoc]
      refine PotOK.bind' (m := 0) (r := B st) (hU uq) (fun u => ?_) (by omega)
      rw [pure_bind]
      exact ih u st
    · change PotOK P _
        ((do
            let p ← h.eval (.cons st (.cons (C.qenc gq) .nil))
            return (C.rdec gq p.1, p.2)) >>=
          fun x => (simulateQ (handlerImpl (C := C) h) (k x.1)).run x.2)
        (B st)
      rw [bind_assoc]
      refine PotOK.bindPot (hStep (C.qenc gq) st) (fun p => ?_)
      rw [pure_bind]
      exact ih (C.rdec gq p.1) p.2

end PotOK

end Computational.Proofs.GameHop.ReductionDsl.SupportWP

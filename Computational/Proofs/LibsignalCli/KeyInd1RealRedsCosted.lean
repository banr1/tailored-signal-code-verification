/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Game.ModelIface
public import Computational.Proofs.E2E.BinaryHarnessCostedRedsV1
public import Computational.Proofs.SignalPqxdh.TwoKeyAndAuthStatements
import Computational.Proofs.E2E.BhKindCouplingV1
import Computational.Proofs.ReductionDsl.Bridge

/-!
# Polymorphic `KeyInd` Shallow Reference Reduction Query Bounds

Specializes `compositionLocalStart`, `pqxdhKeyIndExpForHandshake`, and
`KeyIndAdvantageForHandshake` to `SignalPqxdh.pqxdhKeyIndImpl true S P`, and relates tightened
`2 * qTot` reduction query budgets to `2 * qTot + 2`. Establishes structural `Comp` query-bound
helpers and proves `bhKindRedWith_queryBounded_of_B` for an arbitrary `KeyInd` oracle handler `ki`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

open scoped ENNReal
open OracleComp OracleSpec MeasureTheory

namespace CryptoVerification.E2E

open ReductionDsl CryptoVerification.E2E.Costed
open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  CryptoGames.LibsignalSessionApi HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme
  MACScheme WireAEAD FSAEAD CryptoGames.Ratchet.LibsignalSim CryptoGames.FSAEAD.Thm5
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.LibsignalSpqrV1

@[simp]
theorem bhE2ELocalStartWith_pqxdhKeyIndImpl {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (P : SignalPqxdh.Primitives) :
    compositionLocalStart (ℓ := ℓ) (SignalPqxdh.pqxdhKeyIndImpl true S P) =
      bhE2ELocalStart (S := S) (ℓ := ℓ) P := rfl

@[simp]
theorem pqxdhKeyIndExpWith_pqxdhKeyIndImpl (S : SignalPqxdh.Setup)
    (P : SignalPqxdh.Primitives) (A : SignalPqxdh.KeyIndAdversary S) :
    pqxdhKeyIndExpForHandshake S P (SignalPqxdh.pqxdhKeyIndImpl true S P) A =
      SignalPqxdh.pqxdhKeyIndExp S P A := rfl

@[simp]
theorem KeyIndAdvantageWith_pqxdhKeyIndImpl (S : SignalPqxdh.Setup)
    (P : SignalPqxdh.Primitives) (A : SignalPqxdh.KeyIndAdversary S) :
    (KeyIndAdvantageForHandshake S P (SignalPqxdh.pqxdhKeyIndImpl true S P) A).toReal =
      SignalPqxdh.KeyIndAdvantage S P A := rfl

theorem kindRed_queryBudget_le_old (qTot : ℕ) :
    2 * qTot ≤ 2 * qTot + 2 :=
  Nat.le_add_right _ _

/-- `CompositionCostedReductionsBounded` with query budget `2 * qTot` implies the weaker
`2 * qTot + 2` bound. -/
theorem compositionCostedReductionsBounded_imp_old {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (R : CompositionCostedReductions S ℓ P C K qep decT encT)
    (h : CompositionCostedReductionsBounded P C K qep decT encT b qStart qs R) :
    let qDR := ∑ k ∈ Finset.range qStart, qs k
    let qInst := Finset.sup (Finset.range qStart) qs
    let qTot := b.q_total + qStart + qDR
    let B := bhE2ECostBudget S b qStart qDR qInst qep ℓ
    GRedBounded R.kindRed (fun _ => 1) (fun _ => 0) qTot (2 * qTot + 2) B ∧
      (∀ k < qStart,
        GRed2Bounded (R.prefixRed k) (fun _ => 1) (fun _ => 0) qTot qTot B false) :=
  ⟨⟨h.1.1.1, h.1.1.2.1, h.1.1.2.2.1.trans (kindRed_queryBudget_le_old _), h.1.1.2.2.2⟩, h.1.2⟩

namespace KeyInd1RealRedsAux

theorem isQueryBoundP_congr_pred_with {ι : Type} {spec : OracleSpec ι} {α : Type}
    {p q : ι → Prop} [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x, p x ↔ q x) {oa : OracleComp spec α} {n : ℕ}
    (h : oa.IsQueryBoundP p n) : oa.IsQueryBoundP q n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure _ => simp
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h ⊢
    refine ⟨by rw [← hpq t]; exact h.1, fun u => ih u ?_⟩
    have hu := h.2 u
    by_cases hpt : p t
    · have hqt : q t := (hpq t).mp hpt
      simpa [hpt, hqt] using hu
    · have hqt : ¬ q t := fun hq => hpt ((hpq t).mpr hq)
      simpa [hpt, hqt] using hu

section CompQueryHelpersWith

variable {Sig0 : Sig} {ι : Type} {T : OracleSpec ι} {O : Ops Sig0} {I : Iface Sig0 T}
variable (P : ι → Prop) [DecidablePred P]

theorem wqb_ret {Γ : List (Ty Sig0)} {t : Ty Sig0}
    {e : Expr O Γ t} {ρ : Env Γ} (m : ℕ) :
    ((Comp.ret e : Comp O I Γ t).eval ρ).IsQueryBoundP P m :=
  isQueryBoundP_pure P (e.eval ρ) m

theorem wqb0_ret {Γ : List (Ty Sig0)} {t : Ty Sig0}
    {e : Expr O Γ t} {ρ : Env Γ} :
    ((Comp.ret e : Comp O I Γ t).eval ρ).IsQueryBoundP P 0 :=
  isQueryBoundP_pure P (e.eval ρ) 0

theorem wqb_ite {Γ : List (Ty Sig0)} {t : Ty Sig0} {m : ℕ}
    {b : Expr O Γ .bool} {c d : Comp O I Γ t} {ρ : Env Γ}
    (hc : (c.eval ρ).IsQueryBoundP P m) (hd : (d.eval ρ).IsQueryBoundP P m) :
    ((Comp.ite b c d).eval ρ).IsQueryBoundP P m := by
  simp only [Comp.eval]
  split_ifs
  · exact hc
  · exact hd

theorem wqb0_ite {Γ : List (Ty Sig0)} {t : Ty Sig0}
    {b : Expr O Γ .bool} {c d : Comp O I Γ t} {ρ : Env Γ}
    (hc : (c.eval ρ).IsQueryBoundP P 0) (hd : (d.eval ρ).IsQueryBoundP P 0) :
    ((Comp.ite b c d).eval ρ).IsQueryBoundP P 0 :=
  wqb_ite P hc hd

theorem wqb_caseOpt {Γ : List (Ty Sig0)} {a t : Ty Sig0} {m : ℕ}
    {e : Expr O Γ (.opt a)} {n : Comp O I Γ t} {s : Comp O I (a :: Γ) t} {ρ : Env Γ}
    (hn : (n.eval ρ).IsQueryBoundP P m)
    (hs : ∀ x, (s.eval (.cons x ρ)).IsQueryBoundP P m) :
    ((Comp.caseOpt e n s).eval ρ).IsQueryBoundP P m := by
  simp only [Comp.eval]
  cases e.eval ρ with
  | none => exact hn
  | some x => exact hs x

theorem wqb0_caseOpt {Γ : List (Ty Sig0)} {a t : Ty Sig0}
    {e : Expr O Γ (.opt a)} {n : Comp O I Γ t} {s : Comp O I (a :: Γ) t} {ρ : Env Γ}
    (hn : (n.eval ρ).IsQueryBoundP P 0)
    (hs : ∀ x, (s.eval (.cons x ρ)).IsQueryBoundP P 0) :
    ((Comp.caseOpt e n s).eval ρ).IsQueryBoundP P 0 :=
  wqb_caseOpt P hn hs

theorem wqb_caseSum {Γ : List (Ty Sig0)} {a b t : Ty Sig0} {m : ℕ}
    {e : Expr O Γ (.sum a b)} {l : Comp O I (a :: Γ) t} {r : Comp O I (b :: Γ) t} {ρ : Env Γ}
    (hl : ∀ x, (l.eval (.cons x ρ)).IsQueryBoundP P m)
    (hr : ∀ y, (r.eval (.cons y ρ)).IsQueryBoundP P m) :
    ((Comp.caseSum e l r).eval ρ).IsQueryBoundP P m := by
  simp only [Comp.eval]
  cases e.eval ρ with
  | inl x => exact hl x
  | inr y => exact hr y

theorem wqb_caseSum_inl {Γ : List (Ty Sig0)} {a b t : Ty Sig0} {m : ℕ}
    {e : Expr O Γ (.sum a b)} {l : Comp O I (a :: Γ) t} {r : Comp O I (b :: Γ) t}
    {ρ : Env Γ} {x : a.denote} (he : e.eval ρ = .inl x)
    (hl : (l.eval (.cons x ρ)).IsQueryBoundP P m) :
    ((Comp.caseSum e l r).eval ρ).IsQueryBoundP P m := by
  simp only [Comp.eval, he]
  exact hl

theorem wqb0_caseSum_inl {Γ : List (Ty Sig0)} {a b t : Ty Sig0}
    {e : Expr O Γ (.sum a b)} {l : Comp O I (a :: Γ) t} {r : Comp O I (b :: Γ) t}
    {ρ : Env Γ} {x : a.denote} (he : e.eval ρ = .inl x)
    (hl : (l.eval (.cons x ρ)).IsQueryBoundP P 0) :
    ((Comp.caseSum e l r).eval ρ).IsQueryBoundP P 0 :=
  wqb_caseSum_inl P he hl

theorem wqb_caseSum_inr {Γ : List (Ty Sig0)} {a b t : Ty Sig0} {m : ℕ}
    {e : Expr O Γ (.sum a b)} {l : Comp O I (a :: Γ) t} {r : Comp O I (b :: Γ) t}
    {ρ : Env Γ} {y : b.denote} (he : e.eval ρ = .inr y)
    (hr : (r.eval (.cons y ρ)).IsQueryBoundP P m) :
    ((Comp.caseSum e l r).eval ρ).IsQueryBoundP P m := by
  simp only [Comp.eval, he]
  exact hr

theorem wqb0_caseSum_inr {Γ : List (Ty Sig0)} {a b t : Ty Sig0}
    {e : Expr O Γ (.sum a b)} {l : Comp O I (a :: Γ) t} {r : Comp O I (b :: Γ) t}
    {ρ : Env Γ} {y : b.denote} (he : e.eval ρ = .inr y)
    (hr : (r.eval (.cons y ρ)).IsQueryBoundP P 0) :
    ((Comp.caseSum e l r).eval ρ).IsQueryBoundP P 0 :=
  wqb_caseSum_inr P he hr

theorem wqb_bind {Γ : List (Ty Sig0)} {a t : Ty Sig0} {n m : ℕ}
    {c : Comp O I Γ a} {k : Comp O I (a :: Γ) t} {ρ : Env Γ}
    (hc : (c.eval ρ).IsQueryBoundP P n)
    (hk : ∀ x, (k.eval (.cons x ρ)).IsQueryBoundP P m) :
    ((Comp.bind c k).eval ρ).IsQueryBoundP P (n + m) := by
  simpa [Comp.eval] using isQueryBoundP_bind hc (fun x _ => hk x)

theorem wqb0_bind {Γ : List (Ty Sig0)} {a t : Ty Sig0}
    {c : Comp O I Γ a} {k : Comp O I (a :: Γ) t} {ρ : Env Γ}
    (hc : (c.eval ρ).IsQueryBoundP P 0)
    (hk : ∀ x, (k.eval (.cons x ρ)).IsQueryBoundP P 0) :
    ((Comp.bind c k).eval ρ).IsQueryBoundP P 0 := by
  simpa [Comp.eval] using isQueryBoundP_bind hc (fun x _ => hk x)

theorem wqb_sample {Γ : List (Ty Sig0)}
    (hU : ∀ n, (I.fwdU n).IsQueryBoundP P 0)
    {s : I.smp.Samp} {e : Expr O Γ (I.smp.sDom s)} {ρ : Env Γ} (m : ℕ) :
    ((Comp.sample s e : Comp O I Γ (I.smp.sTy s)).eval ρ).IsQueryBoundP P m :=
  (liftP_queryBound P hU _).mono (Nat.zero_le m)

theorem wqb0_sample {Γ : List (Ty Sig0)}
    (hU : ∀ n, (I.fwdU n).IsQueryBoundP P 0)
    {s : I.smp.Samp} {e : Expr O Γ (I.smp.sDom s)} {ρ : Env Γ} :
    ((Comp.sample s e : Comp O I Γ (I.smp.sTy s)).eval ρ).IsQueryBoundP P 0 :=
  liftP_queryBound P hU _

theorem wqb0_query {Γ : List (Ty Sig0)}
    {g : I.Tag} {e : Expr O Γ (I.dom g)} {ρ : Env Γ}
    (hg : ¬ P (I.enc g (e.eval ρ))) :
    ((Comp.query g e : Comp O I Γ (I.cod g)).eval ρ).IsQueryBoundP P 0 := by
  simp only [Comp.eval, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  intro h
  exact False.elim (hg h)

theorem wqb1_query {Γ : List (Ty Sig0)}
    {g : I.Tag} {e : Expr O Γ (I.dom g)} {ρ : Env Γ} :
    ((Comp.query g e : Comp O I Γ (I.cod g)).eval ρ).IsQueryBoundP P 1 := by
  simp only [Comp.eval, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  intro _
  exact Nat.zero_lt_one

end CompQueryHelpersWith

end KeyInd1RealRedsAux

section KindQueryBoundWith

open KeyInd1RealRedsAux

variable {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
variable (P : SignalPqxdh.Primitives)
variable (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
variable (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
variable (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)

private theorem isQueryBoundP_bhFwdU_ki
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (hInl : ∀ n, ¬ P_ki (.inl n)) (n : ℕ) :
    (bhFwdU (G := SignalPqxdh.keyIndSpec S) n).IsQueryBoundP P_ki 0 :=
  (isQueryBoundP_query_iff (spec := unifSpec + SignalPqxdh.keyIndSpec S)
    P_ki (Sum.inl n) 0).2 (fun h => False.elim (hInl n h))

private theorem isQueryBoundP_bhLiftP_ki {α : Type}
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (hInl : ∀ n, ¬ P_ki (.inl n)) (p : ProbComp α) :
    (bhLiftP (G := SignalPqxdh.keyIndSpec S) p).IsQueryBoundP P_ki 0 := by
  unfold bhLiftP
  induction p using OracleComp.inductionOn with
  | pure a => simp [simulateQ_pure]
  | query_bind n mx ih =>
    rw [simulateQ_query_bind]
    exact (isQueryBoundP_bind (isQueryBoundP_bhFwdU_ki hInl n)
      (fun u _ => ih u)).mono (by omega)

private theorem isQueryBoundP_ki_query_zero
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    {kq : SignalPqxdh.KeyIndQuery S} (hnot : ¬ P_ki (.inr kq)) :
    (liftM ((unifSpec + SignalPqxdh.keyIndSpec S).query (.inr kq)) :
      OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) _).IsQueryBoundP P_ki 0 :=
  (isQueryBoundP_query_iff (spec := unifSpec + SignalPqxdh.keyIndSpec S)
    P_ki (Sum.inr kq) 0).2 (fun h => False.elim (hnot h))

private theorem isQueryBoundP_ki_query_one
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (kq : SignalPqxdh.KeyIndQuery S) :
    (liftM ((unifSpec + SignalPqxdh.keyIndSpec S).query (.inr kq)) :
      OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) _).IsQueryBoundP P_ki 1 :=
  (isQueryBoundP_query_iff (spec := unifSpec + SignalPqxdh.keyIndSpec S)
    P_ki (Sum.inr kq) 1).2 (fun _ => Nat.zero_lt_one)

private theorem isQueryBoundP_bhKindHandleWith_subpred
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (hInl : ∀ n, ¬ P_ki (.inl n))
    (hTest : ∀ sid, ¬ P_ki (.inr (.testSession sid)))
    (hRev : ∀ u j, ¬ P_ki (.inr (.revealSpkSk u j)))
    (pKi : SignalPqxdh.KeyIndQuery S → Bool)
    (hSub : ∀ kq, P_ki (.inr kq) → pKi kq = true)
    (s : BHE2EDrvState S ℓ) (t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain) :
    (bhKindHandleWith P ki C K qep decT encT s (bhTargetQenc t)).IsQueryBoundP
      P_ki (if bhClassifyTargetOnly pKi (fun _ => false) (fun _ => false) t then 1 else 0) := by
  rcases t with (kq | cq) | ⟨i, sq⟩
  · simp only [bhClassifyTargetOnly, bhTargetQenc, bhKindHandleWith]
    by_cases hp : pKi kq = true
    · simp only [hp, ↓reduceIte]
      split_ifs
      · simpa only [Nat.add_zero] using
          isQueryBoundP_bind (isQueryBoundP_ki_query_one kq)
            (fun _ _ => isQueryBoundP_pure P_ki _ 0)
      · exact isQueryBoundP_pure P_ki _ 1
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]
      have hnot : ¬ P_ki (.inr kq) := fun h => by simp [hSub kq h] at hp
      split_ifs
      · simpa only [Nat.add_zero] using
          isQueryBoundP_bind (isQueryBoundP_ki_query_zero hnot)
            (fun _ _ => isQueryBoundP_pure P_ki _ 0)
      · exact isQueryBoundP_pure P_ki _ 0
  · rcases cq with ⟨sid⟩
    simp only [bhClassifyTargetOnly, Bool.false_eq_true, ↓reduceIte, bhTargetQenc, bhKindHandleWith]
    cases (bhE2EGuard s sid).map (fun (_, _, uj) => uj) with
    | none => exact isQueryBoundP_pure P_ki _ 0
    | some uj =>
      rcases uj with ⟨u, j⟩
      dsimp only
      exact (isQueryBoundP_bind (isQueryBoundP_ki_query_zero (hTest sid)) (fun _ _ =>
        isQueryBoundP_bind (isQueryBoundP_ki_query_zero (hRev u j)) (fun _ _ =>
          isQueryBoundP_bind (isQueryBoundP_bhLiftP_ki hInl _) (fun _ _ =>
            isQueryBoundP_pure P_ki _ 0)))).mono (by omega)
  · simp only [bhClassifyTargetOnly, Bool.false_eq_true, ↓reduceIte, bhTargetQenc, bhKindHandleWith]
    simpa only [Nat.add_zero] using
      isQueryBoundP_bind (isQueryBoundP_bhLiftP_ki hInl _)
        (fun _ _ => isQueryBoundP_pure P_ki _ 0)

private theorem isQueryBoundP_bhKindRedWith_init
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (hInl : ∀ n, ¬ P_ki (.inl n)) :
    ((bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).init ()).IsQueryBoundP P_ki 0 := by
  dsimp only [bhKindRedWith]
  simpa only [Nat.add_zero] using
    isQueryBoundP_bind (isQueryBoundP_bhLiftP_ki hInl _)
      (fun _ _ => isQueryBoundP_pure P_ki _ 0)

private theorem simulateQ_run_StateT_of_step_le
    {ι κ : Type} {G : OracleSpec κ} {T : OracleSpec ι} {σ α : Type}
    {P_src : κ → Prop} [DecidablePred P_src] {P_tgt : ι → Prop} [DecidablePred P_tgt]
    {so : QueryImpl G (StateT σ (OracleComp T))}
    (hstep : ∀ q s, ((so q).run s).IsQueryBoundP P_tgt (if P_src q then 1 else 0))
    {oa : OracleComp G α} {n : ℕ} (hB : oa.IsQueryBoundP P_src n) (s : σ) :
    ((simulateQ so oa).run s).IsQueryBoundP P_tgt n := by
  induction oa using OracleComp.inductionOn generalizing n s with
  | pure _ => simp [simulateQ_pure]
  | query_bind q mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hB
    rw [simulateQ_query_bind, StateT.run_bind]
    by_cases hp : P_src q
    · have hpos : 0 < n := hB.1.resolve_left (not_not.mpr hp)
      have hq : ((so q).run s).IsQueryBoundP P_tgt 1 := by simpa [hp] using hstep q s
      exact (isQueryBoundP_bind hq fun y _ =>
        ih y.1 (by simpa [hp] using hB.2 y.1) y.2).mono (by omega)
    · have hq : ((so q).run s).IsQueryBoundP P_tgt 0 := by simpa [hp] using hstep q s
      exact (isQueryBoundP_bind hq fun y _ =>
        ih y.1 (by simpa [hp] using hB.2 y.1) y.2).mono (by omega)

private theorem isQueryBoundP_bhKindRedWith_eval_subpred
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (hInl : ∀ n, ¬ P_ki (.inl n))
    (hTest : ∀ sid, ¬ P_ki (.inr (.testSession sid)))
    (hRev : ∀ u j, ¬ P_ki (.inr (.revealSpkSk u j)))
    (pKi : SignalPqxdh.KeyIndQuery S → Bool)
    (hSub : ∀ kq, P_ki (.inr kq) → pKi kq = true)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) (n : ℕ)
    (hB : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget pKi (fun _ => false) (fun _ => false) q = true) n) :
    ((bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).eval (fun _ => B_A) ()).IsQueryBoundP P_ki n := by
  have hstep : ∀ (q : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain)
      (s : BHE2EDrvState S ℓ),
      (((bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).impl q).run s).IsQueryBoundP
        P_ki (if bhClassifyTarget pKi (fun _ => false) (fun _ => false) q = true then 1 else 0) := by
    intro q s
    cases q with
    | inl m =>
      show (bhFwdU (G := SignalPqxdh.keyIndSpec S) m >>= fun a => pure (a, s)).IsQueryBoundP P_ki 0
      exact isQueryBoundP_bind (n := 0) (m := 0)
        (isQueryBoundP_bhFwdU_ki hInl m)
        (fun a _ => isQueryBoundP_pure P_ki (a, s) 0)
    | inr t =>
      show (bhKindHandleWith P ki C K qep decT encT s (bhTargetQenc t) >>=
          fun p => pure (bhTargetRdec t p.1, p.2)).IsQueryBoundP
        P_ki (if bhClassifyTargetOnly pKi (fun _ => false) (fun _ => false) t = true then 1 else 0)
      simpa only [Nat.add_zero] using isQueryBoundP_bind
        (isQueryBoundP_bhKindHandleWith_subpred P ki C K qep decT encT hInl hTest hRev pKi hSub s t)
        (fun p _ => isQueryBoundP_pure P_ki (bhTargetRdec t p.1, p.2) 0)
  have hsim := simulateQ_run_StateT_of_step_le hstep hB
  have hinit := isQueryBoundP_bhKindRedWith_init (ℓ := ℓ) P ki C K qep decT encT hInl
  have hfin : ∀ s' b,
      ((bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).finish s' b).IsQueryBoundP P_ki 0 := by
    intro s' b
    dsimp only [bhKindRedWith]
    exact isQueryBoundP_pure P_ki _ 0
  unfold BhShallowRed.eval
  exact (isQueryBoundP_bind hinit
    (fun ⟨_, s⟩ _ =>
      isQueryBoundP_bind (hsim s)
        (fun ⟨b, s'⟩ _ => hfin s' b))).mono (by omega)

private theorem isQueryBoundP_bhKindHandleWith_ki_p
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (pKi : SignalPqxdh.KeyIndQuery S → Bool)
    (hSub : ∀ kq, P_ki (.inr kq) → pKi kq = true)
    (s : BHE2EDrvState S ℓ) (kq : SignalPqxdh.KeyIndQuery S) :
    (bhKindHandleWith P ki C K qep decT encT s (bhTargetQenc (.inl (.inl kq)))).IsQueryBoundP
      P_ki (if pKi kq then 1 else 0) := by
  dsimp only [bhTargetQenc, bhKindHandleWith]
  by_cases hp : pKi kq = true
  · simp only [hp, ↓reduceIte]
    split_ifs
    · simpa only [Nat.add_zero] using
        isQueryBoundP_bind (isQueryBoundP_ki_query_one (P_ki := P_ki) kq)
          (fun _ _ => isQueryBoundP_pure P_ki _ 0)
    · exact isQueryBoundP_pure P_ki _ 1
  · simp only [hp, Bool.false_eq_true, ↓reduceIte]
    have hnot : ¬ P_ki (.inr kq) := fun h => hp (hSub kq h)
    split_ifs
    · simpa only [Nat.add_zero] using
        isQueryBoundP_bind (isQueryBoundP_ki_query_zero hnot)
          (fun _ _ => isQueryBoundP_pure P_ki _ 0)
    · exact isQueryBoundP_pure P_ki _ 0

private theorem isQueryBoundP_bhKindHandleWith_ctl_two
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (hInl : ∀ n : ℕ, ¬ P_ki (.inl n))
    (s : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S) :
    (bhKindHandleWith P ki C K qep decT encT s (bhTargetQenc (.inl (.inr (.startDR sid))))).IsQueryBoundP
      P_ki 2 := by
  dsimp only [bhTargetQenc, bhKindHandleWith]
  cases (bhE2EGuard s sid).map (fun (_, _, uj) => uj) with
  | none => exact isQueryBoundP_pure P_ki _ 2
  | some uj =>
    rcases uj with ⟨u, j⟩
    dsimp only
    exact (isQueryBoundP_bind (isQueryBoundP_ki_query_one (P_ki := P_ki) (.testSession sid)) (fun _ _ =>
      isQueryBoundP_bind (isQueryBoundP_ki_query_one (P_ki := P_ki) (.revealSpkSk u j)) (fun _ _ =>
        isQueryBoundP_bind (isQueryBoundP_bhLiftP_ki hInl _) (fun _ _ =>
          isQueryBoundP_pure P_ki _ 0)))).mono (by omega)

private theorem isQueryBoundP_bhKindHandleWith_sm_zero
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (hInl : ∀ n : ℕ, ¬ P_ki (.inl n))
    (s : BHE2EDrvState S ℓ) (i : ℕ)
    (sq : (SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    (bhKindHandleWith P ki C K qep decT encT s (bhTargetQenc (.inr ⟨i, sq⟩))).IsQueryBoundP
      P_ki 0 := by
  dsimp only [bhTargetQenc, bhKindHandleWith]
  simpa only [Nat.add_zero] using
    isQueryBoundP_bind (isQueryBoundP_bhLiftP_ki hInl _)
      (fun _ _ => isQueryBoundP_pure P_ki _ 0)

private theorem isQueryBoundP_simulateQ_bhKindRedWith_two
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (hInl : ∀ n : ℕ, ¬ P_ki (.inl n))
    (pKi : SignalPqxdh.KeyIndQuery S → Bool)
    (hSub : ∀ kq, P_ki (.inr kq) → pKi kq = true)
    {α : Type} (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
    (s : BHE2EDrvState S ℓ) (n₁ n₂ : ℕ)
    (h₁ : oa.IsQueryBoundP
      (fun q => bhClassifyTarget pKi (fun _ => false) (fun _ => false) q = true) n₁)
    (h₂ : oa.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true) n₂) :
    ((simulateQ (bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).impl oa).run s).IsQueryBoundP
      P_ki (n₁ + 2 * n₂) := by
  induction oa using OracleComp.inductionOn generalizing s n₁ n₂ with
  | pure a =>
    simp [simulateQ_pure, StateT.run_pure]
  | query_bind q mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h₁ h₂
    rw [simulateQ_query_bind, StateT.run_bind]
    rcases q with m | ((kq | cq) | ⟨i, sq⟩)
    · have hstep :
          (((bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).impl (.inl m)).run s).IsQueryBoundP P_ki 0 :=
        isQueryBoundP_bind (n := 0) (m := 0)
          (isQueryBoundP_bhFwdU_ki hInl m)
          (fun a _ => isQueryBoundP_pure P_ki (a, s) 0)
      have hcont : ∀ y ∈ support (((bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).impl (.inl m)).run s),
          ((simulateQ (bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).impl (mx y.1)).run y.2).IsQueryBoundP
            P_ki (n₁ + 2 * n₂) :=
        fun y _ => ih y.1 y.2 n₁ n₂
          ((h₁.2 y.1).mono (by simp [bhClassifyTarget]))
          ((h₂.2 y.1).mono (by simp [bhClassifyTarget]))
      exact (isQueryBoundP_bind hstep hcont).mono (by omega)
    · by_cases hp : pKi kq = true
      · have hn₁ : 0 < n₁ := h₁.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly, hp])
        have hstep :
            (((bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).impl (.inr (.inl (.inl kq)))).run s).IsQueryBoundP
            P_ki 1 := by
          show (bhKindHandleWith P ki C K qep decT encT s (bhTargetQenc (.inl (.inl kq))) >>=
              fun p => pure (bhTargetRdec (.inl (.inl kq)) p.1, p.2)).IsQueryBoundP
            P_ki 1
          have hk :
              (bhKindHandleWith P ki C K qep decT encT s (bhTargetQenc (.inl (.inl kq)))).IsQueryBoundP
                P_ki 1 := by
            simpa [hp] using isQueryBoundP_bhKindHandleWith_ki_p P ki C K qep decT encT pKi hSub s kq
          simpa only [Nat.add_zero] using
            isQueryBoundP_bind hk
              (fun p _ => isQueryBoundP_pure P_ki
                (bhTargetRdec (.inl (.inl kq)) p.1, p.2) 0)
        have hcont : ∀ y ∈ support
            (((bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).impl (.inr (.inl (.inl kq)))).run s),
            ((simulateQ (bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).impl (mx y.1)).run y.2).IsQueryBoundP
              P_ki ((n₁ - 1) + 2 * n₂) :=
          fun y _ => ih y.1 y.2 (n₁ - 1) n₂
            ((h₁.2 y.1).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly, hp]))
            ((h₂.2 y.1).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
        exact (isQueryBoundP_bind hstep hcont).mono (by omega)
      · have hstep :
            (((bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).impl (.inr (.inl (.inl kq)))).run s).IsQueryBoundP
            P_ki 0 := by
          show (bhKindHandleWith P ki C K qep decT encT s (bhTargetQenc (.inl (.inl kq))) >>=
              fun p => pure (bhTargetRdec (.inl (.inl kq)) p.1, p.2)).IsQueryBoundP
            P_ki 0
          have hk :
              (bhKindHandleWith P ki C K qep decT encT s (bhTargetQenc (.inl (.inl kq)))).IsQueryBoundP
                P_ki 0 := by
            simpa [hp] using isQueryBoundP_bhKindHandleWith_ki_p P ki C K qep decT encT pKi hSub s kq
          simpa only [Nat.add_zero] using
            isQueryBoundP_bind hk
              (fun p _ => isQueryBoundP_pure P_ki
                (bhTargetRdec (.inl (.inl kq)) p.1, p.2) 0)
        have hcont : ∀ y ∈ support
            (((bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).impl (.inr (.inl (.inl kq)))).run s),
            ((simulateQ (bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).impl (mx y.1)).run y.2).IsQueryBoundP
              P_ki (n₁ + 2 * n₂) :=
          fun y _ => ih y.1 y.2 n₁ n₂
            ((h₁.2 y.1).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly, hp]))
            ((h₂.2 y.1).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
        exact (isQueryBoundP_bind hstep hcont).mono (by omega)
    · rcases cq with ⟨sid⟩
      have hn₂ : 0 < n₂ := h₂.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
      have hstep :
          (((bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).impl
            (.inr (.inl (.inr (.startDR sid))))).run s).IsQueryBoundP P_ki 2 := by
        show (bhKindHandleWith P ki C K qep decT encT s (bhTargetQenc (.inl (.inr (.startDR sid)))) >>=
            fun p => pure (bhTargetRdec (.inl (.inr (.startDR sid))) p.1, p.2)).IsQueryBoundP
          P_ki 2
        simpa only [Nat.add_zero] using
          isQueryBoundP_bind (isQueryBoundP_bhKindHandleWith_ctl_two P ki C K qep decT encT hInl s sid)
            (fun p _ => isQueryBoundP_pure P_ki
              (bhTargetRdec (.inl (.inr (.startDR sid))) p.1, p.2) 0)
      have hcont : ∀ y ∈ support
          (((bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).impl
            (.inr (.inl (.inr (.startDR sid))))).run s),
          ((simulateQ (bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).impl (mx y.1)).run y.2).IsQueryBoundP
            P_ki (n₁ + 2 * (n₂ - 1)) :=
        fun y _ => ih y.1 y.2 n₁ (n₂ - 1)
          ((h₁.2 y.1).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
          ((h₂.2 y.1).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
      exact (isQueryBoundP_bind hstep hcont).mono (by omega)
    · have hstep :
          (((bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).impl (.inr (.inr ⟨i, sq⟩))).run s).IsQueryBoundP
          P_ki 0 := by
        show (bhKindHandleWith P ki C K qep decT encT s (bhTargetQenc (.inr ⟨i, sq⟩)) >>=
            fun p => pure (bhTargetRdec (.inr ⟨i, sq⟩) p.1, p.2)).IsQueryBoundP
          P_ki 0
        simpa only [Nat.add_zero] using
          isQueryBoundP_bind (isQueryBoundP_bhKindHandleWith_sm_zero P ki C K qep decT encT hInl s i sq)
            (fun p _ => isQueryBoundP_pure P_ki
              (bhTargetRdec (.inr ⟨i, sq⟩) p.1, p.2) 0)
      have hcont : ∀ y ∈ support
          (((bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).impl (.inr (.inr ⟨i, sq⟩))).run s),
          ((simulateQ (bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).impl (mx y.1)).run y.2).IsQueryBoundP
            P_ki (n₁ + 2 * n₂) :=
        fun y _ => ih y.1 y.2 n₁ n₂
          ((h₁.2 y.1).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
          ((h₂.2 y.1).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
      exact (isQueryBoundP_bind hstep hcont).mono (by omega)

/-- Target-level `KeyInd` query bound for `bhKindRedWith` on a query-bounded adversary `B_A`. -/
theorem bhKindRedWith_queryBounded_of_B
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ)
    (hRo : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun kq => kq matches .roQuery _) (fun _ => false) (fun _ => false) q = true)
      b.q_ro)
    (hSend : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget
        (fun kq => kq matches .initiateOPK .. || kq matches .initiateNoOPK ..)
        (fun _ => false) (fun _ => false) q = true)
      S.N_send_tot)
    (hRecv : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget
        (fun kq => kq matches .acceptOPK .. || kq matches .acceptNoOPK ..)
        (fun _ => false) (fun _ => false) q = true)
      S.N_recv_tot)
    (hTot : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => true) (fun _ => false) (fun _ => false) q = true)
      b.q_total)
    (hOn : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun kq => !(kq matches .roQuery _)) (fun _ => false) (fun _ => false) q = true)
      b.q_on)
    (hCtlSend : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
      S.N_send_tot)
    (hCtlStart : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
      qStart) :
    let advK : SignalPqxdh.KeyIndAdversary S :=
      ⟨(bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).eval (fun _ => B_A) ()⟩
    SignalPqxdh.QueryBounded advK (keyIndReductionBudget S qStart b) := by
  intro advK
  have hCtlMin : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
      (min qStart S.N_send_tot) := by
    rcases le_total qStart S.N_send_tot with h | h
    · simpa [Nat.min_eq_left h] using hCtlStart
    · simpa [Nat.min_eq_right h] using hCtlSend
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact isQueryBoundP_bhKindRedWith_eval_subpred P ki C K qep decT encT
      (by intro n; simp [SignalPqxdh.isKeyIndRoQuery])
      (by intro sid; simp [SignalPqxdh.isKeyIndRoQuery])
      (by intro u j; simp [SignalPqxdh.isKeyIndRoQuery])
      (fun kq => kq matches .roQuery _)
      (by intro kq h; cases kq <;> first | rfl | exact False.elim h)
      B_A b.q_ro hRo
  · exact isQueryBoundP_bhKindRedWith_eval_subpred P ki C K qep decT encT
      (by intro n; simp [SignalPqxdh.isKeyIndSendQuery])
      (by intro sid; simp [SignalPqxdh.isKeyIndSendQuery])
      (by intro u j; simp [SignalPqxdh.isKeyIndSendQuery])
      (fun kq => kq matches .initiateOPK .. || kq matches .initiateNoOPK ..)
      (by intro kq h; cases kq <;> first | rfl | exact False.elim h)
      B_A S.N_send_tot hSend
  · exact isQueryBoundP_bhKindRedWith_eval_subpred P ki C K qep decT encT
      (by intro n; simp [SignalPqxdh.isKeyIndRecvQuery])
      (by intro sid; simp [SignalPqxdh.isKeyIndRecvQuery])
      (by intro u j; simp [SignalPqxdh.isKeyIndRecvQuery])
      (fun kq => kq matches .acceptOPK .. || kq matches .acceptNoOPK ..)
      (by intro kq h; cases kq <;> first | rfl | exact False.elim h)
      B_A S.N_recv_tot hRecv
  · let P_game : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop :=
      fun q => SignalPqxdh.isGameQuery q = true
    have hInl : ∀ n : ℕ, ¬ P_game (.inl n) := by intro n; simp [P_game, SignalPqxdh.isGameQuery]
    have hinit := isQueryBoundP_bhKindRedWith_init (ℓ := ℓ) P ki C K qep decT encT hInl
    have hfin : ∀ s' b_out,
        ((bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).finish s' b_out).IsQueryBoundP P_game 0 := by
      intro s' b_out
      dsimp only [bhKindRedWith]
      exact isQueryBoundP_pure P_game _ 0
    show ((bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).eval (fun _ => B_A) ()).IsQueryBoundP
      P_game (b.q_total + 2 * min qStart S.N_send_tot)
    unfold BhShallowRed.eval
    exact (isQueryBoundP_bind hinit
      (fun ⟨_, s⟩ _ =>
        isQueryBoundP_bind
          (isQueryBoundP_simulateQ_bhKindRedWith_two P ki C K qep decT encT hInl (fun _ => true)
            (by intro _ _; rfl) B_A s b.q_total (min qStart S.N_send_tot) hTot hCtlMin)
          (fun ⟨b_out, s'⟩ _ => hfin s' b_out))).mono (by omega)
  · let P_on : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop :=
      SignalPqxdh.isKeyIndOnlineQuery
    have hInl : ∀ n : ℕ, ¬ P_on (.inl n) := by intro n; simp [P_on, SignalPqxdh.isKeyIndOnlineQuery]
    have hinit := isQueryBoundP_bhKindRedWith_init (ℓ := ℓ) P ki C K qep decT encT hInl
    have hfin : ∀ s' b_out,
        ((bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).finish s' b_out).IsQueryBoundP P_on 0 := by
      intro s' b_out
      dsimp only [bhKindRedWith]
      exact isQueryBoundP_pure P_on _ 0
    show ((bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).eval (fun _ => B_A) ()).IsQueryBoundP
      P_on (b.q_on + 2 * min qStart S.N_send_tot)
    unfold BhShallowRed.eval
    exact (isQueryBoundP_bind hinit
      (fun ⟨_, s⟩ _ =>
        isQueryBoundP_bind
          (isQueryBoundP_simulateQ_bhKindRedWith_two P ki C K qep decT encT hInl
            (fun kq => !(kq matches .roQuery _))
            (by intro kq h; cases kq <;> first | rfl | exact False.elim h)
            B_A s b.q_on (min qStart S.N_send_tot) hOn hCtlMin)
          (fun ⟨b_out, s'⟩ _ => hfin s' b_out))).mono (by omega)

end KindQueryBoundWith

end CryptoVerification.E2E

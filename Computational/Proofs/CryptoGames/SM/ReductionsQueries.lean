/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Reductions
import VCVio.OracleComp.QueryTracking.SubSpec

/-!
# Query bounds for the FS-AEAD reductions

**Checked by Lean.**

**DEV-SM26 (formalization): the FS-AEAD reductions make up to `2q` queries (at most `q` decryption queries).**
Each SM query causes at most two FS-AEAD queries in `redFSAuth`, `redFSPriv`, and `redFSPrivCoin`,
while only `fsRecv` issues a decryption (`deliver` or `inject`) query.
-/

@[expose] public section

open OracleComp OracleSpec

namespace CryptoGames.FSAEAD

variable {SS RS AD Msg C : Type}

/-- Whether an FS-AEAD oracle query is a decryption query (`deliver` or `inject`). -/
protected def isDecQuery : (unifSpec + spec SS RS AD Msg C).Domain → Bool
  | .inr (.inl (.inr _)) => true
  | .inr (.inr _) => true
  | _ => false

/-- `A` makes at most `qd` decryption (`deliver` or `inject`) queries to the Fig. 5 oracles. -/
protected def MakesAtMostDecQueries (A : Adversary SS RS AD Msg C) (qd : ℕ) : Prop :=
  A.IsQueryBoundP (fun t => FSAEAD.isDecQuery (SS := SS) (RS := RS) (AD := AD) (Msg := Msg) (C := C) t = true) qd

end CryptoGames.FSAEAD

namespace CryptoGames.SM.Construction

open Engine

namespace ReductionsQueries

section Generic

variable {ι ι' : Type} {spec : OracleSpec.{0, 0} ι} {spec' : OracleSpec.{0, 0} ι'}
  {σ α β : Type}

theorem isQueryBoundP_false (oa : OracleComp spec α) (n : ℕ) :
    IsQueryBoundP oa (fun _ => False) n := by
  induction oa using OracleComp.inductionOn with
  | pure _ => trivial
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl not_false, fun u => by simp [ih u]⟩

/-- Transfer a predicate-targeted query bound `n` through `simulateQ` when each `p`-query step makes
at most `k` `Q`-queries and each `¬ p`-query step makes `0` `Q`-queries. -/
theorem simulateQ_run_of_step_mul
    {p : ι → Prop} [DecidablePred p] {Q : ι' → Prop} [DecidablePred Q]
    {impl : QueryImpl spec (StateT σ (OracleComp spec'))}
    {oa : OracleComp spec α} {k n : ℕ}
    (h : IsQueryBoundP oa p n)
    (hstep_p : ∀ t, p t → ∀ s, IsQueryBoundP ((impl t).run s) Q k)
    (hstep_np : ∀ t, ¬ p t → ∀ s, IsQueryBoundP ((impl t).run s) Q 0)
    (s : σ) :
    IsQueryBoundP ((simulateQ impl oa).run s) Q (k * n) := by
  induction oa using OracleComp.inductionOn generalizing n s with
  | pure x => simp [simulateQ_pure]
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    rw [simulateQ_query_bind, StateT.run_bind]
    have hlift :
        IsQueryBoundP
          ((liftM (impl t) : StateT σ (OracleComp spec') (spec.Range t)).run s) Q
          (if p t then k else 0) := by
      by_cases hpt : p t
      · simpa [OracleComp.liftM_run_StateT, MonadLift.monadLift, ite_eq_left hpt] using
          hstep_p t hpt s
      · simpa [OracleComp.liftM_run_StateT, MonadLift.monadLift, ite_eq_right hpt] using
          hstep_np t hpt s
    have hbound : (if p t then k else 0) + k * (if p t then n - 1 else n) ≤ k * n := by
      split_ifs with hpt
      · have hn : 0 < n := h.1.resolve_left (fun hnp => hnp hpt)
        rw [Nat.mul_sub_one, Nat.add_sub_cancel' (Nat.le_mul_of_pos_right k hn)]
      · omega
    exact (isQueryBoundP_bind hlift fun pu _ => ih pu.1 (h.2 pu.1) pu.2).mono hbound

end Generic

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}

abbrev FSpec (SS RS T M E : Type) := FSAEAD.spec SS RS (Header T) M E

abbrev RSpec (SS RS T M E : Type) := unifSpec + FSpec SS RS T M E

section QB

variable {Q : (RSpec SS RS T M E).Domain → Prop} [DecidablePred Q] {σ α β : Type}

def QB (Q : (RSpec SS RS T M E).Domain → Prop) [DecidablePred Q]
    {σ α : Type} (x : StateT σ (OracleComp (RSpec SS RS T M E)) α) (n : ℕ) : Prop :=
  ∀ s : σ, IsQueryBoundP (x.run s) Q n

theorem qb_pure (a : α) (n : ℕ) :
    QB Q (pure a : StateT σ (OracleComp (RSpec SS RS T M E)) α) n := fun _ => by
  simp

theorem qb_bind {x : StateT σ (OracleComp (RSpec SS RS T M E)) α}
    {f : α → StateT σ (OracleComp (RSpec SS RS T M E)) β} {n m : ℕ}
    (hx : QB Q x n) (hf : ∀ a, QB Q (f a) m) : QB Q (x >>= f) (n + m) := fun s => by
  rw [StateT.run_bind]
  exact isQueryBoundP_bind (hx s) fun p _ => hf p.1 p.2

theorem qb_bind0 {x : StateT σ (OracleComp (RSpec SS RS T M E)) α}
    {f : α → StateT σ (OracleComp (RSpec SS RS T M E)) β} {m : ℕ}
    (hx : QB Q x 0) (hf : ∀ a, QB Q (f a) m) : QB Q (x >>= f) m := by
  simpa using qb_bind hx hf

theorem qb_bind_r {x : StateT σ (OracleComp (RSpec SS RS T M E)) α}
    {f : α → StateT σ (OracleComp (RSpec SS RS T M E)) β} {n : ℕ}
    (hx : QB Q x n) (hf : ∀ a, QB Q (f a) 0) : QB Q (x >>= f) n := by
  simpa using qb_bind hx hf

theorem qb_mono {x : StateT σ (OracleComp (RSpec SS RS T M E)) α} {n m : ℕ}
    (hx : QB Q x n) (hnm : n ≤ m) : QB Q x m :=
  fun s => (hx s).mono hnm

theorem qb_get : QB Q (get : StateT σ (OracleComp (RSpec SS RS T M E)) σ) 0 := fun _ => by
  simp

theorem qb_set (s' : σ) :
    QB Q (set s' : StateT σ (OracleComp (RSpec SS RS T M E)) PUnit) 0 := fun _ => by
  simp

theorem qb_modify (f : σ → σ) :
    QB Q (modify f : StateT σ (OracleComp (RSpec SS RS T M E)) PUnit) 0 := fun _ => by
  simp

theorem qb_stateT_lift {x : OracleComp (RSpec SS RS T M E) α} {n : ℕ}
    (hx : IsQueryBoundP x Q n) :
    QB Q (StateT.lift x : StateT σ (OracleComp (RSpec SS RS T M E)) α) n := fun s => by
  show IsQueryBoundP (x >>= fun a => pure (a, s)) Q n
  simpa using isQueryBoundP_bind hx (fun a _ => isQueryBoundP_pure Q (a, s) 0)

theorem qb_liftF_query (t : (RSpec SS RS T M E).Domain) :
    QB Q (liftF (SS := SS) (RS := RS) (T := T) (M := M) (E := E) (Sig := Sig) (K := K) (I := I)
      (query (spec := RSpec SS RS T M E) t)) 1 :=
  qb_stateT_lift ((isQueryBoundP_query_iff Q t 1).2 (fun _ => Nat.zero_lt_one))

theorem qb_liftH {Γv Sv SSv RSv HS : Type}
    {x : HM (FSpec SS RS T M E) HS α} {n : ℕ} (hx : QB Q x n) :
    QB Q (liftH x : EM (FSpec SS RS T M E) Γv T Sv SSv RSv M E HS α) n := fun es => by
  unfold liftH
  simpa [StateT.run] using hx es.h

theorem qb_abortE {Γv Sv SSv RSv HS : Type} :
    QB Q (abortE : EM (FSpec SS RS T M E) Γv T Sv SSv RSv M E HS PUnit) 0 :=
  qb_modify _

variable (hQu : ∀ u, ¬ Q (.inl u))
include hQu

theorem isQueryBoundP_sampleT (α : Type) [SampleableType α] :
    IsQueryBoundP (sampleT (tspec := FSpec SS RS T M E) α) Q 0 :=
  IsQueryBoundP.liftComp_subSpec (p := fun _ => False)
    (fun t => ⟨False.elim, fun h => hQu t h⟩) (isQueryBoundP_false ($ᵗ α) 0)

theorem qb_lift_sampleT (α : Type) [SampleableType α] :
    QB Q (StateT.lift (sampleT (tspec := FSpec SS RS T M E) α) :
      StateT σ (OracleComp (RSpec SS RS T M E)) α) 0 :=
  qb_stateT_lift (isQueryBoundP_sampleT hQu α)

end QB

section HooksFS

variable {Q : (RSpec SS RS T M E).Domain → Prop} [DecidablePred Q]
  (hQu : ∀ u, ¬ Q (.inl u))
include hQu

theorem qb_lookupF [DecidableEq I] [SampleableType K] (Ik : I) :
    QB Q (lookupF (T := T) (Sig := Sig) (K := K) (SS := SS) (RS := RS) (M := M) (E := E) Ik) 0 := by
  unfold lookupF
  refine qb_bind0 qb_get fun s => ?_
  cases s.table.lookup Ik with
  | some k => exact qb_pure k 0
  | none =>
    refine qb_bind0 (qb_lift_sampleT hQu K) fun k => ?_
    exact qb_bind0 (qb_modify _) fun _ => qb_pure k 0

omit hQu in
theorem qb_isExt [DecidableEq I] (j : ℕ) (Ik : I) :
    QB Q (isExt (T := T) (Sig := Sig) (K := K) (SS := SS) (RS := RS) (M := M) (E := E) j Ik) 0 := by
  unfold isExt
  refine qb_bind0 qb_get fun s => ?_
  split_ifs
  · exact qb_pure _ 0
  · exact qb_bind0 (qb_set _) fun _ => qb_pure _ 0

omit hQu in
theorem qb_extOf [DecidableEq I] (j : ℕ) (sid : Option I) :
    QB Q (extOf (T := T) (Sig := Sig) (K := K) (SS := SS) (RS := RS) (M := M) (E := E) j sid) 0 := by
  unfold extOf
  cases sid with
  | none => exact qb_pure false 0
  | some Ik => exact qb_isExt j Ik

theorem qb_rootFS [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (mo : Mode) (t : ℕ) (Ik : I) (σ : Sig) :
    QB Q (rootFS (T := T) (SS := SS) (RS := RS) (M := M) (E := E) prng mo t Ik σ) 0 := by
  unfold rootFS
  split_ifs
  · exact qb_pure _ 0
  · refine qb_bind0 (qb_lift_sampleT hQu I) fun Ir => ?_
    refine qb_bind0 (qb_lift_sampleT hQu K) fun k => ?_
    exact qb_pure _ 0
  · refine qb_bind0 (qb_lookupF hQu Ik) fun k => ?_
    exact qb_pure _ 0
  · refine qb_bind0 (qb_lift_sampleT hQu I) fun Ir => ?_
    exact qb_pure _ 0
  · exact qb_pure _ 0

theorem qb_initFS [DecidableEq I] [SampleableType KR] [SampleableType KC]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (mo : Mode) (j : ℕ) :
    QB Q (initFS cka prng fs lam mo j) 0 := by
  unfold initFS
  refine qb_bind0 (qb_lift_sampleT hQu KR) fun kr => ?_
  refine qb_bind0 (qb_lift_sampleT hQu KC) fun kc => ?_
  refine qb_bind0 (qb_rootFS hQu prng mo 0 lam (prng.init kr)) fun p => ?_
  refine qb_bind0 (qb_extOf j p.2.2) fun ext => ?_
  exact qb_pure _ 0

theorem qb_startSend [DecidableEq T] [DecidableEq E] [DecidableEq I] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (ctx : Ctx Γ T Sig (Option SS) (Option RS) M E) (P : Party) (t : ℕ)
    (γ : Γ) (σ : Sig) (r : Option CCoins) :
    QB Q ((hooksFS cka prng fs Δcka mo j).startSend ctx P t γ σ r) 0 := by
  dsimp only [hooksFS]
  cases r with
  | some c =>
    simp only [pure_bind]
    refine qb_bind0 (qb_rootFS hQu prng mo t (cka.send γ c).2.2 σ) fun p => ?_
    refine qb_bind0 (qb_extOf j p.2.2) fun ext => ?_
    exact qb_bind0 (qb_modify _) fun _ => qb_pure _ 0
  | none =>
    refine qb_bind0 (qb_lift_sampleT hQu CCoins) fun c => ?_
    refine qb_bind0 (qb_rootFS hQu prng mo t (cka.send γ c).2.2 σ) fun p => ?_
    refine qb_bind0 (qb_extOf j p.2.2) fun ext => ?_
    exact qb_bind0 (qb_modify _) fun _ => qb_pure _ 0

theorem qb_startRecv [DecidableEq T] [DecidableEq E] [DecidableEq I] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (ctx : Ctx Γ T Sig (Option SS) (Option RS) M E) (P : Party) (t : ℕ)
    (γ : Γ) (σ : Sig) (Tn : T) :
    QB Q ((hooksFS cka prng fs Δcka mo j).startRecv ctx P t γ σ Tn) 0 := by
  dsimp only [hooksFS]
  refine qb_bind0 qb_get fun s => ?_
  cases s.cache t with
  | some quad =>
    rcases quad with ⟨Tc, σc, k, ext⟩
    dsimp only
    by_cases hTc : Tc = Tn
    · simp only [hTc, ↓reduceIte]
      exact qb_pure _ 0
    · simp only [hTc, ↓reduceIte]
      split_ifs
      · exact qb_pure _ 0
      · refine qb_bind0 (qb_lookupF hQu (cka.receive γ Tn).2) fun k' => ?_
        refine qb_bind0 (qb_isExt j (cka.receive γ Tn).2) fun ext' => ?_
        exact qb_pure _ 0
      · exact qb_pure _ 0
  | none =>
    dsimp only
    split_ifs
    · exact qb_pure _ 0
    · refine qb_bind0 (qb_lookupF hQu (cka.receive γ Tn).2) fun k' => ?_
      refine qb_bind0 (qb_isExt j (cka.receive γ Tn).2) fun ext' => ?_
      exact qb_pure _ 0
    · exact qb_pure _ 0

omit hQu in
theorem qb_fsSend [DecidableEq T] [DecidableEq E] [DecidableEq I] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (ctx : Ctx Γ T Sig (Option SS) (Option RS) M E) (P : Party) (t : ℕ)
    (ssv : Option SS) (h : Header T) (m : M) (pair : Option (M × M)) :
    QB Q ((hooksFS cka prng fs Δcka mo j).fsSend ctx P t ssv h m pair) 2 := by
  dsimp only [hooksFS]
  cases ssv with
  | some ss => exact qb_pure _ 2
  | none =>
    refine qb_bind0 qb_get fun s => ?_
    cases s.ext with
    | some sr =>
      exact qb_bind0 (qb_set _) fun _ => qb_pure _ 2
    | none =>
      dsimp only
      by_cases hc : (!ctx.safeCh (2 + Δcka) P && !s.fsSCorr) = true
      · simp only [hc, ↓reduceIte]
        show QB Q _ (1 + 1)
        refine qb_bind (qb_liftF_query _) fun r => ?_
        cases r with
        | none =>
          simp only [pure_bind, Bool.not_false, ↓reduceIte]
          exact qb_pure none 1
        | some _ =>
          refine qb_bind0 (qb_modify _) fun _ => ?_
          simp only [pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          cases pair <;>
            (refine qb_bind_r (qb_liftF_query _) fun e? => ?_
             cases e? with
             | none => exact qb_pure none 0
             | some e => exact qb_bind0 (qb_modify _) fun _ => qb_pure _ 0)
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, pure_bind, Bool.not_true]
        refine qb_mono (n := 1) ?_ (by omega)
        cases pair <;>
          (refine qb_bind_r (qb_liftF_query _) fun e? => ?_
           cases e? with
           | none => exact qb_pure none 0
           | some e => exact qb_bind0 (qb_modify _) fun _ => qb_pure _ 0)

omit hQu in
theorem qb_fsRecv [DecidableEq T] [DecidableEq E] [DecidableEq I] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (ctx : Ctx Γ T Sig (Option SS) (Option RS) M E) (P : Party) (t : ℕ)
    (rsv : Option RS) (h : Header T) (e : E) (rec : Option (Record M (Header T × E))) :
    QB Q ((hooksFS cka prng fs Δcka mo j).fsRecv ctx P t rsv h e rec) 2 := by
  dsimp only [hooksFS]
  cases rsv with
  | some rs => exact qb_pure _ 2
  | none =>
    refine qb_bind0 qb_get fun s => ?_
    cases s.ext with
    | some sr =>
      dsimp only
      cases fs.receive sr.2 h e with
      | none => exact qb_pure _ 2
      | some rim => exact qb_bind0 (qb_set _) fun _ => qb_pure _ 2
    | none =>
      dsimp only
      refine qb_mono (n := 1) ?_ (by omega)
      by_cases hm : (s.fsTrans.find? (fun x => x.2 == (h, e))).isSome = true <;>
        (simp only [hm, Bool.false_eq_true, ↓reduceIte]
         refine qb_bind_r (qb_liftF_query _) fun res => ?_
         cases res with
         | none => exact qb_pure none 0
         | some rr =>
           cases rr with
           | rejected => exact qb_pure (some none) 0
           | accepted i mo' =>
             dsimp only
             refine qb_bind0 (qb_modify _) fun _ => ?_
             cases mo' <;> cases rec <;> exact qb_pure _ 0)

omit hQu in
theorem qb_reveal [DecidableEq T] [DecidableEq E] [DecidableEq I] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (ctx : Ctx Γ T Sig (Option SS) (Option RS) M E) (P : Party)
    (vp : PartyState Γ T Sig (Option SS) (Option RS)) :
    QB Q ((hooksFS cka prng fs Δcka mo j).reveal ctx P vp) 2 := by
  dsimp only [hooksFS]
  cases vp.vS with
  | none =>
    simp only [pure_bind]
    cases vp.vR mo.tStar with
    | none => exact qb_pure _ 2
    | some rsv =>
      cases rsv with
      | some rs => exact qb_pure _ 2
      | none =>
        refine qb_bind0 qb_get fun s => ?_
        cases s.ext with
        | some sr => exact qb_pure _ 2
        | none =>
          split_ifs
          · exact qb_pure none 2
          · refine qb_mono (n := 1) (qb_bind_r (qb_liftF_query _) fun r => ?_) (by omega)
            cases r with
            | none => exact qb_pure none 0
            | some sr => exact qb_bind0 (qb_modify _) fun _ => qb_pure _ 0
  | some ssv =>
    cases ssv with
    | some ss =>
      simp only [pure_bind]
      cases vp.vR mo.tStar with
      | none => exact qb_pure _ 2
      | some rsv =>
        cases rsv with
        | some rs => exact qb_pure _ 2
        | none =>
          refine qb_bind0 qb_get fun s => ?_
          cases s.ext with
          | some sr => exact qb_pure _ 2
          | none =>
            split_ifs
            · exact qb_pure none 2
            · refine qb_mono (n := 1) (qb_bind_r (qb_liftF_query _) fun r => ?_) (by omega)
              cases r with
              | none => exact qb_pure none 0
              | some sr => exact qb_bind0 (qb_modify _) fun _ => qb_pure _ 0
    | none =>
      refine qb_bind0 qb_get fun s => ?_
      cases s.ext with
      | some sr =>
        simp only [pure_bind]
        cases vp.vR mo.tStar with
        | none => exact qb_pure _ 2
        | some rsv =>
          cases rsv with
          | some rs => exact qb_pure _ 2
          | none =>
            refine qb_bind0 qb_get fun s' => ?_
            cases s'.ext with
            | some sr' => exact qb_pure _ 2
            | none =>
              split_ifs
              · exact qb_pure none 2
              · refine qb_mono (n := 1) (qb_bind_r (qb_liftF_query _) fun r => ?_) (by omega)
                cases r with
                | none => exact qb_pure none 0
                | some sr' => exact qb_bind0 (qb_modify _) fun _ => qb_pure _ 0
      | none =>
        show QB Q _ (1 + 1)
        refine qb_bind (qb_liftF_query _) fun r => ?_
        cases r with
        | none =>
          simp only [pure_bind]
          exact qb_pure none 1
        | some ss =>
          refine qb_bind0 (qb_modify _) fun _ => ?_
          simp only [pure_bind]
          cases vp.vR mo.tStar with
          | none => exact qb_pure _ 1
          | some rsv =>
            cases rsv with
            | some rs => exact qb_pure _ 1
            | none =>
              refine qb_bind0 qb_get fun s' => ?_
              cases s'.ext with
              | some sr' => exact qb_pure _ 1
              | none =>
                split_ifs
                · exact qb_pure none 1
                · refine qb_bind_r (qb_liftF_query _) fun r' => ?_
                  cases r' with
                  | none => exact qb_pure none 0
                  | some sr' => exact qb_bind0 (qb_modify _) fun _ => qb_pure _ 0

theorem qb_vSend [DecidableEq T] [DecidableEq E] [DecidableEq I] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (ctx : Ctx Γ T Sig (Option SS) (Option RS) M E) (P : Party)
    (s : VP Γ T Sig (Option SS) (Option RS)) (m : M)
    (pair : Option (M × M)) (r : Option CCoins) :
    QB Q (vSend (hooksFS cka prng fs Δcka mo j) ctx P s m pair r) 2 := by
  unfold vSend
  dsimp only
  split_ifs
  · refine qb_bind0 (qb_startSend hQu cka prng fs Δcka mo j ctx P (s.tcur + 1) s.γ s.root r)
      fun res => ?_
    cases res with
    | none =>
      simp only [pure_bind]
      exact qb_pure none 2
    | some quad =>
      rcases quad with ⟨γ', T', σ', ss⟩
      simp only [pure_bind]
      refine qb_bind_r
        (qb_fsSend cka prng fs Δcka mo j ctx P (s.tcur + 1) ss (s.tcur + 1, some T') m pair)
        fun res' => ?_
      cases res' with
      | none => exact qb_pure none 0
      | some ve => exact qb_pure _ 0
  · simp only [pure_bind]
    cases s.vS with
    | none => exact qb_pure _ 2
    | some v =>
      refine qb_bind_r
        (qb_fsSend cka prng fs Δcka mo j ctx P s.tcur v (s.tcur, s.curCkaMsg) m pair)
        fun res => ?_
      cases res with
      | none => exact qb_pure none 0
      | some ve => exact qb_pure _ 0

theorem qb_vRecv [DecidableEq T] [DecidableEq E] [DecidableEq I]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (ctx : Ctx Γ T Sig (Option SS) (Option RS) M E) (P : Party)
    (s : VP Γ T Sig (Option SS) (Option RS))
    (c : Header T × E) (rec : Option (Record M (Header T × E))) :
    QB Q (vRecv (hooksFS cka prng fs Δcka mo j) ctx P s c rec) 2 := by
  unfold vRecv
  dsimp only
  by_cases h1 : (s.id.sendsIn c.1.1 || decide (s.tcur + 1 < c.1.1)) = true
  · simp only [h1, ↓reduceIte]
    exact qb_pure (some none) 2
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : c.1.1 = s.tcur + 1
    · rw [ite_eq_left h2]
      cases c.1.2 with
      | none =>
        simp only [pure_bind]
        exact qb_pure (some none) 2
      | some Tn =>
        dsimp only
        refine qb_bind0 (qb_startRecv hQu cka prng fs Δcka mo j ctx P c.1.1 s.γ s.root Tn)
          fun res => ?_
        cases res with
        | none =>
          simp only [pure_bind]
          exact qb_pure none 2
        | some inner =>
          cases inner with
          | none =>
            simp only [pure_bind]
            exact qb_pure (some none) 2
          | some triple =>
            rcases triple with ⟨γ', σ', rs⟩
            simp only [pure_bind, Function.update_self]
            refine qb_bind_r
              (qb_fsRecv cka prng fs Δcka mo j ctx P c.1.1 rs c.1 c.2 rec)
              fun res' => ?_
            cases res' with
            | none => exact qb_pure none 0
            | some inner' =>
              cases inner' with
              | none => exact qb_pure (some none) 0
              | some vim => exact qb_pure _ 0
    · simp only [h2, ↓reduceIte, pure_bind]
      cases s.vR c.1.1 with
      | none => exact qb_pure (some none) 2
      | some v =>
        refine qb_bind_r
          (qb_fsRecv cka prng fs Δcka mo j ctx P c.1.1 v c.1 c.2 rec)
          fun res => ?_
        cases res with
        | none => exact qb_pure none 0
        | some inner' =>
          cases inner' with
          | none => exact qb_pure (some none) 0
          | some vim => exact qb_pure _ 0

omit hQu in
theorem qb_commitE [DecidableEq M] [DecidableEq T] [DecidableEq E] [DecidableEq I] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (s : Ctx Γ T Sig (Option SS) (Option RS) M E) (P : Party)
    (old new : VP Γ T Sig (Option SS) (Option RS)) (pos : Pos) :
    QB Q (commitE (hooksFS cka prng fs Δcka mo j) s P old new pos) 0 := by
  unfold commitE
  dsimp only [hooksFS]
  refine qb_bind0 (qb_liftH (qb_pure (some new) 0)) fun res => ?_
  cases res with
  | none => exact qb_bind0 qb_abortE fun _ => qb_pure none 0
  | some new' => exact qb_pure _ 0

theorem qb_transmitE [DecidableEq M] [DecidableEq T] [DecidableEq E] [DecidableEq I] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (mo : Mode) (j : ℕ)
    (q : Party × M × Option CCoins) :
    QB Q (transmitE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep mo.policy q) 2 := by
  rcases q with ⟨P, m, r⟩
  unfold transmitE
  refine qb_bind0 qb_get fun es => ?_
  by_cases h1 : (es.abort || es.g.win) = true
  · simp only [h1, ↓reduceIte]
    exact qb_pure none 2
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases es.g.epMgmt (2 + Δcka) qep P r.isSome with
    | none => exact qb_pure none 2
    | some s₁ =>
      dsimp only
      split_ifs
      · exact qb_bind0 qb_abortE fun _ => qb_pure none 2
      · refine qb_bind_r (qb_liftH (qb_vSend hQu cka prng fs Δcka mo j s₁ P (s₁.st P) m none r))
          fun res => ?_
        cases res with
        | none => exact qb_bind0 qb_abortE fun _ => qb_pure none 0
        | some sc => exact qb_bind0 (qb_modify _) fun _ => qb_pure (some sc.2) 0

theorem qb_challE [DecidableEq M] [DecidableEq T] [DecidableEq E] [DecidableEq I] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (mo : Mode) (j : ℕ)
    (q : Party × M × M × Option CCoins) :
    QB Q (challE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep mo.cfg mo.policy q) 2 := by
  rcases q with ⟨P, m₀, m₁, r⟩
  unfold challE
  refine qb_bind0 qb_get fun es => ?_
  by_cases h1 : (es.abort || es.g.win) = true
  · simp only [h1, ↓reduceIte]
    exact qb_pure none 2
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases es.g.epMgmt (2 + Δcka) qep P r.isSome with
    | none => exact qb_pure none 2
    | some s₁ =>
      dsimp only
      by_cases h2 : (!s₁.safeCh (2 + Δcka) P || !(mo.cfg (M := M)).challAllowedIn (s₁.epoch P)) = true
      · simp only [h2, ↓reduceIte]
        exact qb_pure none 2
      · simp only [h2, Bool.false_eq_true, ↓reduceIte]
        by_cases h3 : mo.policy.leakDoom es.g s₁ = true
        · simp only [h3, ↓reduceIte]
          exact qb_bind0 qb_abortE fun _ => qb_pure none 2
        · simp only [h3, Bool.false_eq_true, ↓reduceIte]
          refine qb_bind_r
            (qb_liftH (qb_vSend hQu cka prng fs Δcka mo j s₁ P (s₁.st P) _ (some (m₀, m₁)) r))
            fun res => ?_
          cases res with
          | none => exact qb_bind0 qb_abortE fun _ => qb_pure none 0
          | some sc => exact qb_bind0 (qb_modify _) fun _ => qb_pure (some sc.2) 0

theorem qb_deliverE [DecidableEq M] [DecidableEq T] [DecidableEq E] [DecidableEq I] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (q : Party × (Header T × E)) :
    QB Q (deliverE (hooksFS cka prng fs Δcka mo j) fs.maxSkip mo.cfg q) 2 := by
  rcases q with ⟨P, c⟩
  unfold deliverE
  refine qb_bind0 qb_get fun es => ?_
  by_cases h1 : (es.abort || es.g.win) = true
  · simp only [h1, ↓reduceIte]
    exact qb_pure none 2
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases es.g.inTransit P.other c with
    | none => exact qb_pure none 2
    | some r =>
      dsimp only
      refine qb_bind_r (qb_liftH (qb_vRecv hQu cka prng fs Δcka mo j es.g P (es.g.st P) c (some r)))
        fun res => ?_
      cases res with
      | none => exact qb_bind0 qb_abortE fun _ => qb_pure none 0
      | some inner =>
        cases inner with
        | none =>
          dsimp only
          split_ifs
          · exact qb_bind0 (qb_modify _) fun _ => qb_pure (some RecvResult.rejected) 0
          · exact qb_pure (some RecvResult.rejected) 0
        | some stim =>
          rcases stim with ⟨st', t', i', m'⟩
          dsimp only
          refine qb_bind0 (qb_commitE cka prng fs Δcka mo j es.g P (es.g.st P) st' r.pos)
            fun s₁? => ?_
          cases s₁? with
          | none => exact qb_pure none 0
          | some s₁ => exact qb_bind0 (qb_modify _) fun _ => qb_pure _ 0

theorem qb_injectE [DecidableEq M] [DecidableEq T] [DecidableEq E] [DecidableEq I] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (mo : Mode) (j : ℕ)
    (q : Party × (Header T × E)) :
    QB Q (injectE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep mo.cfg q) 2 := by
  rcases q with ⟨P, c⟩
  unfold injectE
  refine qb_bind0 qb_get fun es => ?_
  dsimp only
  by_cases h1 :
      (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !es.g.safeInj (2 + Δcka)) = true
  · simp only [h1, ↓reduceIte]
    exact qb_pure none 2
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    refine qb_bind_r (qb_liftH (qb_vRecv hQu cka prng fs Δcka mo j es.g P (es.g.st P) c none))
      fun res => ?_
    cases res with
    | none => exact qb_bind0 qb_abortE fun _ => qb_pure none 0
    | some inner =>
      cases inner with
      | none => exact qb_pure (some RecvResult.rejected) 0
      | some stim =>
        rcases stim with ⟨st', t', i', m'⟩
        dsimp only
        by_cases h2 : qep + 1 < t'
        · simp only [h2, ↓reduceIte]
          exact qb_pure (some RecvResult.rejected) 0
        · simp only [h2, ↓reduceIte]
          by_cases h3 : es.g.trivial (2 + Δcka) ⟨P.other, t', i'⟩ = true
          · simp only [h3, ↓reduceIte]
            refine qb_bind0
              (qb_commitE cka prng fs Δcka mo j es.g P (es.g.st P) st' ⟨P.other, t', i'⟩)
              fun s₁? => ?_
            cases s₁? with
            | none => exact qb_pure none 0
            | some s₁ => exact qb_bind0 (qb_modify _) fun _ => qb_pure _ 0
          · simp only [h3, Bool.false_eq_true, ↓reduceIte]
            split_ifs
            · exact qb_bind0 (qb_modify _) fun _ => qb_pure (some RecvResult.rejected) 0
            · exact qb_pure (some RecvResult.rejected) 0

omit hQu in
theorem qb_corrE [DecidableEq M] [DecidableEq T] [DecidableEq E] [DecidableEq I] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (P : Party) :
    QB Q (corrE (hooksFS cka prng fs Δcka mo j) mo.policy P) 2 := by
  unfold corrE
  refine qb_bind0 qb_get fun es => ?_
  dsimp only
  split_ifs
  · exact qb_pure none 2
  · exact qb_bind0 qb_abortE fun _ => qb_pure none 2
  · refine qb_bind_r (qb_liftH (qb_reveal cka prng fs Δcka mo j es.g P (es.g.st P)))
      fun res => ?_
    cases res with
    | none => exact qb_bind0 qb_abortE fun _ => qb_pure none 0
    | some st => exact qb_bind0 (qb_modify _) fun _ => qb_pure (some st) 0

theorem qb_coinsE (n : ℕ) :
    QB Q (coinsE n : EM (FSpec SS RS T M E) Γ T Sig (Option SS) (Option RS) M E
      (FSState T Sig K I SS RS E) (Fin (n + 1))) 0 :=
  qb_stateT_lift ((isQueryBoundP_query_iff Q (.inl n) 0).2 (fun h => absurd h (hQu n)))

theorem qb_implE_inr [DecidableEq M] [DecidableEq T] [DecidableEq E] [DecidableEq I] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (mo : Mode) (j : ℕ)
    (t : (SM.spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain) :
    QB Q (implE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy
      (.inr t)) 2 := by
  rcases t with ((((q | q) | q) | q) | P)
  · exact qb_transmitE hQu cka prng fs Δcka qep mo j q
  · exact qb_challE hQu cka prng fs Δcka qep mo j q
  · exact qb_deliverE hQu cka prng fs Δcka mo j q
  · exact qb_injectE hQu cka prng fs Δcka qep mo j q
  · exact qb_corrE cka prng fs Δcka mo j P

theorem isQueryBoundP_runFS [DecidableEq M] [DecidableEq T] [DecidableEq E] [DecidableEq I]
    [Inhabited E] [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ) (mo : Mode) (j : ℕ)
    (b : Bool) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) {q : ℕ}
    (hq : MakesAtMostQueries A q) :
    IsQueryBoundP (runFS cka prng fs lam Δcka qep mo j b A) Q (2 * q) := by
  unfold runFS engRun
  have hinit : IsQueryBoundP ((initFS cka prng fs lam mo j).run {}) Q 0 :=
    qb_initFS hQu cka prng fs lam mo j {}
  have hsim : ∀ es, IsQueryBoundP
      ((simulateQ (implE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep fs.maxSkip mo.cfg
        mo.policy) A).run es) Q (2 * q) := by
    intro es
    refine simulateQ_run_of_step_mul hq ?_ ?_ es
    · rintro (u | t) ht s
      · simp at ht
      · exact qb_implE_inr hQu cka prng fs Δcka qep mo j t s
    · rintro (u | t) ht s
      · exact qb_coinsE hQu u s
      · simp at ht
  simpa using isQueryBoundP_bind hinit fun ⟨vs, h⟩ _ => by
    cases vs with
    | none => exact isQueryBoundP_pure Q none (2 * q)
    | some vAvB =>
      rcases vAvB with ⟨vA, vB⟩
      simpa using isQueryBoundP_bind (hsim _) fun res _ => isQueryBoundP_pure Q (some res) 0

end HooksFS

theorem isQueryBoundP_congr {ι α : Type} {spec : OracleSpec.{0, 0} ι}
    {oa : OracleComp spec α} {p q : ι → Prop} [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x, p x ↔ q x) {n : ℕ} (h : IsQueryBoundP oa p n) :
    IsQueryBoundP oa q n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure _ => trivial
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h ⊢
    exact ⟨h.1.imp (mt (hpq t).mpr) id, fun u => by
      simpa [hpq t] using ih u (h.2 u)⟩

abbrev QFS (SS RS T M E : Type) : (RSpec SS RS T M E).Domain → Prop :=
  (· matches .inr _)

theorem hQu_QFS (SS RS T M E : Type) : ∀ u : ℕ, ¬ QFS SS RS T M E (.inl u) := by
  intro _ h; nomatch h

section HooksFSDec

variable {Q : (RSpec SS RS T M E).Domain → Prop} [DecidablePred Q]
  (hQu : ∀ u, ¬ Q (.inl u))
  (hQt : ∀ a m, ¬ Q (.inr (.inl (.inl (.inl (.inl (.inl (a, m))))))))
  (hQch : ∀ a m₀ m₁, ¬ Q (.inr (.inl (.inl (.inl (.inl (.inr (a, m₀, m₁))))))))
  (hQcs : ¬ Q (.inr (.inl (.inl (.inl (.inr ()))))))
  (hQcr : ¬ Q (.inr (.inl (.inl (.inr ())))))

theorem qb_liftF_query_zero (t : (RSpec SS RS T M E).Domain) (ht : ¬ Q t) :
    QB Q (liftF (SS := SS) (RS := RS) (T := T) (M := M) (E := E) (Sig := Sig) (K := K) (I := I)
      (query (spec := RSpec SS RS T M E) t)) 0 :=
  qb_stateT_lift ((isQueryBoundP_query_iff Q t 0).2 (fun h => absurd h ht))

include hQt hQch hQcs in
theorem qb_fsSend_zero [DecidableEq T] [DecidableEq E] [DecidableEq I] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (ctx : Ctx Γ T Sig (Option SS) (Option RS) M E) (P : Party) (t : ℕ)
    (ssv : Option SS) (h : Header T) (m : M) (pair : Option (M × M)) :
    QB Q ((hooksFS cka prng fs Δcka mo j).fsSend ctx P t ssv h m pair) 0 := by
  dsimp only [hooksFS]
  cases ssv with
  | some ss => exact qb_pure _ 0
  | none =>
    refine qb_bind0 qb_get fun s => ?_
    cases s.ext with
    | some sr =>
      exact qb_bind0 (qb_set _) fun _ => qb_pure _ 0
    | none =>
      dsimp only
      by_cases hc : (!ctx.safeCh (2 + Δcka) P && !s.fsSCorr) = true
      · simp only [hc, ↓reduceIte]
        refine qb_bind0 (qb_liftF_query_zero _ hQcs) fun r => ?_
        cases r with
        | none =>
          simp only [pure_bind, Bool.not_false, ↓reduceIte]
          exact qb_pure none 0
        | some _ =>
          refine qb_bind0 (qb_modify _) fun _ => ?_
          simp only [pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          rcases pair with _ | ⟨m₀, m₁⟩
          · refine qb_bind0 (qb_liftF_query_zero _ (hQt h m)) fun e? => ?_
            cases e? with
            | none => exact qb_pure none 0
            | some e => exact qb_bind0 (qb_modify _) fun _ => qb_pure _ 0
          · refine qb_bind0 (qb_liftF_query_zero _ (hQch h m₀ m₁)) fun e? => ?_
            cases e? with
            | none => exact qb_pure none 0
            | some e => exact qb_bind0 (qb_modify _) fun _ => qb_pure _ 0
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, pure_bind, Bool.not_true]
        rcases pair with _ | ⟨m₀, m₁⟩
        · refine qb_bind0 (qb_liftF_query_zero _ (hQt h m)) fun e? => ?_
          cases e? with
          | none => exact qb_pure none 0
          | some e => exact qb_bind0 (qb_modify _) fun _ => qb_pure _ 0
        · refine qb_bind0 (qb_liftF_query_zero _ (hQch h m₀ m₁)) fun e? => ?_
          cases e? with
          | none => exact qb_pure none 0
          | some e => exact qb_bind0 (qb_modify _) fun _ => qb_pure _ 0

theorem qb_fsRecv_one [DecidableEq T] [DecidableEq E] [DecidableEq I] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (ctx : Ctx Γ T Sig (Option SS) (Option RS) M E) (P : Party) (t : ℕ)
    (rsv : Option RS) (h : Header T) (e : E) (rec : Option (Record M (Header T × E))) :
    QB Q ((hooksFS cka prng fs Δcka mo j).fsRecv ctx P t rsv h e rec) 1 := by
  dsimp only [hooksFS]
  cases rsv with
  | some rs => exact qb_pure _ 1
  | none =>
    refine qb_bind0 qb_get fun s => ?_
    cases s.ext with
    | some sr =>
      dsimp only
      cases fs.receive sr.2 h e with
      | none => exact qb_pure _ 1
      | some rim => exact qb_bind0 (qb_set _) fun _ => qb_pure _ 1
    | none =>
      dsimp only
      by_cases hm : (s.fsTrans.find? (fun x => x.2 == (h, e))).isSome = true <;>
        (simp only [hm, Bool.false_eq_true, ↓reduceIte]
         refine qb_bind_r (qb_liftF_query _) fun res => ?_
         cases res with
         | none => exact qb_pure none 0
         | some rr =>
           cases rr with
           | rejected => exact qb_pure (some none) 0
           | accepted i mo' =>
             dsimp only
             refine qb_bind0 (qb_modify _) fun _ => ?_
             cases mo' <;> cases rec <;> exact qb_pure _ 0)

include hQcs hQcr in
theorem qb_reveal_zero [DecidableEq T] [DecidableEq E] [DecidableEq I] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (ctx : Ctx Γ T Sig (Option SS) (Option RS) M E) (P : Party)
    (vp : PartyState Γ T Sig (Option SS) (Option RS)) :
    QB Q ((hooksFS cka prng fs Δcka mo j).reveal ctx P vp) 0 := by
  dsimp only [hooksFS]
  cases vp.vS with
  | none =>
    simp only [pure_bind]
    cases vp.vR mo.tStar with
    | none => exact qb_pure _ 0
    | some rsv =>
      cases rsv with
      | some rs => exact qb_pure _ 0
      | none =>
        refine qb_bind0 qb_get fun s => ?_
        cases s.ext with
        | some sr => exact qb_pure _ 0
        | none =>
          split_ifs
          · exact qb_pure none 0
          · refine qb_bind0 (qb_liftF_query_zero _ hQcr) fun r => ?_
            cases r with
            | none => exact qb_pure none 0
            | some sr => exact qb_bind0 (qb_modify _) fun _ => qb_pure _ 0
  | some ssv =>
    cases ssv with
    | some ss =>
      simp only [pure_bind]
      cases vp.vR mo.tStar with
      | none => exact qb_pure _ 0
      | some rsv =>
        cases rsv with
        | some rs => exact qb_pure _ 0
        | none =>
          refine qb_bind0 qb_get fun s => ?_
          cases s.ext with
          | some sr => exact qb_pure _ 0
          | none =>
            split_ifs
            · exact qb_pure none 0
            · refine qb_bind0 (qb_liftF_query_zero _ hQcr) fun r => ?_
              cases r with
              | none => exact qb_pure none 0
              | some sr => exact qb_bind0 (qb_modify _) fun _ => qb_pure _ 0
    | none =>
      refine qb_bind0 qb_get fun s => ?_
      cases s.ext with
      | some sr =>
        simp only [pure_bind]
        cases vp.vR mo.tStar with
        | none => exact qb_pure _ 0
        | some rsv =>
          cases rsv with
          | some rs => exact qb_pure _ 0
          | none =>
            refine qb_bind0 qb_get fun s' => ?_
            cases s'.ext with
            | some sr' => exact qb_pure _ 0
            | none =>
              split_ifs
              · exact qb_pure none 0
              · refine qb_bind0 (qb_liftF_query_zero _ hQcr) fun r => ?_
                cases r with
                | none => exact qb_pure none 0
                | some sr' => exact qb_bind0 (qb_modify _) fun _ => qb_pure _ 0
      | none =>
        refine qb_bind0 (qb_liftF_query_zero _ hQcs) fun r => ?_
        cases r with
        | none =>
          simp only [pure_bind]
          exact qb_pure none 0
        | some ss =>
          refine qb_bind0 (qb_modify _) fun _ => ?_
          simp only [pure_bind]
          cases vp.vR mo.tStar with
          | none => exact qb_pure _ 0
          | some rsv =>
            cases rsv with
            | some rs => exact qb_pure _ 0
            | none =>
              refine qb_bind0 qb_get fun s' => ?_
              cases s'.ext with
              | some sr' => exact qb_pure _ 0
              | none =>
                split_ifs
                · exact qb_pure none 0
                · refine qb_bind0 (qb_liftF_query_zero _ hQcr) fun r' => ?_
                  cases r' with
                  | none => exact qb_pure none 0
                  | some sr' => exact qb_bind0 (qb_modify _) fun _ => qb_pure _ 0

include hQu hQt hQch hQcs in
theorem qb_vSend_zero [DecidableEq T] [DecidableEq E] [DecidableEq I] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (ctx : Ctx Γ T Sig (Option SS) (Option RS) M E) (P : Party)
    (s : VP Γ T Sig (Option SS) (Option RS)) (m : M)
    (pair : Option (M × M)) (r : Option CCoins) :
    QB Q (vSend (hooksFS cka prng fs Δcka mo j) ctx P s m pair r) 0 := by
  unfold vSend
  dsimp only
  split_ifs
  · refine qb_bind0 (qb_startSend hQu cka prng fs Δcka mo j ctx P (s.tcur + 1) s.γ s.root r)
      fun res => ?_
    cases res with
    | none =>
      simp only [pure_bind]
      exact qb_pure none 0
    | some quad =>
      rcases quad with ⟨γ', T', σ', ss⟩
      simp only [pure_bind]
      refine qb_bind0
        (qb_fsSend_zero hQt hQch hQcs cka prng fs Δcka mo j ctx P (s.tcur + 1) ss (s.tcur + 1, some T') m pair)
        fun res' => ?_
      cases res' with
      | none => exact qb_pure none 0
      | some ve => exact qb_pure _ 0
  · simp only [pure_bind]
    cases s.vS with
    | none => exact qb_pure _ 0
    | some v =>
      refine qb_bind0
        (qb_fsSend_zero hQt hQch hQcs cka prng fs Δcka mo j ctx P s.tcur v (s.tcur, s.curCkaMsg) m pair)
        fun res => ?_
      cases res with
      | none => exact qb_pure none 0
      | some ve => exact qb_pure _ 0

include hQu in
theorem qb_vRecv_one [DecidableEq T] [DecidableEq E] [DecidableEq I]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (ctx : Ctx Γ T Sig (Option SS) (Option RS) M E) (P : Party)
    (s : VP Γ T Sig (Option SS) (Option RS))
    (c : Header T × E) (rec : Option (Record M (Header T × E))) :
    QB Q (vRecv (hooksFS cka prng fs Δcka mo j) ctx P s c rec) 1 := by
  unfold vRecv
  dsimp only
  by_cases h1 : (s.id.sendsIn c.1.1 || decide (s.tcur + 1 < c.1.1)) = true
  · simp only [h1, ↓reduceIte]
    exact qb_pure (some none) 1
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : c.1.1 = s.tcur + 1
    · rw [ite_eq_left h2]
      cases c.1.2 with
      | none =>
        simp only [pure_bind]
        exact qb_pure (some none) 1
      | some Tn =>
        dsimp only
        refine qb_bind0 (qb_startRecv hQu cka prng fs Δcka mo j ctx P c.1.1 s.γ s.root Tn)
          fun res => ?_
        cases res with
        | none =>
          simp only [pure_bind]
          exact qb_pure none 1
        | some inner =>
          cases inner with
          | none =>
            simp only [pure_bind]
            exact qb_pure (some none) 1
          | some triple =>
            rcases triple with ⟨γ', σ', rs⟩
            simp only [pure_bind, Function.update_self]
            refine qb_bind_r
              (qb_fsRecv_one cka prng fs Δcka mo j ctx P c.1.1 rs c.1 c.2 rec)
              fun res' => ?_
            cases res' with
            | none => exact qb_pure none 0
            | some inner' =>
              cases inner' with
              | none => exact qb_pure (some none) 0
              | some vim => exact qb_pure _ 0
    · simp only [h2, ↓reduceIte, pure_bind]
      cases s.vR c.1.1 with
      | none => exact qb_pure (some none) 1
      | some v =>
        refine qb_bind_r
          (qb_fsRecv_one cka prng fs Δcka mo j ctx P c.1.1 v c.1 c.2 rec)
          fun res => ?_
        cases res with
        | none => exact qb_pure none 0
        | some inner' =>
          cases inner' with
          | none => exact qb_pure (some none) 0
          | some vim => exact qb_pure _ 0

include hQu hQt hQch hQcs in
theorem qb_transmitE_zero [DecidableEq M] [DecidableEq T] [DecidableEq E] [DecidableEq I] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (mo : Mode) (j : ℕ)
    (q : Party × M × Option CCoins) :
    QB Q (transmitE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep mo.policy q) 0 := by
  rcases q with ⟨P, m, r⟩
  unfold transmitE
  refine qb_bind0 qb_get fun es => ?_
  by_cases h1 : (es.abort || es.g.win) = true
  · simp only [h1, ↓reduceIte]
    exact qb_pure none 0
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases es.g.epMgmt (2 + Δcka) qep P r.isSome with
    | none => exact qb_pure none 0
    | some s₁ =>
      dsimp only
      split_ifs
      · exact qb_bind0 qb_abortE fun _ => qb_pure none 0
      · refine qb_bind0 (qb_liftH (qb_vSend_zero hQu hQt hQch hQcs cka prng fs Δcka mo j s₁ P (s₁.st P) m none r))
          fun res => ?_
        cases res with
        | none => exact qb_bind0 qb_abortE fun _ => qb_pure none 0
        | some sc => exact qb_bind0 (qb_modify _) fun _ => qb_pure (some sc.2) 0

include hQu hQt hQch hQcs in
theorem qb_challE_zero [DecidableEq M] [DecidableEq T] [DecidableEq E] [DecidableEq I] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (mo : Mode) (j : ℕ)
    (q : Party × M × M × Option CCoins) :
    QB Q (challE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep mo.cfg mo.policy q) 0 := by
  rcases q with ⟨P, m₀, m₁, r⟩
  unfold challE
  refine qb_bind0 qb_get fun es => ?_
  by_cases h1 : (es.abort || es.g.win) = true
  · simp only [h1, ↓reduceIte]
    exact qb_pure none 0
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases es.g.epMgmt (2 + Δcka) qep P r.isSome with
    | none => exact qb_pure none 0
    | some s₁ =>
      dsimp only
      by_cases h2 : (!s₁.safeCh (2 + Δcka) P || !(mo.cfg (M := M)).challAllowedIn (s₁.epoch P)) = true
      · simp only [h2, ↓reduceIte]
        exact qb_pure none 0
      · simp only [h2, Bool.false_eq_true, ↓reduceIte]
        by_cases h3 : mo.policy.leakDoom es.g s₁ = true
        · simp only [h3, ↓reduceIte]
          exact qb_bind0 qb_abortE fun _ => qb_pure none 0
        · simp only [h3, Bool.false_eq_true, ↓reduceIte]
          refine qb_bind0
            (qb_liftH (qb_vSend_zero hQu hQt hQch hQcs cka prng fs Δcka mo j s₁ P (s₁.st P) _ (some (m₀, m₁)) r))
            fun res => ?_
          cases res with
          | none => exact qb_bind0 qb_abortE fun _ => qb_pure none 0
          | some sc => exact qb_bind0 (qb_modify _) fun _ => qb_pure (some sc.2) 0

include hQu in
theorem qb_deliverE_one [DecidableEq M] [DecidableEq T] [DecidableEq E] [DecidableEq I] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (q : Party × (Header T × E)) :
    QB Q (deliverE (hooksFS cka prng fs Δcka mo j) fs.maxSkip mo.cfg q) 1 := by
  rcases q with ⟨P, c⟩
  unfold deliverE
  refine qb_bind0 qb_get fun es => ?_
  by_cases h1 : (es.abort || es.g.win) = true
  · simp only [h1, ↓reduceIte]
    exact qb_pure none 1
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases es.g.inTransit P.other c with
    | none => exact qb_pure none 1
    | some r =>
      dsimp only
      refine qb_bind_r (qb_liftH (qb_vRecv_one hQu cka prng fs Δcka mo j es.g P (es.g.st P) c (some r)))
        fun res => ?_
      cases res with
      | none => exact qb_bind0 qb_abortE fun _ => qb_pure none 0
      | some inner =>
        cases inner with
        | none =>
          dsimp only
          split_ifs
          · exact qb_bind0 (qb_modify _) fun _ => qb_pure (some RecvResult.rejected) 0
          · exact qb_pure (some RecvResult.rejected) 0
        | some stim =>
          rcases stim with ⟨st', t', i', m'⟩
          dsimp only
          refine qb_bind0 (qb_commitE cka prng fs Δcka mo j es.g P (es.g.st P) st' r.pos)
            fun s₁? => ?_
          cases s₁? with
          | none => exact qb_pure none 0
          | some s₁ => exact qb_bind0 (qb_modify _) fun _ => qb_pure _ 0

include hQu in
theorem qb_injectE_one [DecidableEq M] [DecidableEq T] [DecidableEq E] [DecidableEq I] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (mo : Mode) (j : ℕ)
    (q : Party × (Header T × E)) :
    QB Q (injectE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep mo.cfg q) 1 := by
  rcases q with ⟨P, c⟩
  unfold injectE
  refine qb_bind0 qb_get fun es => ?_
  dsimp only
  by_cases h1 :
      (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !es.g.safeInj (2 + Δcka)) = true
  · simp only [h1, ↓reduceIte]
    exact qb_pure none 1
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    refine qb_bind_r (qb_liftH (qb_vRecv_one hQu cka prng fs Δcka mo j es.g P (es.g.st P) c none))
      fun res => ?_
    cases res with
    | none => exact qb_bind0 qb_abortE fun _ => qb_pure none 0
    | some inner =>
      cases inner with
      | none => exact qb_pure (some RecvResult.rejected) 0
      | some stim =>
        rcases stim with ⟨st', t', i', m'⟩
        dsimp only
        by_cases h2 : qep + 1 < t'
        · simp only [h2, ↓reduceIte]
          exact qb_pure (some RecvResult.rejected) 0
        · simp only [h2, ↓reduceIte]
          by_cases h3 : es.g.trivial (2 + Δcka) ⟨P.other, t', i'⟩ = true
          · simp only [h3, ↓reduceIte]
            refine qb_bind0
              (qb_commitE cka prng fs Δcka mo j es.g P (es.g.st P) st' ⟨P.other, t', i'⟩)
              fun s₁? => ?_
            cases s₁? with
            | none => exact qb_pure none 0
            | some s₁ => exact qb_bind0 (qb_modify _) fun _ => qb_pure _ 0
          · simp only [h3, Bool.false_eq_true, ↓reduceIte]
            split_ifs
            · exact qb_bind0 (qb_modify _) fun _ => qb_pure (some RecvResult.rejected) 0
            · exact qb_pure (some RecvResult.rejected) 0

include hQcs hQcr in
theorem qb_corrE_zero [DecidableEq M] [DecidableEq T] [DecidableEq E] [DecidableEq I] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (P : Party) :
    QB Q (corrE (hooksFS cka prng fs Δcka mo j) mo.policy P) 0 := by
  unfold corrE
  refine qb_bind0 qb_get fun es => ?_
  dsimp only
  split_ifs
  · exact qb_pure none 0
  · exact qb_bind0 qb_abortE fun _ => qb_pure none 0
  · refine qb_bind0 (qb_liftH (qb_reveal_zero hQcs hQcr cka prng fs Δcka mo j es.g P (es.g.st P)))
      fun res => ?_
    cases res with
    | none => exact qb_bind0 qb_abortE fun _ => qb_pure none 0
    | some st => exact qb_bind0 (qb_modify _) fun _ => qb_pure (some st) 0

include hQu hQt hQch hQcs hQcr in
theorem qb_implE_inr_one [DecidableEq M] [DecidableEq T] [DecidableEq E] [DecidableEq I] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (mo : Mode) (j : ℕ)
    (t : (SM.spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain) :
    QB Q (implE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy
      (.inr t)) 1 := by
  rcases t with ((((q | q) | q) | q) | P)
  · exact qb_mono (qb_transmitE_zero hQu hQt hQch hQcs cka prng fs Δcka qep mo j q) (by omega)
  · exact qb_mono (qb_challE_zero hQu hQt hQch hQcs cka prng fs Δcka qep mo j q) (by omega)
  · exact qb_deliverE_one hQu cka prng fs Δcka mo j q
  · exact qb_injectE_one hQu cka prng fs Δcka qep mo j q
  · exact qb_mono (qb_corrE_zero hQcs hQcr cka prng fs Δcka mo j P) (by omega)

include hQu hQt hQch hQcs hQcr in
theorem isQueryBoundP_runFS_dec [DecidableEq M] [DecidableEq T] [DecidableEq E] [DecidableEq I]
    [Inhabited E] [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ) (mo : Mode) (j : ℕ)
    (b : Bool) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) {q : ℕ}
    (hq : MakesAtMostQueries A q) :
    IsQueryBoundP (runFS cka prng fs lam Δcka qep mo j b A) Q q := by
  unfold runFS engRun
  have hinit : IsQueryBoundP ((initFS cka prng fs lam mo j).run {}) Q 0 :=
    qb_initFS hQu cka prng fs lam mo j {}
  have hsim : ∀ es, IsQueryBoundP
      ((simulateQ (implE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep fs.maxSkip mo.cfg
        mo.policy) A).run es) Q q := by
    intro es
    simpa only [Nat.one_mul] using
      (simulateQ_run_of_step_mul (k := 1) hq
        (fun t ht s => by
          rcases t with u | t
          · simp at ht
          · exact qb_implE_inr_one hQu hQt hQch hQcs hQcr cka prng fs Δcka qep mo j t s)
        (fun t ht s => by
          rcases t with u | t
          · exact qb_coinsE hQu u s
          · simp at ht)
        es)
  simpa using isQueryBoundP_bind hinit fun ⟨vs, h⟩ _ => by
    cases vs with
    | none => exact isQueryBoundP_pure Q none q
    | some vAvB =>
      rcases vAvB with ⟨vA, vB⟩
      simpa using isQueryBoundP_bind (hsim _) fun res _ => isQueryBoundP_pure Q (some res) 0

end HooksFSDec

abbrev QFSDec (SS RS T M E : Type) : (RSpec SS RS T M E).Domain → Prop :=
  fun t => FSAEAD.isDecQuery (SS := SS) (RS := RS) (AD := Header T) (Msg := M) (C := E) t = true

theorem hQu_QFSDec (SS RS T M E : Type) : ∀ u : ℕ, ¬ QFSDec SS RS T M E (.inl u) := by
  intro _ h; nomatch h

theorem hQt_QFSDec (SS RS T M E : Type) :
    ∀ a m, ¬ QFSDec SS RS T M E (.inr (.inl (.inl (.inl (.inl (.inl (a, m))))))) := by
  intro _ _ h; nomatch h

theorem hQch_QFSDec (SS RS T M E : Type) :
    ∀ a m₀ m₁, ¬ QFSDec SS RS T M E (.inr (.inl (.inl (.inl (.inl (.inr (a, m₀, m₁))))))) := by
  intro _ _ _ h; nomatch h

theorem hQcs_QFSDec (SS RS T M E : Type) :
    ¬ QFSDec SS RS T M E (.inr (.inl (.inl (.inl (.inr ()))))) := by
  intro h; nomatch h

theorem hQcr_QFSDec (SS RS T M E : Type) :
    ¬ QFSDec SS RS T M E (.inr (.inl (.inl (.inr ())))) := by
  intro h; nomatch h

end ReductionsQueries

open ReductionsQueries

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]
  (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)

/-- If `A` makes at most `q` SM oracle queries, `redFSAuth j tL t A` makes at most `2 * q`
FS-AEAD oracle queries. -/
theorem redFSAuth_queries (j : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) {q : ℕ} (hq : MakesAtMostQueries A q) :
    FSAEAD.MakesAtMostQueries (redFSAuth cka prng fs lam Δcka qep j tL t A) (2 * q) := by
  unfold FSAEAD.MakesAtMostQueries redFSAuth
  refine isQueryBoundP_congr (p := QFS SS RS T M E) (by rintro (_ | _) <;> rfl) ?_
  rw [← Nat.add_zero (2 * q)]
  exact isQueryBoundP_bind
    (isQueryBoundP_runFS (hQu_QFS SS RS T M E) cka prng fs lam Δcka qep ⟨true, tL, t⟩ j false A hq)
    fun _ _ => isQueryBoundP_sampleT (hQu_QFS SS RS T M E) Bool

/-- If `A` makes at most `q` SM oracle queries, `redFSPriv tL t A` makes at most `2 * q`
FS-AEAD oracle queries. -/
theorem redFSPriv_queries (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) {q : ℕ} (hq : MakesAtMostQueries A q) :
    FSAEAD.MakesAtMostQueries (redFSPriv cka prng fs lam Δcka qep tL t A) (2 * q) := by
  unfold FSAEAD.MakesAtMostQueries redFSPriv
  refine isQueryBoundP_congr (p := QFS SS RS T M E) (by rintro (_ | _) <;> rfl) ?_
  rw [← Nat.add_zero (2 * q)]
  refine isQueryBoundP_bind
    (isQueryBoundP_runFS (hQu_QFS SS RS T M E) cka prng fs lam Δcka qep ⟨false, tL, t⟩ 0 false A hq)
    fun r _ => ?_
  cases r with
  | none => exact isQueryBoundP_sampleT (hQu_QFS SS RS T M E) Bool
  | some p =>
    dsimp only
    split_ifs
    · exact isQueryBoundP_pure (QFS SS RS T M E) p.1 0
    · exact isQueryBoundP_sampleT (hQu_QFS SS RS T M E) Bool

/-- If `A` makes at most `q` SM oracle queries, `redFSPrivCoin tL t A` makes at most `2 * q`
FS-AEAD oracle queries. -/
theorem redFSPrivCoin_queries (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) {q : ℕ} (hq : MakesAtMostQueries A q) :
    FSAEAD.MakesAtMostQueries (redFSPrivCoin cka prng fs lam Δcka qep tL t A) (2 * q) := by
  unfold FSAEAD.MakesAtMostQueries redFSPrivCoin
  refine isQueryBoundP_congr (p := QFS SS RS T M E) (by rintro (_ | _) <;> rfl) ?_
  rw [← Nat.add_zero (2 * q)]
  exact isQueryBoundP_bind
    (isQueryBoundP_runFS (hQu_QFS SS RS T M E) cka prng fs lam Δcka qep ⟨false, tL, t⟩ 0 false A hq)
    fun _ _ => isQueryBoundP_sampleT (hQu_QFS SS RS T M E) Bool

/-- If `A` makes at most `q` SM oracle queries, `redFSAuth j tL t A` makes at most `q`
FS-AEAD decryption (`deliver` or `inject`) queries. -/
theorem redFSAuth_dec_queries (j : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) {q : ℕ} (hq : MakesAtMostQueries A q) :
    FSAEAD.MakesAtMostDecQueries (redFSAuth cka prng fs lam Δcka qep j tL t A) q := by
  unfold FSAEAD.MakesAtMostDecQueries redFSAuth
  rw [← Nat.add_zero q]
  exact isQueryBoundP_bind
    (isQueryBoundP_runFS_dec (hQu_QFSDec SS RS T M E) (hQt_QFSDec SS RS T M E)
      (hQch_QFSDec SS RS T M E) (hQcs_QFSDec SS RS T M E) (hQcr_QFSDec SS RS T M E)
      cka prng fs lam Δcka qep ⟨true, tL, t⟩ j false A hq)
    fun _ _ => isQueryBoundP_sampleT (hQu_QFSDec SS RS T M E) Bool

/-- If `A` makes at most `q` SM oracle queries, `redFSPriv tL t A` makes at most `q`
FS-AEAD decryption (`deliver` or `inject`) queries. -/
theorem redFSPriv_dec_queries (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) {q : ℕ} (hq : MakesAtMostQueries A q) :
    FSAEAD.MakesAtMostDecQueries (redFSPriv cka prng fs lam Δcka qep tL t A) q := by
  unfold FSAEAD.MakesAtMostDecQueries redFSPriv
  rw [← Nat.add_zero q]
  refine isQueryBoundP_bind
    (isQueryBoundP_runFS_dec (hQu_QFSDec SS RS T M E) (hQt_QFSDec SS RS T M E)
      (hQch_QFSDec SS RS T M E) (hQcs_QFSDec SS RS T M E) (hQcr_QFSDec SS RS T M E)
      cka prng fs lam Δcka qep ⟨false, tL, t⟩ 0 false A hq)
    fun r _ => ?_
  cases r with
  | none => exact isQueryBoundP_sampleT (hQu_QFSDec SS RS T M E) Bool
  | some p =>
    dsimp only
    split_ifs
    · exact isQueryBoundP_pure (QFSDec SS RS T M E) p.1 0
    · exact isQueryBoundP_sampleT (hQu_QFSDec SS RS T M E) Bool

/-- If `A` makes at most `q` SM oracle queries, `redFSPrivCoin tL t A` makes at most `q`
FS-AEAD decryption (`deliver` or `inject`) queries. -/
theorem redFSPrivCoin_dec_queries (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) {q : ℕ} (hq : MakesAtMostQueries A q) :
    FSAEAD.MakesAtMostDecQueries (redFSPrivCoin cka prng fs lam Δcka qep tL t A) q := by
  unfold FSAEAD.MakesAtMostDecQueries redFSPrivCoin
  rw [← Nat.add_zero q]
  exact isQueryBoundP_bind
    (isQueryBoundP_runFS_dec (hQu_QFSDec SS RS T M E) (hQt_QFSDec SS RS T M E)
      (hQch_QFSDec SS RS T M E) (hQcs_QFSDec SS RS T M E) (hQcr_QFSDec SS RS T M E)
      cka prng fs lam Δcka qep ⟨false, tL, t⟩ 0 false A hq)
    fun _ _ => isQueryBoundP_sampleT (hQu_QFSDec SS RS T M E) Bool

end CryptoGames.SM.Construction

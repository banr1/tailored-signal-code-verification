/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionsAuthHmac
import Computational.Proofs.SignalPqxdh.Security.SigHopA

/-!
# PQXDH authentication: query bounds of `prfHmacOfMu`

Proves that `prfHmacOfMu B` makes at most `B.q_dec + 1` `PrfHmac` oracle queries and at most
`B.q_prim + B.q_enc + B.q_dec` primitive queries whenever `B` is bounded.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ENNReal BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh
open RoKem

/-! ## Runner -/

/-- `prfHmacOfMuRunAt` generalized to an arbitrary computation and initial state. -/
def prfMuRun (j : ℕ) {α : Type} (mx : OracleComp AeadMuIntSimSpec α) (st : PrfHmacMuState) :
    OracleComp PrfHmacSimSpec (α × PrfHmacMuState) :=
  OracleComp.construct
    (C := fun _ => PrfHmacMuState → OracleComp PrfHmacSimSpec (α × PrfHmacMuState))
    (fun a s => pure (a, s))
    (fun q _ r s =>
      match q with
      | Sum.inl pq => do
        let u ← liftM (OracleSpec.query (spec := PrfHmacSimSpec) (Sum.inl pq))
        r u s
      | Sum.inr mq => do
        let p ← prfHmacMuStep j mq s
        r p.1 p.2)
    mx st

theorem construct_congr_step {ι : Type} {spec : OracleSpec ι} {α : Type}
    {C : OracleComp spec α → Type _} (pu : (a : α) → C (pure a))
    (f g : (q : spec.Domain) → (oa : spec.Range q → OracleComp spec α) →
      ((u : spec.Range q) → C (oa u)) → C (liftM (OracleSpec.query q) >>= oa))
    (h : f = g) (mx : OracleComp spec α) :
    OracleComp.construct (C := C) pu f mx = OracleComp.construct (C := C) pu g mx := by
  subst h; rfl

theorem prfHmacOfMuRunAt_eq (j : ℕ) (B : AeadMuIntCtxtAdv) :
    prfHmacOfMuRunAt j B = prfMuRun j B.run {} := by
  unfold prfHmacOfMuRunAt prfMuRun
  refine congrFun (construct_congr_step _ _ _ ?_ _) _
  funext q x r s
  rcases q with pq | mq <;> rfl

@[simp] theorem prfMuRun_pure (j : ℕ) {α : Type} (a : α) (st : PrfHmacMuState) :
    prfMuRun j (pure a : OracleComp AeadMuIntSimSpec α) st = pure (a, st) := rfl

theorem prfMuRun_query_inl (j : ℕ) {α : Type} (pq : ℕ ⊕ PrimQuery)
    (mx : AeadMuIntSimSpec.Range (Sum.inl pq) → OracleComp AeadMuIntSimSpec α)
    (st : PrfHmacMuState) :
    prfMuRun j (liftM (OracleSpec.query (spec := AeadMuIntSimSpec) (Sum.inl pq)) >>= mx) st =
      (liftM (OracleSpec.query (spec := PrfHmacSimSpec) (Sum.inl pq)) >>= fun u =>
        prfMuRun j (mx u) st) := rfl

theorem prfMuRun_query_inr (j : ℕ) {α : Type} (mq : AeadMuIntQuery)
    (mx : AeadMuIntSimSpec.Range (Sum.inr mq) → OracleComp AeadMuIntSimSpec α)
    (st : PrfHmacMuState) :
    prfMuRun j (liftM (OracleSpec.query (spec := AeadMuIntSimSpec) (Sum.inr mq)) >>= mx) st =
      (prfHmacMuStep j mq st >>= fun p => prfMuRun j (mx p.1) p.2) := rfl

/-! ## Basic query bounds -/

abbrev isPrfQ : ((ℕ ⊕ PrimQuery) ⊕ PrfHmacQuery) → Prop := fun q => q.isRight = true

abbrev isPrimQ : ((ℕ ⊕ PrimQuery) ⊕ PrfHmacQuery) → Prop := fun q => isPrimQuery q = true

theorem prfHmacUnif_prf {α : Type} (mx : ProbComp α) (n : ℕ) :
    IsQueryBoundP (prfHmacUnif mx) isPrfQ n :=
  isQueryBoundP_embedPrim_isRight _ n

theorem prfHmacUnif_prim {α : Type} (mx : ProbComp α) (n : ℕ) :
    IsQueryBoundP (prfHmacUnif mx) isPrimQ n :=
  isQueryBoundP_embedPrim_isPrimQuery _ n (primBounded_embedUnif mx n)

theorem prfHmacPrimQ_prf (op : PrimQuery) (n : ℕ) :
    IsQueryBoundP (prfHmacPrimQ op) isPrfQ n :=
  isQueryBoundP_embedPrim_isRight _ n

theorem prfHmacPrimQ_prim (op : PrimQuery) :
    IsQueryBoundP (prfHmacPrimQ op) isPrimQ 1 :=
  isQueryBoundP_embedPrim_isPrimQuery _ 1 (primBounded_primQ op)

theorem prfHmacEvalQ_prf (m : Bytes) :
    IsQueryBoundP (prfHmacEvalQ m) isPrfQ 1 :=
  (isQueryBoundP_query_iff (spec := PrfHmacSimSpec) isPrfQ (Sum.inr (.eval m)) 1).2
    (fun _ => Nat.zero_lt_one)

theorem prfHmacEvalQ_prim (m : Bytes) (n : ℕ) :
    IsQueryBoundP (prfHmacEvalQ m) isPrimQ n :=
  (isQueryBoundP_query_iff (spec := PrfHmacSimSpec) isPrimQ (Sum.inr (.eval m)) n).2
    (fun h => by cases h)

theorem prfHmacTagQ_prim (j r : ℕ) (x : Bytes) (n : ℕ) :
    IsQueryBoundP (prfHmacTagQ j r x) isPrimQ n := by
  unfold prfHmacTagQ
  split
  · exact prfHmacUnif_prim _ n
  · exact prfHmacEvalQ_prim x n

theorem prfHmacTagQ_prf (j r : ℕ) (x : Bytes) :
    IsQueryBoundP (prfHmacTagQ j r x) isPrfQ (if r < j then 0 else 1) := by
  unfold prfHmacTagQ
  split
  · exact prfHmacUnif_prf _ _
  · exact prfHmacEvalQ_prf x

/-! ## Primitive query bound -/

theorem prfHmacMuKey_prim (i : ℕ) (st : PrfHmacMuState) (n : ℕ) :
    IsQueryBoundP (prfHmacMuKey i st) isPrimQ n := by
  unfold prfHmacMuKey
  split
  · exact isQueryBoundP_pure _ _ _
  · exact (isQueryBoundP_bind (prfHmacUnif_prim _ n) (fun _ _ => isQueryBoundP_pure _ _ 0)).mono
      (by omega)

theorem prfHmacMuKey_prf (i : ℕ) (st : PrfHmacMuState) (n : ℕ) :
    IsQueryBoundP (prfHmacMuKey i st) isPrfQ n := by
  unfold prfHmacMuKey
  split
  · exact isQueryBoundP_pure _ _ _
  · exact (isQueryBoundP_bind (prfHmacUnif_prf _ n) (fun _ _ => isQueryBoundP_pure _ _ 0)).mono
      (by omega)

theorem prfHmacMuStep_prim (j : ℕ) (q : AeadMuIntQuery) (st : PrfHmacMuState) :
    IsQueryBoundP (prfHmacMuStep j q st) isPrimQ 1 := by
  rcases q with ⟨i, ad, pt⟩ | ⟨i, ad, ct⟩
  · simp only [prfHmacMuStep]
    split
    · exact isQueryBoundP_pure _ _ _
    · refine (isQueryBoundP_bind (m := 1) (prfHmacMuKey_prim i st 0) (fun p _ => ?_)).mono (by omega)
      refine (isQueryBoundP_bind (m := 0) (prfHmacPrimQ_prim _) (fun ct _ => ?_)).mono (by omega)
      split
      · exact (isQueryBoundP_bind (prfHmacTagQ_prim j _ _ 0)
          (fun _ _ => isQueryBoundP_pure _ _ 0)).mono (by omega)
      · exact isQueryBoundP_pure _ _ _
  · simp only [prfHmacMuStep]
    split
    · exact isQueryBoundP_pure _ _ _
    · refine (isQueryBoundP_bind (m := 1) (prfHmacMuKey_prim i st 0) (fun p _ => ?_)).mono (by omega)
      repeat' split
      all_goals first
        | exact isQueryBoundP_pure _ _ _
        | exact (isQueryBoundP_bind (m := 0) (prfHmacPrimQ_prim _)
            (fun _ _ => isQueryBoundP_pure _ _ 0)).mono (by omega)

theorem prfMuRun_prim (j : ℕ) {α : Type} (mx : OracleComp AeadMuIntSimSpec α) (P E D : ℕ)
    (hP : IsQueryBoundP mx (fun q => isPrimQuery q = true) P)
    (hE : IsQueryBoundP mx isMuEncQuery E) (hD : IsQueryBoundP mx isMuForgeQuery D)
    (st : PrfHmacMuState) :
    IsQueryBoundP (prfMuRun j mx st) isPrimQ (P + E + D) := by
  induction mx using OracleComp.inductionOn generalizing P E D st with
  | pure x => exact isQueryBoundP_pure _ _ _
  | query_bind q mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hP hE hD
    rcases q with pq | mq
    · rw [prfMuRun_query_inl, isQueryBoundP_query_bind_iff]
      have hE' : ¬ isMuEncQuery (Sum.inl pq) := fun h => by cases h
      have hD' : ¬ isMuForgeQuery (Sum.inl pq) := fun h => by cases h
      simp only [hE', hD', ↓reduceIte] at hE hD
      rcases pq with n | op
      · simp only [isPrimQ, isPrimQuery, Bool.false_eq_true, ↓reduceIte, not_false_eq_true,
          true_or, true_and] at hP ⊢
        exact fun u => ih u _ _ _ (hP u) (hE.2 u) (hD.2 u) st
      · simp only [isPrimQ, isPrimQuery, ↓reduceIte, not_true_eq_false, false_or] at hP ⊢
        exact ⟨by omega, fun u => (ih u _ _ _ (hP.2 u) (hE.2 u) (hD.2 u) st).mono (by omega)⟩
    · rw [prfMuRun_query_inr]
      have hP' : ¬ (isPrimQuery (Sum.inr mq : (ℕ ⊕ PrimQuery) ⊕ AeadMuIntQuery) = true) := by
        simp [isPrimQuery]
      simp only [isPrimQuery, Bool.false_eq_true, ↓reduceIte] at hP
      rcases mq with ⟨i, ad, pt⟩ | ⟨i, ad, ct⟩
      · have hEq : isMuEncQuery (Sum.inr (.encOnce i ad pt)) := trivial
        have hDq : ¬ isMuForgeQuery (Sum.inr (.encOnce i ad pt)) := fun h => by cases h
        simp only [hEq, hDq, ↓reduceIte] at hE hD
        have hEpos : 0 < E := by rcases hE.1 with h | h; exact absurd hEq h; exact h
        exact (isQueryBoundP_bind (prfHmacMuStep_prim j _ st)
          (fun p _ => ih p.1 _ _ _ (hP.2 p.1) (hE.2 p.1) (hD.2 p.1) p.2)).mono (by omega)
      · have hEq : ¬ isMuEncQuery (Sum.inr (.tryForge i ad ct)) := fun h => by cases h
        have hDq : isMuForgeQuery (Sum.inr (.tryForge i ad ct)) := trivial
        simp only [hEq, hDq, ↓reduceIte] at hE hD
        have hDpos : 0 < D := by rcases hD.1 with h | h; exact absurd hDq h; exact h
        exact (isQueryBoundP_bind (prfHmacMuStep_prim j _ st)
          (fun p _ => ih p.1 _ _ _ (hP.2 p.1) (hE.2 p.1) (hD.2 p.1) p.2)).mono (by omega)

theorem prfHmacFinish_prim (j : ℕ) (pending : List (ℕ × Bytes × Bytes)) (pts : List (ℕ × Bytes))
    (n : ℕ) : IsQueryBoundP (prfHmacFinish j pending pts) isPrimQ n := by
  induction pts generalizing n with
  | nil => exact isQueryBoundP_pure _ _ _
  | cons p pts ih =>
    obtain ⟨r, x⟩ := p
    simp only [prfHmacFinish]
    exact (isQueryBoundP_bind (prfHmacTagQ_prim j r x 0) (fun _ _ =>
      (isQueryBoundP_bind (ih n) (fun _ _ => isQueryBoundP_pure _ _ 0)).mono le_rfl)).mono
      (by omega)

theorem prfHmacOfMu_prim (B : AeadMuIntCtxtAdv) (hB : B.Bounded) :
    IsQueryBoundP (prfHmacOfMu B).run isPrimQ (prfHmacOfMu B).q_prim := by
  show IsQueryBoundP (prfHmacOfMuRun B) isPrimQ (B.q_prim + B.q_enc + B.q_dec)
  unfold prfHmacOfMuRun
  refine (isQueryBoundP_bind (m := B.q_prim + B.q_enc + B.q_dec) (prfHmacUnif_prim _ 0)
    (fun j _ => ?_)).mono (by omega)
  rw [prfHmacOfMuRunAt_eq]
  refine (isQueryBoundP_bind (m := 0) (prfMuRun_prim j B.run B.q_prim B.q_enc B.q_dec hB.2.2 hB.1 hB.2.1 {})
    (fun p _ => ?_)).mono (by omega)
  exact (isQueryBoundP_bind (m := 0) (prfHmacFinish_prim j _ _ 0)
    (fun _ _ => isQueryBoundP_pure _ _ 0)).mono (by omega)

/-! ## Oracle query bound -/

def prfUnchL (j : ℕ) (keys : List (ℕ × (ℕ × MessageKeys))) (chal : List (ℕ × (Bytes × Bytes))) :
    ℕ :=
  keys.countP (fun e => e.2.1 == j && (chal.lookup e.1).isNone)

/-- Potential bounding the remaining `PrfHmac` oracle queries beyond remaining forgeries. -/
def prfPot (j : ℕ) (st : PrfHmacMuState) : ℕ :=
  prfUnchL j st.keys st.chal + (if st.keys.length ≤ j then 1 else 0) + st.pending.length

theorem prf_lookup_mem {β : Type} : ∀ (l : List (ℕ × β)) (i : ℕ) (e : β),
    l.lookup i = some e → (i, e) ∈ l
  | [], _, _, h => by simp at h
  | (k, b) :: l, i, e, h => by
    by_cases hk : i = k
    · subst hk
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self
    · have hb : (i == k) = false := by simpa using hk
      simp only [List.lookup, hb] at h
      exact List.mem_cons_of_mem _ (prf_lookup_mem l i e h)

theorem prf_countP_lt {γ : Type} (p q : γ → Bool) : ∀ (l : List γ) (y : γ), y ∈ l →
    (∀ x ∈ l, p x = true → q x = true) → p y = false → q y = true →
    l.countP p + 1 ≤ l.countP q
  | [], _, h, _, _, _ => by simp at h
  | x :: l, y, hy, himp, hpy, hqy => by
    have hl : l.countP p ≤ l.countP q :=
      List.countP_mono_left (fun z hz => himp z (List.mem_cons_of_mem _ hz))
    simp only [List.countP_cons]
    rcases List.mem_cons.1 hy with rfl | hy'
    · simp only [hpy, hqy, Bool.false_eq_true, ↓reduceIte]; omega
    · have := prf_countP_lt p q l y hy' (fun z hz => himp z (List.mem_cons_of_mem _ hz)) hpy hqy
      have hx := himp x List.mem_cons_self
      split <;> split <;> simp_all

theorem prfUnch_chal_cons (j : ℕ) (keys : List (ℕ × (ℕ × MessageKeys)))
    (chal : List (ℕ × (Bytes × Bytes))) (i r : ℕ) (mk : MessageKeys) (c : Bytes × Bytes)
    (hi : (i, (r, mk)) ∈ keys) (hnone : chal.lookup i = none) :
    prfUnchL j keys ((i, c) :: chal) + (if r = j then 1 else 0) ≤ prfUnchL j keys chal := by
  unfold prfUnchL
  have himp : ∀ e ∈ keys,
      (e.2.1 == j && (((i, c) :: chal).lookup e.1).isNone) = true →
      (e.2.1 == j && (chal.lookup e.1).isNone) = true := by
    intro e _ he
    by_cases hei : e.1 = i
    · simp [List.lookup, hei] at he
    · have hb : (e.1 == i) = false := by simpa using hei
      simpa [List.lookup, hb] using he
  split
  · rename_i hrj
    refine prf_countP_lt _ _ keys (i, (r, mk)) hi himp ?_ ?_
    · simp [List.lookup]
    · simp [hrj, hnone]
  · simpa using List.countP_mono_left himp

theorem prfHmacMuKey_support (j i : ℕ) (st : PrfHmacMuState)
    (p : (ℕ × MessageKeys) × PrfHmacMuState) (hp : p ∈ support (prfHmacMuKey i st)) :
    (i, p.1) ∈ p.2.keys ∧ p.2.chal = st.chal ∧ p.2.pending = st.pending ∧ p.2.bad = st.bad ∧
      prfPot j p.2 ≤ prfPot j st := by
  unfold prfHmacMuKey at hp
  split at hp
  · rename_i e he
    simp only [support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨prf_lookup_mem _ _ _ he, rfl, rfl, rfl, le_rfl⟩
  · rename_i hnone
    simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hp
    obtain ⟨mk, _, rfl⟩ := hp
    refine ⟨List.mem_cons_self, rfl, rfl, rfl, ?_⟩
    unfold prfPot prfUnchL
    simp only [List.countP_cons, List.length_cons]
    rcases Nat.lt_trichotomy st.keys.length j with h | h | h
    · have h1 : (st.keys.length == j) = false := by simpa using h.ne
      simp only [h1, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      split <;> split <;> omega
    · subst h
      simp only [beq_self_eq_true, Bool.true_and, le_refl, ↓reduceIte, Nat.not_succ_le_self]
      split <;> omega
    · have h1 : (st.keys.length == j) = false := by simpa using h.ne'
      simp only [h1, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      split <;> split <;> omega

theorem prfHmacMuStep_enc_prf (j i : ℕ) (ad pt : Bytes) (st : PrfHmacMuState) {β : Type}
    (g : aeadMuIntSpec.Range (.encOnce i ad pt) × PrfHmacMuState → OracleComp PrfHmacSimSpec β)
    (n : ℕ) (hg : ∀ p, IsQueryBoundP (g p) isPrfQ (n + prfPot j p.2)) :
    IsQueryBoundP (prfHmacMuStep j (.encOnce i ad pt) st >>= g) isPrfQ (n + prfPot j st) := by
  simp only [prfHmacMuStep]
  split
  · rw [pure_bind]; exact hg _
  · rename_i hnone
    rw [bind_assoc]
    refine (isQueryBoundP_bind (m := n + prfPot j st) (prfHmacMuKey_prf i st 0)
      (fun p hp => ?_)).mono (by omega)
    obtain ⟨hmem, hc, hpend, -, hpot⟩ := prfHmacMuKey_support j i st p hp
    obtain ⟨⟨r, mk⟩, st'⟩ := p
    simp only at hmem hc hpend hpot ⊢
    rw [bind_assoc]
    refine (isQueryBoundP_bind (m := n + prfPot j st) (prfHmacPrimQ_prf _ 0)
      (fun ct _ => ?_)).mono (by omega)
    have hnone' : st'.chal.lookup i = none := by rw [hc]; exact hnone
    unfold prfPot at hpot
    split
    · rename_i hrj
      rw [bind_assoc]
      refine (isQueryBoundP_bind (m := n + prfPot j st - (if r < j then 0 else 1))
        (prfHmacTagQ_prf j r _) (fun t _ => ?_)).mono ?_
      · rw [pure_bind]
        refine (hg _).mono ?_
        have hU := prfUnch_chal_cons j st'.keys st'.chal i r mk (ad, etmBody ct ++ t.take 8)
          hmem hnone'
        have hF := List.length_filter_le
          (fun e : ℕ × Bytes × Bytes => !(e.1 == r && e.2.1 == aeadMacInput ad (etmBody ct)))
          st'.pending
        unfold prfPot
        simp only at hU ⊢
        split_ifs at * <;> omega
      · have hU := prfUnch_chal_cons j st'.keys st'.chal i r mk (ad, ct) hmem hnone'
        unfold prfPot
        split_ifs at * <;> omega
    · rename_i hrj
      rw [pure_bind]
      refine (hg _).mono ?_
      have hU := prfUnch_chal_cons j st'.keys st'.chal i r mk (ad, ct) hmem hnone'
      unfold prfPot
      simp only at hU ⊢
      split_ifs at * <;> omega

theorem prfHmacMuStep_forge_prf (j i : ℕ) (ad ct : Bytes) (st : PrfHmacMuState) {β : Type}
    (g : aeadMuIntSpec.Range (.tryForge i ad ct) × PrfHmacMuState → OracleComp PrfHmacSimSpec β)
    (n : ℕ) (hg : ∀ p, IsQueryBoundP (g p) isPrfQ (n + prfPot j p.2)) :
    IsQueryBoundP (prfHmacMuStep j (.tryForge i ad ct) st >>= g) isPrfQ
      (n + (prfPot j st + 1)) := by
  simp only [prfHmacMuStep]
  split
  · rw [pure_bind]; exact (hg _).mono (by dsimp only; omega)
  · rw [bind_assoc]
    refine (isQueryBoundP_bind (m := n + (prfPot j st + 1)) (prfHmacMuKey_prf i st 0)
      (fun p hp => ?_)).mono (by omega)
    obtain ⟨-, -, -, -, hpot⟩ := prfHmacMuKey_support j i st p hp
    obtain ⟨⟨r, mk⟩, st'⟩ := p
    simp only at hpot ⊢
    unfold prfPot at hpot
    repeat' split
    all_goals first
      | (rw [pure_bind]; refine (hg _).mono ?_; unfold prfPot
         simp only [List.length_cons]; omega)
      | (rw [bind_assoc]
         refine (isQueryBoundP_bind (m := n + (prfPot j st + 1)) (prfHmacPrimQ_prf _ 0)
           (fun res _ => ?_)).mono (by omega)
         rw [pure_bind]; refine (hg _).mono ?_; unfold prfPot; simp only; omega)

theorem prfMuRun_prf (j : ℕ) {α : Type} (mx : OracleComp AeadMuIntSimSpec α) (D : ℕ)
    (hD : IsQueryBoundP mx isMuForgeQuery D) (st : PrfHmacMuState) {β : Type}
    (g : α × PrfHmacMuState → OracleComp PrfHmacSimSpec β) (n : ℕ)
    (hg : ∀ p, IsQueryBoundP (g p) isPrfQ (n + prfPot j p.2)) :
    IsQueryBoundP (prfMuRun j mx st >>= g) isPrfQ (n + D + prfPot j st) := by
  induction mx using OracleComp.inductionOn generalizing D st with
  | pure x => rw [prfMuRun_pure, pure_bind]; exact (hg _).mono (by dsimp only; omega)
  | query_bind q mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hD
    rcases q with pq | mq
    · rw [prfMuRun_query_inl, bind_assoc, isQueryBoundP_query_bind_iff]
      have hD' : ¬ isMuForgeQuery (Sum.inl pq) := fun h => by cases h
      simp only [hD', ↓reduceIte] at hD
      refine ⟨Or.inl (by simp [isPrfQ]), fun u => ?_⟩
      simpa [isPrfQ] using ih u D (hD.2 u) st
    · rw [prfMuRun_query_inr, bind_assoc]
      rcases mq with ⟨i, ad, pt⟩ | ⟨i, ad, ct⟩
      · have hDq : ¬ isMuForgeQuery (Sum.inr (.encOnce i ad pt)) := fun h => by cases h
        simp only [hDq, ↓reduceIte] at hD
        exact prfHmacMuStep_enc_prf j i ad pt st _ (n + D)
          (fun p => ih p.1 D (hD.2 p.1) p.2)
      · have hDq : isMuForgeQuery (Sum.inr (.tryForge i ad ct)) := trivial
        simp only [hDq, ↓reduceIte] at hD
        have hDpos : 0 < D := by rcases hD.1 with h | h; exact absurd hDq h; exact h
        exact (prfHmacMuStep_forge_prf j i ad ct st _ (n + (D - 1))
          (fun p => ih p.1 (D - 1) (hD.2 p.1) p.2)).mono (by omega)

theorem prfHmacFinish_prf (j : ℕ) (pending : List (ℕ × Bytes × Bytes)) (pts : List (ℕ × Bytes)) :
    IsQueryBoundP (prfHmacFinish j pending pts) isPrfQ pts.length := by
  induction pts with
  | nil => exact isQueryBoundP_pure _ _ _
  | cons p pts ih =>
    obtain ⟨r, x⟩ := p
    simp only [prfHmacFinish, List.length_cons]
    refine (isQueryBoundP_bind (m := pts.length) ((prfHmacTagQ_prf j r x).mono
      (n := if r < j then 0 else 1) (m := 1) (by split <;> omega)) (fun _ _ =>
      (isQueryBoundP_bind (m := 0) ih (fun _ _ => isQueryBoundP_pure _ _ 0)).mono le_rfl)).mono
      (by omega)

theorem prfHmacOfMu_prf (B : AeadMuIntCtxtAdv) (hB : B.Bounded) :
    IsQueryBoundP (prfHmacOfMu B).run isPrfQ (prfHmacOfMu B).q_prf := by
  show IsQueryBoundP (prfHmacOfMuRun B) isPrfQ (B.q_dec + 1)
  unfold prfHmacOfMuRun
  refine (isQueryBoundP_bind (m := B.q_dec + 1) (prfHmacUnif_prf _ 0)
    (fun j _ => ?_)).mono (by omega)
  rw [prfHmacOfMuRunAt_eq]
  refine (prfMuRun_prf j B.run B.q_dec hB.2.1 {} _ 0 (fun p => ?_)).mono ?_
  · obtain ⟨_, st⟩ := p
    simp only
    refine (isQueryBoundP_bind (m := 0) (prfHmacFinish_prf j _ _)
      (fun _ _ => isQueryBoundP_pure _ _ 0)).mono ?_
    have h1 := ((st.pending.map (fun e => (e.1, e.2.1))).dedup_sublist).length_le
    simp only [List.length_map] at h1
    unfold prfPot
    omega
  · simp [prfPot, prfUnchL]

/-- Query bounds for `prfHmacOfMu B`. -/
theorem prfHmacOfMu_bounded (B : AeadMuIntCtxtAdv) (hB : B.Bounded) : (prfHmacOfMu B).Bounded :=
  ⟨prfHmacOfMu_prf B hB, prfHmacOfMu_prim B hB⟩

end SignalPqxdh.Security

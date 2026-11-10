/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthPrfHmacD
import Computational.Proofs.SignalPqxdh.Security.SigHopA
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

/-!
# PQXDH authentication: hybrid (C), the lazy random function at the target rank

In the ideal world the `PrfHmac` oracle is a lazily sampled random function. Every oracle query of
the hybrid at the target rank `j` is at a point not yet in the random-function cache, so it is a
fresh uniform sample, exactly like `unifTag`.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ENNReal BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh
open RoKem

/-! ## Couplings -/

theorem lookup_cons_nat {β : Type} (a k : ℕ) (b : β) (l : List (ℕ × β)) :
    ((k, b) :: l).lookup a = if a = k then some b else l.lookup a := by
  by_cases h : a = k
  · simp [h]
  · have h' : (a == k) = false := by simpa using h
    simp [List.lookup_cons, h, h']

def Cpl {α β : Type} (R : α → β → Prop) (mx : ProbComp α) (my : ProbComp β) : Prop :=
  ∀ (FL : α → ProbComp Bool) (FR : β → ProbComp Bool),
    (∀ a b, R a b → 𝒟[FL a] = 𝒟[FR b]) → 𝒟[mx >>= FL] = 𝒟[my >>= FR]

theorem Cpl_pure {α β : Type} {R : α → β → Prop} {a : α} {b : β} (h : R a b) :
    Cpl R (pure a) (pure b) := by
  intro FL FR hF
  simpa using hF a b h

theorem Cpl_bind {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}
    {mx : ProbComp α} {my : ProbComp β} {f : α → ProbComp γ} {g : β → ProbComp δ}
    (h : Cpl R mx my) (hfg : ∀ a b, R a b → Cpl S (f a) (g b)) :
    Cpl S (mx >>= f) (my >>= g) := by
  intro FL FR hF
  rw [bind_assoc, bind_assoc]
  exact h (fun a => f a >>= FL) (fun b => g b >>= FR) (fun a b hab => hfg a b hab FL FR hF)

theorem Cpl_same {α β γ : Type} {R : β → γ → Prop} (mx : ProbComp α)
    {f : α → ProbComp β} {g : α → ProbComp γ}
    (h : ∀ a ∈ support mx, Cpl R (f a) (g a)) : Cpl R (mx >>= f) (mx >>= g) := by
  intro FL FR hF
  rw [bind_assoc, bind_assoc]
  exact OracleComp.evalDist_bind_congr_of_support _ _ _ (fun a ha => h a ha FL FR hF)

theorem Cpl_simulateQ {ι : Type} {spec : OracleSpec.{0, 0} ι} {σ₁ σ₂ α : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ ProbComp)) (impl₂ : QueryImpl spec (StateT σ₂ ProbComp))
    (I : σ₁ → σ₂ → Prop)
    (himpl : ∀ (t : ι) (s₁ : σ₁) (s₂ : σ₂), I s₁ s₂ →
      Cpl (fun p q => p.1 = q.1 ∧ I p.2 q.2) ((impl₁ t).run s₁) ((impl₂ t).run s₂))
    (mx : OracleComp spec α) :
    ∀ (s₁ : σ₁) (s₂ : σ₂), I s₁ s₂ →
      Cpl (fun p q => p.1 = q.1 ∧ I p.2 q.2)
        ((simulateQ impl₁ mx).run s₁) ((simulateQ impl₂ mx).run s₂) := by
  induction mx using OracleComp.inductionOn with
  | pure a =>
    intro s₁ s₂ hs
    simp only [simulateQ_pure, StateT.run_pure]
    exact Cpl_pure ⟨rfl, hs⟩
  | query_bind t mx ih =>
    intro s₁ s₂ hs
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    refine Cpl_bind (himpl t s₁ s₂ hs) ?_
    rintro ⟨u₁, s₁'⟩ ⟨u₂, s₂'⟩ ⟨h1, h2⟩
    simp only at h1 h2
    subst h1
    exact ih u₁ s₁' s₂' h2


/-! ## Basic simulation lemmas -/

section Basic

variable (P : Primitives) {σ : Type} (ev : QueryImpl prfHmacSpec (StateT σ ProbComp))

theorem gFull_unif_run {α : Type} (mx : ProbComp α) (c : σ) :
    (simulateQ (gFull P ev) (prfHmacUnif mx)).run c = (fun a => (a, c)) <$> mx := by
  unfold prfHmacUnif gFull
  rw [simulateQ_embedPrim_run, simulateQ_embedUnif]

theorem gFull_primQ_run (op : PrimQuery) (c : σ) :
    (simulateQ (gFull P ev) (prfHmacPrimQ op)).run c = (fun a => (a, c)) <$> primImpl P op := by
  unfold prfHmacPrimQ gFull
  rw [simulateQ_embedPrim_run, simulateQ_primQ]

theorem gFull_evalQ_run (x : Bytes) (c : σ) :
    (simulateQ (gFull P ev) (prfHmacEvalQ x)).run c = (ev (.eval x)).run c := by
  unfold prfHmacEvalQ gFull
  simp

end Basic

theorem length_of_mem_support_sampleBytes32' {bs : Bytes}
    (h : bs ∈ support sampleBytes32) : bs.length = 32 := by
  unfold sampleBytes32 at h
  simp only [support_map, Set.mem_image] at h
  rcases h with ⟨w, _, rfl⟩
  simp [word256ToBytes]

theorem prfEval_false_fresh_run (P : Primitives) (k x : Bytes) (c : List (Bytes × Bytes))
    (hx : x ∉ c.map Prod.fst) :
    (prfEvalImpl P false k (.eval x)).run c = (fun t => (t, (x, t) :: c)) <$> sampleBytes32 := by
  have hf : c.find? (fun (m, _) => m == x) = none := by
    rw [List.find?_eq_none]
    intro p hp
    have : p.1 ≠ x := fun h => hx (List.mem_map.2 ⟨p, hp, h⟩)
    simpa using this
  simp [prfEvalImpl, hf]


/-! ## The invariant -/

/-- Invariant of the left run (random-function cache `c`) at target rank `j`. -/
structure HCInv (j : ℕ) (st : PrfHmacMuState) (c : List (Bytes × Bytes)) : Prop where
  rank_lt : ∀ i e, st.keys.lookup i = some e → e.1 < st.keys.length
  rank_inj : ∀ i i' e e', st.keys.lookup i = some e → st.keys.lookup i' = some e' →
    e.1 = e'.1 → i = i'
  cache : ∀ x ∈ c.map Prod.fst, ∃ i e ad ct, st.keys.lookup i = some e ∧ e.1 = j ∧
    st.chal.lookup i = some (ad, ct) ∧ x = aeadMacInput ad (etmBody ct)
  pend : ∀ e ∈ st.pending, e.1 ≤ j ∧ (e.1 = j → e.2.1 ∉ c.map Prod.fst)

theorem HCInv_init (j : ℕ) : HCInv j {} [] where
  rank_lt := by simp
  rank_inj := by simp
  cache := by simp
  pend := by simp

noncomputable def muKeyP (i : ℕ) (st : PrfHmacMuState) :
    ProbComp ((ℕ × MessageKeys) × PrfHmacMuState) :=
  match st.keys.lookup i with
  | some e => pure (e, st)
  | none => (fun mk => ((st.keys.length, mk),
      { st with keys := (i, (st.keys.length, mk)) :: st.keys })) <$> sampleMessageKeys80

theorem muKey_run (P : Primitives) {σ : Type} (ev : QueryImpl prfHmacSpec (StateT σ ProbComp))
    (i : ℕ) (st : PrfHmacMuState) (c : σ) :
    (simulateQ (gFull P ev) (prfHmacMuKey i st)).run c = (fun p => (p, c)) <$> muKeyP i st := by
  unfold prfHmacMuKey muKeyP
  cases h : st.keys.lookup i with
  | none => simp [gFull_unif_run]
  | some e => simp

theorem muKeyP_spec {j i : ℕ} {st : PrfHmacMuState} {c : List (Bytes × Bytes)}
    (hI : HCInv j st c) {p : (ℕ × MessageKeys) × PrfHmacMuState}
    (hp : p ∈ support (muKeyP i st)) :
    p.2.chal = st.chal ∧ p.2.pending = st.pending ∧ p.2.bad = st.bad ∧
      p.2.keys.lookup i = some p.1 ∧ HCInv j p.2 c := by
  unfold muKeyP at hp
  cases h : st.keys.lookup i with
  | some e =>
    rw [h] at hp
    simp only [support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨rfl, rfl, rfl, h, hI⟩
  | none =>
    rw [h] at hp
    simp only [support_map, Set.mem_image] at hp
    obtain ⟨mk, _, rfl⟩ := hp
    have hlook : ∀ i', ((i, (st.keys.length, mk)) :: st.keys).lookup i' =
        if i' = i then some (st.keys.length, mk) else st.keys.lookup i' :=
      fun i' => lookup_cons_nat _ _ _ _
    refine ⟨rfl, rfl, rfl, by simp [hlook], ?_⟩
    refine ⟨?_, ?_, ?_, hI.pend⟩
    · intro i' e he
      dsimp only at he ⊢
      rw [hlook] at he
      simp only [List.length_cons]
      by_cases hi : i' = i
      · rw [ite_eq_left hi] at he
        obtain rfl := Option.some.inj he
        simp
      · rw [ite_eq_right hi] at he
        have := hI.rank_lt i' e he
        omega
    · intro i1 i2 e1 e2 h1 h2 heq
      dsimp only at h1 h2
      rw [hlook] at h1 h2
      by_cases hi1 : i1 = i <;> by_cases hi2 : i2 = i
      · rw [hi1, hi2]
      · rw [ite_eq_left hi1] at h1
        rw [ite_eq_right hi2] at h2
        obtain rfl := Option.some.inj h1
        have := hI.rank_lt i2 e2 h2
        simp only at heq
        omega
      · rw [ite_eq_right hi1] at h1
        rw [ite_eq_left hi2] at h2
        obtain rfl := Option.some.inj h2
        have := hI.rank_lt i1 e1 h1
        simp only at heq
        omega
      · rw [ite_eq_right hi1] at h1
        rw [ite_eq_right hi2] at h2
        exact hI.rank_inj i1 i2 e1 e2 h1 h2 heq
    · intro x hx
      obtain ⟨i0, e, ad, ct, hk, he, hc, hx⟩ := hI.cache x hx
      refine ⟨i0, e, ad, ct, ?_, he, hc, hx⟩
      dsimp only
      rw [hlook, ite_eq_right]
      · exact hk
      · rintro rfl
        rw [h] at hk
        cases hk


/-! ## Invariant preservation -/

theorem HCInv_addChal {j : ℕ} {st : PrfHmacMuState} {c : List (Bytes × Bytes)} (hI : HCInv j st c)
    {i : ℕ} (hn : st.chal.lookup i = none) (v : Bytes × Bytes)
    (pend : List (ℕ × Bytes × Bytes)) (hpend : ∀ e ∈ pend, e ∈ st.pending) (b : Bool) :
    HCInv j { st with chal := (i, v) :: st.chal, pending := pend, bad := b } c where
  rank_lt := hI.rank_lt
  rank_inj := hI.rank_inj
  cache := by
    intro x hx
    obtain ⟨i0, e, ad, ct, hk, he, hc, hx⟩ := hI.cache x hx
    refine ⟨i0, e, ad, ct, hk, he, ?_, hx⟩
    dsimp only
    rw [lookup_cons_nat, ite_eq_right]
    · exact hc
    · rintro rfl
      rw [hn] at hc
      cases hc
  pend := fun e he => hI.pend e (hpend e he)

theorem HCInv_setPend {j : ℕ} {st : PrfHmacMuState} {c : List (Bytes × Bytes)} (hI : HCInv j st c)
    (pend : List (ℕ × Bytes × Bytes))
    (hpend : ∀ e ∈ pend, e.1 ≤ j ∧ (e.1 = j → e.2.1 ∉ c.map Prod.fst)) (b : Bool) :
    HCInv j { st with pending := pend, bad := b } c where
  rank_lt := hI.rank_lt
  rank_inj := hI.rank_inj
  cache := hI.cache
  pend := hpend

theorem HCInv_fresh {j : ℕ} {st : PrfHmacMuState} {c : List (Bytes × Bytes)} (hI : HCInv j st c)
    {i : ℕ} {e : ℕ × MessageKeys} (hk : st.keys.lookup i = some e) (he : e.1 = j)
    (hn : st.chal.lookup i = none) (x : Bytes) : x ∉ c.map Prod.fst := by
  intro hx
  obtain ⟨i0, e0, ad0, ct0, hk0, he0, hc0, _⟩ := hI.cache x hx
  have := hI.rank_inj i0 i e0 e hk0 hk (he0.trans he.symm)
  subst this
  rw [hn] at hc0
  cases hc0

def freshB (st : PrfHmacMuState) (i : ℕ) (x : Bytes) : Bool :=
  match st.chal.lookup i with
  | some (ad0, ct0) => x != aeadMacInput ad0 (etmBody ct0)
  | none => true

theorem HCInv_forge_fresh {j : ℕ} {st : PrfHmacMuState} {c : List (Bytes × Bytes)}
    (hI : HCInv j st c) {i : ℕ} {e : ℕ × MessageKeys} (hk : st.keys.lookup i = some e)
    (he : e.1 = j) {x : Bytes} (hfr : freshB st i x = true) : x ∉ c.map Prod.fst := by
  intro hx
  obtain ⟨i0, e0, ad0, ct0, hk0, he0, hc0, hx0⟩ := hI.cache x hx
  have := hI.rank_inj i0 i e0 e hk0 hk (he0.trans he.symm)
  subst this
  unfold freshB at hfr
  rw [hc0] at hfr
  simp [hx0] at hfr

theorem etmBody_append_take (b t : Bytes) (ht : 8 ≤ t.length) :
    etmBody (b ++ t.take 8) = b := by
  have h8 : (t.take 8).length = 8 := by simp; omega
  unfold etmBody
  simp [h8]

theorem HCInv_encEq {j : ℕ} {st : PrfHmacMuState} {c : List (Bytes × Bytes)} (hI : HCInv j st c)
    {i : ℕ} {e : ℕ × MessageKeys} (hk : st.keys.lookup i = some e) (he : e.1 = j)
    (hn : st.chal.lookup i = none) (ad ct t : Bytes) (ht : t.length = 32) (b : Bool) :
    HCInv j { st with
      chal := (i, (ad, etmBody ct ++ t.take 8)) :: st.chal
      pending := st.pending.filter
        (fun e' => !(e'.1 == e.1 && e'.2.1 == aeadMacInput ad (etmBody ct)))
      bad := b } ((aeadMacInput ad (etmBody ct), t) :: c) where
  rank_lt := hI.rank_lt
  rank_inj := hI.rank_inj
  cache := by
    intro x hx
    simp only [List.map_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · refine ⟨i, e, ad, etmBody ct ++ t.take 8, hk, he, ?_, ?_⟩
      · simp
      · rw [etmBody_append_take _ _ (by omega)]
    · obtain ⟨i0, e0, ad0, ct0, hk0, he0, hc0, hx0⟩ := hI.cache x hx
      refine ⟨i0, e0, ad0, ct0, hk0, he0, ?_, hx0⟩
      dsimp only
      rw [lookup_cons_nat, ite_eq_right]
      · exact hc0
      · rintro rfl
        rw [hn] at hc0
        cases hc0
  pend := by
    intro e' he'
    simp only [List.mem_filter] at he'
    obtain ⟨he', hf⟩ := he'
    refine ⟨(hI.pend e' he').1, fun hj => ?_⟩
    simp only [List.map_cons, List.mem_cons, not_or]
    refine ⟨?_, (hI.pend e' he').2 hj⟩
    intro hx
    rw [hj, he, hx] at hf
    simp at hf


/-! ## One step of `gStep` -/

def encK (D : ℕ → Prop) [DecidablePred D] (tag : ℕ → Bytes → OracleComp PrfHmacSimSpec Bytes)
    (i : ℕ) (ad : Bytes) (p : (ℕ × MessageKeys) × PrfHmacMuState) (ct : Bytes) :
    OracleComp PrfHmacSimSpec (Option Bytes × PrfHmacMuState) :=
  if D p.1.1 then do
    let x0 := aeadMacInput ad (etmBody ct)
    let t ← tag p.1.1 x0
    let ct' := etmBody ct ++ t.take 8
    pure (some ct',
      { p.2 with
        chal := (i, (ad, ct')) :: p.2.chal
        pending := p.2.pending.filter (fun e => !(e.1 == p.1.1 && e.2.1 == x0))
        bad := p.2.bad || prfHmacPendingHit p.2.pending p.1.1 x0 t })
  else
    pure (some ct, { p.2 with chal := (i, (ad, ct)) :: p.2.chal })

theorem gStep_enc_none (D : ℕ → Prop) [DecidablePred D]
    (tag : ℕ → Bytes → OracleComp PrfHmacSimSpec Bytes) (i : ℕ) (ad pt : Bytes)
    (st : PrfHmacMuState) (hn : st.chal.lookup i = none) :
    gStep D tag (.encOnce i ad pt) st =
      (prfHmacMuKey i st >>= fun p => prfHmacPrimQ (.aeadEnc p.1.2 ad pt) >>= fun ct =>
        encK D tag i ad p ct) := by
  simp only [gStep, hn]
  rfl

theorem gStep_enc_some (D : ℕ → Prop) [DecidablePred D]
    (tag : ℕ → Bytes → OracleComp PrfHmacSimSpec Bytes) (i : ℕ) (ad pt : Bytes)
    (st : PrfHmacMuState) (v : Bytes × Bytes) (hv : st.chal.lookup i = some v) :
    gStep D tag (.encOnce i ad pt) st = pure (none, st) := by
  simp only [gStep, hv]

def forgeK (D : ℕ → Prop) [DecidablePred D] (i : ℕ) (ad ct : Bytes)
    (p : (ℕ × MessageKeys) × PrfHmacMuState) :
    OracleComp PrfHmacSimSpec (Bool × PrfHmacMuState) :=
  if freshB p.2 i (aeadMacInput ad (etmBody ct)) = true ∧ 24 ≤ ct.length then
    if D p.1.1 then
      pure (false, { p.2 with pending := (p.1.1, aeadMacInput ad (etmBody ct), etmTag ct) ::
        p.2.pending })
    else do
      let res ← prfHmacPrimQ (.aeadDec p.1.2 ad ct)
      pure (false, { p.2 with bad := p.2.bad || res.isSome })
  else pure (false, p.2)

theorem gStep_forge (D : ℕ → Prop) [DecidablePred D]
    (tag : ℕ → Bytes → OracleComp PrfHmacSimSpec Bytes) (i : ℕ) (ad ct : Bytes)
    (st : PrfHmacMuState) (hne : ¬ (st.chal.lookup i == some (ad, ct)) = true) :
    gStep D tag (.tryForge i ad ct) st = (prfHmacMuKey i st >>= forgeK D i ad ct) := by
  simp only [gStep, hne]
  rfl

theorem gStep_forge_eq (D : ℕ → Prop) [DecidablePred D]
    (tag : ℕ → Bytes → OracleComp PrfHmacSimSpec Bytes) (i : ℕ) (ad ct : Bytes)
    (st : PrfHmacMuState) (he : (st.chal.lookup i == some (ad, ct)) = true) :
    gStep D tag (.tryForge i ad ct) st = pure (false, st) := by
  simp only [gStep, he]
  rfl


/-! ## Per-step coupling -/

def StepR (j : ℕ) {α : Type} (p : (α × PrfHmacMuState) × List (Bytes × Bytes))
    (q : (α × PrfHmacMuState) × List (Bytes × Bytes)) : Prop :=
  p.1 = q.1 ∧ HCInv j p.1.2 p.2

theorem prfFullImpl_false (P : Primitives) (k : Bytes) :
    prfFullImpl P false k = gFull P (prfEvalImpl P false k) := rfl

section Step

variable (P : Primitives) (k : Bytes) (j : ℕ)

local notation "EvL" => prfEvalImpl P false k

theorem step_encK {i : ℕ} {ad : Bytes} {p : (ℕ × MessageKeys) × PrfHmacMuState}
    {c₁ c₂ : List (Bytes × Bytes)} (hI : HCInv j p.2 c₁) (hk : p.2.keys.lookup i = some p.1)
    (hn : p.2.chal.lookup i = none) (ct : Bytes) :
    Cpl (StepR j)
      ((simulateQ (gFull P EvL) (encK (fun r => r ≤ j) (prfHmacTagQ j) i ad p ct)).run c₁)
      ((simulateQ (gFull P EvL) (encK (fun r => r ≤ j) unifTag i ad p ct)).run c₂) := by
  unfold encK
  by_cases hD : p.1.1 ≤ j
  · rw [ite_eq_left hD, ite_eq_left hD]
    by_cases hlt : p.1.1 < j
    · simp only [prfHmacTagQ, ite_eq_left hlt, unifTag, simulateQ_bind, simulateQ_pure,
        StateT.run_bind, gFull_unif_run, map_eq_bind_pure_comp, bind_assoc, Function.comp,
        pure_bind, StateT.run_pure]
      refine Cpl_same _ (fun t _ => Cpl_pure ⟨rfl, ?_⟩)
      refine HCInv_addChal hI hn _ _ (fun e he => (List.mem_filter.1 he).1) _
    · have hj : p.1.1 = j := by omega
      have hfr := HCInv_fresh hI hk hj hn (aeadMacInput ad (etmBody ct))
      simp only [prfHmacTagQ, ite_eq_right hlt, unifTag, simulateQ_bind, simulateQ_pure,
        StateT.run_bind, gFull_unif_run, gFull_evalQ_run, prfEval_false_fresh_run P k _ _ hfr,
        map_eq_bind_pure_comp, bind_assoc, Function.comp, pure_bind, StateT.run_pure]
      refine Cpl_same _ (fun t ht => Cpl_pure ⟨rfl, ?_⟩)
      exact HCInv_encEq hI hk hj hn ad ct t (length_of_mem_support_sampleBytes32' ht) _
  · rw [ite_eq_right hD, ite_eq_right hD]
    simp only [simulateQ_pure, StateT.run_pure]
    exact Cpl_pure ⟨rfl, HCInv_addChal hI hn _ _ (fun e he => he) _⟩

theorem step_enc (i : ℕ) (ad pt : Bytes) (st : PrfHmacMuState) {c₁ c₂ : List (Bytes × Bytes)}
    (hI : HCInv j st c₁) :
    Cpl (StepR j)
      ((simulateQ (gFull P EvL) (gStep (fun r => r ≤ j) (prfHmacTagQ j) (.encOnce i ad pt) st)).run c₁)
      ((simulateQ (gFull P EvL) (gStep (fun r => r ≤ j) unifTag (.encOnce i ad pt) st)).run c₂) := by
  cases hc : st.chal.lookup i with
  | some v =>
    rw [gStep_enc_some _ _ _ _ _ _ v hc, gStep_enc_some _ _ _ _ _ _ v hc]
    simp only [simulateQ_pure, StateT.run_pure]
    exact Cpl_pure ⟨rfl, hI⟩
  | none =>
    rw [gStep_enc_none _ _ _ _ _ _ hc, gStep_enc_none _ _ _ _ _ _ hc]
    simp only [simulateQ_bind, StateT.run_bind, muKey_run, bind_map_left]
    refine Cpl_same _ (fun p hp => ?_)
    obtain ⟨hch, -, -, hk, hI'⟩ := muKeyP_spec hI hp
    rw [gFull_primQ_run, gFull_primQ_run, bind_map_left, bind_map_left]
    refine Cpl_same _ (fun ct _ => ?_)
    exact step_encK P k j hI' hk (hch.symm ▸ hc) ct

theorem step_forge (i : ℕ) (ad ct : Bytes) (st : PrfHmacMuState) {c₁ c₂ : List (Bytes × Bytes)}
    (hI : HCInv j st c₁) :
    Cpl (StepR j)
      ((simulateQ (gFull P EvL) (gStep (fun r => r ≤ j) (prfHmacTagQ j) (.tryForge i ad ct) st)).run c₁)
      ((simulateQ (gFull P EvL) (gStep (fun r => r ≤ j) unifTag (.tryForge i ad ct) st)).run c₂) := by
  by_cases he : (st.chal.lookup i == some (ad, ct)) = true
  · rw [gStep_forge_eq _ _ _ _ _ _ he, gStep_forge_eq _ _ _ _ _ _ he]
    simp only [simulateQ_pure, StateT.run_pure]
    exact Cpl_pure ⟨rfl, hI⟩
  · rw [gStep_forge _ _ _ _ _ _ he, gStep_forge _ _ _ _ _ _ he]
    simp only [simulateQ_bind, StateT.run_bind, muKey_run, bind_map_left]
    refine Cpl_same _ (fun p hp => ?_)
    obtain ⟨-, -, -, hk, hI'⟩ := muKeyP_spec hI hp
    unfold forgeK
    by_cases hf : freshB p.2 i (aeadMacInput ad (etmBody ct)) = true ∧ 24 ≤ ct.length
    · rw [ite_eq_left hf]
      by_cases hD : p.1.1 ≤ j
      · rw [ite_eq_left hD]
        simp only [simulateQ_pure, StateT.run_pure]
        refine Cpl_pure ⟨rfl, HCInv_setPend hI' _ ?_ _⟩
        intro e he'
        simp only [List.mem_cons] at he'
        rcases he' with rfl | he'
        · exact ⟨hD, fun hj => HCInv_forge_fresh hI' hk hj hf.1⟩
        · exact hI'.pend e he'
      · rw [ite_eq_right hD]
        simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
        rw [gFull_primQ_run, gFull_primQ_run, bind_map_left, bind_map_left]
        exact Cpl_same _ (fun _ _ => Cpl_pure ⟨rfl, HCInv_setPend hI' _ hI'.pend _⟩)
    · rw [ite_eq_right hf]
      simp only [simulateQ_pure, StateT.run_pure]
      exact Cpl_pure ⟨rfl, hI'⟩

end Step


/-! ## Whole run, deferred checks, and the hybrid equality -/

theorem Cpl_map {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}
    {mx : ProbComp α} {my : ProbComp β} {f : α → γ} {g : β → δ}
    (h : Cpl R mx my) (hfg : ∀ a b, R a b → S (f a) (g b)) : Cpl S (f <$> mx) (g <$> my) := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  exact Cpl_bind h (fun a b hab => Cpl_pure (hfg a b hab))

def OutR (j : ℕ) (s₁ s₂ : PrfHmacMuState × List (Bytes × Bytes)) : Prop :=
  s₁.1 = s₂.1 ∧ HCInv j s₁.1 s₁.2

section Run

variable (P : Primitives) (k : Bytes) (j : ℕ)

local notation "EvL" => prfEvalImpl P false k

theorem step_outer (t : (ℕ ⊕ PrimQuery) ⊕ AeadMuIntQuery)
    (s₁ s₂ : PrfHmacMuState × List (Bytes × Bytes)) (hs : OutR j s₁ s₂) :
    Cpl (fun p q => p.1 = q.1 ∧ OutR j p.2 q.2)
      ((gOuter P EvL (fun r => r ≤ j) (prfHmacTagQ j) t).run s₁)
      ((gOuter P EvL (fun r => r ≤ j) unifTag t).run s₂) := by
  obtain ⟨st, c₁⟩ := s₁
  obtain ⟨st', c₂⟩ := s₂
  obtain ⟨h1, hI⟩ := hs
  dsimp only at h1 hI
  subst h1
  rcases t with pq | mq
  · change Cpl _ ((primBaseImpl P pq) >>= fun u => pure (u, (st, c₁)))
      ((primBaseImpl P pq) >>= fun u => pure (u, (st, c₂)))
    exact Cpl_same _ (fun u _ => Cpl_pure ⟨rfl, rfl, hI⟩)
  · change Cpl _
      ((simulateQ (gFull P EvL) (gStep (fun r => r ≤ j) (prfHmacTagQ j) mq st)).run c₁ >>=
        fun z => pure (z.1.1, (z.1.2, z.2)))
      ((simulateQ (gFull P EvL) (gStep (fun r => r ≤ j) unifTag mq st)).run c₂ >>=
        fun z => pure (z.1.1, (z.1.2, z.2)))
    have hs : Cpl (StepR j)
        ((simulateQ (gFull P EvL) (gStep (fun r => r ≤ j) (prfHmacTagQ j) mq st)).run c₁)
        ((simulateQ (gFull P EvL) (gStep (fun r => r ≤ j) unifTag mq st)).run c₂) := by
      cases mq with
      | encOnce i ad pt => exact step_enc P k j i ad pt st hI
      | tryForge i ad ct => exact step_forge P k j i ad ct st hI
    refine Cpl_bind hs ?_
    rintro ⟨⟨a, s⟩, c⟩ ⟨⟨a', s'⟩, c'⟩ ⟨h, hI'⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact Cpl_pure ⟨rfl, rfl, hI'⟩

theorem gRun_cpl (B : AeadMuIntCtxtAdv) :
    Cpl (fun p q => p.1.2 = q.1.2 ∧ HCInv j p.1.2 p.2)
      ((simulateQ (gFull P EvL) (gRun (fun r => r ≤ j) (prfHmacTagQ j) B.run {})).run [])
      ((simulateQ (gFull P EvL) (gRun (fun r => r ≤ j) unifTag B.run {})).run []) := by
  rw [simulateQ_gRun, simulateQ_gRun]
  refine Cpl_map (Cpl_simulateQ _ _ (OutR j) (step_outer P k j) B.run ({}, []) ({}, [])
    ⟨rfl, HCInv_init j⟩) ?_
  rintro ⟨a, s₁⟩ ⟨b, s₂⟩ ⟨-, h1, h2⟩
  exact ⟨h1, h2⟩

theorem finish_cpl (pending : List (ℕ × Bytes × Bytes)) :
    ∀ (pts : List (ℕ × Bytes)) (c₁ c₂ : List (Bytes × Bytes)), pts.Nodup →
      (∀ e ∈ pts, e.1 ≤ j ∧ (e.1 = j → e.2 ∉ c₁.map Prod.fst)) →
      Cpl (fun p q => p.1 = q.1)
        ((simulateQ (gFull P EvL) (gFinish (prfHmacTagQ j) pending pts)).run c₁)
        ((simulateQ (gFull P EvL) (gFinish unifTag pending pts)).run c₂)
  | [], c₁, c₂, _, _ => by
    simp only [gFinish, simulateQ_pure, StateT.run_pure]
    exact Cpl_pure rfl
  | (r, x) :: pts, c₁, c₂, hnd, hpts => by
    have htag : Cpl (fun p q => p.1 = q.1 ∧
        (∀ e ∈ pts, e.1 ≤ j ∧ (e.1 = j → e.2 ∉ p.2.map Prod.fst)))
        ((simulateQ (gFull P EvL) (prfHmacTagQ j r x)).run c₁)
        ((simulateQ (gFull P EvL) (unifTag r x)).run c₂) := by
      by_cases hlt : r < j
      · simp only [prfHmacTagQ, ite_eq_left hlt, unifTag, gFull_unif_run, map_eq_bind_pure_comp]
        exact Cpl_same _ (fun t _ => Cpl_pure ⟨rfl, fun e he => hpts e (List.mem_cons_of_mem _ he)⟩)
      · have hj : r = j := by have := (hpts (r, x) (by simp)).1; omega
        have hfr := (hpts (r, x) (by simp)).2 hj
        simp only [prfHmacTagQ, ite_eq_right hlt, unifTag, gFull_unif_run, gFull_evalQ_run,
          prfEval_false_fresh_run P k _ _ hfr, map_eq_bind_pure_comp]
        refine Cpl_same _ (fun t _ => Cpl_pure ⟨rfl, fun e he =>
          ⟨(hpts e (List.mem_cons_of_mem _ he)).1, fun hej => ?_⟩⟩)
        simp only [List.map_cons, List.mem_cons, not_or]
        refine ⟨fun hx => ?_, (hpts e (List.mem_cons_of_mem _ he)).2 hej⟩
        have : e = (r, x) := Prod.ext (hej.trans hj.symm) hx
        subst this
        exact (List.nodup_cons.1 hnd).1 he
    simp only [gFinish, simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure]
    refine Cpl_bind htag ?_
    rintro ⟨t, c₁'⟩ ⟨t', c₂'⟩ ⟨h, hp⟩
    dsimp only at h hp
    subst h
    refine Cpl_bind (finish_cpl pending pts c₁' c₂' (List.nodup_cons.1 hnd).2 hp) ?_
    rintro ⟨b, _⟩ ⟨b', _⟩ h
    dsimp only at h
    subst h
    exact Cpl_pure rfl

theorem gAfter_cpl (B : AeadMuIntCtxtAdv) :
    Cpl (fun p q => p.1 = q.1)
      ((simulateQ (prfFullImpl P false k) (gAfter (fun r => r ≤ j) (prfHmacTagQ j) B)).run [])
      ((simulateQ (prfFullImpl P false k) (gAfter (fun r => r ≤ j) unifTag B)).run []) := by
  rw [prfFullImpl_false]
  unfold gAfter
  simp only [simulateQ_bind, StateT.run_bind]
  refine Cpl_bind (gRun_cpl P k j B) ?_
  rintro ⟨⟨u, st⟩, c₁⟩ ⟨⟨u', st'⟩, c₂⟩ ⟨h1, hI⟩
  dsimp only at h1 hI
  subst h1
  simp only [simulateQ_pure, StateT.run_pure]
  refine Cpl_bind (finish_cpl P k j st.pending (pendPts st.pending) c₁ c₂
    (List.nodup_dedup _) ?_) ?_
  · intro e he
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (List.mem_dedup.1 he)
    exact hI.pend p hp
  · rintro ⟨b, _⟩ ⟨b', _⟩ h
    dsimp only at h
    subst h
    exact Cpl_pure rfl

end Run

theorem gProb_rf_eq_unif (P : Primitives) (B : AeadMuIntCtxtAdv) (j : ℕ) :
    gProb P false (fun r => r ≤ j) (prfHmacTagQ j) B = gProb P false (fun r => r ≤ j) unifTag B := by
  have key : ∀ k, 𝒟[(do
      let (z, _) ← (simulateQ (prfFullImpl P false k)
        (gAfter (fun r => r ≤ j) (prfHmacTagQ j) B)).run []
      return z : ProbComp Bool)] =
    𝒟[(do
      let (z, _) ← (simulateQ (prfFullImpl P false k) (gAfter (fun r => r ≤ j) unifTag B)).run []
      return z : ProbComp Bool)] := fun k =>
    gAfter_cpl P k j B (fun z => pure z.1) (fun z => pure z.1) (fun a b h => by rw [h])
  unfold gProb
  rw [OracleComp.evalDist_bind_congr_of_support _ _ _ (fun k _ => key k)]

end SignalPqxdh.Security

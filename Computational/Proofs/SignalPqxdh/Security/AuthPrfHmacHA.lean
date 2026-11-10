/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthPrfHmacD
public import Computational.Specifications.Assumptions.KemCorrect
import Computational.Proofs.SignalPqxdh.Security.SigHopA
import LibsignalBinary.Proofs.SpecLemmas.SignalPqxdh.Model
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure


/-!
# PQXDH authentication: hybrid (A0), multi-key INT-CTXT ≤ all-real hybrid

Proves `aeadMuIntCtxt_le_gProb_allReal`: when `B` only uses associated data from a set `Good` on
which `aeadMacInput` is injective, any winning forgery in `aeadMuIntCtxtExp` is fresh and has length
at least `24`, so the all-real hybrid `gStep (fun _ => False) unifTag` sets `bad`.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ENNReal BigOperators


namespace SignalPqxdh.Security

open SignalPqxdh
open RoKem

/-- `Good` ADs have an injective MAC-input encoding. -/
def MacAdGood (Good : Bytes → Bool) : Prop :=
  ∀ ad ad' body body', Good ad = true → Good ad' = true →
    aeadMacInput ad body = aeadMacInput ad' body' → ad = ad' ∧ body = body'

def badAdQuery (Good : Bytes → Bool) : ((ℕ ⊕ PrimQuery) ⊕ AeadMuIntQuery) → Prop
  | .inr (.encOnce _ ad _) => Good ad = false
  | .inr (.tryForge _ ad _) => Good ad = false
  | _ => False

instance (Good : Bytes → Bool) : DecidablePred (badAdQuery Good) := fun q => by
  rcases q with _ | q
  · simp only [badAdQuery]; infer_instance
  · cases q <;> simp only [badAdQuery] <;> infer_instance

/-- `B` only ever uses `Good` ADs. -/
def MacInputDisciplined (Good : Bytes → Bool) (B : AeadMuIntCtxtAdv) : Prop :=
  OracleComp.IsQueryBoundP B.run (badAdQuery Good) 0

/-! ## Crypto facts -/

theorem ha_dec_length (P : Primitives) (hP : WellFormedPrimitivesδ P) (mk : MessageKeys)
    (ad ct : Bytes) (h : (P.aeadDec mk ad ct).isSome) : 24 ≤ ct.length := by
  rw [hP.aeadDec_eq_ref] at h
  unfold aes256CbcHmacDecRef at h
  by_contra hc
  simp only [ge_iff_le, show ¬ 24 ≤ ct.length from hc, ↓reduceIte, Option.isSome_none,
    Bool.false_eq_true] at h

/-- A successful decryption under the challenge key whose MAC input equals that of the challenge
    is the challenge itself. -/
theorem ha_dec_eq_chal (P : Primitives) (hP : WellFormedPrimitivesδ P) (Good : Bytes → Bool)
    (hGood : MacAdGood Good) (mk : MessageKeys) (ad ct ad0 pt0 : Bytes)
    (hg : Good ad = true) (hg0 : Good ad0 = true)
    (h : (P.aeadDec mk ad ct).isSome)
    (hx : aeadMacInput ad (etmBody ct) = aeadMacInput ad0 (etmBody (P.aeadEnc mk ad0 pt0))) :
    ad = ad0 ∧ ct = P.aeadEnc mk ad0 pt0 := by
  have hlen := ha_dec_length P hP mk ad ct h
  rw [hP.aeadDec_eq_ref] at h
  rw [hP.aeadEnc_eq_ref] at hx ⊢
  unfold aes256CbcHmacEncRef at hx ⊢
  set body0 := aes256CbcEncRef P mk.cipherKey mk.iv pt0
  have htl : ((hmacSha256Ref P mk.macKey (aeadMacInput ad0 body0)).take 8).length = 8 := by
    simp [hmacSha256Ref_length]
  have hb0 : etmBody (body0 ++ (hmacSha256Ref P mk.macKey (aeadMacInput ad0 body0)).take 8) =
      body0 := by
    unfold etmBody
    rw [List.length_append, htl, Nat.add_sub_cancel, List.take_left' rfl]
  simp only [hb0] at hx
  obtain ⟨rfl, hbody⟩ := hGood _ _ _ _ hg hg0 hx
  refine ⟨rfl, ?_⟩
  unfold aes256CbcHmacDecRef at h
  simp only [ge_iff_le, hlen, ↓reduceIte] at h
  split_ifs at h with htag
  · have htag' : etmTag ct = (hmacSha256Ref P mk.macKey (aeadMacInput ad (etmBody ct))).take 8 := by
      simpa [etmTag, etmBody] using htag
    rw [← List.take_append_drop (ct.length - 8) ct]
    change etmBody ct ++ etmTag ct = _
    rw [htag', hbody]
  · simp at h

/-! ## The two games -/

noncomputable def haMuImpl (P : Primitives) :
    QueryImpl aeadMuIntSpec (StateT AeadMuIntState ProbComp) := fun q =>
  match q with
  | .encOnce i ad pt => do
    if !goodFirstMsgAD ad then return none
    let (_, chal, _) ← get
    match chal.lookup i with
    | some _ => return none
    | none =>
      let mk ← aeadMuIntKey i
      let ct := P.aeadEnc mk ad pt
      let (keys, chal', w) ← get
      set (keys, (i, (ad, ct)) :: chal', w)
      return (some ct)
  | .tryForge i ad ct => do
    if !goodFirstMsgAD ad then return false
    let (_, chal, _) ← get
    if chal.lookup i == some (ad, ct) then return false
    let mk ← aeadMuIntKey i
    match P.aeadDec mk ad ct with
    | some _ =>
      let (keys, chal', _) ← get
      set (keys, chal', true)
      return true
    | none => return false

noncomputable def haMuFull (P : Primitives) :
    QueryImpl AeadMuIntSimSpec (StateT AeadMuIntState ProbComp) :=
  (primBaseImpl P).liftTarget (StateT AeadMuIntState ProbComp) + haMuImpl P

theorem ha_exp_eq (P : Primitives) (B : AeadMuIntCtxtAdv) :
    aeadMuIntCtxtExp P B = (do
      let (_, (_, _, w)) ← (simulateQ (haMuFull P) B.run).run ([], [], false)
      return w) := rfl

/-! ## Generic until-bad domination -/

section Core

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {σ₁ σ₂ : Type}

theorem ha_bad_persist (impl : QueryImpl spec (StateT σ₂ ProbComp)) (bad : σ₂ → Bool)
    (hmono : ∀ t s, bad s = true → ∀ z ∈ support ((impl t).run s), bad z.2 = true)
    {α : Type} (oa : OracleComp spec α) :
    ∀ s, bad s = true → ∀ z ∈ support ((simulateQ impl oa).run s), bad z.2 = true := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s hs z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hs
  | query_bind t k ih =>
    intro s hs z hz
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨us, hus, hz⟩ := hz
    exact ih us.1 us.2 (hmono t s hs us hus) z hz

/-- If from agreeing states every allowed query of the first implementation can be coupled with the
    second so that afterwards the states agree with equal answers or the second has set `bad`, then
    `Pr[win] ≤ Pr[bad]`. -/
theorem ha_core (impl₁ : QueryImpl spec (StateT σ₁ ProbComp))
    (impl₂ : QueryImpl spec (StateT σ₂ ProbComp)) (Q : ι → Prop)
    [DecidablePred Q] (Ag : σ₁ → σ₂ → Prop) (bad : σ₂ → Bool) (win : σ₁ → Bool)
    (hmono : ∀ t s, bad s = true → ∀ z ∈ support ((impl₂ t).run s), bad z.2 = true)
    (hwin : ∀ s₁ s₂, Ag s₁ s₂ → win s₁ = false)
    (hstep : ∀ t s₁ s₂, Ag s₁ s₂ → ¬ Q t → ∃ (β : Type) (X : ProbComp β)
      (g₁ : β → spec.Range t × σ₁) (g₂ : β → spec.Range t × σ₂),
      (impl₁ t).run s₁ = g₁ <$> X ∧ (impl₂ t).run s₂ = g₂ <$> X ∧
      ∀ a ∈ support X, bad (g₂ a).2 = true ∨ ((g₁ a).1 = (g₂ a).1 ∧ Ag (g₁ a).2 (g₂ a).2))
    {α : Type} (oa : OracleComp spec α) :
    IsQueryBoundP oa Q 0 → ∀ s₁ s₂, (bad s₂ = true ∨ Ag s₁ s₂) →
      Pr{let z ← (simulateQ impl₁ oa).run s₁}[win z.2 = true] ≤
        Pr{let z ← (simulateQ impl₂ oa).run s₂}[bad z.2 = true] := by
  have hbad : ∀ {γ : Type} (ob ob' : OracleComp spec γ) s₁ s₂, bad s₂ = true →
      Pr{let z ← (simulateQ impl₁ ob).run s₁}[win z.2 = true] ≤
        Pr{let z ← (simulateQ impl₂ ob').run s₂}[bad z.2 = true] := by
    intro γ ob ob' s₁ s₂ hs
    rw [prEvent_eq_one_of_forall_mem_support _ _ (ha_bad_persist impl₂ bad hmono ob' s₂ hs)]
    exact prEvent_le_one _
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro _ s₁ s₂ h
    rcases h with hb | hag
    · exact hbad _ _ s₁ s₂ hb
    · simp [hwin _ _ hag]
  | query_bind t k ih =>
    intro hQ s₁ s₂ h
    rcases h with hb | hag
    · exact hbad _ _ s₁ s₂ hb
    rw [isQueryBoundP_query_bind_iff] at hQ
    obtain ⟨h1, h2⟩ := hQ
    have hnQ : ¬ Q t := by
      rcases h1 with h | h
      · exact h
      · exact absurd h (Nat.lt_irrefl 0)
    simp only [hnQ, ↓reduceIte] at h2
    obtain ⟨β, X, g₁, g₂, e₁, e₂, hg⟩ := hstep t s₁ s₂ hag hnQ
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    rw [e₁, e₂, bind_map_left, bind_map_left]
    refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ (fun a ha => ?_)
    rcases hg a ha with hb | ⟨heq, hag'⟩
    · exact hbad _ _ _ _ hb
    · rw [heq]
      exact ih _ (h2 _) _ _ (Or.inr hag')

end Core

/-! ## Simulation normal forms -/

section Basic

variable (P : Primitives) {σ : Type} (ev : QueryImpl prfHmacSpec (StateT σ ProbComp))

theorem ha_unif_run {α : Type} (mx : ProbComp α) (c : σ) :
    (simulateQ (gFull P ev) (prfHmacUnif mx)).run c = (fun a => (a, c)) <$> mx := by
  unfold prfHmacUnif gFull
  rw [simulateQ_embedPrim_run, simulateQ_embedUnif]

theorem ha_primQ_run (op : PrimQuery) (c : σ) :
    (simulateQ (gFull P ev) (prfHmacPrimQ op)).run c = (fun a => (a, c)) <$> primImpl P op := by
  unfold prfHmacPrimQ gFull
  rw [simulateQ_embedPrim_run, simulateQ_primQ]

theorem ha_enc_run (mk : MessageKeys) (ad pt : Bytes) (c : σ) :
    (simulateQ (gFull P ev) (prfHmacPrimQ (.aeadEnc mk ad pt))).run c =
      (pure (P.aeadEnc mk ad pt, c) : ProbComp (primSpec.Range (.aeadEnc mk ad pt) × σ)) := by
  rw [ha_primQ_run]; rfl

theorem ha_dec_run (mk : MessageKeys) (ad ct : Bytes) (c : σ) :
    (simulateQ (gFull P ev) (prfHmacPrimQ (.aeadDec mk ad ct))).run c =
      (pure (P.aeadDec mk ad ct, c) : ProbComp (primSpec.Range (.aeadDec mk ad ct) × σ)) := by
  rw [ha_primQ_run]; rfl

end Basic

theorem ha_lookup_map {β γ : Type} (f : β → γ) :
    ∀ (l : List (ℕ × β)) (i : ℕ), (l.map (fun e => (e.1, f e.2))).lookup i = (l.lookup i).map f
  | [], _ => rfl
  | (k, b) :: l, i => by
    by_cases hk : i = k
    · subst hk; simp [List.lookup]
    · have hb : (i == k) = false := by simpa using hk
      simp [List.lookup, hb, ha_lookup_map f l i]

/-! ## Agreement relation -/

/-- Challenge invariant: every challenge has a `Good` AD and is `aeadEnc` under the key's key. -/
def HaInv (P : Primitives) (Good : Bytes → Bool) (keys : List (ℕ × (ℕ × MessageKeys)))
    (chal : List (ℕ × (Bytes × Bytes))) : Prop :=
  ∀ i ad0 ct0, chal.lookup i = some (ad0, ct0) →
    Good ad0 = true ∧ ∃ e pt0, keys.lookup i = some e ∧ ct0 = P.aeadEnc e.2 ad0 pt0

/-- The two games agree (and nobody has won / set `bad` yet). -/
structure HaAgree (P : Primitives) (Good : Bytes → Bool) (s₁ : AeadMuIntState)
    (s : PrfHmacMuState) : Prop where
  keys : s₁.1 = s.keys.map (fun e => (e.1, e.2.2))
  chal : s₁.2.1 = s.chal
  win : s₁.2.2 = false
  bad : s.bad = false
  inv : HaInv P Good s.keys s.chal

theorem haInv_cons_key (P : Primitives) (Good : Bytes → Bool)
    (keys : List (ℕ × (ℕ × MessageKeys))) (chal : List (ℕ × (Bytes × Bytes))) (i : ℕ)
    (e : ℕ × MessageKeys) (h : HaInv P Good keys chal) (hc : chal.lookup i = none) :
    HaInv P Good ((i, e) :: keys) chal := by
  intro j ad0 ct0 hj
  obtain ⟨hg, e', pt0, hk, hct⟩ := h j ad0 ct0 hj
  refine ⟨hg, e', pt0, ?_, hct⟩
  have hji : j ≠ i := by rintro rfl; rw [hc] at hj; cases hj
  have hb : (j == i) = false := by simpa using hji
  simp [List.lookup, hb, hk]

theorem haInv_cons_chal (P : Primitives) (Good : Bytes → Bool)
    (keys : List (ℕ × (ℕ × MessageKeys))) (chal : List (ℕ × (Bytes × Bytes))) (i : ℕ)
    (e : ℕ × MessageKeys) (ad pt : Bytes) (h : HaInv P Good keys chal)
    (hk : keys.lookup i = some e) (hg : Good ad = true) :
    HaInv P Good keys ((i, (ad, P.aeadEnc e.2 ad pt)) :: chal) := by
  intro j ad0 ct0 hj
  by_cases hji : j = i
  · subst hji
    simp only [List.lookup, beq_self_eq_true, Option.some.injEq, Prod.mk.injEq] at hj
    obtain ⟨rfl, rfl⟩ := hj
    exact ⟨hg, e, pt, hk, rfl⟩
  · have hb : (j == i) = false := by simpa using hji
    simp only [List.lookup, hb] at hj
    exact h j ad0 ct0 hj

section Step

variable (P : Primitives) (Good : Bytes → Bool) {σ : Type}
  (ev : QueryImpl prfHmacSpec (StateT σ ProbComp))

def HaCoupled (t : (ℕ ⊕ PrimQuery) ⊕ AeadMuIntQuery) (s₁ : AeadMuIntState)
    (s₂ : PrfHmacMuState × σ) : Prop :=
  ∃ (β : Type) (X : ProbComp β) (g₁ : β → AeadMuIntSimSpec.Range t × AeadMuIntState)
    (g₂ : β → AeadMuIntSimSpec.Range t × (PrfHmacMuState × σ)),
    (haMuFull P t).run s₁ = g₁ <$> X ∧
    (gOuter P ev (fun _ => False) unifTag t).run s₂ = g₂ <$> X ∧
    ∀ a ∈ support X, (g₂ a).2.1.bad = true ∨
      ((g₁ a).1 = (g₂ a).1 ∧ HaAgree P Good (g₁ a).2 (g₂ a).2.1)

theorem ha_step_inl (pq : ℕ ⊕ PrimQuery) (s₁ : AeadMuIntState) (s₂ : PrfHmacMuState × σ)
    (hag : HaAgree P Good s₁ s₂.1) : HaCoupled P Good ev (Sum.inl pq) s₁ s₂ :=
  ⟨_, primBaseImpl P pq, fun u => (u, s₁), fun u => (u, s₂), by simp [haMuFull],
    by simp [gOuter], fun _ _ => Or.inr ⟨rfl, hag⟩⟩

theorem ha_step_enc (i : ℕ) (ad pt : Bytes) (keys : List (ℕ × (ℕ × MessageKeys)))
    (chal : List (ℕ × (Bytes × Bytes))) (pend : List (ℕ × Bytes × Bytes)) (c : σ)
    (hinv : HaInv P Good keys chal) (hg : Good ad = true) (hgg : goodFirstMsgAD ad = true) :
    HaCoupled P Good ev (Sum.inr (.encOnce i ad pt))
      (keys.map (fun e => (e.1, e.2.2)), chal, false) (⟨keys, chal, pend, false⟩, c) := by
  rcases hc : chal.lookup i with _ | ch
  · rcases hk : keys.lookup i with _ | e
    · refine ⟨MessageKeys, sampleMessageKeys80,
        fun mk => (some (P.aeadEnc mk ad pt), ((i, mk) :: keys.map (fun e => (e.1, e.2.2)),
          (i, (ad, P.aeadEnc mk ad pt)) :: chal, false)),
        fun mk => (some (P.aeadEnc mk ad pt), (⟨(i, (keys.length, mk)) :: keys,
          (i, (ad, P.aeadEnc mk ad pt)) :: chal, pend, false⟩, c)), ?_, ?_, ?_⟩
      · simp [haMuFull, haMuImpl, hgg, aeadMuIntKey, hc, hk, ha_lookup_map]
      · simp [gOuter, gStep, prfHmacMuKey, hc, hk, ha_unif_run]
        simp only [ha_enc_run P ev, map_pure]
        rfl
      · intro mk _
        right
        refine ⟨rfl, ⟨rfl, rfl, rfl, rfl, ?_⟩⟩
        exact haInv_cons_chal P Good _ _ i (keys.length, mk) ad pt
          (haInv_cons_key P Good _ _ i _ hinv hc) (by simp [List.lookup]) hg
    · refine ⟨Unit, pure (),
        fun _ => (some (P.aeadEnc e.2 ad pt), (keys.map (fun e => (e.1, e.2.2)),
          (i, (ad, P.aeadEnc e.2 ad pt)) :: chal, false)),
        fun _ => (some (P.aeadEnc e.2 ad pt), (⟨keys, (i, (ad, P.aeadEnc e.2 ad pt)) :: chal,
          pend, false⟩, c)), ?_, ?_, ?_⟩
      · simp [haMuFull, haMuImpl, hgg, aeadMuIntKey, hc, hk, ha_lookup_map]
      · simp [gOuter, gStep, prfHmacMuKey, hc, hk]
        simp only [ha_enc_run P ev, map_pure]
      · intro _ _
        right
        exact ⟨rfl, ⟨rfl, rfl, rfl, rfl, haInv_cons_chal P Good _ _ i e ad pt hinv hk hg⟩⟩
  · refine ⟨Unit, pure (), fun _ => (none, (keys.map (fun e => (e.1, e.2.2)), chal, false)),
      fun _ => (none, (⟨keys, chal, pend, false⟩, c)), ?_, ?_, ?_⟩
    · simp [haMuFull, haMuImpl, hgg, hc]
    · simp [gOuter, gStep, hc]
    · intro _ _
      right
      exact ⟨rfl, ⟨rfl, rfl, rfl, rfl, hinv⟩⟩

theorem ha_step_forge (hP : WellFormedPrimitivesδ P) (hGood : MacAdGood Good) (i : ℕ)
    (ad ct : Bytes) (keys : List (ℕ × (ℕ × MessageKeys)))
    (chal : List (ℕ × (Bytes × Bytes))) (pend : List (ℕ × Bytes × Bytes)) (c : σ)
    (hinv : HaInv P Good keys chal) (hg : Good ad = true) (hgg : goodFirstMsgAD ad = true) :
    HaCoupled P Good ev (Sum.inr (.tryForge i ad ct))
      (keys.map (fun e => (e.1, e.2.2)), chal, false) (⟨keys, chal, pend, false⟩, c) := by
  rcases hc : chal.lookup i with _ | ⟨ad0, ct0⟩
  · rcases hk : keys.lookup i with _ | e
    · refine ⟨MessageKeys, sampleMessageKeys80,
        fun mk => ((P.aeadDec mk ad ct).isSome, ((i, mk) :: keys.map (fun e => (e.1, e.2.2)),
          chal, (P.aeadDec mk ad ct).isSome)),
        fun mk => (false, (⟨(i, (keys.length, mk)) :: keys, chal, pend,
          decide (24 ≤ ct.length) && (P.aeadDec mk ad ct).isSome⟩, c)), ?_, ?_, ?_⟩
      · simp [haMuFull, haMuImpl, hgg, aeadMuIntKey, hc, hk, ha_lookup_map]
        rw [map_eq_bind_pure_comp]
        refine bind_congr fun mk => ?_
        rcases hd : P.aeadDec mk ad ct with _ | m <;> simp [hd]
      · simp [gOuter, gStep, prfHmacMuKey, hc, hk, ha_unif_run]
        rw [map_eq_bind_pure_comp]
        refine bind_congr fun mk => ?_
        by_cases hl : 24 ≤ ct.length <;> simp [hl, ha_dec_run P ev]
      · intro mk _
        rcases hd : P.aeadDec mk ad ct with _ | m
        · right
          refine ⟨by simp [hd], ⟨rfl, rfl, by simp [hd], by simp [hd], ?_⟩⟩
          exact haInv_cons_key P Good _ _ i _ hinv hc
        · left
          have hl := ha_dec_length P hP mk ad ct (by simp [hd])
          simp [hd, hl]
    · rcases hd : P.aeadDec e.2 ad ct with _ | m
      · refine ⟨Unit, pure (), fun _ => (false, (keys.map (fun e => (e.1, e.2.2)), chal, false)),
          fun _ => (false, (⟨keys, chal, pend, false⟩, c)), ?_, ?_, ?_⟩
        · simp [haMuFull, haMuImpl, hgg, aeadMuIntKey, hc, hk, ha_lookup_map, hd]
        · by_cases hl : 24 ≤ ct.length <;> simp [gOuter, gStep, prfHmacMuKey, hc, hk, hl,
            ha_dec_run P ev, hd]
        · intro _ _
          exact Or.inr ⟨rfl, ⟨rfl, rfl, rfl, rfl, hinv⟩⟩
      · have hl := ha_dec_length P hP e.2 ad ct (by simp [hd])
        refine ⟨Unit, pure (), fun _ => (true, (keys.map (fun e => (e.1, e.2.2)), chal, true)),
          fun _ => (false, (⟨keys, chal, pend, true⟩, c)), ?_, ?_, ?_⟩
        · simp [haMuFull, haMuImpl, hgg, aeadMuIntKey, hc, hk, ha_lookup_map, hd]
        · simp [gOuter, gStep, prfHmacMuKey, hc, hk, hl, ha_dec_run P ev, hd]
        · intro _ _
          exact Or.inl rfl
  · by_cases hq : ad0 = ad ∧ ct0 = ct
    · obtain ⟨rfl, rfl⟩ := hq
      refine ⟨Unit, pure (), fun _ => (false, (keys.map (fun e => (e.1, e.2.2)), chal, false)),
        fun _ => (false, (⟨keys, chal, pend, false⟩, c)), ?_, ?_, ?_⟩
      · simp [haMuFull, haMuImpl, hgg, hc]
      · simp [gOuter, gStep, hc]
      · intro _ _
        exact Or.inr ⟨rfl, ⟨rfl, rfl, rfl, rfl, hinv⟩⟩
    · obtain ⟨hg0, e, pt0, hk, hct0⟩ := hinv i ad0 ct0 hc
      rcases hd : P.aeadDec e.2 ad ct with _ | m
      · refine ⟨Unit, pure (), fun _ => (false, (keys.map (fun e => (e.1, e.2.2)), chal, false)),
          fun _ => (false, (⟨keys, chal, pend, false⟩, c)), ?_, ?_, ?_⟩
        · simp [haMuFull, haMuImpl, hgg, aeadMuIntKey, hc, hk, ha_lookup_map, hd, hq]
        · by_cases hl : 24 ≤ ct.length <;>
          by_cases hx : aeadMacInput ad (etmBody ct) = aeadMacInput ad0 (etmBody ct0) <;>
          simp [gOuter, gStep, prfHmacMuKey, hc, hk, hl, hx, ha_dec_run P ev, hd, hq]
        · intro _ _
          exact Or.inr ⟨rfl, ⟨rfl, rfl, rfl, rfl, hinv⟩⟩
      · have hl := ha_dec_length P hP e.2 ad ct (by simp [hd])
        have hx : aeadMacInput ad (etmBody ct) ≠ aeadMacInput ad0 (etmBody ct0) := by
          intro hx
          rw [hct0] at hx
          obtain ⟨h1, h2⟩ := ha_dec_eq_chal P hP Good hGood e.2 ad ct ad0 pt0 hg hg0
            (by simp [hd]) hx
          exact hq ⟨h1.symm, by rw [hct0, h2]⟩
        refine ⟨Unit, pure (), fun _ => (true, (keys.map (fun e => (e.1, e.2.2)), chal, true)),
          fun _ => (false, (⟨keys, chal, pend, true⟩, c)), ?_, ?_, ?_⟩
        · simp [haMuFull, haMuImpl, hgg, aeadMuIntKey, hc, hk, ha_lookup_map, hd, hq]
        · simp [gOuter, gStep, prfHmacMuKey, hc, hk, hl, hx, ha_dec_run P ev, hd, hq]
        · intro _ _
          exact Or.inl rfl

theorem ha_step (hP : WellFormedPrimitivesδ P) (hGood : MacAdGood Good)
    (hGG : ∀ ad, Good ad = true → goodFirstMsgAD ad = true)
    (t : (ℕ ⊕ PrimQuery) ⊕ AeadMuIntQuery) (s₁ : AeadMuIntState) (s₂ : PrfHmacMuState × σ)
    (hag : HaAgree P Good s₁ s₂.1) (hq : ¬ badAdQuery Good t) :
    HaCoupled P Good ev t s₁ s₂ := by
  rcases t with pq | mq
  · exact ha_step_inl P Good ev pq s₁ s₂ hag
  obtain ⟨keys1, chal1, w1⟩ := s₁
  obtain ⟨⟨keys, chal, pend, b⟩, c⟩ := s₂
  obtain ⟨hk, hc, hw, hb, hinv⟩ := hag
  simp only at hk hc hw hb hinv
  subst hk hc hw hb
  rcases mq with ⟨i, ad, pt⟩ | ⟨i, ad, ct⟩
  · have hg : Good ad = true := by simpa [badAdQuery] using hq
    exact ha_step_enc P Good ev i ad pt _ _ pend c hinv hg (hGG ad hg)
  · have hg : Good ad = true := by simpa [badAdQuery] using hq
    exact ha_step_forge P Good ev hP hGood i ad ct _ _ pend c hinv hg (hGG ad hg)

end Step

/-! ## `bad` is monotone in the all-real hybrid -/

theorem ha_support_simulateQ_fst {ι : Type} {spec : OracleSpec.{0, 0} ι} {σ α : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) (oa : OracleComp spec α) :
    ∀ c, ∀ z ∈ support ((simulateQ impl oa).run c), z.1 ∈ support oa := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro c z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    simp
  | query_bind t k ih =>
    intro c z hz
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨us, _, hz⟩ := hz
    exact (mem_support_bind_iff _ _ _).2 ⟨us.1, mem_support_query t us.1, ih us.1 us.2 z hz⟩

theorem ha_gStep_bad (q : AeadMuIntQuery) (st : PrfHmacMuState) (hb : st.bad = true) :
    ∀ z ∈ support (gStep (fun _ => False) unifTag q st), z.2.bad = true := by
  intro z hz
  rcases q with ⟨i, ad, pt⟩ | ⟨i, ad, ct⟩
  · simp only [gStep] at hz
    split at hz
    · simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hb
    · simp only [mem_support_bind_iff] at hz
      obtain ⟨p, hp, ct, _, hz⟩ := hz
      have hpb := (prfHmacMuKey_support 0 i st p hp).2.2.2.1
      simp only [↓reduceIte, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      simpa [hpb] using hb
  · simp only [gStep] at hz
    split at hz
    · simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hb
    · simp only [mem_support_bind_iff] at hz
      obtain ⟨p, hp, hz⟩ := hz
      have hpb := (prfHmacMuKey_support 0 i st p hp).2.2.2.1
      split at hz <;>
      · split_ifs at hz <;>
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz <;>
        first
        | (subst hz; simpa [hpb] using hb)
        | (obtain ⟨res, _, rfl⟩ := hz; simp [hpb, hb])

theorem ha_outer_mono (P : Primitives) {σ : Type} (ev : QueryImpl prfHmacSpec (StateT σ ProbComp))
    (t : (ℕ ⊕ PrimQuery) ⊕ AeadMuIntQuery) (s : PrfHmacMuState × σ) (hb : s.1.bad = true) :
    ∀ z ∈ support ((gOuter P ev (fun _ => False) unifTag t).run s), z.2.1.bad = true := by
  intro z hz
  rcases t with pq | mq
  · simp only [gOuter, StateT.run_mk, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨u, _, rfl⟩ := hz
    exact hb
  · simp only [gOuter, StateT.run_mk, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact ha_gStep_bad mq s.1 hb w.1 (ha_support_simulateQ_fst _ _ s.2 w hw)

/-! ## Assembly -/

theorem ha_prEvent_le_bind {α β : Type} (mx : ProbComp α) (f : α → ProbComp β)
    (p : α → Prop) (q : β → Prop)
    (h : ∀ x ∈ support mx, p x → ∀ y ∈ support (f x), q y) :
    Pr{let x ← mx}[p x] ≤ Pr{let y ← mx >>= f}[q y] := by
  classical
  calc Pr{let x ← mx}[p x] = Pr{let y ← mx >>= fun x => (pure x : ProbComp α)}[p y] := by
        rw [bind_pure]
    _ ≤ _ := by
      refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ (fun x hx => ?_)
      rw [prEvent_pure]
      split_ifs with hp
      · rw [prEvent_eq_one_of_forall_mem_support _ _ (h x hx hp)]
      · exact bot_le

theorem ha_prEvent_bind_le {α β : Type} (mx : ProbComp α) (f : α → ProbComp β)
    (p : α → Prop) (q : β → Prop)
    (h : ∀ x ∈ support mx, ∀ y ∈ support (f x), q y → p x) :
    Pr{let y ← mx >>= f}[q y] ≤ Pr{let x ← mx}[p x] := by
  classical
  calc Pr{let y ← mx >>= f}[q y] ≤ Pr{let y ← mx >>= fun x => (pure x : ProbComp α)}[p y] := by
        refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ (fun x hx => ?_)
        rw [prEvent_pure]
        split_ifs with hp
        · exact prEvent_le_one _
        · rw [prEvent_eq_zero_of_forall_mem_support _ _ (fun y hy hq => hp (h x hx y hy hq))]
    _ = _ := by rw [bind_pure]

/-- Bounds multi-key INT-CTXT advantage by the all-real hybrid under `MacInputDisciplined`. -/
theorem aeadMuIntCtxt_le_gProb_allReal (P : Primitives) (hP : WellFormedPrimitivesδ P)
    (B : AeadMuIntCtxtAdv) (Good : Bytes → Bool) (hGood : MacAdGood Good)
    (hGG : ∀ ad, Good ad = true → goodFirstMsgAD ad = true)
    (hDisc : MacInputDisciplined Good B) :
    AeadMuIntCtxt P B ≤ gProb P false (fun _ => False) unifTag B := by
  classical
  unfold AeadMuIntCtxt gProb
  refine ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top (evalDist_apply_le_one _ _)) ?_
  rw [← prEvent_eq_evalDist_singleton, ← prEvent_eq_evalDist_singleton, ha_exp_eq]
  refine (ha_prEvent_bind_le _ _ (fun z => z.2.2.2 = true) _ ?_).trans ?_
  · rintro ⟨_, _, _, w⟩ _ y hy hyt
    simp only [support_pure, Set.mem_singleton_iff] at hy
    subst hy; exact hyt
  refine le_prEvent_bind_of_forall_le_of_support _ (prEvent_true_eq_one _) _ _ (fun k _ => ?_)
  have hcore := ha_core (haMuFull P) (gOuter P (prfEvalImpl P false k) (fun _ => False) unifTag)
    (badAdQuery Good) (fun s₁ s₂ => HaAgree P Good s₁ s₂.1) (fun s => s.1.bad)
    (fun s => s.2.2) (ha_outer_mono P _) (fun s₁ s₂ h => h.win)
    (fun t s₁ s₂ hag hq => ha_step P Good _ hP hGood hGG t s₁ s₂ hag hq) B.run hDisc
    ([], [], false) ({}, []) (Or.inr ⟨rfl, rfl, rfl, rfl, fun _ _ _ h => by cases h⟩)
  refine hcore.trans ?_
  have hfull : prfFullImpl P false k = gFull P (prfEvalImpl P false k) := rfl
  unfold gAfter
  rw [hfull, simulateQ_bind, StateT.run_bind, simulateQ_gRun, bind_assoc, bind_map_left]
  refine ha_prEvent_le_bind _ _ _ _ (fun z _ hb y hy => ?_)
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, bind_assoc,
    pure_bind, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hy
  obtain ⟨h1, _, rfl⟩ := hy
  simp [hb]

end SignalPqxdh.Security

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
# PQXDH authentication: hybrid (B), key swap at the target rank

`gProb P false D unifTag B ≤ gProb P true (· ≤ m) (prfHmacTagQ m) B` when `D r ↔ r < m`.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ENNReal BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh
open RoKem

/-! ## `ProbComp` transliteration of `gStep` -/

def pKey (gen : ℕ → ProbComp MessageKeys) (i : ℕ) (st : PrfHmacMuState) :
    ProbComp ((ℕ × MessageKeys) × PrfHmacMuState) :=
  match st.keys.lookup i with
  | some e => pure (e, st)
  | none => do
    let mk ← gen st.keys.length
    pure ((st.keys.length, mk), { st with keys := (i, (st.keys.length, mk)) :: st.keys })

def pEncRest (P : Primitives) (defer : ℕ → Prop) [DecidablePred defer]
    (ptag : ℕ → Bytes → ProbComp Bytes) (i : ℕ) (ad pt : Bytes)
    (x : (ℕ × MessageKeys) × PrfHmacMuState) : ProbComp (Option Bytes × PrfHmacMuState) :=
  if defer x.1.1 then do
    let t ← ptag x.1.1 (aeadMacInput ad (etmBody (P.aeadEnc x.1.2 ad pt)))
    pure (some (etmBody (P.aeadEnc x.1.2 ad pt) ++ t.take 8),
      { x.2 with
        chal := (i, (ad, etmBody (P.aeadEnc x.1.2 ad pt) ++ t.take 8)) :: x.2.chal
        pending := x.2.pending.filter (fun e => !(e.1 == x.1.1 &&
          e.2.1 == aeadMacInput ad (etmBody (P.aeadEnc x.1.2 ad pt))))
        bad := x.2.bad || prfHmacPendingHit x.2.pending x.1.1
          (aeadMacInput ad (etmBody (P.aeadEnc x.1.2 ad pt))) t })
  else
    pure (some (P.aeadEnc x.1.2 ad pt), { x.2 with chal := (i, (ad, P.aeadEnc x.1.2 ad pt)) :: x.2.chal })

def pFresh (chal : List (ℕ × (Bytes × Bytes))) (i : ℕ) (ad ct : Bytes) : Bool :=
  match chal.lookup i with
  | some (ad0, ct0) => aeadMacInput ad (etmBody ct) != aeadMacInput ad0 (etmBody ct0)
  | none => true

def pForgeRest (P : Primitives) (defer : ℕ → Prop) [DecidablePred defer] (i : ℕ) (ad ct : Bytes)
    (x : (ℕ × MessageKeys) × PrfHmacMuState) : ProbComp (Bool × PrfHmacMuState) :=
  if pFresh x.2.chal i ad ct = true ∧ 24 ≤ ct.length then
    if defer x.1.1 then
      pure (false, { x.2 with pending := (x.1.1, aeadMacInput ad (etmBody ct), etmTag ct) :: x.2.pending })
    else
      pure (false, { x.2 with bad := x.2.bad || (P.aeadDec x.1.2 ad ct).isSome })
  else pure (false, x.2)

/-- `ProbComp` version of `gStep`. -/
def pStep (P : Primitives) (gen : ℕ → ProbComp MessageKeys) (defer : ℕ → Prop) [DecidablePred defer]
    (ptag : ℕ → Bytes → ProbComp Bytes) (q : AeadMuIntQuery) (st : PrfHmacMuState) :
    ProbComp (aeadMuIntSpec.Range q × PrfHmacMuState) :=
  match q with
  | .encOnce i ad pt =>
    match st.chal.lookup i with
    | some _ => pure (none, st)
    | none => pKey gen i st >>= pEncRest P defer ptag i ad pt
  | .tryForge i ad ct =>
    if st.chal.lookup i = some (ad, ct) then pure (false, st)
    else pKey gen i st >>= pForgeRest P defer i ad ct

def gen80 : ℕ → ProbComp MessageKeys := fun _ => sampleMessageKeys80

/-! ## Bridge from `simulateQ` -/

section Bridge

variable (P : Primitives) (b : Bool) (k : Bytes)

theorem sim_prfHmacMuKey (i : ℕ) (st : PrfHmacMuState) (c : List (Bytes × Bytes)) :
    (simulateQ (prfFullImpl P b k) (prfHmacMuKey i st)).run c =
      (fun z => (z, c)) <$> pKey gen80 i st := by
  unfold prfHmacMuKey pKey
  cases h : st.keys.lookup i
  · simp [prfHmacUnif, prfFullImpl, simulateQ_embedPrim_run, simulateQ_embedUnif, gen80]
  · simp

theorem sim_prfHmacPrimQ (op : PrimQuery) (c : List (Bytes × Bytes)) :
    (simulateQ (prfFullImpl P b k) (prfHmacPrimQ op)).run c =
      (fun z => (z, c)) <$> primImpl P op := by
  simp [prfHmacPrimQ, prfFullImpl, simulateQ_embedPrim_run]

theorem sim_aeadEnc (mk : MessageKeys) (ad pt : Bytes) (c : List (Bytes × Bytes)) :
    (simulateQ (prfFullImpl P b k) (prfHmacPrimQ (.aeadEnc mk ad pt))).run c =
      pure (P.aeadEnc mk ad pt, c) := by
  rw [sim_prfHmacPrimQ]; rfl

theorem sim_aeadDec (mk : MessageKeys) (ad ct : Bytes) (c : List (Bytes × Bytes)) :
    (simulateQ (prfFullImpl P b k) (prfHmacPrimQ (.aeadDec mk ad ct))).run c =
      pure (P.aeadDec mk ad ct, c) := by
  rw [sim_prfHmacPrimQ]; rfl

theorem sim_gStep (defer : ℕ → Prop) [DecidablePred defer]
    (tag : ℕ → Bytes → OracleComp PrfHmacSimSpec Bytes) (ptag : ℕ → Bytes → ProbComp Bytes)
    (htag : ∀ r x c, (simulateQ (prfFullImpl P b k) (tag r x)).run c = (fun t => (t, c)) <$> ptag r x)
    (q : AeadMuIntQuery) (st : PrfHmacMuState) (c : List (Bytes × Bytes)) :
    (simulateQ (prfFullImpl P b k) (gStep defer tag q st)).run c =
      (fun z => (z, c)) <$> pStep P gen80 defer ptag q st := by
  rcases q with ⟨i, ad, pt⟩ | ⟨i, ad, ct⟩
  · simp only [gStep, pStep]
    cases h : st.chal.lookup i
    · simp only [simulateQ_bind, StateT.run_bind, sim_prfHmacMuKey, bind_map_left, map_bind]
      refine bind_congr (fun x => ?_)
      obtain ⟨⟨r, mk⟩, st'⟩ := x
      simp only [pEncRest]
      erw [sim_aeadEnc]
      rw [pure_bind]
      split_ifs
      · simp [htag]
      · simp
    · simp
  · simp only [gStep, pStep, beq_iff_eq]
    split_ifs
    · simp
    · simp only [simulateQ_bind, StateT.run_bind, sim_prfHmacMuKey, bind_map_left, map_bind]
      refine bind_congr (fun x => ?_)
      obtain ⟨⟨r, mk⟩, st'⟩ := x
      simp only [pForgeRest]
      rcases hc : st'.chal.lookup i with _ | ⟨ad0, ct0⟩
      all_goals simp only [pFresh, hc]
      all_goals split_ifs <;> simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure,
        StateT.run_pure, map_pure]
      all_goals erw [sim_aeadDec]
      all_goals simp

noncomputable def pOuter (gen : ℕ → ProbComp MessageKeys) (defer : ℕ → Prop) [DecidablePred defer]
    (ptag : ℕ → Bytes → ProbComp Bytes) :
    QueryImpl AeadMuIntSimSpec (StateT PrfHmacMuState ProbComp) := fun q =>
  match q with
  | Sum.inl pq => StateT.mk fun s => (primBaseImpl P pq) >>= fun u => pure (u, s)
  | Sum.inr mq => StateT.mk fun s => pStep P gen defer ptag mq s

def pFinish (ptag : ℕ → Bytes → ProbComp Bytes) (pending : List (ℕ × Bytes × Bytes)) :
    List (ℕ × Bytes) → ProbComp Bool
  | [] => pure false
  | (r, x) :: pts => do
    let t ← ptag r x
    let rest ← pFinish ptag pending pts
    pure (prfHmacPendingHit pending r x t || rest)

theorem sim_gOuter (defer : ℕ → Prop) [DecidablePred defer]
    (tag : ℕ → Bytes → OracleComp PrfHmacSimSpec Bytes) (ptag : ℕ → Bytes → ProbComp Bytes)
    (htag : ∀ r x c, (simulateQ (prfFullImpl P b k) (tag r x)).run c = (fun t => (t, c)) <$> ptag r x)
    {α : Type} (mx : OracleComp AeadMuIntSimSpec α) (st : PrfHmacMuState) (c : List (Bytes × Bytes)) :
    (simulateQ (gOuter P (prfEvalImpl P b k) defer tag) mx).run (st, c) =
      (fun z => (z.1, (z.2, c))) <$> (simulateQ (pOuter P gen80 defer ptag) mx).run st := by
  induction mx using OracleComp.inductionOn generalizing st with
  | pure a => simp
  | query_bind t mx ih =>
    rcases t with pq | mq
    · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind, map_bind]
      simp [gOuter, pOuter, ih]
    · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind, map_bind]
      have h := sim_gStep P b k defer tag ptag htag mq st c
      simp only [gOuter, pOuter, StateT.run_mk, gFull]
      erw [h]
      simp [ih]

theorem sim_gFinish (tag : ℕ → Bytes → OracleComp PrfHmacSimSpec Bytes)
    (ptag : ℕ → Bytes → ProbComp Bytes)
    (htag : ∀ r x c, (simulateQ (prfFullImpl P b k) (tag r x)).run c = (fun t => (t, c)) <$> ptag r x)
    (pending : List (ℕ × Bytes × Bytes)) (c : List (Bytes × Bytes)) :
    ∀ pts, (simulateQ (prfFullImpl P b k) (gFinish tag pending pts)).run c =
      (fun z => (z, c)) <$> pFinish ptag pending pts
  | [] => by simp [gFinish, pFinish]
  | (r, x) :: pts => by
    simp [gFinish, pFinish, simulateQ_bind, StateT.run_bind, htag, sim_gFinish tag ptag htag pending c pts]

end Bridge

/-- The generic hybrid in `ProbComp`. -/
noncomputable def pGame (P : Primitives) (gen : ℕ → ProbComp MessageKeys) (defer : ℕ → Prop)
    [DecidablePred defer] (ptag : ℕ → Bytes → ProbComp Bytes) (B : AeadMuIntCtxtAdv) :
    ProbComp Bool := do
  let z ← (simulateQ (pOuter P gen defer ptag) B.run).run {}
  let hit ← pFinish ptag z.2.pending (pendPts z.2.pending)
  pure (z.2.bad || hit)

theorem sim_gAfter_eq_pGame (P : Primitives) (b : Bool) (k : Bytes) (defer : ℕ → Prop)
    [DecidablePred defer]
    (tag : ℕ → Bytes → OracleComp PrfHmacSimSpec Bytes) (ptag : ℕ → Bytes → ProbComp Bytes)
    (htag : ∀ r x c, (simulateQ (prfFullImpl P b k) (tag r x)).run c =
      (fun t => (t, c)) <$> ptag r x)
    (B : AeadMuIntCtxtAdv) :
    (Prod.fst <$> (simulateQ (prfFullImpl P b k) (gAfter defer tag B)).run []) =
      pGame P gen80 defer ptag B := by
  unfold gAfter pGame
  have h1 := simulateQ_gRun P (prfEvalImpl P b k) defer tag B.run {} []
  have h2 := sim_gOuter P b k defer tag ptag htag B.run {} []
  simp only [simulateQ_bind, StateT.run_bind]
  erw [h1, h2]
  simp only [map_bind, bind_map_left, Functor.map_map]
  refine bind_congr (fun z => ?_)
  erw [sim_gFinish P b k tag ptag htag]
  simp

theorem gProb_eq_pGame (P : Primitives) (b : Bool) (defer : ℕ → Prop) [DecidablePred defer]
    (tag : ℕ → Bytes → OracleComp PrfHmacSimSpec Bytes) (ptag : Bytes → ℕ → Bytes → ProbComp Bytes)
    (htag : ∀ k r x c, (simulateQ (prfFullImpl P b k) (tag r x)).run c =
      (fun t => (t, c)) <$> ptag k r x)
    (B : AeadMuIntCtxtAdv) :
    gProb P b defer tag B =
      (𝒟[sampleBytes32 >>= fun k => pGame P gen80 defer (ptag k) B] {true}).toReal := by
  unfold gProb
  congr 3
  refine bind_congr (fun k => ?_)
  rw [← sim_gAfter_eq_pGame P b k defer tag (ptag k) (htag k) B, map_eq_bind_pure_comp]
  rfl

/-! ## Eager/lazy swap of the rank-`m` MAC key -/

theorem evalDist_bind_const_pc {α : Type} (mx : ProbComp α) (my : ProbComp Bool) :
    𝒟[mx >>= fun _ => my] = 𝒟[my] :=
  OracleComp.evalDist_bind_const mx my

def genK (m : ℕ) (k : Bytes) : ℕ → ProbComp MessageKeys := fun n =>
  if n = m then (fun mk => { mk with macKey := k }) <$> sampleMessageKeys80 else sampleMessageKeys80

theorem resample_macKey (H : MessageKeys → ProbComp Bool) :
    𝒟[sampleBytes32 >>= fun k => sampleMessageKeys80 >>= fun mk => H { mk with macKey := k }] =
      𝒟[sampleMessageKeys80 >>= H] := by
  unfold sampleMessageKeys80
  simp only [bind_assoc, pure_bind]
  rw [OracleComp.evalDist_bind_bind_swap]
  refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ck _ => ?_)
  refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun k _ => ?_)
  exact evalDist_bind_const_pc _ _

theorem pKey_support (gen : ℕ → ProbComp MessageKeys) (i : ℕ) (st : PrfHmacMuState)
    (z : (ℕ × MessageKeys) × PrfHmacMuState) (hz : z ∈ support (pKey gen i st)) :
    z.2.keys.length = st.keys.length ∨ z.2.keys.length = st.keys.length + 1 := by
  unfold pKey at hz
  cases h : st.keys.lookup i <;> simp only [h] at hz
  · simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨mk, _, rfl⟩ := hz
    simp
  · simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz; simp

theorem pEncRest_keys (P : Primitives) (defer : ℕ → Prop) [DecidablePred defer]
    (ptag : ℕ → Bytes → ProbComp Bytes) (i : ℕ) (ad pt : Bytes)
    (x : (ℕ × MessageKeys) × PrfHmacMuState) (z : Option Bytes × PrfHmacMuState)
    (hz : z ∈ support (pEncRest P defer ptag i ad pt x)) : z.2.keys = x.2.keys := by
  unfold pEncRest at hz
  split_ifs at hz
  · simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨t, _, rfl⟩ := hz
    rfl
  · simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz; rfl

theorem pForgeRest_keys (P : Primitives) (defer : ℕ → Prop) [DecidablePred defer]
    (i : ℕ) (ad ct : Bytes)
    (x : (ℕ × MessageKeys) × PrfHmacMuState) (z : Bool × PrfHmacMuState)
    (hz : z ∈ support (pForgeRest P defer i ad ct x)) : z.2.keys = x.2.keys := by
  unfold pForgeRest at hz
  split_ifs at hz <;> (simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz; rfl)

theorem pStep_support (P : Primitives) (gen : ℕ → ProbComp MessageKeys) (defer : ℕ → Prop)
    [DecidablePred defer] (ptag : ℕ → Bytes → ProbComp Bytes) (q : AeadMuIntQuery)
    (st : PrfHmacMuState) (z : aeadMuIntSpec.Range q × PrfHmacMuState)
    (hz : z ∈ support (pStep P gen defer ptag q st)) :
    st.keys.length ≤ z.2.keys.length ∧ z.2.keys.length ≤ st.keys.length + 1 := by
  rcases q with ⟨i, ad, pt⟩ | ⟨i, ad, ct⟩
  · simp only [pStep] at hz
    cases h : st.chal.lookup i <;> simp only [h] at hz
    · simp only [support_bind, Set.mem_iUnion] at hz
      obtain ⟨x, hx, hz⟩ := hz
      rw [pEncRest_keys P defer ptag i ad pt x z hz]
      rcases pKey_support gen i st x hx with h' | h' <;> omega
    · simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz; simp
  · simp only [pStep] at hz
    split_ifs at hz
    · simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz; simp
    · simp only [support_bind, Set.mem_iUnion] at hz
      obtain ⟨x, hx, hz⟩ := hz
      rw [pForgeRest_keys P defer i ad ct x z hz]
      rcases pKey_support gen i st x hx with h' | h' <;> omega

theorem pStep_congr_gen (P : Primitives) (gen gen' : ℕ → ProbComp MessageKeys) (defer : ℕ → Prop)
    [DecidablePred defer] (ptag : ℕ → Bytes → ProbComp Bytes) (q : AeadMuIntQuery)
    (st : PrfHmacMuState) (h : gen st.keys.length = gen' st.keys.length) :
    pStep P gen defer ptag q st = pStep P gen' defer ptag q st := by
  rcases q with ⟨i, ad, pt⟩ | ⟨i, ad, ct⟩ <;> simp only [pStep, pKey, h]

theorem genK_ne (m : ℕ) (k : Bytes) (n : ℕ) (h : n ≠ m) : genK m k n = gen80 n := by
  simp [genK, gen80, h]

theorem sim_genK_past (P : Primitives) (m : ℕ) (k : Bytes) (defer : ℕ → Prop) [DecidablePred defer]
    (ptag : ℕ → Bytes → ProbComp Bytes) {α : Type} (mx : OracleComp AeadMuIntSimSpec α)
    (F : α × PrfHmacMuState → ProbComp Bool) (st : PrfHmacMuState) (hst : m < st.keys.length) :
    𝒟[(simulateQ (pOuter P (genK m k) defer ptag) mx).run st >>= F] =
      𝒟[(simulateQ (pOuter P gen80 defer ptag) mx).run st >>= F] := by
  induction mx using OracleComp.inductionOn generalizing st with
  | pure a => rfl
  | query_bind t mx ih =>
    rcases t with pq | mq
    · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind, bind_assoc, pOuter, StateT.run_mk]
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun u _ => ?_)
      simp only [pure_bind]
      exact ih u st hst
    · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind, bind_assoc, pOuter, StateT.run_mk]
      rw [pStep_congr_gen P (genK m k) gen80 defer ptag mq st (genK_ne m k _ (by omega))]
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun z hz => ?_)
      have := pStep_support P gen80 defer ptag mq st z hz
      exact ih z.1 z.2 (by omega)

theorem pKeySwap (m : ℕ) (i : ℕ) (st : PrfHmacMuState) (hlen : st.keys.length = m)
    (H0 : (ℕ × MessageKeys) × PrfHmacMuState → ProbComp Bool)
    (Hk : Bytes → (ℕ × MessageKeys) × PrfHmacMuState → ProbComp Bool)
    (ha : ∀ z : (ℕ × MessageKeys) × PrfHmacMuState, z.2.keys.length ≤ m →
      𝒟[H0 z] = 𝒟[sampleBytes32 >>= fun k => Hk k z])
    (hb : ∀ k (z : (ℕ × MessageKeys) × PrfHmacMuState), m < z.2.keys.length →
      𝒟[Hk k z] = 𝒟[H0 z]) :
    𝒟[pKey gen80 i st >>= H0] = 𝒟[sampleBytes32 >>= fun k => pKey (genK m k) i st >>= Hk k] := by
  unfold pKey
  cases h : st.keys.lookup i
  · simp only [genK, hlen, ite_true, gen80, bind_assoc, pure_bind, bind_map_left]
    have e1 : 𝒟[sampleBytes32 >>= fun k => sampleMessageKeys80 >>= fun mk =>
        Hk k ((m, { mk with macKey := k }),
          { st with keys := (i, (m, { mk with macKey := k })) :: st.keys })] =
        𝒟[sampleBytes32 >>= fun k => sampleMessageKeys80 >>= fun mk =>
        H0 ((m, { mk with macKey := k }),
          { st with keys := (i, (m, { mk with macKey := k })) :: st.keys })] := by
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun k _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun mk _ => ?_)
      exact hb k _ (by simp [hlen])
    rw [e1]
    exact (resample_macKey (fun mk => H0 ((m, mk), { st with keys := (i, (m, mk)) :: st.keys }))).symm
  · simp only [pure_bind]
    exact ha _ (by simp [hlen])

theorem stepSwap (P : Primitives) (m : ℕ) (defer : ℕ → Prop) [DecidablePred defer]
    (ptag : ℕ → Bytes → ProbComp Bytes) (q : AeadMuIntQuery) (st : PrfHmacMuState)
    (hlen : st.keys.length = m)
    (G : aeadMuIntSpec.Range q × PrfHmacMuState → ProbComp Bool)
    (Gk : Bytes → aeadMuIntSpec.Range q × PrfHmacMuState → ProbComp Bool)
    (h1 : ∀ z : aeadMuIntSpec.Range q × PrfHmacMuState, z.2.keys.length ≤ m →
      𝒟[G z] = 𝒟[sampleBytes32 >>= fun k => Gk k z])
    (h2 : ∀ k (z : aeadMuIntSpec.Range q × PrfHmacMuState), m < z.2.keys.length →
      𝒟[Gk k z] = 𝒟[G z]) :
    𝒟[pStep P gen80 defer ptag q st >>= G] =
      𝒟[sampleBytes32 >>= fun k => pStep P (genK m k) defer ptag q st >>= Gk k] := by
  rcases q with ⟨i, ad, pt⟩ | ⟨i, ad, ct⟩
  · simp only [pStep]
    cases h : st.chal.lookup i
    · simp only [bind_assoc]
      refine pKeySwap m i st hlen _ _ (fun z hz => ?_) (fun k z hz => ?_)
      · rw [OracleComp.evalDist_bind_bind_swap]
        refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun w hw => ?_)
        exact h1 w (by rw [pEncRest_keys P defer ptag i ad pt z w hw]; exact hz)
      · refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun w hw => ?_)
        exact h2 k w (by rw [pEncRest_keys P defer ptag i ad pt z w hw]; exact hz)
    · simp only [pure_bind]
      exact h1 _ (by simp [hlen])
  · simp only [pStep]
    split_ifs
    · simp only [pure_bind]
      exact h1 _ (by simp [hlen])
    · simp only [bind_assoc]
      refine pKeySwap m i st hlen _ _ (fun z hz => ?_) (fun k z hz => ?_)
      · rw [OracleComp.evalDist_bind_bind_swap]
        refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun w hw => ?_)
        exact h1 w (by rw [pForgeRest_keys P defer i ad ct z w hw]; exact hz)
      · refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun w hw => ?_)
        exact h2 k w (by rw [pForgeRest_keys P defer i ad ct z w hw]; exact hz)

/-- Swaps eager sampling of MAC key `k` before the run with lazy sampling at rank `m`. -/
theorem sim_swap (P : Primitives) (m : ℕ) (defer : ℕ → Prop) [DecidablePred defer]
    (ptag : ℕ → Bytes → ProbComp Bytes) {α : Type} (mx : OracleComp AeadMuIntSimSpec α)
    (F : α × PrfHmacMuState → ProbComp Bool) (st : PrfHmacMuState) (hst : st.keys.length ≤ m) :
    𝒟[(simulateQ (pOuter P gen80 defer ptag) mx).run st >>= F] =
      𝒟[sampleBytes32 >>= fun k => (simulateQ (pOuter P (genK m k) defer ptag) mx).run st >>= F] := by
  induction mx using OracleComp.inductionOn generalizing st with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact (evalDist_bind_const_pc _ _).symm
  | query_bind t mx ih =>
    rcases t with pq | mq
    · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind, bind_assoc, pOuter, StateT.run_mk, pure_bind]
      rw [OracleComp.evalDist_bind_bind_swap]
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun u _ => ?_)
      exact ih u st hst
    · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind, bind_assoc, pOuter, StateT.run_mk]
      rcases Nat.lt_or_ge st.keys.length m with hlt | hge
      · have e : ∀ k, pStep P (genK m k) defer ptag mq st = pStep P gen80 defer ptag mq st :=
          fun k => pStep_congr_gen P _ _ defer ptag mq st (genK_ne m k _ (by omega))
        simp only [e]
        rw [OracleComp.evalDist_bind_bind_swap]
        refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun z hz => ?_)
        have := pStep_support P gen80 defer ptag mq st z hz
        exact ih z.1 z.2 (by omega)
      · refine stepSwap P m defer ptag mq st (by omega) _ _ (fun z hz => ih z.1 z.2 hz)
          (fun k z hz => sim_genK_past P m k defer ptag (mx z.1) F z.2 hz)

/-! ## Monotonicity of deferred checks -/

theorem pFinish_congr (t1 t2 : ℕ → Bytes → ProbComp Bytes) (p1 p2 : List (ℕ × Bytes × Bytes))
    (pts : List (ℕ × Bytes)) (ht : ∀ q ∈ pts, t1 q.1 q.2 = t2 q.1 q.2)
    (hp : ∀ q ∈ pts, ∀ t, prfHmacPendingHit p1 q.1 q.2 t = prfHmacPendingHit p2 q.1 q.2 t) :
    pFinish t1 p1 pts = pFinish t2 p2 pts := by
  induction pts with
  | nil => rfl
  | cons q pts ih =>
    obtain ⟨r, x⟩ := q
    simp only [pFinish]
    rw [ht (r, x) (by simp), ih (fun q hq => ht q (by simp [hq])) (fun q hq => hp q (by simp [hq]))]
    refine bind_congr (fun t => bind_congr (fun b => ?_))
    rw [hp (r, x) (by simp) t]

theorem pFinish_perm (tg : ℕ → Bytes → ProbComp Bytes) (pend : List (ℕ × Bytes × Bytes))
    {l1 l2 : List (ℕ × Bytes)} (h : l1.Perm l2) : 𝒟[pFinish tg pend l1] = 𝒟[pFinish tg pend l2] := by
  induction h with
  | nil => rfl
  | cons q _ ih =>
    obtain ⟨r, x⟩ := q
    simp only [pFinish]
    refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun t _ => ?_)
    rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete, ih]
  | swap q1 q2 l =>
    obtain ⟨r1, x1⟩ := q1
    obtain ⟨r2, x2⟩ := q2
    simp only [pFinish, bind_assoc, pure_bind]
    rw [OracleComp.evalDist_bind_bind_swap]
    refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun t1 _ => ?_)
    refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun t2 _ => ?_)
    refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun b _ => ?_)
    rw [Bool.or_left_comm]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem pFinish_sublist (tg : ℕ → Bytes → ProbComp Bytes) (pend : List (ℕ × Bytes × Bytes))
    {l1 l2 : List (ℕ × Bytes)} (h : l1.Sublist l2) :
    Pr{let b ← pFinish tg pend l1}[b = true] ≤ Pr{let b ← pFinish tg pend l2}[b = true] := by
  induction h with
  | slnil => exact le_rfl
  | @cons l₁ l₂ q _ ih =>
    obtain ⟨r, x⟩ := q
    simp only [pFinish]
    have hor : ∀ t, Pr{let b ← pFinish tg pend l₂}[b = true] ≤
        Pr{let b ← pFinish tg pend l₂ >>= fun rest =>
          (pure (prfHmacPendingHit pend r x t || rest) : ProbComp Bool)}[b = true] := by
      intro t
      conv_lhs => rw [← bind_pure (pFinish tg pend l₂)]
      refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ (fun b _ => ?_)
      simp only [prEvent_pure]
      cases b <;> simp
    calc Pr{let b ← pFinish tg pend l₁}[b = true]
        ≤ Pr{let b ← tg r x >>= fun _ => pFinish tg pend l₂}[b = true] := by
          rw [prEvent_eq_evalDist_singleton, prEvent_eq_evalDist_singleton,
            OracleComp.evalDist_bind_const, ← prEvent_eq_evalDist_singleton,
            ← prEvent_eq_evalDist_singleton]
          exact ih
      _ ≤ _ := prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ (fun t _ => hor t)
  | cons_cons q _ ih =>
    obtain ⟨r, x⟩ := q
    simp only [pFinish]
    refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ (fun t _ => ?_)
    cases hh : prfHmacPendingHit pend r x t
    · simp only [Bool.false_or, bind_pure]; exact ih
    · rw [prEvent_eq_one_of_forall_mem_support _ _ (fun y hy => by
          simp only [Bool.true_or, mem_support_bind_iff, support_pure,
            Set.mem_singleton_iff] at hy
          obtain ⟨_, _, rfl⟩ := hy; rfl)]
      rw [prEvent_eq_one_of_forall_mem_support _ _ (fun y hy => by
          simp only [Bool.true_or, mem_support_bind_iff, support_pure,
            Set.mem_singleton_iff] at hy
          obtain ⟨_, _, rfl⟩ := hy; rfl)]

theorem pFinish_true_of_mem (tg : ℕ → Bytes → ProbComp Bytes) (pend : List (ℕ × Bytes × Bytes))
    (q : ℕ × Bytes) (hq : ∀ t ∈ support (tg q.1 q.2), prfHmacPendingHit pend q.1 q.2 t = true) :
    ∀ pts : List (ℕ × Bytes), q ∈ pts → ∀ b ∈ support (pFinish tg pend pts), b = true
  | [] => by simp
  | (r, x) :: pts => by
    intro hmem b hb
    simp only [pFinish, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hb
    obtain ⟨t, ht, b', hb', rfl⟩ := hb
    rcases List.mem_cons.1 hmem with rfl | hmem
    · simp [hq t ht]
    · simp [pFinish_true_of_mem tg pend q hq pts hmem b' hb']

/-! ## One-sided couplings -/

/-- One-sided coupling: related outcomes can be post-processed so that `Pr[true]` only grows. -/
def CplLe {α β : Type} (R : α → β → Prop) (mx : ProbComp α) (my : ProbComp β) : Prop :=
  ∀ (FL : α → ProbComp Bool) (FR : β → ProbComp Bool),
    (∀ a b, R a b → Pr{let x ← FL a}[x = true] ≤ Pr{let x ← FR b}[x = true]) →
      Pr{let x ← mx >>= FL}[x = true] ≤ Pr{let x ← my >>= FR}[x = true]

theorem CplLe_pure {α β : Type} {R : α → β → Prop} {a : α} {b : β} (h : R a b) :
    CplLe R (pure a) (pure b) := by
  intro FL FR hF
  simpa only [pure_bind] using hF a b h

theorem CplLe_bind {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}
    {mx : ProbComp α} {my : ProbComp β} {f : α → ProbComp γ} {g : β → ProbComp δ}
    (h : CplLe R mx my) (hfg : ∀ a b, R a b → CplLe S (f a) (g b)) :
    CplLe S (mx >>= f) (my >>= g) := by
  intro FL FR hF
  rw [bind_assoc, bind_assoc]
  exact h (fun a => f a >>= FL) (fun b => g b >>= FR) (fun a b hab => hfg a b hab FL FR hF)

theorem CplLe_same {α β γ : Type} {R : β → γ → Prop} (mx : ProbComp α)
    {f : α → ProbComp β} {g : α → ProbComp γ}
    (h : ∀ a ∈ support mx, CplLe R (f a) (g a)) : CplLe R (mx >>= f) (mx >>= g) := by
  intro FL FR hF
  rw [bind_assoc, bind_assoc]
  exact prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ (fun a ha => h a ha FL FR hF)

theorem CplLe_simulateQ {ι : Type} {spec : OracleSpec.{0, 0} ι} {σ₁ σ₂ α : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ ProbComp)) (impl₂ : QueryImpl spec (StateT σ₂ ProbComp))
    (I : σ₁ → σ₂ → Prop)
    (himpl : ∀ (t : ι) (s₁ : σ₁) (s₂ : σ₂), I s₁ s₂ →
      CplLe (fun p q => p.1 = q.1 ∧ I p.2 q.2) ((impl₁ t).run s₁) ((impl₂ t).run s₂))
    (mx : OracleComp spec α) :
    ∀ (s₁ : σ₁) (s₂ : σ₂), I s₁ s₂ →
      CplLe (fun p q => p.1 = q.1 ∧ I p.2 q.2)
        ((simulateQ impl₁ mx).run s₁) ((simulateQ impl₂ mx).run s₂) := by
  induction mx using OracleComp.inductionOn with
  | pure a =>
    intro s₁ s₂ hs
    simp only [simulateQ_pure, StateT.run_pure]
    exact CplLe_pure ⟨rfl, hs⟩
  | query_bind t mx ih =>
    intro s₁ s₂ hs
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    refine CplLe_bind (himpl t s₁ s₂ hs) ?_
    rintro ⟨u₁, s₁'⟩ ⟨u₂, s₂'⟩ ⟨h1, h2⟩
    simp only at h1 h2
    subst h1
    exact ih u₁ s₁' s₂' h2

/-! ## Coupling invariant -/

def fixMk (m : ℕ) (k : Bytes) (e : ℕ × MessageKeys) : MessageKeys :=
  if e.1 = m then { e.2 with macKey := k } else e.2

def fixE (m : ℕ) (k : Bytes) (e : ℕ × MessageKeys) : ℕ × MessageKeys := (e.1, fixMk m k e)

def fixK (m : ℕ) (k : Bytes) (l : List (ℕ × (ℕ × MessageKeys))) : List (ℕ × (ℕ × MessageKeys)) :=
  l.map (fun p => (p.1, fixE m k p.2))

theorem lookup_fixK (m : ℕ) (k : Bytes) (i : ℕ) :
    ∀ l : List (ℕ × (ℕ × MessageKeys)), (fixK m k l).lookup i = (l.lookup i).map (fixE m k)
  | [] => rfl
  | (a, e) :: l => by
    have ih := lookup_fixK m k i l
    by_cases h : i = a
    · subst h; simp [fixK]
    · have h' : (i == a) = false := by simpa using h
      simp only [fixK, List.map_cons, List.lookup_cons, h'] at ih ⊢
      exact ih

theorem length_fixK (m : ℕ) (k : Bytes) (l : List (ℕ × (ℕ × MessageKeys))) :
    (fixK m k l).length = l.length := by simp [fixK]

/-- Invariant between the left (`unifTag`, real at rank `m`) and right (`HMAC_k` deferred at
    rank `m`) states. -/
structure HBInv (P : Primitives) (m : ℕ) (k : Bytes) (sL sR : PrfHmacMuState) : Prop where
  chal : sL.chal = sR.chal
  keys : sL.keys = fixK m k sR.keys
  pend : sL.pending = sR.pending.filter (fun e => decide (e.1 < m))
  bad : sL.bad = true → sR.bad = true ∨
    ∃ e ∈ sR.pending, e.1 = m ∧ e.2.2 = (hmacSha256Ref P k e.2.1).take 8

theorem hit_filter_lt (pend : List (ℕ × Bytes × Bytes)) (m r : ℕ) (hr : r < m) (x t : Bytes) :
    prfHmacPendingHit (pend.filter (fun e => decide (e.1 < m))) r x t =
      prfHmacPendingHit pend r x t := by
  unfold prfHmacPendingHit
  rw [List.any_filter]
  congr 1; funext e
  by_cases h : e.1 = r
  · simp [h, hr]
  · have h' : (e.1 == r) = false := by simpa using h
    simp [h']

theorem enc_eq (P : Primitives) (hP : WellFormedPrimitivesδ P) (mk : MessageKeys) (k ad pt : Bytes) :
    P.aeadEnc { mk with macKey := k } ad pt =
      etmBody (P.aeadEnc mk ad pt) ++
        (hmacSha256Ref P k (aeadMacInput ad (etmBody (P.aeadEnc mk ad pt)))).take 8 := by
  have hb : ∀ mk' : MessageKeys, etmBody (P.aeadEnc mk' ad pt) =
      aes256CbcEncRef P mk'.cipherKey mk'.iv pt := by
    intro mk'
    rw [hP.aeadEnc_eq_ref]
    simp [aes256CbcHmacEncRef, etmBody, hmacSha256Ref_length]
  rw [hb mk, hP.aeadEnc_eq_ref]
  rfl

theorem dec_tag (P : Primitives) (hP : WellFormedPrimitivesδ P) (mk : MessageKeys) (ad ct : Bytes)
    (h : (P.aeadDec mk ad ct).isSome = true) :
    etmTag ct = (hmacSha256Ref P mk.macKey (aeadMacInput ad (etmBody ct))).take 8 := by
  rw [hP.aeadDec_eq_ref] at h
  unfold aes256CbcHmacDecRef at h
  simp only [ge_iff_le] at h
  split_ifs at h with h1 h2
  all_goals first | (simp at h) | (simp only [beq_iff_eq] at *; simpa [etmTag, etmBody] using h2)

/-! ## Per-query couplings -/

def uT : ℕ → Bytes → ProbComp Bytes := fun _ _ => sampleBytes32

def pT (P : Primitives) (m : ℕ) (k : Bytes) : ℕ → Bytes → ProbComp Bytes := fun r x =>
  if r < m then sampleBytes32 else pure (hmacSha256Ref P k x)

section Steps

variable (P : Primitives) (hP : WellFormedPrimitivesδ P) (m : ℕ) (k : Bytes)
  (D : ℕ → Prop) [DecidablePred D] (hD : ∀ r, D r ↔ r < m)

theorem key_cpl (i : ℕ) (sL sR : PrfHmacMuState) (hI : HBInv P m k sL sR) :
    CplLe (fun zL zR => zL.1 = fixE m k zR.1 ∧ HBInv P m k zL.2 zR.2)
      (pKey (genK m k) i sL) (pKey gen80 i sR) := by
  have hl : sL.keys.lookup i = (sR.keys.lookup i).map (fixE m k) := by
    rw [hI.keys, lookup_fixK]
  have hlen : sL.keys.length = sR.keys.length := by rw [hI.keys, length_fixK]
  unfold pKey
  cases h : sR.keys.lookup i with
  | some e =>
    rw [h] at hl
    simp only [Option.map_some] at hl
    rw [hl]
    exact CplLe_pure ⟨rfl, hI⟩
  | none =>
    rw [h] at hl
    simp only [Option.map_none] at hl
    rw [hl]
    simp only [hlen]
    by_cases hm : sR.keys.length = m
    · simp only [genK, gen80, hm, ite_true, bind_map_left]
      refine CplLe_same _ (fun mk _ => CplLe_pure ⟨?_, ?_⟩)
      · simp [fixE, fixMk]
      · exact ⟨hI.chal, by simp [hI.keys, fixK, fixE, fixMk], hI.pend, hI.bad⟩
    · simp only [genK, gen80, hm, ite_false]
      refine CplLe_same _ (fun mk _ => CplLe_pure ⟨?_, ?_⟩)
      · simp [fixE, fixMk, hm]
      · exact ⟨hI.chal, by simp [hI.keys, fixK, fixE, fixMk, hm], hI.pend, hI.bad⟩

include hP hD in
theorem enc_cpl (i : ℕ) (ad pt : Bytes) (zL zR : (ℕ × MessageKeys) × PrfHmacMuState)
    (h1 : zL.1 = fixE m k zR.1) (hI : HBInv P m k zL.2 zR.2) :
    CplLe (fun p q => p.1 = q.1 ∧ HBInv P m k p.2 q.2)
      (pEncRest P D uT i ad pt zL) (pEncRest P (fun r => r ≤ m) (pT P m k) i ad pt zR) := by
  obtain ⟨⟨r, mk⟩, sR⟩ := zR
  obtain ⟨eL, sL⟩ := zL
  simp only [fixE] at h1
  subst h1
  simp only at hI
  rcases Nat.lt_trichotomy r m with hr | hr | hr
  · have hfix : fixMk m k (r, mk) = mk := by simp [fixMk, hr.ne]
    simp only [pEncRest, hfix, (hD r).2 hr, hr.le, ite_true, uT, pT, hr]
    refine CplLe_same _ (fun t _ => CplLe_pure ⟨rfl, ?_⟩)
    refine ⟨by simp [hI.chal], hI.keys, ?_, ?_⟩
    · simp only [hI.pend, List.filter_filter]
      congr 1; funext e
      exact Bool.and_comm _ _
    · intro hb
      simp only [Bool.or_eq_true] at hb
      rcases hb with hb | hb
      · rcases hI.bad hb with hb' | ⟨e, he, hem, het⟩
        · left; simp [hb']
        · right
          refine ⟨e, List.mem_filter.2 ⟨he, ?_⟩, hem, het⟩
          have : e.1 ≠ r := by omega
          simp [this]
      · left
        rw [hI.pend, hit_filter_lt _ m r hr] at hb
        simp [hb]
  · subst hr
    have hfix : fixMk r k (r, mk) = { mk with macKey := k } := by simp [fixMk]
    have hD' : ¬ D r := fun h => lt_irrefl r ((hD r).1 h)
    simp only [pEncRest, hfix, hD', ite_false, le_refl, ite_true, pT, lt_irrefl, pure_bind]
    refine CplLe_pure ⟨by rw [enc_eq P hP], ?_⟩
    refine ⟨by simp only; rw [enc_eq P hP, hI.chal], hI.keys, ?_, ?_⟩
    · simp only [hI.pend, List.filter_filter]
      congr 1; funext e
      by_cases he : e.1 < r
      · simp [he, he.ne]
      · simp [he]
    · intro hb
      rcases hI.bad hb with hb' | ⟨e, he, hem, het⟩
      · left; simp [hb']
      · by_cases hx : e.2.1 = aeadMacInput ad (etmBody (P.aeadEnc mk ad pt))
        · left
          simp only [Bool.or_eq_true]
          right
          unfold prfHmacPendingHit
          rw [List.any_eq_true]
          refine ⟨e, he, ?_⟩
          rw [hx] at het
          simp [hem, hx, het]
        · right
          refine ⟨e, List.mem_filter.2 ⟨he, ?_⟩, hem, het⟩
          simp [hx]
  · have hfix : fixMk m k (r, mk) = mk := by simp [fixMk, hr.ne']
    have hD' : ¬ D r := fun h => by have := (hD r).1 h; omega
    have hle : ¬ r ≤ m := by omega
    simp only [pEncRest, hfix, hD', hle, ite_false]
    exact CplLe_pure ⟨rfl, by simp [hI.chal], hI.keys, hI.pend, hI.bad⟩

include hP hD in
theorem forge_cpl (i : ℕ) (ad ct : Bytes) (zL zR : (ℕ × MessageKeys) × PrfHmacMuState)
    (h1 : zL.1 = fixE m k zR.1) (hI : HBInv P m k zL.2 zR.2) :
    CplLe (fun p q => p.1 = q.1 ∧ HBInv P m k p.2 q.2)
      (pForgeRest P D i ad ct zL) (pForgeRest P (fun r => r ≤ m) i ad ct zR) := by
  obtain ⟨⟨r, mk⟩, sR⟩ := zR
  obtain ⟨eL, sL⟩ := zL
  simp only [fixE] at h1
  subst h1
  simp only at hI
  simp only [pForgeRest, hI.chal]
  by_cases hc : pFresh sR.chal i ad ct = true ∧ 24 ≤ ct.length
  swap
  · simp only [hc, ite_false]
    exact CplLe_pure ⟨rfl, hI⟩
  simp only [hc, and_self, ite_true]
  rcases Nat.lt_trichotomy r m with hr | hr | hr
  · simp only [(hD r).2 hr, hr.le, ite_true]
    refine CplLe_pure ⟨rfl, rfl, hI.keys, ?_, ?_⟩
    · simp [hI.pend, hr]
    · intro hb
      rcases hI.bad hb with hb' | ⟨e, he, hem, het⟩
      · left; exact hb'
      · right; exact ⟨e, List.mem_cons_of_mem _ he, hem, het⟩
  · subst hr
    have hD' : ¬ D r := fun h => lt_irrefl r ((hD r).1 h)
    simp only [hD', le_refl, ite_false, ite_true]
    refine CplLe_pure ⟨rfl, rfl, hI.keys, ?_, ?_⟩
    · simp [hI.pend]
    · intro hb
      simp only [Bool.or_eq_true] at hb
      rcases hb with hb | hb
      · rcases hI.bad hb with hb' | ⟨e, he, hem, het⟩
        · left; exact hb'
        · right; exact ⟨e, List.mem_cons_of_mem _ he, hem, het⟩
      · right
        refine ⟨_, List.mem_cons_self, rfl, ?_⟩
        have := dec_tag P hP _ ad ct hb
        simpa [fixMk] using this
  · have hfix : fixMk m k (r, mk) = mk := by simp [fixMk, hr.ne']
    have hD' : ¬ D r := fun h => by have := (hD r).1 h; omega
    have hle : ¬ r ≤ m := by omega
    simp only [hfix, hD', hle, ite_false]
    refine CplLe_pure ⟨rfl, rfl, hI.keys, hI.pend, ?_⟩
    intro hb
    simp only [Bool.or_eq_true] at hb
    rcases hb with hb | hb
    · rcases hI.bad hb with hb' | h'
      · left; simp [hb']
      · right; exact h'
    · left; simp [hb]

include hP hD in
theorem step_cpl (q : AeadMuIntQuery) (sL sR : PrfHmacMuState) (hI : HBInv P m k sL sR) :
    CplLe (fun p q => p.1 = q.1 ∧ HBInv P m k p.2 q.2)
      (pStep P (genK m k) D uT q sL) (pStep P gen80 (fun r => r ≤ m) (pT P m k) q sR) := by
  rcases q with ⟨i, ad, pt⟩ | ⟨i, ad, ct⟩
  · simp only [pStep, hI.chal]
    cases sR.chal.lookup i with
    | some _ => exact CplLe_pure ⟨rfl, hI⟩
    | none =>
      exact CplLe_bind (key_cpl P m k i sL sR hI)
        (fun zL zR h => enc_cpl P hP m k D hD i ad pt zL zR h.1 h.2)
  · simp only [pStep, hI.chal]
    split_ifs
    · exact CplLe_pure ⟨rfl, hI⟩
    · exact CplLe_bind (key_cpl P m k i sL sR hI)
        (fun zL zR h => forge_cpl P hP m k D hD i ad ct zL zR h.1 h.2)

include hP hD in
theorem outer_cpl (t : AeadMuIntSimSpec.Domain) (sL sR : PrfHmacMuState) (hI : HBInv P m k sL sR) :
    CplLe (fun p q => p.1 = q.1 ∧ HBInv P m k p.2 q.2)
      ((pOuter P (genK m k) D uT t).run sL) ((pOuter P gen80 (fun r => r ≤ m) (pT P m k) t).run sR) := by
  rcases t with pq | mq
  · simp only [pOuter, StateT.run_mk]
    exact CplLe_same _ (fun u _ => CplLe_pure ⟨rfl, hI⟩)
  · simp only [pOuter, StateT.run_mk]
    exact step_cpl P hP m k D hD mq sL sR hI

theorem finish_le (sL sR : PrfHmacMuState) (hI : HBInv P m k sL sR) :
    Pr{let b ← (pFinish uT sL.pending (pendPts sL.pending) >>= fun hit =>
        (pure (sL.bad || hit) : ProbComp Bool))}[b = true] ≤
      Pr{let b ← (pFinish (pT P m k) sR.pending (pendPts sR.pending) >>= fun hit =>
        (pure (sR.bad || hit) : ProbComp Bool))}[b = true] := by
  have rhs_one : ∀ (h : ∀ y ∈ support (pFinish (pT P m k) sR.pending (pendPts sR.pending) >>=
      fun hit => (pure (sR.bad || hit) : ProbComp Bool)), y = true),
      Pr{let b ← (pFinish uT sL.pending (pendPts sL.pending) >>= fun hit =>
        (pure (sL.bad || hit) : ProbComp Bool))}[b = true] ≤
      Pr{let b ← (pFinish (pT P m k) sR.pending (pendPts sR.pending) >>= fun hit =>
        (pure (sR.bad || hit) : ProbComp Bool))}[b = true] := fun h => by
    rw [prEvent_eq_one_of_forall_mem_support _ _ h]
    exact prEvent_le_one (m := ProbComp) _
  by_cases hRb : sR.bad = true
  · refine rhs_one (fun y hy => ?_)
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hy
    obtain ⟨hit, _, rfl⟩ := hy
    simp [hRb]
  by_cases hLb : sL.bad = true
  · rcases hI.bad hLb with h | ⟨e, he, hem, het⟩
    · exact absurd h hRb
    refine rhs_one (fun y hy => ?_)
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hy
    obtain ⟨hit, hhit, rfl⟩ := hy
    have hq : ∀ t ∈ support (pT P m k e.1 e.2.1), prfHmacPendingHit sR.pending e.1 e.2.1 t = true := by
      intro t ht
      simp only [pT, hem, lt_irrefl, ite_false, support_pure, Set.mem_singleton_iff] at ht
      subst ht
      unfold prfHmacPendingHit
      rw [List.any_eq_true]
      exact ⟨e, he, by simp [hem, het]⟩
    have hmem : (e.1, e.2.1) ∈ pendPts sR.pending := by
      simp only [pendPts, List.mem_dedup, List.mem_map]
      exact ⟨e, he, rfl⟩
    simp [pFinish_true_of_mem (pT P m k) sR.pending (e.1, e.2.1) hq _ hmem hit hhit]
  simp only [Bool.not_eq_true] at hRb hLb
  simp only [hRb, hLb, Bool.false_or, bind_pure]
  rw [hI.pend]
  have hlt : ∀ q ∈ pendPts (sR.pending.filter (fun e => decide (e.1 < m))), q.1 < m := by
    intro q hq
    simp only [pendPts, List.mem_dedup, List.mem_map, List.mem_filter, decide_eq_true_eq] at hq
    obtain ⟨e, ⟨_, he⟩, rfl⟩ := hq
    exact he
  have hc : pFinish uT (sR.pending.filter (fun e => decide (e.1 < m)))
      (pendPts (sR.pending.filter (fun e => decide (e.1 < m)))) =
      pFinish (pT P m k) sR.pending (pendPts (sR.pending.filter (fun e => decide (e.1 < m)))) :=
    pFinish_congr _ _ _ _ _ (fun q hq => by simp [uT, pT, hlt q hq])
      (fun q hq t => hit_filter_lt _ m q.1 (hlt q hq) q.2 t)
  rw [hc]
  have hsub : (pendPts (sR.pending.filter (fun e => decide (e.1 < m)))).Subperm
      (pendPts sR.pending) := by
    refine List.Nodup.subperm (List.nodup_dedup _) (fun q hq => ?_)
    simp only [pendPts, List.mem_dedup, List.mem_map, List.mem_filter] at hq ⊢
    obtain ⟨e, ⟨he, _⟩, rfl⟩ := hq
    exact ⟨e, he, rfl⟩
  obtain ⟨l, hperm, hsl⟩ := hsub
  rw [prEvent_eq_evalDist_singleton, ← pFinish_perm _ _ hperm, ← prEvent_eq_evalDist_singleton]
  exact pFinish_sublist _ _ hsl

end Steps

/-! ## Main theorem -/

theorem gProb_unif_le_hmac (P : Primitives) (hP : WellFormedPrimitivesδ P) (B : AeadMuIntCtxtAdv)
    (m : ℕ) (D : ℕ → Prop) [DecidablePred D] (hD : ∀ r, D r ↔ r < m) :
    gProb P false D unifTag B ≤ gProb P true (fun r => r ≤ m) (prfHmacTagQ m) B := by
  have hu : ∀ (k : Bytes) r x c, (simulateQ (prfFullImpl P false k) (unifTag r x)).run c =
      (fun t => (t, c)) <$> (fun (_ : Bytes) => uT) k r x := by
    intro k r x c
    simp [unifTag, prfHmacUnif, prfFullImpl, simulateQ_embedPrim_run, simulateQ_embedUnif, uT]
  have hp : ∀ (k : Bytes) r x c, (simulateQ (prfFullImpl P true k) (prfHmacTagQ m r x)).run c =
      (fun t => (t, c)) <$> pT P m k r x := by
    intro k r x c
    unfold prfHmacTagQ pT
    split_ifs
    · simp [prfHmacUnif, prfFullImpl, simulateQ_embedPrim_run, simulateQ_embedUnif]
    · simp [prfHmacEvalQ, prfFullImpl, prfEvalImpl]
  rw [gProb_eq_pGame P false D unifTag (fun _ => uT) hu B,
    gProb_eq_pGame P true _ (prfHmacTagQ m) (pT P m) hp B]
  refine ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top (evalDist_apply_le_one _ _)) ?_
  rw [OracleComp.evalDist_bind_const]
  unfold pGame
  rw [sim_swap P m D uT B.run _ {} (by simp)]
  rw [← prEvent_eq_evalDist_singleton, ← prEvent_eq_evalDist_singleton]
  refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ (fun k _ => ?_)
  exact CplLe_simulateQ (pOuter P (genK m k) D uT) (pOuter P gen80 (fun r => r ≤ m) (pT P m k))
    (HBInv P m k) (fun t sL sR hI => outer_cpl P hP m k D hD t sL sR hI) B.run {} {}
    ⟨rfl, rfl, rfl, fun h => by simp at h⟩ _ _
    (fun a b h => finish_le P m k a.2 b.2 h.2)

end SignalPqxdh.Security

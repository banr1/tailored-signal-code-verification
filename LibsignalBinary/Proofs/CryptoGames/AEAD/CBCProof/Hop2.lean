/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCLazy
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EtM
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EtMDefs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Lazy
public import LibsignalBinary.Specifications.CryptoGames.Primitives

/-!
# Hop 2 of `cbc_indcpa`: One-Query Ideal Hybrid (`cbc_branch_true_le`)

**Checked by Lean.**

Reduces the distance between the ideal PRF branch of `cbcRed encode A` and the ideal IND-CPA branch
of `cbcScheme E encode` to the single-query distance between `cbcLazy (encode m)` and
`$ᵗ (List.Vector Block n)`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory
open CryptoGames.AEADScheme.EtMProof
namespace CryptoGames.CBC.Hop2

variable {M C : Type}

private def prfImpl (E : AesKey → Block → Block) :
    QueryImpl (unifSpec + MACScheme.prfSpec Block Block)
      (StateT (MACScheme.PRFState AesKey Block Block) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (MACScheme.PRFState AesKey Block Block) ProbComp) + MACScheme.prfEval (blockPRF E)

private def implOnce1 {M C : Type} (enc : M → ProbComp C) :
    QueryImpl (unifSpec + CipherScheme.indcpaSpec M C) (StateT Bool ProbComp)
  | .inl k => AEADScheme.EtMProof.coin k
  | .inr m => StateT.mk fun qd =>
      if qd then pure (none, true)
      else (fun c => (some c, true)) <$> enc m

private theorem ideal_indcpa_eq_implOnce1 {n : ℕ} (E : AesKey → Block → Block)
    (encode : M → List.Vector Block n)
    {α : Type} (oa : OracleComp (unifSpec + CipherScheme.indcpaSpec M (List.Vector Block n)) α)
    (s : CipherScheme.INDCPAState (AesKey × Block)) (hb : s.b = true) :
    (simulateQ (implOnce1 (fun _ => $ᵗ (List.Vector Block n))) oa).run s.queried =
      Prod.map id (fun z => z.queried) <$>
        (simulateQ (cImpl (cbcScheme E encode)) oa).run s := by
  refine run_map (implOnce1 (fun _ => $ᵗ (List.Vector Block n))) (cImpl (cbcScheme E encode))
    (fun z => z.queried) (fun z => z.b = true) (fun t z hz => ?_) oa s hb
  rcases t with k | m
  · refine ⟨by simp [implOnce1, cImpl, AEADScheme.EtMProof.coin], fun w hw => ?_⟩
    have hw' : w ∈ support ((AEADScheme.EtMProof.coin k : StateT _ ProbComp _).run z) := by
      simpa [cImpl] using hw
    rw [mem_support_coin hw']; exact hz
  · by_cases hq : z.queried = true
    · refine ⟨by simp [implOnce1, cImpl, CipherScheme.indcpaEncrypt, hq], fun w hw => ?_⟩
      simp [cImpl, CipherScheme.indcpaEncrypt, hq] at hw
      subst hw; exact hz
    · have hqf : z.queried = false := Bool.eq_false_iff.mpr hq
      refine ⟨?_, fun w hw => ?_⟩
      · simp [implOnce1, cImpl, CipherScheme.indcpaEncrypt, hqf, hz, map_eq_bind_pure_comp]
      · simp [cImpl, CipherScheme.indcpaEncrypt, hqf, hz] at hw
        rcases hw with ⟨_, _, rfl⟩; rfl

private theorem evalDist_cbc_branch_true {n : ℕ} (E : AesKey → Block → Block)
    (encode : M → List.Vector Block n)
    (A : CipherScheme.INDCPAAdversary M (List.Vector Block n)) :
    𝒟[(cbcScheme E encode).branch true A] =
      𝒟[(simulateQ (implOnce1 (fun _ => $ᵗ (List.Vector Block n))) A).run' false] := by
  rw [cipher_branch_eq]
  have h : ∀ key : AesKey × Block,
      (simulateQ (cImpl (cbcScheme E encode)) A).run' { key, b := true } =
        (simulateQ (implOnce1 (fun _ => $ᵗ (List.Vector Block n))) A).run' false := by
    intro key
    have h1 := congrArg (Prod.fst <$> ·)
      (ideal_indcpa_eq_implOnce1 E encode A { key, b := true } rfl)
    simpa [StateT.run'_eq, Functor.map_map] using h1.symm
  simp only [h, OracleComp.evalDist_bind_const]

private theorem prfEval_eq_lazyStep (E : AesKey → Block → Block) (x : Block)
    (pst : MACScheme.PRFState AesKey Block Block) (hb : pst.b = true) :
    (simulateQ (prfImpl E) (MACScheme.evalQuery x)).run pst =
      Prod.map id (fun tbl => { pst with table := tbl }) <$> (lazyStep x).run pst.table := by
  rcases pst with ⟨key, b, tbl⟩
  subst hb
  cases hlk : tbl.lookup x with
  | some t =>
    simp [prfImpl, MACScheme.evalQuery, MACScheme.prfEval, lazyStep, hlk]
  | none =>
    simp [prfImpl, MACScheme.evalQuery, MACScheme.prfEval, lazyStep, hlk,
      map_eq_bind_pure_comp]

private theorem simulateQ_prfImpl_cbcM_true {n : ℕ} (E : AesKey → Block → Block)
    (iv : Block) (P : List.Vector Block n)
    (pst : MACScheme.PRFState AesKey Block Block) (hb : pst.b = true) :
    (simulateQ (prfImpl E) (cbcM MACScheme.evalQuery iv P)).run pst =
      Prod.map id (fun tbl => { pst with table := tbl }) <$> (cbcM lazyStep iv P).run pst.table := by
  induction n generalizing iv pst with
  | zero =>
    simp [cbcM]
  | succ n ih =>
    simp only [cbcM, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
    rw [prfEval_eq_lazyStep E (P.head ^^^ iv) pst hb, bind_map_left, map_bind]
    refine bind_congr fun ⟨c, tbl'⟩ => ?_
    dsimp only [Prod.map_apply, id_eq]
    rw [ih c P.tail { pst with table := tbl' } hb, map_bind]
    simp

private theorem ideal_prf_eq_implOnce1 {n : ℕ} (E : AesKey → Block → Block)
    (encode : M → List.Vector Block n)
    {α : Type} (oa : OracleComp (unifSpec + CipherScheme.indcpaSpec M (List.Vector Block n)) α) :
    ∀ (qd : Bool) (pst : MACScheme.PRFState AesKey Block Block),
      (qd = false → pst.table = []) → pst.b = true →
      (fun w => w.1.1) <$>
        (simulateQ (prfImpl E) ((simulateQ (cbcRedImpl encode) oa).run qd)).run pst =
      Prod.fst <$> (simulateQ (implOnce1 (fun m => cbcLazy (encode m))) oa).run qd := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro qd pst _ _
    simp
  | query_bind t cont ih =>
    intro qd pst hqd hpb
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    rcases t with k | msg
    · have hL : (simulateQ (prfImpl E) ((cbcRedImpl encode (.inl k)).run qd)).run pst =
          (liftM (OracleSpec.query (spec := unifSpec) k) : ProbComp (Fin (k + 1))) >>=
            fun u => pure ((u, qd), pst) := by
        simp [cbcRedImpl, prfImpl]
      have hR : (implOnce1 (fun m => cbcLazy (encode m)) (.inl k)).run qd =
          (liftM (OracleSpec.query (spec := unifSpec) k) : ProbComp (Fin (k + 1))) >>=
            fun u => pure (u, qd) := by
        simp [implOnce1, AEADScheme.EtMProof.coin]
      rw [hL, hR]
      simp only [bind_assoc, pure_bind]
      exact bind_congr fun u => ih u qd pst hqd hpb
    · cases qd
      · have htbl : pst.table = [] := hqd rfl
        have hrun : (cbcRedImpl encode (.inr msg)).run false =
            (do
              let iv ← liftM ($ᵗ Block : ProbComp Block)
              let c ← cbcM MACScheme.evalQuery iv (encode msg)
              pure (some c, true)) := by
          simp [cbcRedImpl]
        have hlift : (simulateQ (prfImpl E)
            (liftM ($ᵗ Block : ProbComp Block) :
              OracleComp (unifSpec + MACScheme.prfSpec Block Block) Block)).run pst =
            ($ᵗ Block) >>= fun iv => pure (iv, pst) := by
          simp [prfImpl, QueryImpl.simulateQ_add_liftM_left, simulateQ_liftTarget]
        have hL : (simulateQ (prfImpl E) ((cbcRedImpl encode (.inr msg)).run false)).run pst =
            ($ᵗ Block) >>= fun iv =>
              (fun ct : List.Vector Block n × List (Block × Block) =>
                ((some ct.1, true), { pst with table := ct.2 })) <$>
                (cbcM lazyStep iv (encode msg)).run [] := by
          rw [hrun]
          simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, hlift,
            bind_assoc, pure_bind]
          refine bind_congr fun iv => ?_
          rw [simulateQ_prfImpl_cbcM_true E iv (encode msg) pst hpb, htbl, bind_map_left]
          simp [map_eq_bind_pure_comp]
        have hR : (implOnce1 (fun m => cbcLazy (encode m)) (.inr msg)).run false =
            ($ᵗ Block) >>= fun iv =>
              (fun ct : List.Vector Block n × List (Block × Block) => (some ct.1, true)) <$>
                (cbcM lazyStep iv (encode msg)).run [] := by
          simp [implOnce1, cbcLazy, StateT.run'_eq, map_eq_bind_pure_comp, bind_assoc]
        rw [hL, hR]
        simp only [bind_assoc, bind_map_left]
        refine bind_congr fun iv => bind_congr fun ⟨c, tbl'⟩ => ?_
        dsimp only
        exact ih (some c) true { pst with table := tbl' } (by intro h; cases h) hpb
      · have hL : (simulateQ (prfImpl E) ((cbcRedImpl encode (.inr msg)).run true)).run pst =
            pure ((none, true), pst) := by
          simp [cbcRedImpl]
        have hR : (implOnce1 (fun m => cbcLazy (encode m)) (.inr msg)).run true =
            pure (none, true) := by
          simp [implOnce1]
        rw [hL, hR, pure_bind, pure_bind]
        exact ih none true pst (by intro h; cases h) hpb

private theorem evalDist_prf_branch_true {n : ℕ} (E : AesKey → Block → Block)
    (encode : M → List.Vector Block n)
    (A : CipherScheme.INDCPAAdversary M (List.Vector Block n)) :
    𝒟[(blockPRF E).branch true (cbcRed encode A)] =
      𝒟[(simulateQ (implOnce1 (fun m => cbcLazy (encode m))) A).run' false] := by
  unfold MACScheme.branch
  have h : ∀ key : AesKey,
      (simulateQ (prfImpl E) (cbcRed encode A)).run' { key, b := true } =
        (simulateQ (implOnce1 (fun m => cbcLazy (encode m))) A).run' false := by
    intro key
    unfold cbcRed
    have hl := ideal_prf_eq_implOnce1 E encode A false { key, b := true } (fun _ => rfl) rfl
    simpa [StateT.run'_eq, simulateQ_map, Functor.map_map] using hl
  change 𝒟[do let key ← $ᵗ AesKey
              (simulateQ (prfImpl E) (cbcRed encode A)).run' { key, b := true }] = _
  simp only [h, OracleComp.evalDist_bind_const]

private theorem implOnce1_true_eq (enc₁ enc₂ : M → ProbComp C)
    {α : Type} (oa : OracleComp (unifSpec + CipherScheme.indcpaSpec M C) α) :
    (simulateQ (implOnce1 enc₁) oa).run true = (simulateQ (implOnce1 enc₂) oa).run true := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t cont ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    rcases t with k | m
    · simp only [implOnce1]
      refine bind_congr_of_forall_mem_support _ fun z hz => ?_
      rw [mem_support_coin hz]
      exact ih z.1
    · simp only [implOnce1, StateT.run_mk, ↓reduceIte, pure_bind]
      exact ih none

private theorem implOnce1_false_le {n : ℕ} (encode : M → List.Vector Block n) (ε : ℝ≥0∞)
    (h : ∀ (m : M) (F : List.Vector Block n → ProbComp Bool),
      𝒟[cbcLazy (encode m) >>= F].boolDist 𝒟[$ᵗ (List.Vector Block n) >>= F] ≤ ε)
    (oa : OracleComp (unifSpec + CipherScheme.indcpaSpec M (List.Vector Block n)) Bool)
    (b : Bool) :
    𝒟[(simulateQ (implOnce1 (fun m => cbcLazy (encode m))) oa).run' false] {b} ≤
      𝒟[(simulateQ (implOnce1 (fun _ => $ᵗ (List.Vector Block n))) oa).run' false] {b} + ε := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    simp
  | query_bind t cont ih =>
    simp only [StateT.run'_eq, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
    rcases t with k | m
    · have hcoin (enc : M → ProbComp (List.Vector Block n)) :
          (implOnce1 enc (.inl k)).run false =
            (liftM (OracleSpec.query (spec := unifSpec) k) : ProbComp (Fin (k + 1))) >>=
              fun u => pure (u, false) := by
        simp [implOnce1, AEADScheme.EtMProof.coin]
      simp only [hcoin, bind_assoc, pure_bind]
      rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete,
        Measure.bind_apply (measurableSet_singleton b) Measurable.of_discrete.aemeasurable,
        Measure.bind_apply (measurableSet_singleton b) Measurable.of_discrete.aemeasurable]
      calc ∫⁻ u, 𝒟[Prod.fst <$> (simulateQ (implOnce1 (fun m => cbcLazy (encode m)))
                (cont u)).run false] {b}
              ∂𝒟[(liftM (OracleSpec.query (spec := unifSpec) k) : ProbComp (Fin (k + 1)))]
          ≤ ∫⁻ u, (𝒟[Prod.fst <$> (simulateQ (implOnce1 (fun _ => $ᵗ (List.Vector Block n)))
                (cont u)).run false] {b} + ε)
              ∂𝒟[(liftM (OracleSpec.query (spec := unifSpec) k) : ProbComp (Fin (k + 1)))] :=
            lintegral_mono ih
        _ = ∫⁻ u, 𝒟[Prod.fst <$> (simulateQ (implOnce1 (fun _ => $ᵗ (List.Vector Block n)))
                (cont u)).run false] {b}
              ∂𝒟[(liftM (OracleSpec.query (spec := unifSpec) k) : ProbComp (Fin (k + 1)))] + ε := by
            rw [lintegral_add_right _ measurable_const, lintegral_const,
              evalDist_apply_univ_eq_one, mul_one]
    · have hstep (enc : M → ProbComp (List.Vector Block n)) :
          (implOnce1 enc (.inr m)).run false = enc m >>= fun c => pure (some c, true) := by
        simp [implOnce1, map_eq_bind_pure_comp]
      simp only [hstep, bind_assoc, pure_bind]
      let F : List.Vector Block n → ProbComp Bool := fun c =>
        Prod.fst <$>
          (simulateQ (implOnce1 (fun _ => $ᵗ (List.Vector Block n))) (cont (some c))).run true
      have hcont : ∀ c : List.Vector Block n,
          (Prod.fst <$>
            (simulateQ (implOnce1 (fun m => cbcLazy (encode m))) (cont (some c))).run true) =
          F c := fun c => by
        dsimp only [F]
        rw [implOnce1_true_eq]
      simp only [hcont]
      rw [apply_eq_beq (cbcLazy (encode m) >>= F) b,
        apply_eq_beq ($ᵗ (List.Vector Block n) >>= F) b, map_bind, map_bind]
      exact (Measure.apply_true_le_add_boolDist
        𝒟[cbcLazy (encode m) >>= fun c => (· == b) <$> F c]
        𝒟[$ᵗ (List.Vector Block n) >>= fun c => (· == b) <$> F c]).trans
        (add_le_add le_rfl (h m fun c => (· == b) <$> F c))

theorem cbc_branch_true_le {n : ℕ} (E : AesKey → Block → Block)
    (encode : M → List.Vector Block n)
    (A : CipherScheme.INDCPAAdversary M (List.Vector Block n)) (ε : ℝ≥0∞)
    (h : ∀ (m : M) (F : List.Vector Block n → ProbComp Bool),
      𝒟[cbcLazy (encode m) >>= F].boolDist 𝒟[$ᵗ (List.Vector Block n) >>= F] ≤ ε) :
    𝒟[(blockPRF E).branch true (cbcRed encode A)].boolDist
      𝒟[(cbcScheme E encode).branch true A] ≤ ε := by
  rw [evalDist_prf_branch_true, evalDist_cbc_branch_true]
  exact Measure.boolDist_le_of_apply_le _ _ (implOnce1_false_le encode ε h A)

end CryptoGames.CBC.Hop2

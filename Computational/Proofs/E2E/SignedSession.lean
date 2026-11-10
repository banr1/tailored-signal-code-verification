/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.SignedAdv
public import Computational.Proofs.E2E.SpkHop2Red
public import Computational.Proofs.E2E.SpkLeakRedModel
import Computational.Proofs.E2E.HeadlineSpkSession
import Computational.Proofs.E2E.SpkHop1InitBridge

/-!
# Leaked-SPK session chain on mixtures

**Checked by Lean.** Bounds the bias of a prefix-indexed mixture of `sessionSchemeFixedSpk`
games by that of `sessionSchemeU` plus single prefix-averaged PRF and PRG reduction advantages
across Hops 1–3.
-/

@[expose] public section

open OracleComp OracleSpec MeasureTheory ENNReal

namespace CryptoVerification.E2E.Signed

open CryptoGames CryptoGames.SM CryptoGames.Ratchet CryptoGames.Ratchet.LibsignalInst
open CryptoGames.LibsignalSM.Proofs CryptoVerification.E2E CryptoVerification.E2E.SpkHop2
open CryptoGames.LibsignalSession CryptoGames.CKA LibsignalProtoCodec

/-! ## Prefix integration helpers -/

section Integrate

theorem evalDist_bind_apply_lintegral {α : Type} (oa : ProbComp α) (f : α → ProbComp Bool)
    (v : Bool) :
    letI : MeasurableSpace α := ⊤
    𝒟[oa >>= f] {v} = ∫⁻ a, 𝒟[f a] {v} ∂𝒟[oa] := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  rw [evalDist_bind_of_discrete,
    Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]

theorem evalDist_bind_apply_le_add {α : Type} (oa : ProbComp α) (f g h : α → ProbComp Bool)
    (c : ℝ≥0∞) (v w : Bool) (H : ∀ a, 𝒟[f a] {v} ≤ 𝒟[g a] {v} + (c + 𝒟[h a] {w})) :
    𝒟[oa >>= f] {v} ≤ 𝒟[oa >>= g] {v} + (c + 𝒟[oa >>= h] {w}) := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  rw [evalDist_bind_apply_lintegral, evalDist_bind_apply_lintegral,
    evalDist_bind_apply_lintegral]
  calc ∫⁻ a, 𝒟[f a] {v} ∂𝒟[oa]
      ≤ ∫⁻ a, (𝒟[g a] {v} + (c + 𝒟[h a] {w})) ∂𝒟[oa] := lintegral_mono H
    _ = ∫⁻ a, 𝒟[g a] {v} ∂𝒟[oa] + (c + ∫⁻ a, 𝒟[h a] {w} ∂𝒟[oa]) := by
      rw [lintegral_add_left Measurable.of_discrete, lintegral_add_left measurable_const,
        lintegral_const, evalDist_apply_univ_eq_one, mul_one]

theorem evalDist_bind_apply_le_add_const {α : Type} (oa : ProbComp α) (f g : α → ProbComp Bool)
    (c : ℝ≥0∞) (v : Bool) (H : ∀ a, 𝒟[f a] {v} ≤ 𝒟[g a] {v} + c) :
    𝒟[oa >>= f] {v} ≤ 𝒟[oa >>= g] {v} + c := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  rw [evalDist_bind_apply_lintegral, evalDist_bind_apply_lintegral]
  calc ∫⁻ a, 𝒟[f a] {v} ∂𝒟[oa]
      ≤ ∫⁻ a, (𝒟[g a] {v} + c) ∂𝒟[oa] := lintegral_mono H
    _ = ∫⁻ a, 𝒟[g a] {v} ∂𝒟[oa] + c := by
      rw [lintegral_add_right _ measurable_const, lintegral_const, evalDist_apply_univ_eq_one,
        mul_one]

theorem evalDist_bind_apply_le_const {α : Type} (oa : ProbComp α) (f : α → ProbComp Bool)
    (c : ℝ≥0∞) (v : Bool) (H : ∀ a, 𝒟[f a] {v} ≤ c) : 𝒟[oa >>= f] {v} ≤ c := by
  let _ : MeasurableSpace α := ⊤
  rw [evalDist_bind_apply_lintegral]
  calc ∫⁻ a, 𝒟[f a] {v} ∂𝒟[oa] ≤ ∫⁻ _a, c ∂𝒟[oa] := lintegral_mono H
    _ = c := by rw [lintegral_const, evalDist_apply_univ_eq_one, mul_one]

theorem hybrid_chain_le (R T a : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) (n : ℕ) (h1 : ∀ k, R k ≤ a k + T k)
    (h2 : ∀ k < n, T k ≤ R (k + 1) + ε) :
    R 0 ≤ (∑ k ∈ Finset.range (n + 1), a k) + (n : ℝ≥0∞) * ε + T n := by
  have hm : ∀ m ≤ n, R 0 ≤ (∑ k ∈ Finset.range m, a k) + (m : ℝ≥0∞) * ε + R m := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hmn
      calc R 0 ≤ (∑ k ∈ Finset.range m, a k) + (m : ℝ≥0∞) * ε + R m := ih (by omega)
        _ ≤ (∑ k ∈ Finset.range m, a k) + (m : ℝ≥0∞) * ε + (a m + (R (m + 1) + ε)) := by
          gcongr
          exact (h1 m).trans (add_le_add le_rfl (h2 m (by omega)))
        _ = (∑ k ∈ Finset.range (m + 1), a k) + ((m + 1 : ℕ) : ℝ≥0∞) * ε + R (m + 1) := by
          rw [Finset.sum_range_succ]; push_cast; ring
  calc R 0 ≤ (∑ k ∈ Finset.range n, a k) + (n : ℝ≥0∞) * ε + R n := hm n le_rfl
    _ ≤ (∑ k ∈ Finset.range n, a k) + (n : ℝ≥0∞) * ε + (a n + T n) := by gcongr; exact h1 n
    _ = (∑ k ∈ Finset.range (n + 1), a k) + (n : ℝ≥0∞) * ε + T n := by
      rw [Finset.sum_range_succ]; ring

end Integrate

/-! ## SPQR-parametric session chain on mixtures -/

section MixWithSpqr

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
  {PQC : Type} [SampleableType PQC]

def leakAvgWithSpqr {α : Type} (C : Crypto) (spqr : Spqr Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) :
    MACScheme.PRFAdversary Pt (BitVec 256) :=
  prfAvg oa fun o =>
    spkLeakRed (paramsIdsWithSpqr C spqr (ida o) (idb o)) Dh encPt encT decT qep (s o) (A o)

def leakUAvgWithSpqr {α : Type} (C : Crypto) (spqr : Spqr Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (oa : ProbComp α) (ida idb : α → IdentityKey)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) :
    MACScheme.PRFAdversary Pt (BitVec 256) :=
  prfAvg oa fun o =>
    spkLeakRedU spkLeakRed (paramsIdsWithSpqr C spqr (ida o) (idb o)) Dh encPt encT decT qep (A o)

def hop2PrgAvgWithSpqr {α : Type} (C : Crypto) (spqr : Spqr Bytes PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (s : α → BitVec 256) (k : ℕ)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) :=
  prgAvg oa fun o =>
    hop2PrgRedK (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ Dh encPt encT decT qep (s o) k (A o)

def hop2PrfAvgWithSpqr {α : Type} (C : Crypto) (spqr : Spqr Bytes PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256) (k : ℕ)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) :
    MACScheme.PRFAdversary Pt (BitVec 256) :=
  prfAvg oa fun o =>
    hop2PrfRedK (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ Dh encT decT qep (s o) k (A o)

/-- Hop-2 mixture error bound using prefix-averaged PRG and PRF reductions. -/
noncomputable def hop2TermAvgWithSpqr {α : Type} (C : Crypto) (spqr : Spqr Bytes PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep q : ℕ) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (s : α → BitVec 256)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) : ℝ≥0∞ :=
  epoch0ChainForgeryTerm C.F q
    + (∑ k ∈ Finset.range spkSwapHybridCount,
        ((Ratchet.expandPRG C.F).prgAdvantage
            (hop2PrgAvgWithSpqr C spqr ℓ Dh encPt encT decT qep oa ida idb s k A)
          + (extractPRF C.F encPt).prfAdvantage
            (hop2PrfAvgWithSpqr C spqr ℓ Dh encT decT qep oa ida idb s k A)))
    + hop2CreateCollTerm Dh q
    + spkSwapSpuriousStepTerm C.F q
    + spkSwapCreationPointHitTerm Dh q
    + spkSwapHiddenScalarGuessTerm Dh q

variable {α : Type} (C : Crypto) (spqr : Spqr Bytes PQC)
  (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (hℓ : ℓ < 2 ^ 31)
  (hLspqr : ∀ st rq st' salt msg, spqr.send st rq = some (st', salt, msg) → msg.length < 2 ^ 29)
  (hDh : Dh.Commutes) (hX : X25519RealizesDh C Dh encPt encT)
  (hdec : ∀ T, decT (encT T) = some T) (hz : ∀ x, Dh.dh x 0 = 0)
  (qep q : ℕ) (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256)
  (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes)

include hℓ hLspqr hDh hX hdec hz in
theorem boolDist_mixHop1WithSpqr :
    𝒟[oa >>= fun o =>
        SM.gameR (sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ (s o)) 3 qep
          (configRefuseEarlyBobCorr decT encT) (A o)].boolDist
      𝒟[oa >>= fun o => MACScheme.branch (extractPRF C.F encPt) true
        (spkLeakRed (paramsIdsWithSpqr C spqr (ida o) (idb o)) Dh encPt encT decT qep (s o)
          (A o))] =
      (extractPRF C.F encPt).prfAdvantage
        (leakAvgWithSpqr C spqr Dh encPt encT decT qep oa ida idb s A) := by
  have h0 :
      𝒟[oa >>= fun o =>
          SM.gameR (sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ (s o)) 3 qep
            (configRefuseEarlyBobCorr decT encT) (A o)] =
        𝒟[oa >>= fun o => MACScheme.branch (extractPRF C.F encPt) false
          (spkLeakRed (paramsIdsWithSpqr C spqr (ida o) (idb o)) Dh encPt encT decT qep (s o)
            (A o))] :=
    evalDist_bind_congr oa _ _ fun o =>
      evalDist_gameR_sessionSchemeSpk_eq_branch_false (paramsIdsWithSpqr C spqr (ida o) (idb o))
        rfl (HeadlineSpk.lengthsOk_paramsIdsWithSpqr C spqr (ida o) (idb o) ℓ hℓ hLspqr)
        Dh hDh encPt encT decT hX hdec hz qep (s o) (A o)
  rw [h0, leakAvgWithSpqr, MACScheme.prfAdvantage_eq_boolDist, prfBranch_avg, prfBranch_avg,
    Measure.boolDist_comm]

include hℓ hLspqr hDh hX hdec hz in
theorem boolDist_mixHop3WithSpqr :
    𝒟[oa >>= fun o => MACScheme.branch (extractPRF C.F encPt) true
        (spkLeakRedU spkLeakRed (paramsIdsWithSpqr C spqr (ida o) (idb o)) Dh encPt encT decT qep
          (A o))].boolDist
      𝒟[oa >>= fun o =>
        SM.gameR (sessionSchemeU (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ) 3 qep
          (configRefuseEarlyBobCorr decT encT) (A o)] =
      (extractPRF C.F encPt).prfAdvantage
        (leakUAvgWithSpqr C spqr Dh encPt encT decT qep oa ida idb A) := by
  have h3 :
      𝒟[oa >>= fun o =>
          SM.gameR (sessionSchemeU (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ) 3 qep
            (configRefuseEarlyBobCorr decT encT) (A o)] =
        𝒟[oa >>= fun o => MACScheme.branch (extractPRF C.F encPt) false
          (spkLeakRedU spkLeakRed (paramsIdsWithSpqr C spqr (ida o) (idb o)) Dh encPt encT decT qep
            (A o))] :=
    evalDist_bind_congr oa _ _ fun o =>
      evalDist_gameR_sessionSchemeU_eq_branch_false_spkLeakRedU
        (paramsIdsWithSpqr C spqr (ida o) (idb o)) rfl
        (HeadlineSpk.lengthsOk_paramsIdsWithSpqr C spqr (ida o) (idb o) ℓ hℓ hLspqr)
        Dh hDh encPt encT decT hX hdec hz qep (A o)
  rw [h3, leakUAvgWithSpqr, MACScheme.prfAdvantage_eq_boolDist, prfBranch_avg, prfBranch_avg]

include hℓ hLspqr hDh hX hdec hz in
theorem boolDist_mixHop2WithSpqr_le
    (hker : ∀ o (x : BitVec 256) (P₁ P₂ : Pt),
      Dh.dh x P₁ = Dh.dh x P₂ ↔ Dh.dh (s o) P₁ = Dh.dh (s o) P₂)
    (hq : ∀ o, SM.MakesAtMostQueries (A o) q) :
    𝒟[oa >>= fun o => MACScheme.branch (extractPRF C.F encPt) true
        (spkLeakRed (paramsIdsWithSpqr C spqr (ida o) (idb o)) Dh encPt encT decT qep (s o)
          (A o))].boolDist
      𝒟[oa >>= fun o => MACScheme.branch (extractPRF C.F encPt) true
        (spkLeakRedU spkLeakRed (paramsIdsWithSpqr C spqr (ida o) (idb o)) Dh encPt encT decT qep
          (A o))] ≤
      hop2TermAvgWithSpqr C spqr ℓ Dh encPt encT decT qep q oa ida idb s A := by
  set R : ℕ → ℝ≥0∞ := fun k => 𝒟[oa >>= fun o => (Ratchet.expandPRG C.F).prgRealExperiment
    (hop2PrgRedK (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ Dh encPt encT decT qep (s o) k
      (A o))] {true} with hR
  set T : ℕ → ℝ≥0∞ := fun k => 𝒟[oa >>= fun o => (extractPRF C.F encPt).branch true
    (hop2PrfRedK (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ Dh encT decT qep (s o) k
      (A o))] {true} with hT
  set a : ℕ → ℝ≥0∞ := fun k =>
    (Ratchet.expandPRG C.F).prgAdvantage
        (hop2PrgAvgWithSpqr C spqr ℓ Dh encPt encT decT qep oa ida idb s k A)
      + (extractPRF C.F encPt).prfAdvantage
        (hop2PrfAvgWithSpqr C spqr ℓ Dh encT decT qep oa ida idb s k A)
    with ha
  have h1 : ∀ k, R k ≤ a k + T k := by
    intro k
    have hreal := prgReal_avg (Ratchet.expandPRG C.F) oa fun o =>
      hop2PrgRedK (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ Dh encPt encT decT qep (s o) k
        (A o)
    have hideal := prgIdeal_avg oa fun o =>
      hop2PrgRedK (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ Dh encPt encT decT qep (s o) k
        (A o)
    have hidealF :
        𝒟[oa >>= fun o => PRGScheme.prgIdealExperiment
          (hop2PrgRedK (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ Dh encPt encT decT qep (s o) k
            (A o))] =
        𝒟[oa >>= fun o => (extractPRF C.F encPt).branch false
          (hop2PrfRedK (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ Dh encT decT qep (s o) k
            (A o))] :=
      evalDist_bind_congr oa _ _ fun o =>
        evalDist_hop2PrgRedK_ideal_eq_hop2PrfRedK_false
          (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ Dh encPt encT decT qep (s o) k (A o)
    have hF := prfBranch_avg (extractPRF C.F encPt) false oa fun o =>
      hop2PrfRedK (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ Dh encT decT qep (s o) k (A o)
    have hTr := prfBranch_avg (extractPRF C.F encPt) true oa fun o =>
      hop2PrfRedK (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ Dh encT decT qep (s o) k (A o)
    simp only [hR, hT, ha]
    rw [← hreal, ← hTr]
    calc 𝒟[(Ratchet.expandPRG C.F).prgRealExperiment
            (hop2PrgAvgWithSpqr C spqr ℓ Dh encPt encT decT qep oa ida idb s k A)] {true}
        ≤ (Ratchet.expandPRG C.F).prgAdvantage
            (hop2PrgAvgWithSpqr C spqr ℓ Dh encPt encT decT qep oa ida idb s k A) +
          𝒟[PRGScheme.prgIdealExperiment
            (hop2PrgAvgWithSpqr C spqr ℓ Dh encPt encT decT qep oa ida idb s k A)] {true} :=
          SpkHop2.prgReal_true_le _ _
      _ = (Ratchet.expandPRG C.F).prgAdvantage
            (hop2PrgAvgWithSpqr C spqr ℓ Dh encPt encT decT qep oa ida idb s k A) +
          𝒟[(extractPRF C.F encPt).branch false
            (hop2PrfAvgWithSpqr C spqr ℓ Dh encT decT qep oa ida idb s k A)] {true} := by
          rw [hop2PrgAvgWithSpqr, hideal, hidealF, hop2PrfAvgWithSpqr, hF]
      _ ≤ (Ratchet.expandPRG C.F).prgAdvantage
            (hop2PrgAvgWithSpqr C spqr ℓ Dh encPt encT decT qep oa ida idb s k A) +
          ((extractPRF C.F encPt).prfAdvantage
              (hop2PrfAvgWithSpqr C spqr ℓ Dh encT decT qep oa ida idb s k A) +
            𝒟[(extractPRF C.F encPt).branch true
              (hop2PrfAvgWithSpqr C spqr ℓ Dh encT decT qep oa ida idb s k A)] {true}) :=
          add_le_add le_rfl (SpkHop2.prfBranch_false_true_le _ _)
      _ = _ := by rw [hop2PrfAvgWithSpqr, add_assoc]
  have h2 : ∀ k < spkSwapHybridCount - 1,
      T k ≤ R (k + 1) + ((6 * q : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh := by
    intro k _
    exact evalDist_bind_apply_le_add_const oa _ _ _ true fun o =>
      SpkHop1.evalDist_hop2PrfRedK_true_le_hop2PrgRedK_succ
        (paramsIdsWithSpqr C spqr (ida o) (idb o)) rfl
        (HeadlineSpk.lengthsOk_paramsIdsWithSpqr C spqr (ida o) (idb o) ℓ hℓ hLspqr)
        Dh encPt encT decT hX hdec hz qep q (s o) k (A o) (hq o)
  have hchain := hybrid_chain_le R T a _ (spkSwapHybridCount - 1) h1 h2
  have hlast : T (spkSwapHybridCount - 1) ≤ spkSwapSpuriousStepTerm C.F q + spkSwapCreationPointHitTerm Dh q :=
    evalDist_bind_apply_le_const oa _ _ true fun o =>
      HeadlineSpk.evalDist_hop2PrfRedK_last_le (paramsIdsWithSpqr C spqr (ida o) (idb o))
        Dh encPt encT decT qep q hX hdec hDh (s o) (hker o) rfl
        (HeadlineSpk.lengthsOk_paramsIdsWithSpqr C spqr (ida o) (idb o) ℓ hℓ hLspqr) (A o) (hq o)
  have hinit : ∀ v : Bool,
      𝒟[oa >>= fun o => MACScheme.branch (extractPRF C.F encPt) true
        (spkLeakRed (paramsIdsWithSpqr C spqr (ida o) (idb o)) Dh encPt encT decT qep (s o)
          (A o))] {v} ≤
      𝒟[oa >>= fun o => MACScheme.branch (extractPRF C.F encPt) true
        (spkLeakRedU spkLeakRed (paramsIdsWithSpqr C spqr (ida o) (idb o)) Dh encPt encT decT qep
          (A o))] {v} +
        ((epoch0ChainForgeryTerm C.F q + spkSwapHiddenScalarGuessTerm Dh q) + R 0) := fun v =>
    evalDist_bind_apply_le_add oa _ _ _ _ v true fun o =>
      SpkHop1.evalDist_spkLeakRed_apply_le_hop2PrgRedK_zero
        (paramsIdsWithSpqr C spqr (ida o) (idb o)) rfl
        (HeadlineSpk.lengthsOk_paramsIdsWithSpqr C spqr (ida o) (idb o) ℓ hℓ hLspqr)
        Dh encPt encT decT hX hdec hz qep q (s o) (hker o) (A o) (hq o) v
  have : IsProbabilityMeasure
      𝒟[oa >>= fun o => MACScheme.branch (extractPRF C.F encPt) true
        (spkLeakRed (paramsIdsWithSpqr C spqr (ida o) (idb o)) Dh encPt encT decT qep (s o)
          (A o))] :=
    ⟨evalDist_apply_univ_eq_one _⟩
  have : IsProbabilityMeasure
      𝒟[oa >>= fun o => MACScheme.branch (extractPRF C.F encPt) true
        (spkLeakRedU spkLeakRed (paramsIdsWithSpqr C spqr (ida o) (idb o)) Dh encPt encT decT qep
          (A o))] :=
    ⟨evalDist_apply_univ_eq_one _⟩
  refine (Measure.boolDist_le_of_apply_le _ _ hinit).trans ?_
  have hn : spkSwapHybridCount - 1 + 1 = spkSwapHybridCount := rfl
  rw [hn] at hchain
  calc (epoch0ChainForgeryTerm C.F q + spkSwapHiddenScalarGuessTerm Dh q) + R 0
      ≤ (epoch0ChainForgeryTerm C.F q + spkSwapHiddenScalarGuessTerm Dh q) +
          ((∑ k ∈ Finset.range spkSwapHybridCount, a k) +
            ((spkSwapHybridCount - 1 : ℕ) : ℝ≥0∞) * (((6 * q : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh) +
            (spkSwapSpuriousStepTerm C.F q + spkSwapCreationPointHitTerm Dh q)) :=
        add_le_add le_rfl (hchain.trans (add_le_add le_rfl hlast))
    _ = hop2TermAvgWithSpqr C spqr ℓ Dh encPt encT decT qep q oa ida idb s A := by
        rw [hop2TermAvgWithSpqr, hop2CreateCollTerm_eq_mul]
        simp only [ha]
        ac_rfl

include hℓ hLspqr hDh hX hdec hz in
/-- Three-hop leaked-SPK session mixture bound parametric in `spqr`. -/
theorem boolBias_mixSpkWithSpqr_le
    (hker : ∀ o (x : BitVec 256) (P₁ P₂ : Pt),
      Dh.dh x P₁ = Dh.dh x P₂ ↔ Dh.dh (s o) P₁ = Dh.dh (s o) P₂)
    (hq : ∀ o, SM.MakesAtMostQueries (A o) q) :
    𝒟[oa >>= fun o =>
        SM.gameR (sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ (s o)) 3 qep
          (configRefuseEarlyBobCorr decT encT) (A o)].boolBias ≤
      𝒟[oa >>= fun o =>
          SM.gameR (sessionSchemeU (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ) 3 qep
            (configRefuseEarlyBobCorr decT encT) (A o)].boolBias
        + 2 * (extractPRF C.F encPt).prfAdvantage
            (leakAvgWithSpqr C spqr Dh encPt encT decT qep oa ida idb s A)
        + 2 * (extractPRF C.F encPt).prfAdvantage
            (leakUAvgWithSpqr C spqr Dh encPt encT decT qep oa ida idb A)
        + 2 * hop2TermAvgWithSpqr C spqr ℓ Dh encPt encT decT qep q oa ida idb s A := by
  have h1 := SM.Construction.boolBias_le_add_two_mul_boolDist
    𝒟[oa >>= fun o =>
        SM.gameR (sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ (s o)) 3 qep
          (configRefuseEarlyBobCorr decT encT) (A o)]
    𝒟[oa >>= fun o => MACScheme.branch (extractPRF C.F encPt) true
        (spkLeakRed (paramsIdsWithSpqr C spqr (ida o) (idb o)) Dh encPt encT decT qep (s o)
          (A o))]
  have h2 := SM.Construction.boolBias_le_add_two_mul_boolDist
    𝒟[oa >>= fun o => MACScheme.branch (extractPRF C.F encPt) true
        (spkLeakRed (paramsIdsWithSpqr C spqr (ida o) (idb o)) Dh encPt encT decT qep (s o)
          (A o))]
    𝒟[oa >>= fun o => MACScheme.branch (extractPRF C.F encPt) true
        (spkLeakRedU spkLeakRed (paramsIdsWithSpqr C spqr (ida o) (idb o)) Dh encPt encT decT qep
          (A o))]
  have h3 := SM.Construction.boolBias_le_add_two_mul_boolDist
    𝒟[oa >>= fun o => MACScheme.branch (extractPRF C.F encPt) true
        (spkLeakRedU spkLeakRed (paramsIdsWithSpqr C spqr (ida o) (idb o)) Dh encPt encT decT qep
          (A o))]
    𝒟[oa >>= fun o =>
        SM.gameR (sessionSchemeU (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ) 3 qep
          (configRefuseEarlyBobCorr decT encT) (A o)]
  rw [boolDist_mixHop1WithSpqr C spqr Dh encPt encT decT hℓ hLspqr hDh hX hdec hz qep oa ida idb s
    A] at h1
  rw [boolDist_mixHop3WithSpqr C spqr Dh encPt encT decT hℓ hLspqr hDh hX hdec hz qep oa ida idb
    A] at h3
  have h2' := h2.trans (add_le_add le_rfl (mul_le_mul_right
    (boolDist_mixHop2WithSpqr_le C spqr Dh encPt encT decT hℓ hLspqr hDh hX hdec hz qep q oa ida
      idb s A hker hq) 2))
  refine (h1.trans (add_le_add (h2'.trans (add_le_add h3 le_rfl)) le_rfl)).trans_eq ?_
  ac_rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [SampleableType PQC] in
theorem prfAdvantage_prfAvg_congr_of_support' {α Key Input Tag : Type}
    [DecidableEq Input] [SampleableType Key] [SampleableType Tag]
    (mac : MACScheme Key Input Tag) (oa : ProbComp α)
    (D₁ D₂ : α → MACScheme.PRFAdversary Input Tag)
    (hD : ∀ o ∈ support oa, D₁ o = D₂ o) :
    mac.prfAdvantage (prfAvg oa D₁) = mac.prfAdvantage (prfAvg oa D₂) := by
  have hb : ∀ b, 𝒟[oa >>= fun o => mac.branch b (D₁ o)] =
      𝒟[oa >>= fun o => mac.branch b (D₂ o)] := fun b =>
    OracleComp.evalDist_bind_congr_of_support oa _ _ fun o ho => by rw [hD o ho]
  rw [MACScheme.prfAdvantage_eq_boolDist, MACScheme.prfAdvantage_eq_boolDist,
    prfBranch_avg, prfBranch_avg, prfBranch_avg, prfBranch_avg, hb true, hb false]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [SampleableType PQC] in
theorem prgAdvantage_prgAvg_congr_of_support' {α S R : Type}
    [SampleableType S] [SampleableType R]
    (prg : PRGScheme S R) (oa : ProbComp α)
    (D₁ D₂ : α → PRGScheme.PRGAdversary R)
    (hD : ∀ o ∈ support oa, D₁ o = D₂ o) :
    prg.prgAdvantage (prgAvg oa D₁) = prg.prgAdvantage (prgAvg oa D₂) := by
  have hr : 𝒟[oa >>= fun o => prg.prgRealExperiment (D₁ o)] =
      𝒟[oa >>= fun o => prg.prgRealExperiment (D₂ o)] :=
    OracleComp.evalDist_bind_congr_of_support oa _ _ fun o ho => by rw [hD o ho]
  have hi : 𝒟[oa >>= fun o => PRGScheme.prgIdealExperiment (D₁ o)] =
      𝒟[oa >>= fun o => PRGScheme.prgIdealExperiment (D₂ o)] :=
    OracleComp.evalDist_bind_congr_of_support oa _ _ fun o ho => by rw [hD o ho]
  unfold PRGScheme.prgAdvantage
  rw [prgReal_avg, prgReal_avg, prgIdeal_avg, prgIdeal_avg, hr, hi]

omit [SampleableType Pt] in
theorem hop2TermAvgWithSpqr_congr_of_support
    (A₁ A₂ : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes)
    (hA : ∀ o ∈ support oa, A₁ o = A₂ o) :
    hop2TermAvgWithSpqr C spqr ℓ Dh encPt encT decT qep q oa ida idb s A₁ =
      hop2TermAvgWithSpqr C spqr ℓ Dh encPt encT decT qep q oa ida idb s A₂ := by
  unfold hop2TermAvgWithSpqr hop2PrgAvgWithSpqr hop2PrfAvgWithSpqr
  have hsum :
      (∑ k ∈ Finset.range spkSwapHybridCount,
        ((Ratchet.expandPRG C.F).prgAdvantage
            (prgAvg oa fun o =>
              hop2PrgRedK (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ Dh encPt encT decT qep
                (s o) k (A₁ o))
          + (extractPRF C.F encPt).prfAdvantage
            (prfAvg oa fun o =>
              hop2PrfRedK (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ Dh encT decT qep
                (s o) k (A₁ o)))) =
      (∑ k ∈ Finset.range spkSwapHybridCount,
        ((Ratchet.expandPRG C.F).prgAdvantage
            (prgAvg oa fun o =>
              hop2PrgRedK (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ Dh encPt encT decT qep
                (s o) k (A₂ o))
          + (extractPRF C.F encPt).prfAdvantage
            (prfAvg oa fun o =>
              hop2PrfRedK (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ Dh encT decT qep
                (s o) k (A₂ o)))) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    have hprg := prgAdvantage_prgAvg_congr_of_support' (Ratchet.expandPRG C.F) oa
      (fun o => hop2PrgRedK (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ Dh encPt encT decT qep
        (s o) k (A₁ o))
      (fun o => hop2PrgRedK (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ Dh encPt encT decT qep
        (s o) k (A₂ o))
      (fun o ho => by rw [hA o ho])
    have hprf := prfAdvantage_prfAvg_congr_of_support' (extractPRF C.F encPt) oa
      (fun o => hop2PrfRedK (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ Dh encT decT qep
        (s o) k (A₁ o))
      (fun o => hop2PrfRedK (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ Dh encT decT qep
        (s o) k (A₂ o))
      (fun o ho => by rw [hA o ho])
    rw [hprg, hprf]
  rw [hsum]

include hℓ hLspqr hDh hX hdec hz in
theorem boolBias_mixSpkWithSpqr_le_of_support
    (hker : ∀ o (x : BitVec 256) (P₁ P₂ : Pt),
      Dh.dh x P₁ = Dh.dh x P₂ ↔ Dh.dh (s o) P₁ = Dh.dh (s o) P₂)
    (hq : ∀ o ∈ support oa, SM.MakesAtMostQueries (A o) q) :
    𝒟[oa >>= fun o =>
        SM.gameR (sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ (s o)) 3 qep
          (configRefuseEarlyBobCorr decT encT) (A o)].boolBias ≤
      𝒟[oa >>= fun o =>
          SM.gameR (sessionSchemeU (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ) 3 qep
            (configRefuseEarlyBobCorr decT encT) (A o)].boolBias
        + 2 * (extractPRF C.F encPt).prfAdvantage
            (leakAvgWithSpqr C spqr Dh encPt encT decT qep oa ida idb s A)
        + 2 * (extractPRF C.F encPt).prfAdvantage
            (leakUAvgWithSpqr C spqr Dh encPt encT decT qep oa ida idb A)
        + 2 * hop2TermAvgWithSpqr C spqr ℓ Dh encPt encT decT qep q oa ida idb s A := by
  obtain ⟨A', hsup, hq'⟩ : ∃ A' : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes,
      (∀ o ∈ support oa, A' o = A o) ∧ (∀ o, SM.MakesAtMostQueries (A' o) q) := by
    classical
    refine ⟨fun o => if o ∈ support oa then A o
      else (pure false : OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) Bool),
      fun o ho => ?_, fun o => ?_⟩
    · dsimp only; split_ifs; rfl
    · dsimp only
      split_ifs with ho
      · exact hq o ho
      · unfold SM.MakesAtMostQueries; simp
  have hle := boolBias_mixSpkWithSpqr_le C spqr Dh encPt encT decT hℓ hLspqr hDh hX hdec hz
    qep q oa ida idb s A' hker hq'
  have hg1 :
      𝒟[oa >>= fun o =>
          SM.gameR (sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ (s o)) 3 qep
            (configRefuseEarlyBobCorr decT encT) (A' o)] =
      𝒟[oa >>= fun o =>
          SM.gameR (sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ (s o)) 3 qep
            (configRefuseEarlyBobCorr decT encT) (A o)] :=
    OracleComp.evalDist_bind_congr_of_support oa _ _ fun o ho => by rw [hsup o ho]
  have hg2 :
      𝒟[oa >>= fun o =>
          SM.gameR (sessionSchemeU (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ) 3 qep
            (configRefuseEarlyBobCorr decT encT) (A' o)] =
      𝒟[oa >>= fun o =>
          SM.gameR (sessionSchemeU (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ) 3 qep
            (configRefuseEarlyBobCorr decT encT) (A o)] :=
    OracleComp.evalDist_bind_congr_of_support oa _ _ fun o ho => by rw [hsup o ho]
  have hl1 :
      (extractPRF C.F encPt).prfAdvantage
        (leakAvgWithSpqr C spqr Dh encPt encT decT qep oa ida idb s A') =
      (extractPRF C.F encPt).prfAdvantage
        (leakAvgWithSpqr C spqr Dh encPt encT decT qep oa ida idb s A) :=
    prfAdvantage_prfAvg_congr_of_support' (extractPRF C.F encPt) oa _ _ fun o ho => by
      rw [hsup o ho]
  have hl2 :
      (extractPRF C.F encPt).prfAdvantage
        (leakUAvgWithSpqr C spqr Dh encPt encT decT qep oa ida idb A') =
      (extractPRF C.F encPt).prfAdvantage
        (leakUAvgWithSpqr C spqr Dh encPt encT decT qep oa ida idb A) :=
    prfAdvantage_prfAvg_congr_of_support' (extractPRF C.F encPt) oa _ _ fun o ho => by
      rw [hsup o ho]
  have hh2 := hop2TermAvgWithSpqr_congr_of_support C spqr Dh encPt encT decT qep q oa ida idb s
    _ _ hsup
  rw [hg1, hg2, hl1, hl2, hh2] at hle
  exact hle

end MixWithSpqr

section Mix

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}

variable {α : Type} (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (hℓ : ℓ < 2 ^ 31) (hDh : Dh.Commutes) (hX : X25519RealizesDh C Dh encPt encT)
  (hdec : ∀ T, decT (encT T) = some T) (hz : ∀ x, Dh.dh x 0 = 0)
  (qep q : ℕ) (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256)
  (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) Unit Bytes)

end Mix

end CryptoVerification.E2E.Signed

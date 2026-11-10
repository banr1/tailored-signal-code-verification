/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Game.StatementPqOomGame
public import Computational.Specifications.Session.StatementSession
public import Computational.Specifications.Composition.StatementModel
public import Computational.Specifications.Assumptions.KeyInd1KeyReal
public import Computational.Proofs.LibsignalCli.StatementPqSecure
public import Computational.Proofs.LibsignalCli.CliPqAdapterDefs
public import Computational.Proofs.LibsignalCli.CliPqBadKemBound
public import Computational.Proofs.LibsignalCli.CliKemFailCouplingDefs
import Computational.Proofs.LibsignalCli.CliKemFailCouplingHopA
import Computational.Proofs.LibsignalCli.CliKemFailCouplingHopB
import VCVio.EvalDist.MeasureTVDist.Event
import VCVio.OracleComp.EvalDist.Measure

/-!
# CLI ML-KEM failure bad-event coupling

Couples the pairwise ML-KEM failure event `KemFailBad` on `cliPqxdhExpFlagged`'s CLI coins log with
the SPQR V1 send-coin log of `cliE2EExpWithKiCoinLogged` (`DEV-CLI18`), yielding top-level
halted-game bounds on `CliPqxdhAdvantage`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.LibsignalCli.CliKemFailCoupling

open OracleComp
open scoped ENNReal
open CryptoGames.CKA (DHFun)
open CryptoGames.LibsignalSession (PublicKey)
open CryptoGames.Ratchet.LibsignalInst (X25519RealizesDh dummyKey)
open CryptoVerification.LibsignalSpqrV1 (coinBytes)
open CryptoVerification.SignalSession (CliRun CliSpecPqxdh Inputs)
open CryptoVerification.E2E (Bytes CliGameAdversary CliGameAdversaryPerInstanceBounded
  CliKemFailProb CliPqxdhAdvantage CliPqxdhFlagProb L_bh MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds
  PEParams UnreachedPqxdhPrimitives cliCoinsTape? cliGameAdversaryReassoc cliPqxdhExpFlagged
  cliRunBadKemExp modelPrims two_mul_cliBadKemProb_modelPrims_le_kemCorrTerm)
open Computational.Proofs.LibsignalCli.CliKemFailCouplingDefs (
  cliPqAdvantage_le_of_good_val_le cliPqAdvantage_le_of_good_val_le_and_badProb
  cliPqExpProjCoinLogged kemFailBad_sendTapesOfInputs sendTapesOfInputs)

export Computational.Proofs.LibsignalCli.CliKemFailCouplingDefs (
  CoinLogM bhE2EStepLocalSmCoinLogged cliE2EDrvImplWithCoinLogged
  cliE2EExpWithKiCoinLogged cliE2EExpWithKiCoinLogged_fst)

theorem cliPqxdhExpFlagged_sendTapes_eq_projCoinLogged
    {Pt : Type} (S : SignalPqxdh.Setup) (run : CliRun)
    (X : UnreachedPqxdhPrimitives) (W : PEParams) (ℓ qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S ℓ (BitVec 512))
    (hCli : CliSpecPqxdh run X W) (hℓ : ℓ < 10 ^ 6) :
    Prod.map id sendTapesOfInputs <$> cliPqxdhExpFlagged S run X W ℓ qep decT encT A =
      Prod.map id (List.map coinBytes) <$> cliPqExpProjCoinLogged S run X W ℓ qep decT encT A :=
  Computational.Proofs.LibsignalCli.CliKemFailCouplingHopA.cliPqxdhExpFlagged_sendTapes_eq_projCoinLogged
    S run X W ℓ qep decT encT A hCli hℓ

theorem cliPqExpProjCoinLogged_good_val_le_e2eCoinLogged
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (hCli : CliSpecPqxdh run X W)
    (hK_tot : MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds W.Q.K)
    (hP : SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X W))
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ) (hℓ : ℓ < 10 ^ 6)
    (hDh : Dh.Commutes) (hX : X25519RealizesDh W.C Dh encPt encT)
    (hdec : ∀ T, decT (encT T) = some T)
    (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (hD : ∀ k x, W.C.D k (W.C.E k x) = x)
    (b_bud : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (hq32 : ∀ k < qStart, 2 * (qs k + 1) + 25002 < 2 ^ 32)
    (A : CliGameAdversary S ℓ (BitVec 512))
    (hA : CliGameAdversaryPerInstanceBounded A b_bud qStart qs)
    (val : Bool) :
    let P := modelPrims X W
    let B_Lbh := (L_bh (S := S) (ℓ := ℓ) (PQC := BitVec 512) decT encT).eval
      (fun _ => cliGameAdversaryReassoc A) ()
    Pr{let w ← cliPqExpProjCoinLogged S run X W ℓ qep decT encT A}[
        w.1 = val ∧ ¬ (W.Q.K.KemFailBad (w.2.map coinBytes) = true)] ≤
      Pr{let w ← cliE2EExpWithKiCoinLogged true S P
          (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) W.C W.Q.K ℓ qep decT encT B_Lbh}[
        w.1 = val ∧ ¬ (W.Q.K.KemFailBad (w.2.map coinBytes) = true)] +
      𝒟[cliRunBadKemExp S P run W ℓ qep decT encT A] {true} :=
  Computational.Proofs.LibsignalCli.CliKemFailCouplingHopB.cliPqExpProjCoinLogged_good_val_le_e2eCoinLogged
    S ℓ run X W hCli hK_tot hP Dh encPt encT decT qep hℓ hDh hX hdec hdum hz hD
    b_bud qStart qs hq32 A hA val

theorem cliPqxdhExpFlagged_good_val_le_e2eCoinLogged
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (run₀ : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (hCli : CliSpecPqxdh run₀ X W)
    (hK_tot : MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds W.Q.K)
    (hP : SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X W))
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ) (hℓ : ℓ < 10 ^ 6)
    (hDh : Dh.Commutes) (hX : X25519RealizesDh W.C Dh encPt encT)
    (hdec : ∀ T, decT (encT T) = some T)
    (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (hD : ∀ k x, W.C.D k (W.C.E k x) = x)
    (b_bud : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (hq32 : ∀ k < qStart, 2 * (qs k + 1) + 25002 < 2 ^ 32)
    (A : CliGameAdversary S ℓ (BitVec 512))
    (hA : CliGameAdversaryPerInstanceBounded A b_bud qStart qs)
    (val : Bool) :
    let P := modelPrims X W
    let B_Lbh := (L_bh (S := S) (ℓ := ℓ) (PQC := BitVec 512) decT encT).eval
      (fun _ => cliGameAdversaryReassoc A) ()
    Pr{let z ← cliPqxdhExpFlagged S run₀ X W ℓ qep decT encT A}[
        z.1 = val ∧ ¬ (W.Q.K.KemFailBad (z.2.filterMap cliCoinsTape?) = true)] ≤
      Pr{let w ← cliE2EExpWithKiCoinLogged true S P
          (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) W.C W.Q.K ℓ qep decT encT B_Lbh}[
        w.1 = val ∧ ¬ (W.Q.K.KemFailBad (w.2.map coinBytes) = true)] +
      𝒟[cliRunBadKemExp S P run₀ W ℓ qep decT encT A] {true} := by
  intro P B_Lbh
  have hProj :=
    cliPqxdhExpFlagged_sendTapes_eq_projCoinLogged S run₀ X W ℓ qep decT encT A hCli hℓ
  have hL :
      Pr{let z ← cliPqxdhExpFlagged S run₀ X W ℓ qep decT encT A}[
          z.1 = val ∧ ¬ (W.Q.K.KemFailBad (z.2.filterMap cliCoinsTape?) = true)] =
        Pr{let p ← Prod.map id sendTapesOfInputs <$>
            cliPqxdhExpFlagged S run₀ X W ℓ qep decT encT A}[
          p.1 = val ∧ ¬ (W.Q.K.KemFailBad p.2 = true)] := by
    rw [prEvent_map]
    exact prEvent_congr _ _ _ fun z => by
      dsimp only [Prod.map, id]
      rw [kemFailBad_sendTapesOfInputs]
  have hR :
      Pr{let p ← Prod.map id (List.map coinBytes) <$>
            cliPqExpProjCoinLogged S run₀ X W ℓ qep decT encT A}[
          p.1 = val ∧ ¬ (W.Q.K.KemFailBad p.2 = true)] =
        Pr{let w ← cliPqExpProjCoinLogged S run₀ X W ℓ qep decT encT A}[
          w.1 = val ∧ ¬ (W.Q.K.KemFailBad (w.2.map coinBytes) = true)] := by
    rw [prEvent_map]
    exact prEvent_congr _ _ _ fun w => Iff.rfl
  rw [hL, hProj, hR]
  exact cliPqExpProjCoinLogged_good_val_le_e2eCoinLogged S ℓ run₀ X W hCli hK_tot hP
    Dh encPt encT decT qep hℓ hDh hX hdec hdum hz hD b_bud qStart qs hq32 A hA val

/-- Packages the ML-KEM Clause-2 failure witness together with the good-log bound from
`cliPqxdhExpFlagged` to `cliE2EExpWithKiCoinLogged true`. -/
theorem exists_cliKemFail_e2eCoinLogged_bound
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (run₀ : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (hCli : CliSpecPqxdh run₀ X W)
    (hK_tot : MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds W.Q.K)
    (hP : SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X W))
    (δ_kem : ℝ≥0∞) (hKemBin : SignalPqxdh.KemDeltaCorrect (modelPrims X W) δ_kem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ) (hℓ : ℓ < 10 ^ 6)
    (hDh : Dh.Commutes) (hX : X25519RealizesDh W.C Dh encPt encT)
    (hdec : ∀ T, decT (encT T) = some T)
    (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (hD : ∀ k x, W.C.D k (W.C.E k x) = x)
    (b_bud : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (hq32 : ∀ k < qStart, 2 * (qs k + 1) + 25002 < 2 ^ 32)
    (A : CliGameAdversary S ℓ (BitVec 512))
    (hA : CliGameAdversaryPerInstanceBounded A b_bud qStart qs) :
    let P := modelPrims X W
    let B_Lbh := (L_bh (S := S) (ℓ := ℓ) (PQC := BitVec 512) decT encT).eval
      (fun _ => cliGameAdversaryReassoc A) ()
    ∃ δ_extra : ℝ≥0∞,
      2 * δ_extra ≤ SignalPqxdh.Security.kemDecapsFailureTerm S δ_kem ∧
      ∀ val : Bool,
        Pr{let z ← cliPqxdhExpFlagged S run₀ X W ℓ qep decT encT A}[
            z.1 = val ∧ ¬ (W.Q.K.KemFailBad (z.2.filterMap cliCoinsTape?) = true)] ≤
          Pr{let w ← cliE2EExpWithKiCoinLogged true S P
              (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) W.C W.Q.K ℓ qep decT encT B_Lbh}[
            w.1 = val ∧ ¬ (W.Q.K.KemFailBad (w.2.map coinBytes) = true)] + δ_extra := by
  intro P B_Lbh
  refine ⟨𝒟[cliRunBadKemExp S P run₀ W ℓ qep decT encT A] {true},
    two_mul_cliBadKemProb_modelPrims_le_kemCorrTerm S ℓ qep X run₀ W decT encT δ_kem hKemBin A,
    fun val => cliPqxdhExpFlagged_good_val_le_e2eCoinLogged S ℓ run₀ X W hCli hK_tot hP
      Dh encPt encT decT qep hℓ hDh hX hdec hdum hz hD b_bud qStart qs hq32 A hA val⟩

/-- Bounds `CliPqxdhAdvantage` by the bias of a halted experiment `exp_H` plus
`kemDecapsFailureTerm` and `2 * CliKemFailProb`. -/
theorem cliPqAdvantage_le_of_e2eHalted
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (hCli : CliSpecPqxdh run X W)
    (hK_tot : MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds W.Q.K)
    (hP : SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X W))
    (δ_kem : ℝ≥0∞) (hKemBin : SignalPqxdh.KemDeltaCorrect (modelPrims X W) δ_kem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ) (hℓ : ℓ < 10 ^ 6)
    (hDh : Dh.Commutes) (hX : X25519RealizesDh W.C Dh encPt encT)
    (hdec : ∀ T, decT (encT T) = some T)
    (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (hD : ∀ k x, W.C.D k (W.C.E k x) = x)
    (b_bud : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (hq32 : ∀ k < qStart, 2 * (qs k + 1) + 25002 < 2 ^ 32)
    (A : CliGameAdversary S ℓ (BitVec 512))
    (hA : CliGameAdversaryPerInstanceBounded A b_bud qStart qs)
    (exp_H : ProbComp Bool)
    (hHalted : ∀ val : Bool,
      let P := modelPrims X W
      let B_Lbh := (L_bh (S := S) (ℓ := ℓ) (PQC := BitVec 512) decT encT).eval
        (fun _ => cliGameAdversaryReassoc A) ()
      Pr{let w ← cliE2EExpWithKiCoinLogged true S P
          (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) W.C W.Q.K ℓ qep decT encT B_Lbh}[
        w.1 = val ∧ ¬ (W.Q.K.KemFailBad (w.2.map coinBytes) = true)] ≤
      Pr{let b ← exp_H}[b = val]) :
    CliPqxdhAdvantage S run X W ℓ qep decT encT A ≤
      𝒟[exp_H].boolBias +
        SignalPqxdh.Security.kemDecapsFailureTerm S δ_kem +
        2 * CliKemFailProb S run X W ℓ qep decT encT A := by
  obtain ⟨δ_extra, hδ, hCoupl⟩ := exists_cliKemFail_e2eCoinLogged_bound S ℓ run X W hCli hK_tot hP
    δ_kem hKemBin Dh encPt encT decT qep hℓ hDh hX hdec hdum hz hD b_bud qStart qs hq32 A hA
  have hGood : ∀ val : Bool,
      Pr{let z ← cliPqxdhExpFlagged S run X W ℓ qep decT encT A}[
          z.1 = val ∧ W.Q.K.KemFailBad (z.2.filterMap cliCoinsTape?) = false] ≤
        Pr{let b ← exp_H}[b = val] + δ_extra := by
    intro val
    have hnot :
        Pr{let z ← cliPqxdhExpFlagged S run X W ℓ qep decT encT A}[
            z.1 = val ∧ W.Q.K.KemFailBad (z.2.filterMap cliCoinsTape?) = false] =
          Pr{let z ← cliPqxdhExpFlagged S run X W ℓ qep decT encT A}[
            z.1 = val ∧ ¬ (W.Q.K.KemFailBad (z.2.filterMap cliCoinsTape?) = true)] :=
      prEvent_congr _ _ _ fun z => by simp
    rw [hnot]
    exact (hCoupl val).trans (add_le_add (hHalted val) le_rfl)
  exact (cliPqAdvantage_le_of_good_val_le S run X W ℓ qep decT encT A exp_H δ_extra hGood).trans
    (add_le_add (add_le_add le_rfl hδ) le_rfl)

/-- Variant of `cliPqAdvantage_le_of_e2eHalted` incorporating an excused-abort predicate `bad` on
`run`. -/
theorem cliPqAdvantage_le_of_e2eHalted_and_badProb
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (S : SignalPqxdh.Setup) (ℓ : ℕ)
    {run run₀ : CliRun} (X : UnreachedPqxdhPrimitives) (W : PEParams)
    {bad : Inputs → Prop} (hrun : ∀ i, ¬ bad i → run i = run₀ i)
    (hCli₀ : CliSpecPqxdh run₀ X W)
    (hK_tot : MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds W.Q.K)
    (hP : SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X W))
    (δ_kem : ℝ≥0∞) (hKemBin : SignalPqxdh.KemDeltaCorrect (modelPrims X W) δ_kem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ) (hℓ : ℓ < 10 ^ 6)
    (hDh : Dh.Commutes) (hX : X25519RealizesDh W.C Dh encPt encT)
    (hdec : ∀ T, decT (encT T) = some T)
    (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (hD : ∀ k x, W.C.D k (W.C.E k x) = x)
    (b_bud : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (hq32 : ∀ k < qStart, 2 * (qs k + 1) + 25002 < 2 ^ 32)
    (A : CliGameAdversary S ℓ (BitVec 512))
    (hA : CliGameAdversaryPerInstanceBounded A b_bud qStart qs)
    (exp_H : ProbComp Bool)
    (hHalted : ∀ val : Bool,
      let P := modelPrims X W
      let B_Lbh := (L_bh (S := S) (ℓ := ℓ) (PQC := BitVec 512) decT encT).eval
        (fun _ => cliGameAdversaryReassoc A) ()
      Pr{let w ← cliE2EExpWithKiCoinLogged true S P
          (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) W.C W.Q.K ℓ qep decT encT B_Lbh}[
        w.1 = val ∧ ¬ (W.Q.K.KemFailBad (w.2.map coinBytes) = true)] ≤
      Pr{let b ← exp_H}[b = val]) :
    CliPqxdhAdvantage S run X W ℓ qep decT encT A ≤
      𝒟[exp_H].boolBias +
        SignalPqxdh.Security.kemDecapsFailureTerm S δ_kem +
        2 * CliKemFailProb S run X W ℓ qep decT encT A +
        2 * CliPqxdhFlagProb S run X W ℓ qep decT encT A bad := by
  obtain ⟨δ_extra, hδ, hCoupl⟩ := exists_cliKemFail_e2eCoinLogged_bound S ℓ run₀ X W hCli₀ hK_tot hP
    δ_kem hKemBin Dh encPt encT decT qep hℓ hDh hX hdec hdum hz hD b_bud qStart qs hq32 A hA
  have hGood : ∀ val : Bool,
      Pr{let z ← cliPqxdhExpFlagged S run₀ X W ℓ qep decT encT A}[
          z.1 = val ∧ W.Q.K.KemFailBad (z.2.filterMap cliCoinsTape?) = false] ≤
        Pr{let b ← exp_H}[b = val] + δ_extra := by
    intro val
    have hnot :
        Pr{let z ← cliPqxdhExpFlagged S run₀ X W ℓ qep decT encT A}[
            z.1 = val ∧ W.Q.K.KemFailBad (z.2.filterMap cliCoinsTape?) = false] =
          Pr{let z ← cliPqxdhExpFlagged S run₀ X W ℓ qep decT encT A}[
            z.1 = val ∧ ¬ (W.Q.K.KemFailBad (z.2.filterMap cliCoinsTape?) = true)] :=
      prEvent_congr _ _ _ fun z => by simp
    rw [hnot]
    exact (hCoupl val).trans (add_le_add (hHalted val) le_rfl)
  exact (cliPqAdvantage_le_of_good_val_le_and_badProb S X W ℓ qep decT encT A hrun exp_H δ_extra
    hGood).trans (add_le_add (add_le_add (add_le_add le_rfl hδ) le_rfl) le_rfl)

end Computational.Proofs.LibsignalCli.CliKemFailCoupling

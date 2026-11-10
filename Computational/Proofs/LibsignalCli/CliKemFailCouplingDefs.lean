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
import VCVio.EvalDist.MeasureTVDist.Event
import VCVio.EvalDist.ProbabilityBounds
import VCVio.OracleComp.EvalDist.Measure
import Computational.Proofs.GameHop.Advantage
import Computational.Proofs.LibsignalCli.Oom.Agree
import Computational.Proofs.LibsignalCli.Oom.Bias
import Computational.Proofs.LibsignalCli.Oom.Faithful

/-!
# Shared definitions for CLI ML-KEM failure coupling

Defines the send-coin-logged E2E model game `cliE2EExpWithKiCoinLogged`, the send-coin-logged
projected CLI game `cliPqExpProjCoinLogged`, and probability-transfer lemmas for `KemFailBad`
and `sendTapesOfInputs`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.LibsignalCli.CliKemFailCouplingDefs

open MeasureTheory (Measure)
open OracleComp OracleSpec
open scoped ENNReal
open CryptoGames.CBC (Plain)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (Crypto GhostState PublicKey)
open CryptoVerification.LibsignalSpqrV1 (MlKem coinBytes coinBytes_length
  spqrV1SessionUniformCoins)
open CryptoVerification.SignalSession (CliRun Cmd Inputs PqParty coinsFile
  pqInitInputs pqInputs)
open CryptoVerification.E2E (BHDrvM BHDrvMode BHE2EDrvState BHE2ESmResp BinState Bytes
  CliGameAdversary CliKemFailProb CliPartyState CliPqxdhAdvantage CliPqxdhFlagProb
  ModelDriverInstance ModelDriverInstanceMeta ModelDriverState PEParams PreKeyBundleFields
  UnreachedPqxdhPrimitives allTestedSessionsFresh bhAlignTransForBob bhConfigSpkS
  bhDecodePreKeyMsgE bhDrvInstClean bhDrvKeyInd bhDrvKiQueryOk bhE2EDrvInstClean bhE2EDrvWon
  bhE2EInstIkACorr bhE2EMirror bhE2EStepLocalSm bhExpectedPreKeyMsg bhHdrOfPreKeyMsg bhInitRegId
  bhInstIkACorrupted bhIsBobAcceptSMResp bhIsBobRecvSMQuery bhMetaAfterSM bhNoExtWithSpqr
  bhNoOpkRespPromoted bhPackSmResp bhPartneredInTransitA bhPartneredInnerBytes bhSmDefaultWithSpqr
  bhTargetGameSpec bhUnpackSmResp cliCoinsTape? cliDrvCtl cliE2EDrvImplWith cliE2EExpWithKi
  cliGameDrSpec cliGameSmSpec cliGameSpec cliPqDirInputs cliPqRecvInp cliPqScheme cliPqSendInp
  cliPqSigsOf cliPqxdhExpFlagged compositionLocalStart configRefuseEarlyBobCorr
  driverSomeInstanceWon initiateTapeLen liftQueryImplStateT2 modelPrims oracleImplRM
  paramsIdsWithSpqr sessionSchemeFixedSpk shortCiphertext smSchemeCoinLogged wirePrekey)
open Computational.Proofs.GameHop.Advantage (boolDist_le_of_both_true_le)
open Computational.Proofs.LibsignalCli.Oom.Agree (GoodLog cliPqxdhExpFlagged_agree)
open Computational.Proofs.LibsignalCli.Oom.Bias (boolBias_le_add_two_mul_of_boolDist_le)
open Computational.Proofs.LibsignalCli.Oom.Faithful (cli_pq_exp_b_faithful_proof
  instLawfulMonadWriterTList)

/-! ## `KemFailBad` and `sendTapesOfInputs` -/

theorem tapePairFails_eq_false_of_length_ne_left (K : MlKem) {t₁ t₂ : List (BitVec 8)}
    (h₁ : t₁.length ≠ 64) : K.tapePairFails t₁ t₂ = false := by
  unfold MlKem.tapePairFails
  split
  · contradiction
  · rfl

theorem tapePairFails_eq_false_of_length_ne_right (K : MlKem) {t₁ t₂ : List (BitVec 8)}
    (h₂ : t₂.length ≠ 64) : K.tapePairFails t₁ t₂ = false := by
  unfold MlKem.tapePairFails
  simp [h₂]

theorem length_eq_64_of_tapePairFails (K : MlKem) {t₁ t₂ : List (BitVec 8)}
    (h : K.tapePairFails t₁ t₂ = true) : t₁.length = 64 ∧ t₂.length = 64 := by
  refine ⟨?_, ?_⟩
  · by_contra h₁
    rw [tapePairFails_eq_false_of_length_ne_left K h₁] at h
    exact Bool.false_ne_true h
  · by_contra h₂
    rw [tapePairFails_eq_false_of_length_ne_right K h₂] at h
    exact Bool.false_ne_true h

theorem kemFailBad_eq_true_iff (K : MlKem) (ts : List (List (BitVec 8))) :
    K.KemFailBad ts = true ↔ ∃ t₁ ∈ ts, ∃ t₂ ∈ ts, K.tapePairFails t₁ t₂ = true := by
  unfold MlKem.KemFailBad
  simp only [List.any_eq_true]

theorem kemFailBad_mono (K : MlKem) {ts₁ ts₂ : List (List (BitVec 8))}
    (hsub : ts₁ ⊆ ts₂) (h : K.KemFailBad ts₁ = true) : K.KemFailBad ts₂ = true := by
  rw [kemFailBad_eq_true_iff] at h ⊢
  rcases h with ⟨t₁, ht₁, t₂, ht₂, hfail⟩
  exact ⟨t₁, hsub ht₁, t₂, hsub ht₂, hfail⟩

theorem kemFailBad_append_of_left (K : MlKem) (ts₁ ts₂ : List (List (BitVec 8)))
    (h : K.KemFailBad ts₁ = true) : K.KemFailBad (ts₁ ++ ts₂) = true :=
  kemFailBad_mono K (List.subset_append_left ts₁ ts₂) h

theorem kemFailBad_filter_length_64 (K : MlKem) (ts : List (List (BitVec 8))) :
    K.KemFailBad (ts.filter (·.length == 64)) = K.KemFailBad ts := by
  apply Bool.eq_iff_iff.mpr
  rw [kemFailBad_eq_true_iff, kemFailBad_eq_true_iff]
  constructor
  · rintro ⟨t₁, ht₁, t₂, ht₂, hfail⟩
    exact ⟨t₁, List.mem_of_mem_filter ht₁, t₂, List.mem_of_mem_filter ht₂, hfail⟩
  · rintro ⟨t₁, ht₁, t₂, ht₂, hfail⟩
    obtain ⟨hl₁, hl₂⟩ := length_eq_64_of_tapePairFails K hfail
    exact ⟨t₁, List.mem_filter.mpr ⟨ht₁, by simp [hl₁]⟩,
      t₂, List.mem_filter.mpr ⟨ht₂, by simp [hl₂]⟩, hfail⟩

theorem kemFailBad_append_singleton_of_length_ne_64 (K : MlKem) (ts : List (List (BitVec 8)))
    (t : List (BitVec 8)) (ht : t.length ≠ 64) :
    K.KemFailBad (ts ++ [t]) = K.KemFailBad ts := by
  rw [← kemFailBad_filter_length_64 K (ts ++ [t]), ← kemFailBad_filter_length_64 K ts,
    List.filter_append]
  have hnil : ([t].filter (·.length == 64)) = [] := by simp [ht]
  rw [hnil, List.append_nil]

@[simp]
theorem cliCoinsTape?_cliPqSendInp (s : CliPartyState) (m : List (BitVec 8)) (rs : BitVec 512) :
    cliCoinsTape? (cliPqSendInp s m rs) = some (coinBytes rs) := by
  simp [cliCoinsTape?, cliPqSendInp, cliPqDirInputs]

@[simp]
theorem cliCoinsTape?_cliPqRecvInp (s : CliPartyState) (c : List (BitVec 8)) (rc : BitVec 256) :
    cliCoinsTape? (cliPqRecvInp s c rc) = some (keyToBytes32 rc) := by
  simp [cliCoinsTape?, cliPqRecvInp, cliPqDirInputs]

@[simp]
theorem cliCoinsTape?_pqInputs (W : PEParams) (st : PqParty) (cmd : Cmd)
    (extra : List (String × List (BitVec 8))) (coins stdin : List (BitVec 8)) :
    cliCoinsTape? (pqInputs W st cmd extra coins stdin) = some coins := by
  simp [cliCoinsTape?, pqInputs]

@[simp]
theorem cliCoinsTape?_pqInitInputs (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    cliCoinsTape? (pqInitInputs W st b t) = some t.toList := by
  simp [pqInitInputs]

/-- Extracts the 64-byte `coinsFile` tapes from a CLI input log. -/
def sendTapesOfInputs (w : List Inputs) : List (List (BitVec 8)) :=
  (w.filterMap cliCoinsTape?).filter (·.length == 64)

@[simp]
theorem sendTapesOfInputs_nil : sendTapesOfInputs [] = [] := rfl

@[simp]
theorem sendTapesOfInputs_append (w₁ w₂ : List Inputs) :
    sendTapesOfInputs (w₁ ++ w₂) = sendTapesOfInputs w₁ ++ sendTapesOfInputs w₂ := by
  simp [sendTapesOfInputs, List.filterMap_append, List.filter_append]

theorem kemFailBad_sendTapesOfInputs (K : MlKem) (w : List Inputs) :
    K.KemFailBad (sendTapesOfInputs w) = K.KemFailBad (w.filterMap cliCoinsTape?) :=
  kemFailBad_filter_length_64 K (w.filterMap cliCoinsTape?)

@[simp]
theorem sendTapesOfInputs_cliPqSendInp (s : CliPartyState) (m : List (BitVec 8)) (rs : BitVec 512) :
    sendTapesOfInputs [cliPqSendInp s m rs] = [coinBytes rs] := by
  simp [sendTapesOfInputs, coinBytes_length]

@[simp]
theorem sendTapesOfInputs_cliPqRecvInp (s : CliPartyState) (c : List (BitVec 8)) (rc : BitVec 256) :
    sendTapesOfInputs [cliPqRecvInp s c rc] = [] := by
  simp [sendTapesOfInputs, keyToBytes32]

@[simp]
theorem sendTapesOfInputs_pqInitInputs (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    sendTapesOfInputs [pqInitInputs W st b t] = [] := by
  simp [sendTapesOfInputs]

/-! ## Identical-until-bad bounds on `cliPqxdhExpFlagged` -/

theorem boolDist_fst_le_prEvent_of_agree {α : Type} (exp exp₀ : ProbComp (Bool × α))
    (badEv : Bool × α → Prop)
    (hagree : ∀ p : Bool × α → Prop,
      Pr{let z ← exp}[p z ∧ ¬ badEv z] = Pr{let z ← exp₀}[p z ∧ ¬ badEv z]) :
    (𝒟[Prod.fst <$> exp]).boolDist (𝒟[Prod.fst <$> exp₀]) ≤ Pr{let z ← exp}[badEv z] := by
  have hgood : Pr{let z ← exp}[¬ badEv z] = Pr{let z ← exp₀}[¬ badEv z] := by
    simpa only [true_and] using hagree fun _ => True
  have h₁ := prEvent_add_prEvent_not_eq_prEvent_true exp badEv
  have h₂ := prEvent_add_prEvent_not_eq_prEvent_true exp₀ badEv
  rw [OracleComp.prEvent_true_eq_one, hgood] at h₁
  rw [OracleComp.prEvent_true_eq_one] at h₂
  have hne : Pr{let z ← exp₀}[¬ badEv z] ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (prEvent_le_one _)
  have hbad_eq : Pr{let z ← exp}[badEv z] = Pr{let z ← exp₀}[badEv z] := by
    rw [ENNReal.eq_sub_of_add_eq hne h₁, ENNReal.eq_sub_of_add_eq hne h₂]
  rw [Measure.boolDist]
  exact (measure_absDiff_apply_le_measureETVDist (Prod.fst <$> exp) (Prod.fst <$> exp₀)
    (measurableSet_singleton true)).trans
    (measureETVDist_map_le_prEvent_of_agree exp exp₀ Prod.fst badEv hagree hbad_eq.ge)

/-- Identical-until-bad bound from `CliPqxdhAdvantage` to any experiment agreeing with
`cliPqxdhExpFlagged` outside `KemFailBad`. -/
theorem cliPqAdvantage_le_of_kemFailBad_agree (S : SignalPqxdh.Setup) (run : CliRun)
    (X : UnreachedPqxdhPrimitives) (W : PEParams) (l qep : Nat) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S l (BitVec 512))
    (exp₀ : ProbComp (Bool × List Inputs))
    (hagree : ∀ p : Bool × List Inputs → Prop,
      Pr{let z ← cliPqxdhExpFlagged S run X W l qep decT encT A}[
        p z ∧ ¬ (W.Q.K.KemFailBad (z.2.filterMap cliCoinsTape?) = true)] =
      Pr{let z ← exp₀}[
        p z ∧ ¬ (W.Q.K.KemFailBad (z.2.filterMap cliCoinsTape?) = true)]) :
    CliPqxdhAdvantage S run X W l qep decT encT A ≤
      𝒟[Prod.fst <$> exp₀].boolBias + 2 * CliKemFailProb S run X W l qep decT encT A := by
  unfold CliPqxdhAdvantage CliKemFailProb
  rw [← cli_pq_exp_b_faithful_proof S run X W l qep decT encT A]
  exact boolBias_le_add_two_mul_of_boolDist_le _ _ _
    (boolDist_fst_le_prEvent_of_agree
      (cliPqxdhExpFlagged S run X W l qep decT encT A) exp₀
      (fun z => W.Q.K.KemFailBad (z.2.filterMap cliCoinsTape?) = true) hagree)

/-- Bounds Boolean distance between `Prod.fst <$> exp` and `expH` from pointwise good-event bounds
on both outcomes. -/
theorem boolDist_le_of_good_val_le {α : Type} (exp : ProbComp (Bool × α)) (expH : ProbComp Bool)
    (badEv : Bool × α → Prop) (δ : ℝ≥0∞)
    (hval : ∀ val : Bool,
      Pr{let z ← exp}[z.1 = val ∧ ¬ badEv z] ≤ Pr{let b ← expH}[b = val] + δ) :
    (𝒟[Prod.fst <$> exp]).boolDist (𝒟[expH]) ≤ δ + Pr{let z ← exp}[badEv z] := by
  have hsplit : ∀ val : Bool,
      Pr{let z ← exp}[z.1 = val] ≤ Pr{let b ← expH}[b = val] + (δ + Pr{let z ← exp}[badEv z]) := by
    intro val
    have hsub : Pr{let z ← exp}[z.1 = val] ≤
        Pr{let z ← exp}[(z.1 = val ∧ ¬ badEv z) ∨ badEv z] :=
      prEvent_mono exp _ _ fun z hz => by
        by_cases hb : badEv z
        · exact Or.inr hb
        · exact Or.inl ⟨hz, hb⟩
    calc Pr{let z ← exp}[z.1 = val]
        ≤ Pr{let z ← exp}[z.1 = val ∧ ¬ badEv z] + Pr{let z ← exp}[badEv z] :=
          hsub.trans (prEvent_or_le exp _ _)
      _ ≤ (Pr{let b ← expH}[b = val] + δ) + Pr{let z ← exp}[badEv z] :=
          add_le_add (hval val) le_rfl
      _ = Pr{let b ← expH}[b = val] + (δ + Pr{let z ← exp}[badEv z]) := by ac_rfl
  have hp₁ : 𝒟[Prod.fst <$> exp] {true} = Pr{let z ← exp}[z.1 = true] := by
    rw [← prEvent_eq_evalDist_singleton (Prod.fst <$> exp) true, prEvent_map]
  have hq₁ : Pr{let z ← exp}[¬ (z.1 = true)] = Pr{let z ← exp}[z.1 = false] :=
    prEvent_congr exp _ _ fun z => by cases z.1 <;> simp
  have hp₂ : 𝒟[expH] {true} = Pr{let b ← expH}[b = true] :=
    (prEvent_eq_evalDist_singleton expH true).symm
  have hq₂ : Pr{let b ← expH}[¬ (b = true)] = Pr{let b ← expH}[b = false] :=
    prEvent_congr expH _ _ fun b => by cases b <;> simp
  have hsum₁ : Pr{let z ← exp}[z.1 = true] + Pr{let z ← exp}[z.1 = false] = 1 := by
    rw [← hq₁, prEvent_add_prEvent_not_eq_prEvent_true, OracleComp.prEvent_true_eq_one]
  have hsum₂ : Pr{let b ← expH}[b = true] + Pr{let b ← expH}[b = false] = 1 := by
    rw [← hq₂, prEvent_add_prEvent_not_eq_prEvent_true, OracleComp.prEvent_true_eq_one]
  refine boolDist_le_of_both_true_le 𝒟[Prod.fst <$> exp] 𝒟[expH] ?_ ?_
  · rw [hp₁, hp₂]
    exact hsplit true
  · rw [hp₁, hp₂]
    refine (ENNReal.add_le_add_iff_right ENNReal.one_ne_top).mp ?_
    calc Pr{let b ← expH}[b = true] + 1
        = Pr{let b ← expH}[b = true] +
            (Pr{let z ← exp}[z.1 = true] + Pr{let z ← exp}[z.1 = false]) := by rw [hsum₁]
      _ ≤ Pr{let b ← expH}[b = true] +
            (Pr{let z ← exp}[z.1 = true] +
              (Pr{let b ← expH}[b = false] + (δ + Pr{let z ← exp}[badEv z]))) :=
          add_le_add le_rfl (add_le_add le_rfl (hsplit false))
      _ = (Pr{let z ← exp}[z.1 = true] + (δ + Pr{let z ← exp}[badEv z])) +
            (Pr{let b ← expH}[b = true] + Pr{let b ← expH}[b = false]) := by ac_rfl
      _ = (Pr{let z ← exp}[z.1 = true] + (δ + Pr{let z ← exp}[badEv z])) + 1 := by rw [hsum₂]

/-- Bounds `CliPqxdhAdvantage` from pointwise good-log bounds against a halted experiment `expH`. -/
theorem cliPqAdvantage_le_of_good_val_le (S : SignalPqxdh.Setup) (run : CliRun)
    (X : UnreachedPqxdhPrimitives) (W : PEParams) (l qep : Nat) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S l (BitVec 512))
    (expH : ProbComp Bool) (δ : ℝ≥0∞)
    (hval : ∀ val : Bool,
      Pr{let z ← cliPqxdhExpFlagged S run X W l qep decT encT A}[
        z.1 = val ∧ W.Q.K.KemFailBad (z.2.filterMap cliCoinsTape?) = false] ≤
      Pr{let b ← expH}[b = val] + δ) :
    CliPqxdhAdvantage S run X W l qep decT encT A ≤
      𝒟[expH].boolBias + 2 * δ + 2 * CliKemFailProb S run X W l qep decT encT A := by
  unfold CliPqxdhAdvantage CliKemFailProb
  rw [← cli_pq_exp_b_faithful_proof S run X W l qep decT encT A]
  have hval' : ∀ val : Bool,
      Pr{let z ← cliPqxdhExpFlagged S run X W l qep decT encT A}[
        z.1 = val ∧ ¬ (W.Q.K.KemFailBad (z.2.filterMap cliCoinsTape?) = true)] ≤
      Pr{let b ← expH}[b = val] + δ := by
    intro val
    simpa only [Bool.not_eq_true] using hval val
  have hdist := boolDist_le_of_good_val_le
    (cliPqxdhExpFlagged S run X W l qep decT encT A) expH
    (fun z => W.Q.K.KemFailBad (z.2.filterMap cliCoinsTape?) = true) δ hval'
  calc 𝒟[Prod.fst <$> cliPqxdhExpFlagged S run X W l qep decT encT A].boolBias
      ≤ 𝒟[expH].boolBias +
          2 * (δ + Pr{let z ← cliPqxdhExpFlagged S run X W l qep decT encT A}[
            W.Q.K.KemFailBad (z.2.filterMap cliCoinsTape?) = true]) :=
        boolBias_le_add_two_mul_of_boolDist_le _ _ _ hdist
    _ = 𝒟[expH].boolBias + 2 * δ +
          2 * Pr{let z ← cliPqxdhExpFlagged S run X W l qep decT encT A}[
            W.Q.K.KemFailBad (z.2.filterMap cliCoinsTape?) = true] := by
        rw [mul_add, add_assoc]

/-- Variant of `cliPqAdvantage_le_of_good_val_le` incorporating an excused-abort predicate `bad` on
`run`. -/
theorem cliPqAdvantage_le_of_good_val_le_and_badProb (S : SignalPqxdh.Setup) {run run₀ : CliRun}
    (X : UnreachedPqxdhPrimitives) (W : PEParams) (l qep : Nat) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S l (BitVec 512))
    {bad : Inputs → Prop} (hrun : ∀ i, ¬ bad i → run i = run₀ i)
    (expH : ProbComp Bool) (δ : ℝ≥0∞)
    (hval₀ : ∀ val : Bool,
      Pr{let z ← cliPqxdhExpFlagged S run₀ X W l qep decT encT A}[
        z.1 = val ∧ W.Q.K.KemFailBad (z.2.filterMap cliCoinsTape?) = false] ≤
      Pr{let b ← expH}[b = val] + δ) :
    CliPqxdhAdvantage S run X W l qep decT encT A ≤
      𝒟[expH].boolBias + 2 * δ +
        2 * CliKemFailProb S run X W l qep decT encT A +
        2 * CliPqxdhFlagProb S run X W l qep decT encT A bad := by
  unfold CliPqxdhAdvantage CliKemFailProb CliPqxdhFlagProb
  rw [← cli_pq_exp_b_faithful_proof S run X W l qep decT encT A]
  let E₁ : Bool × List Inputs → Prop := fun z => ∃ i ∈ z.2, bad i
  let E₂ : Bool × List Inputs → Prop :=
    fun z => W.Q.K.KemFailBad (z.2.filterMap cliCoinsTape?) = true
  have hval : ∀ val : Bool,
      Pr{let z ← cliPqxdhExpFlagged S run X W l qep decT encT A}[
        z.1 = val ∧ ¬ (E₂ z ∨ E₁ z)] ≤
      Pr{let b ← expH}[b = val] + δ := by
    intro val
    have hcongr (r : CliRun) :
        Pr{let z ← cliPqxdhExpFlagged S r X W l qep decT encT A}[
          z.1 = val ∧ ¬ (E₂ z ∨ E₁ z)] =
        Pr{let z ← cliPqxdhExpFlagged S r X W l qep decT encT A}[
          (z.1 = val ∧ W.Q.K.KemFailBad (z.2.filterMap cliCoinsTape?) = false) ∧
            GoodLog bad z.2] := by
      refine prEvent_congr _ _ _ fun z => ?_
      simp only [E₁, E₂, GoodLog, not_or, not_exists, not_and, Bool.not_eq_true]
      tauto
    rw [hcongr run,
      cliPqxdhExpFlagged_agree S X W l qep decT encT A hrun
        (fun z => z.1 = val ∧ W.Q.K.KemFailBad (z.2.filterMap cliCoinsTape?) = false)]
    exact (prEvent_mono _ _ _ fun _ hz => hz.1).trans (hval₀ val)
  have hdist := boolDist_le_of_good_val_le
    (cliPqxdhExpFlagged S run X W l qep decT encT A) expH
    (fun z => E₂ z ∨ E₁ z) δ hval
  have hor : Pr{let z ← cliPqxdhExpFlagged S run X W l qep decT encT A}[E₂ z ∨ E₁ z] ≤
      Pr{let z ← cliPqxdhExpFlagged S run X W l qep decT encT A}[E₂ z] +
        Pr{let z ← cliPqxdhExpFlagged S run X W l qep decT encT A}[E₁ z] :=
    prEvent_or_le _ E₂ E₁
  calc 𝒟[Prod.fst <$> cliPqxdhExpFlagged S run X W l qep decT encT A].boolBias
      ≤ 𝒟[expH].boolBias +
          2 * (δ + Pr{let z ← cliPqxdhExpFlagged S run X W l qep decT encT A}[E₂ z ∨ E₁ z]) :=
        boolBias_le_add_two_mul_of_boolDist_le _ _ _ hdist
    _ ≤ 𝒟[expH].boolBias +
          2 * (δ + (Pr{let z ← cliPqxdhExpFlagged S run X W l qep decT encT A}[E₂ z] +
            Pr{let z ← cliPqxdhExpFlagged S run X W l qep decT encT A}[E₁ z])) := by
        gcongr
    _ = 𝒟[expH].boolBias + 2 * δ +
          2 * Pr{let z ← cliPqxdhExpFlagged S run X W l qep decT encT A}[E₂ z] +
          2 * Pr{let z ← cliPqxdhExpFlagged S run X W l qep decT encT A}[E₁ z] := by
        simp only [mul_add, add_assoc]

/-! ## Send-coin-logged E2E model game -/

theorem kemFailBad_map_coinBytes_mono (K : MlKem) {cs₁ cs₂ : List (BitVec 512)}
    (hsub : cs₁ ⊆ cs₂) (h : K.KemFailBad (cs₁.map coinBytes) = true) :
    K.KemFailBad (cs₂.map coinBytes) = true :=
  kemFailBad_mono K (List.map_subset coinBytes hsub) h

/-- `WriterT` monad accumulating 512-bit SPQR V1 send coins over `ProbComp`. -/
abbrev CoinLogM : Type → Type := WriterT (List (BitVec 512)) ProbComp

def bhE2EStepLocalSmCoinLogged {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σ : BHE2EDrvState S ℓ) (i : ℕ)
    (q : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    CoinLogM (BHE2ESmResp ℓ × BHE2EDrvState S ℓ) := do
  if !bhE2EDrvInstClean σ i then return ((none, none, none), σ)
  else
    match σ.insts[i]?, σ.instMeta[i]? with
    | some d, some im =>
      if !im.bobAccepted && bhIsBobRecvSMQuery q && bhE2EInstIkACorr σ d then
        let imCorr := { im with bobAccepted := true, ikACorrAtAccept := true }
        let σ' := { σ with instMeta := σ.instMeta.set i imCorr }
        return ((none, none, none), σ')
      else
        match d.gs with
        | none => return ((none, none, none), σ)
        | some gs =>
          let spqr := spqrV1SessionUniformCoins C.F K
          let sch := sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr d.idA d.idB) ℓ d.spkCoins
          let cfg := configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT
          let runStd (q' : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
              (σ0 : BHE2EDrvState S ℓ) : CoinLogM (BHE2ESmResp ℓ × BHE2EDrvState S ℓ) := do
            let (r, gs') ← (oracleImplRM (smSchemeCoinLogged sch) (2 + 1) qep cfg q').run gs
            let accepted := bhIsBobAcceptSMResp q' r
            let im' := if !im.bobAccepted && accepted then
                { im with bobAccepted := true, ikACorrAtAccept := bhE2EInstIkACorr σ0 d }
              else im
            let σ1 := { σ0 with insts := σ0.insts.set i { d with gs := some gs' },
                                instMeta := σ0.instMeta.set i im' }
            return (bhPackSmResp q' r, σ1)
          match q with
          | .inl (.inl (.inr (.A, c))) =>
            if (bhDecodePreKeyMsgE c).isSome then return ((none, none, none), σ)
            else runStd q σ
          | .inl (.inr (.A, c)) =>
            if (bhDecodePreKeyMsgE c).isSome then return ((none, none, none), σ)
            else runStd q σ
          | .inl (.inl (.inr (.B, c))) =>
            if !im.bobAccepted then
              match bhDecodePreKeyMsgE c with
              | some m =>
                if c == wirePrekey ::
                    (bhExpectedPreKeyMsg (bhInitRegId d.sid) d.hdr m.inner).bytes then
                  runStd (.inl (.inl (.inr (.B, m.inner)))) σ
                else return ((none, none, none), σ)
              | none => return ((none, none, none), σ)
            else
              match bhDecodePreKeyMsgE c with
              | some m =>
                if bhHdrOfPreKeyMsg m == d.hdr then
                  runStd (.inl (.inl (.inr (.B, m.inner)))) σ
                else return ((none, none, none), σ)
              | none => runStd (.inl (.inl (.inr (.B, c)))) σ
          | .inl (.inr (.B, c)) =>
            if !im.bobAccepted then return ((none, none, none), σ)
            else
              match bhDecodePreKeyMsgE c with
              | some m =>
                if bhHdrOfPreKeyMsg m == d.hdr && shortCiphertext c &&
                   decide (m.inner.length + 2048 < 2 ^ 32) then
                  runStd (.inl (.inr (.B, m.inner))) σ
                else return ((none, none, none), σ)
              | none => runStd (.inl (.inr (.B, c))) σ
          | _ => runStd q σ
    | _, _ => return ((none, none, none), σ)

def cliE2EDrvImplWithCoinLogged {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    QueryImpl (unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
      (StateT (BHE2EDrvState S ℓ) CoinLogM) := fun q =>
  match q with
  | .inl n => liftM (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))
  | .inr (.inl (.inl kq)) => do
    let σ ← get
    if !bhDrvKiQueryOk P σ.toModelDriverBase kq then
      return .noneResp
    else if (match kq with | .corruptIK u => bhNoOpkRespPromoted σ.instMeta u | _ => false) then
      return .noneResp
    else
      let (kr, st') ← StateT.lift (liftM ((ki kq).run σ.st))
      set (bhE2EMirror { σ with st := st' } kq kr)
      return kr
  | .inr (.inl (.inr (.startDR sid))) => do
    let σ ← get
    let (idx?, σ') ← StateT.lift (liftM (compositionLocalStart ki C K (some σ.b) σ sid))
    set σ'
    return idx?
  | .inr (.inr ⟨i, sq⟩) => do
    let σ ← get
    let (sr, σ') ← StateT.lift (bhE2EStepLocalSmCoinLogged C K qep decT encT σ i sq)
    set σ'
    return bhUnpackSmResp sq sr

/-- Send-coin-logged E2E model experiment recording every 512-bit coin passed to SPQR V1 `send`. -/
def cliE2EExpWithKiCoinLogged (secb : Bool) (S : SignalPqxdh.Setup)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    ProbComp (Bool × List (BitVec 512)) :=
  WriterT.run do
    let b ← liftM ($ᵗ Bool : ProbComp Bool)
    let (b', σ) ← (simulateQ (cliE2EDrvImplWithCoinLogged P ki C K qep decT encT) B).run
      { b := b, st := SignalPqxdh.KeyIndState.empty S secb }
    if !allTestedSessionsFresh P σ.st then liftM ($ᵗ Bool : ProbComp Bool)
    else return (b' == b || bhE2EDrvWon σ b)

def forgetCoinW {α : Type} (m : CoinLogM α) : ProbComp α :=
  Prod.fst <$> m.run

@[simp] theorem forgetCoinW_pure {α : Type} (a : α) :
    forgetCoinW (pure a) = pure a := by
  simp [forgetCoinW]

@[simp] theorem forgetCoinW_map {α β : Type} (f : α → β) (m : CoinLogM α) :
    forgetCoinW (f <$> m) = f <$> forgetCoinW m := by
  simp [forgetCoinW, Functor.map_map]

@[simp] theorem forgetCoinW_bind {α β : Type} (m : CoinLogM α) (k : α → CoinLogM β) :
    forgetCoinW (m >>= k) = forgetCoinW m >>= fun a => forgetCoinW (k a) := by
  simp [forgetCoinW, map_eq_bind_pure_comp, bind_assoc]

@[simp] theorem forgetCoinW_liftM {α : Type} (c : ProbComp α) :
    forgetCoinW (liftM c) = c := by
  dsimp [forgetCoinW, liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, WriterT.liftTell]
  simp [Functor.map_map]

@[simp] theorem forgetCoinW_tell (w : List (BitVec 512)) :
    forgetCoinW (MonadWriter.tell w) = pure () := by
  simp [forgetCoinW]

@[simp] theorem forgetCoinW_ite {α : Type} (c : Prop) [Decidable c] (t e : CoinLogM α) :
    forgetCoinW (if c then t else e) = if c then forgetCoinW t else forgetCoinW e := by
  split_ifs <;> rfl

def forgetCoinS1 {σ α : Type} (m : StateT σ CoinLogM α) : StateT σ ProbComp α :=
  fun s => forgetCoinW (m.run s)

@[simp] theorem forgetCoinS1_run {σ α : Type} (m : StateT σ CoinLogM α) (s : σ) :
    (forgetCoinS1 m).run s = forgetCoinW (m.run s) := rfl

@[simp] theorem forgetCoinS1_pure {σ α : Type} (a : α) :
    forgetCoinS1 (pure a : StateT σ CoinLogM α) = pure a := by
  ext s; simp

@[simp] theorem forgetCoinS1_map {σ α β : Type} (f : α → β) (m : StateT σ CoinLogM α) :
    forgetCoinS1 (f <$> m) = f <$> forgetCoinS1 m := by
  ext s; simp [StateT.run_map]

@[simp] theorem forgetCoinS1_bind {σ α β : Type}
    (m : StateT σ CoinLogM α) (k : α → StateT σ CoinLogM β) :
    forgetCoinS1 (m >>= k) = forgetCoinS1 m >>= fun a => forgetCoinS1 (k a) := by
  ext s; simp

@[simp] theorem forgetCoinS1_get {σ : Type} :
    forgetCoinS1 (get : StateT σ CoinLogM σ) = get := by
  ext s; simp

@[simp] theorem forgetCoinS1_set {σ : Type} (s' : σ) :
    forgetCoinS1 (set s' : StateT σ CoinLogM PUnit) = set s' := by
  ext s; simp

@[simp] theorem forgetCoinS1_lift {σ α : Type} (m : CoinLogM α) :
    forgetCoinS1 (StateT.lift m : StateT σ CoinLogM α) = StateT.lift (forgetCoinW m) := by
  ext s; simp [StateT.run_lift]

@[simp] theorem forgetCoinS1_liftM_prob {σ α : Type} (c : ProbComp α) :
    forgetCoinS1 (liftM c : StateT σ CoinLogM α) = liftM c := by
  ext s
  change forgetCoinW ((StateT.lift (liftM c : CoinLogM α)).run s) = (StateT.lift c).run s
  simp [StateT.run_lift]

@[simp] theorem forgetCoinS1_liftStateT {σ α : Type} (x : StateT σ ProbComp α) :
    forgetCoinS1 (CryptoVerification.E2E.liftStateT (n := CoinLogM) x) = x := by
  ext s; exact forgetCoinW_liftM (x s)

@[simp] theorem forgetCoinS1_ite {σ α : Type} (c : Prop) [Decidable c]
    (t e : StateT σ CoinLogM α) :
    forgetCoinS1 (if c then t else e) = if c then forgetCoinS1 t else forgetCoinS1 e := by
  split_ifs <;> rfl

@[simp] private theorem stateT_run_ite {σ : Type} {m : Type → Type} {α : Type}
    (c : Prop) [Decidable c] (t e : StateT σ m α) (s : σ) :
    (if c then t else e).run s = if c then t.run s else e.run s := by
  split_ifs <;> rfl

theorem forgetCoinS1_oracleImplRM_smSchemeCoinLogged
    {Key St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    (sch : CryptoGames.SMSchemeR Key St Msg (BitVec 512) (BitVec 256) C)
    (Δ qep : ℕ) (cfg : CryptoGames.SM.ConfigR St Msg C)
    (q : (CryptoGames.SM.spec St Msg (BitVec 512) C).Domain) :
    forgetCoinS1 (oracleImplRM (smSchemeCoinLogged sch) Δ qep cfg q) =
      CryptoGames.SM.oracleImplR sch Δ qep cfg q := by
  have hsend : ∀ s m r, forgetCoinW ((smSchemeCoinLogged sch).send s m r) = pure (sch.send s m r) := by
    intro s m r; simp [smSchemeCoinLogged]
  have hrecv : ∀ s c rc, forgetCoinW ((smSchemeCoinLogged sch).receive s c rc) = pure (sch.receive s c rc) := by
    intro s c rc; simp [smSchemeCoinLogged]
  rcases q with (((⟨p, m, r⟩ | ⟨p, m₀, m₁, r⟩) | ⟨p, c⟩) | ⟨p, c⟩) | p
  · change forgetCoinS1 (CryptoVerification.E2E.transmitRM (smSchemeCoinLogged sch) Δ qep cfg (p, m, r)) =
      CryptoGames.SM.transmitR sch Δ qep cfg (p, m, r)
    ext gs
    unfold CryptoVerification.E2E.transmitRM CryptoGames.SM.transmitR
      CryptoGames.SM.transmitImpl CryptoGames.SMSchemeR.sendPart
    simp only [forgetCoinS1_run, StateT.run_bind, StateT.run_get, pure_bind]
    cases cfg.sendOK gs p
    · simp [StateT.run_pure]
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
      cases gs.win
      · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift, StateT.run_monadLift,
          monadLift_self, forgetCoinW_bind, forgetCoinW_liftM, bind_assoc]
        congr 1; funext ⟨cns, bad⟩
        rcases hep : gs.epMgmt Δ qep p bad with _ | s₁
        · simp [hep, StateT.run_pure]
        · simp [hep, hsend, StateT.run_bind, StateT.run_lift, StateT.run_map, StateT.run_set]
      · simp [StateT.run_pure]
  · change forgetCoinS1 (CryptoVerification.E2E.challRM (smSchemeCoinLogged sch) Δ qep cfg (p, m₀, m₁, r)) =
      CryptoGames.SM.challR sch Δ qep cfg (p, m₀, m₁, r)
    ext gs
    unfold CryptoVerification.E2E.challRM CryptoGames.SM.challR
      CryptoGames.SM.challImpl CryptoGames.SMSchemeR.sendPart
    simp only [forgetCoinS1_run, StateT.run_bind, StateT.run_get, pure_bind]
    cases cfg.sendOK gs p
    · simp [StateT.run_pure]
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
      cases gs.win
      · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift, StateT.run_monadLift,
          monadLift_self, forgetCoinW_bind, forgetCoinW_liftM, bind_assoc]
        congr 1; funext ⟨cns, bad⟩
        rcases hep : gs.epMgmt Δ qep p bad with _ | s₁
        · simp [hep, StateT.run_pure]
        · simp [hep, hsend, stateT_run_ite, StateT.run_pure, StateT.run_bind, StateT.run_lift,
            StateT.run_map, StateT.run_set]
      · simp [StateT.run_pure]
  · change forgetCoinS1 (CryptoVerification.E2E.deliverRM (smSchemeCoinLogged sch) cfg (p, c)) =
      CryptoGames.SM.deliverR sch cfg (p, c)
    ext gs
    unfold CryptoVerification.E2E.deliverRM CryptoGames.SM.deliverR
    simp only [forgetCoinS1_run, StateT.run_bind, StateT.run_get, pure_bind]
    cases gs.win
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rcases htr : gs.inTransit p.other c with _ | r
      · simp [StateT.run_pure]
      · simp only [StateT.run_bind, StateT.run_lift, StateT.run_monadLift, monadLift_self,
          forgetCoinW_bind, forgetCoinW_liftM, hrecv, pure_bind, bind_assoc]
        congr 1; funext rc
        rcases hrc : sch.receive (gs.st p) c rc with _ | ⟨st', t', i', m'⟩ <;>
          simp [stateT_run_ite, StateT.run_pure, StateT.run_map, StateT.run_set]
    · simp [StateT.run_pure]
  · change forgetCoinS1 (CryptoVerification.E2E.injectRM (smSchemeCoinLogged sch) Δ qep cfg (p, c)) =
      CryptoGames.SM.injectR sch Δ qep cfg (p, c)
    ext gs
    unfold CryptoVerification.E2E.injectRM CryptoGames.SM.injectR
    simp only [forgetCoinS1_run, StateT.run_bind, StateT.run_get, pure_bind]
    cases hcond : (gs.win || (gs.inTransit p.other c).isSome || !(gs.safeInj Δ) || !(cfg.injOK c))
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
        StateT.run_monadLift, monadLift_self, forgetCoinW_bind, forgetCoinW_liftM, hrecv,
        pure_bind, bind_assoc]
      congr 1; funext rc
      rcases hrc : sch.receive (gs.st p) c rc with _ | ⟨st', t', i', m'⟩ <;>
        simp [stateT_run_ite, StateT.run_pure, StateT.run_map, StateT.run_set]
    · simp [StateT.run_pure]
  · exact forgetCoinS1_liftStateT (CryptoGames.SM.corrR cfg p)

theorem forgetCoinW_bhE2EStepLocalSmCoinLogged {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σ : BHE2EDrvState S ℓ) (i : ℕ)
    (q : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    forgetCoinW (bhE2EStepLocalSmCoinLogged C K qep decT encT σ i q) =
      bhE2EStepLocalSm C K qep decT encT σ i q := by
  unfold bhE2EStepLocalSmCoinLogged bhE2EStepLocalSm
  cases hclean : (!bhE2EDrvInstClean σ i)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rcases σ.insts[i]? with _ | d
    · simp
    · rcases σ.instMeta[i]? with _ | im
      · simp
      · dsimp only
        cases hcorr : (!im.bobAccepted && bhIsBobRecvSMQuery q && bhE2EInstIkACorr σ d)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rcases d.gs with _ | gs
          · simp
          · dsimp only
            rcases q with (((q₁ | q₂) | ⟨p, c⟩) | ⟨p, c⟩) | q₅
            · rw [forgetCoinW_bind, ← forgetCoinS1_run, forgetCoinS1_oracleImplRM_smSchemeCoinLogged]; simp
            · rw [forgetCoinW_bind, ← forgetCoinS1_run, forgetCoinS1_oracleImplRM_smSchemeCoinLogged]; simp
            · cases p
              · dsimp only
                cases (bhDecodePreKeyMsgE c).isSome
                · simp only [Bool.false_eq_true, ↓reduceIte]
                  rw [forgetCoinW_bind, ← forgetCoinS1_run, forgetCoinS1_oracleImplRM_smSchemeCoinLogged]; simp
                · simp
              · dsimp only
                cases (!im.bobAccepted)
                · simp only [Bool.false_eq_true, ↓reduceIte]
                  rcases bhDecodePreKeyMsgE c with _ | m <;> dsimp only
                  · rw [forgetCoinW_bind, ← forgetCoinS1_run, forgetCoinS1_oracleImplRM_smSchemeCoinLogged]; simp
                  · cases (bhHdrOfPreKeyMsg m == d.hdr)
                    · simp
                    · simp only [↓reduceIte]
                      rw [forgetCoinW_bind, ← forgetCoinS1_run, forgetCoinS1_oracleImplRM_smSchemeCoinLogged]; simp
                · simp only [↓reduceIte]
                  rcases bhDecodePreKeyMsgE c with _ | m <;> dsimp only
                  · simp
                  · cases (c == wirePrekey :: (bhExpectedPreKeyMsg (bhInitRegId d.sid) d.hdr m.inner).bytes)
                    · simp
                    · simp only [↓reduceIte]
                      rw [forgetCoinW_bind, ← forgetCoinS1_run, forgetCoinS1_oracleImplRM_smSchemeCoinLogged]; simp
            · cases p
              · dsimp only
                cases (bhDecodePreKeyMsgE c).isSome
                · simp only [Bool.false_eq_true, ↓reduceIte]
                  rw [forgetCoinW_bind, ← forgetCoinS1_run, forgetCoinS1_oracleImplRM_smSchemeCoinLogged]; simp
                · simp
              · dsimp only
                cases (!im.bobAccepted)
                · simp only [Bool.false_eq_true, ↓reduceIte]
                  rcases bhDecodePreKeyMsgE c with _ | m <;> dsimp only
                  · rw [forgetCoinW_bind, ← forgetCoinS1_run, forgetCoinS1_oracleImplRM_smSchemeCoinLogged]; simp
                  · cases (bhHdrOfPreKeyMsg m == d.hdr && shortCiphertext c &&
                      decide (m.inner.length + 2048 < 2 ^ 32))
                    · simp
                    · simp only [↓reduceIte]
                      rw [forgetCoinW_bind, ← forgetCoinS1_run, forgetCoinS1_oracleImplRM_smSchemeCoinLogged]; simp
                · simp
            · rw [forgetCoinW_bind, ← forgetCoinS1_run, forgetCoinS1_oracleImplRM_smSchemeCoinLogged]; simp
        · simp
  · simp

theorem forgetCoinS1_cliE2EDrvImplWithCoinLogged {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (q : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain) :
    forgetCoinS1 (cliE2EDrvImplWithCoinLogged P ki C K qep decT encT q) =
      cliE2EDrvImplWith P ki C K qep decT encT q := by
  rcases q with n | ((kq | ⟨sid⟩) | ⟨i, sq⟩)
  · simp [cliE2EDrvImplWithCoinLogged, cliE2EDrvImplWith]
  · unfold cliE2EDrvImplWithCoinLogged cliE2EDrvImplWith
    simp only [forgetCoinS1_bind, forgetCoinS1_get, forgetCoinS1_ite, forgetCoinS1_pure,
      forgetCoinS1_set, forgetCoinS1_lift, forgetCoinW_liftM]
    rfl
  · unfold cliE2EDrvImplWithCoinLogged cliE2EDrvImplWith
    simp only [forgetCoinS1_bind, forgetCoinS1_get]
    congr 1; funext σ
    simp only [forgetCoinS1_lift, forgetCoinW_liftM]
    rfl
  · unfold cliE2EDrvImplWithCoinLogged cliE2EDrvImplWith
    simp only [forgetCoinS1_bind, forgetCoinS1_get]
    congr 1; funext σ
    simp only [forgetCoinS1_lift, forgetCoinW_bhE2EStepLocalSmCoinLogged]
    rfl

theorem forgetCoinS1_simulateQ {ι σ α : Type} {spec : OracleSpec ι}
    {implM : QueryImpl spec (StateT σ CoinLogM)}
    {impl : QueryImpl spec (StateT σ ProbComp)}
    (h : ∀ q, forgetCoinS1 (implM q) = impl q) (oa : OracleComp spec α) :
    forgetCoinS1 (simulateQ implM oa) = simulateQ impl oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, forgetCoinS1_bind, h]
    congr 1; funext u; exact ih u

/-- Forgetting the coin log of `cliE2EExpWithKiCoinLogged` recovers `cliE2EExpWithKi`. -/
theorem cliE2EExpWithKiCoinLogged_fst (secb : Bool) (S : SignalPqxdh.Setup)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    Prod.fst <$> cliE2EExpWithKiCoinLogged secb S P ki C K ℓ qep decT encT B =
      cliE2EExpWithKi secb S P ki C K ℓ qep decT encT B := by
  change forgetCoinW (do
      let b ← liftM ($ᵗ Bool : ProbComp Bool)
      let (b', σ) ← (simulateQ (cliE2EDrvImplWithCoinLogged P ki C K qep decT encT) B).run
        { b := b, st := SignalPqxdh.KeyIndState.empty S secb }
      if !allTestedSessionsFresh P σ.st then liftM ($ᵗ Bool : ProbComp Bool)
      else return (b' == b || bhE2EDrvWon σ b)) =
    cliE2EExpWithKi secb S P ki C K ℓ qep decT encT B
  unfold cliE2EExpWithKi
  simp only [forgetCoinW_bind, forgetCoinW_liftM]
  congr 1; funext b
  rw [← forgetCoinS1_run, forgetCoinS1_simulateQ
    (forgetCoinS1_cliE2EDrvImplWithCoinLogged P ki C K qep decT encT) B]
  congr 1; funext ⟨b', σ⟩
  split_ifs <;> simp

/-! ## Send-coin-logged projected CLI game -/

abbrev BHDrvMCoinLogged (S : SignalPqxdh.Setup) (ℓ : ℕ) : Type → Type :=
  StateT (ModelDriverState S ℓ) (StateT (SignalPqxdh.KeyIndState S) CoinLogM)

def cliRunStdSMCoinLogged (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (run : CliRun) (W : PEParams) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ds : ModelDriverState S ℓ) (i : ℕ) (bi : ModelDriverInstance S ℓ)
    (im : ModelDriverInstanceMeta S)
    (gs : CryptoGames.SM.GameState BinState (Plain ℓ) Bytes)
    (q : (cliGameSmSpec ℓ (BitVec 512)).Domain) :
    BHDrvMCoinLogged S ℓ ((cliGameSmSpec ℓ (BitVec 512)).Range q) := do
  let kst ← StateT.lift get
  let scheme := cliPqScheme run W ℓ bi (cliPqSigsOf kst bi) bi.stA0 bi.stB0
  let cfg := bhConfigSpkS (Msg := Plain ℓ) decT encT
  let gsIn : CryptoGames.SM.GameState BinState (Plain ℓ) Bytes := match q with
    | .inl (.inl (.inr (.B, c))) => bhAlignTransForBob im.bobAccepted bi.meA.regId bi.hdr c gs
    | _ => gs
  let (r, gsOut) ← StateT.lift (StateT.lift
    ((oracleImplRM (smSchemeCoinLogged scheme) (2 + 1) qep cfg q).run gsIn))
  let gs' : CryptoGames.SM.GameState BinState (Plain ℓ) Bytes := match q, r with
    | .inl (.inl (.inr (.B, c))), some (.accepted _ _ _) =>
      match gsIn.inTransit .A c with
      | some rMatched =>
        { gsOut with trans := gs.trans.filter (fun rec => rec.pos != rMatched.pos) }
      | none => { gsOut with trans := gs.trans }
    | .inl (.inl (.inr (.B, _))), _ => { gsOut with trans := gs.trans }
    | _, _ => gsOut
  let im' := bhMetaAfterSM ds bi im q r
  set { ds with bhInsts := ds.bhInsts.set i { bi with gs := some gs' },
                instMeta := ds.instMeta.set i im' }
  return r

def cliStepLocalSMCoinLogged (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (run : CliRun) (W : PEParams) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ds : ModelDriverState S ℓ) (i : ℕ) (bi : ModelDriverInstance S ℓ)
    (im : ModelDriverInstanceMeta S)
    (gs : CryptoGames.SM.GameState BinState (Plain ℓ) Bytes) :
    (q : (cliGameSmSpec ℓ (BitVec 512)).Domain) →
      BHDrvMCoinLogged S ℓ ((cliGameSmSpec ℓ (BitVec 512)).Range q)
  | .inl (.inl (.inr (.A, c))) => do
    if (bhDecodePreKeyMsgE c).isSome then return none
    else cliRunStdSMCoinLogged S ℓ run W qep decT encT ds i bi im gs (.inl (.inl (.inr (.A, c))))
  | .inl (.inr (.A, c)) => do
    if (bhDecodePreKeyMsgE c).isSome then return none
    else cliRunStdSMCoinLogged S ℓ run W qep decT encT ds i bi im gs (.inl (.inr (.A, c)))
  | .inl (.inl (.inr (.B, c))) => do
    if (bhPartneredInnerBytes im.bobAccepted bi.meA.regId bi.hdr c).isNone then return none
    else cliRunStdSMCoinLogged S ℓ run W qep decT encT ds i bi im gs (.inl (.inl (.inr (.B, c))))
  | .inl (.inr (.B, c)) => do
    if !im.bobAccepted then return none
    else if (bhPartneredInnerBytes true bi.meA.regId bi.hdr c).isNone ||
        bhPartneredInTransitA true bi.meA.regId bi.hdr c gs then return none
    else cliRunStdSMCoinLogged S ℓ run W qep decT encT ds i bi im gs (.inl (.inr (.B, c)))
  | q => cliRunStdSMCoinLogged S ℓ run W qep decT encT ds i bi im gs q

def cliDrvSMCoinLogged (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (run : CliRun) (W : PEParams) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ext : QueryImpl (cliGameSmSpec ℓ (BitVec 512)) (BHDrvMCoinLogged S ℓ)) :
    QueryImpl (cliGameDrSpec ℓ (BitVec 512)) (BHDrvMCoinLogged S ℓ) := fun ⟨i, q⟩ => do
  let ds ← get
  if !bhDrvInstClean ds i then return bhSmDefaultWithSpqr q
  else
    match ds.bhInsts[i]?, ds.instMeta[i]? with
    | some bi, some im =>
      if !im.bobAccepted && bhIsBobRecvSMQuery q && bhInstIkACorrupted ds bi then
        let imCorr : ModelDriverInstanceMeta S := { im with bobAccepted := true, ikACorrAtAccept := true }
        set { ds with instMeta := ds.instMeta.set i imCorr }; return bhSmDefaultWithSpqr q
      else
        match bi.gs with
        | none =>
          let r ← ext q
          set { ds with instMeta := ds.instMeta.set i (bhMetaAfterSM ds bi im q r) }; return r
        | some gs => cliStepLocalSMCoinLogged S ℓ run W qep decT encT ds i bi im gs q
    | _, _ => return bhSmDefaultWithSpqr q

def cliDrvImplCoinLogged (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (P : SignalPqxdh.Primitives) (run : CliRun) (W : PEParams) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ext : QueryImpl (cliGameSmSpec ℓ (BitVec 512)) (BHDrvM S ℓ)) (mode : BHDrvMode S) :
    QueryImpl (cliGameSpec S ℓ (BitVec 512)) (BHDrvMCoinLogged S ℓ) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (BHDrvMCoinLogged S ℓ) +
    liftQueryImplStateT2 (n := CoinLogM) (bhDrvKeyInd S ℓ P false) +
    liftQueryImplStateT2 (n := CoinLogM) (cliDrvCtl S ℓ P run W mode) +
    cliDrvSMCoinLogged S ℓ run W qep decT encT (liftQueryImplStateT2 (n := CoinLogM) ext)

/-- Send-coin-logged counterpart of `cliPqExpProj` over `CoinLogM`. -/
def cliPqExpProjCoinLogged (S : SignalPqxdh.Setup) (run : CliRun) (X : UnreachedPqxdhPrimitives)
    (W : PEParams) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S ℓ (BitVec 512)) : ProbComp (Bool × List (BitVec 512)) :=
  WriterT.run do
    let P := modelPrims X W
    let b ← liftM ($ᵗ Bool : ProbComp Bool)
    let ((b', ds), st) ←
      (((simulateQ (cliDrvImplCoinLogged S ℓ P run W qep decT encT bhNoExtWithSpqr
          (fun _ _ _ _ _ => some b)) A.run).run {}).run (SignalPqxdh.KeyIndState.empty S true))
    if !allTestedSessionsFresh P st then liftM ($ᵗ Bool : ProbComp Bool)
    else return (b' == b || driverSomeInstanceWon ds b)

end Computational.Proofs.LibsignalCli.CliKemFailCouplingDefs

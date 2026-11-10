/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.Soundness
public import Computational.Proofs.LibsignalCli.KeyInd1RealReds
public import Computational.Proofs.E2E.SignedSession
public import Computational.Specifications.Session.StatementComposed
public import Computational.Specifications.Reductions.Pqxdh.StatementPqReds
public import Computational.Proofs.SignalPqxdh.KeyInd1KeyRoSplit
public import Computational.Specifications.Pqxdh.Security.HeadlineDelta
public import Computational.Specifications.Game.StatementPq

/-!
# Mixture bound equality and bridge propositions for CLI security

Provides `IsQueryBoundP` monotonicity and disjunction combinators, rewrites the prefix-mixture
session bound into the `Signed` mixture form (`prefixFullBoundMix_generic_eq`), and defines the
adapter and prefix-hybrid bridge propositions `CliPqAdapterBoundProp` and `CliPqPrefixBoundProp`.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal BigOperators
open ReductionDsl OracleComp OracleSpec MeasureTheory
open CryptoGames CryptoGames.LibsignalSM
open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst
open CryptoGames.Ratchet.LibsignalSim
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalProtoCodec
open CryptoVerification.SignalSession
open CryptoVerification.E2E.Signed

namespace CryptoVerification.E2E

local instance instInhabitedOfZeroHeadlinePqCliMixEq {Pt : Type} [Zero Pt] : Inhabited Pt := ⟨0⟩

/-! ## Query-bound helpers -/

theorem isQueryBoundP_of_imp_pq {ι : Type} {spec : OracleSpec ι} {α : Type}
    {p p' : ι → Prop} [DecidablePred p] [DecidablePred p']
    (himp : ∀ t, p' t → p t) {oa : OracleComp spec α} {n : ℕ}
    (h : oa.IsQueryBoundP p n) : oa.IsQueryBoundP p' n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure _ => trivial
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h ⊢
    refine ⟨?_, fun u => ?_⟩
    · by_cases hp' : p' t
      · exact Or.inr (h.1.resolve_left (not_not.mpr (himp t hp')))
      · exact Or.inl hp'
    · have := ih u (h.2 u)
      by_cases hp' : p' t
      · simp only [hp', ite_true, himp t hp'] at this ⊢; exact this
      · by_cases hp : p t
        · simp only [hp', hp, ite_true, ite_false] at this ⊢; exact this.mono (Nat.sub_le _ _)
        · simp only [hp', hp, ite_false] at this ⊢; exact this

theorem isQueryBoundP_or_add_pq {ι : Type} {spec : OracleSpec ι} {α : Type}
    {p₁ p₂ p : ι → Prop} [DecidablePred p₁] [DecidablePred p₂] [DecidablePred p]
    (hsplit : ∀ t, p t → p₁ t ∨ p₂ t) {oa : OracleComp spec α} {n₁ n₂ : ℕ}
    (h₁ : oa.IsQueryBoundP p₁ n₁) (h₂ : oa.IsQueryBoundP p₂ n₂) :
    oa.IsQueryBoundP p (n₁ + n₂) := by
  induction oa using OracleComp.inductionOn generalizing n₁ n₂ with
  | pure _ => trivial
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h₁ h₂ ⊢
    refine ⟨?_, fun u => ?_⟩
    · by_cases hp : p t
      · rcases hsplit t hp with hp1 | hp2
        · exact Or.inr (by have := h₁.1.resolve_left (not_not.mpr hp1); omega)
        · exact Or.inr (by have := h₂.1.resolve_left (not_not.mpr hp2); omega)
      · exact Or.inl hp
    · have k₁ := h₁.2 u
      have k₂ := h₂.2 u
      by_cases hp : p t
      · rcases hsplit t hp with hp1 | hp2
        · have _hpos := h₁.1.resolve_left (not_not.mpr hp1)
          simp only [hp1, ite_true] at k₁
          have k₂' : (mx u).IsQueryBoundP p₂ n₂ := k₂.mono (by split <;> omega)
          have := ih u k₁ k₂'
          simp only [hp, ite_true]
          exact this.mono (by omega)
        · have _hpos := h₂.1.resolve_left (not_not.mpr hp2)
          simp only [hp2, ite_true] at k₂
          have k₁' : (mx u).IsQueryBoundP p₁ n₁ := k₁.mono (by split <;> omega)
          have := ih u k₁' k₂
          simp only [hp, ite_true]
          exact this.mono (by omega)
      · simp only [hp, ite_false]
        exact (ih u (k₁.mono (by split <;> omega)) (k₂.mono (by split <;> omega))).mono le_rfl

/-! ## Prefix mixture bound rewrite -/

/-- Rewrites the prefix-mixture bound into `uniformStartMixtureBound` plus the `Signed` mixture
terms when SPK reduction evaluations agree across `support oa`. -/
theorem prefixFullBoundMix_generic_eq
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {α : Type}
    (ℓ : ℕ) (D : SessionCostedReductionFamily Pt ℓ)
    (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256)
    (Ak : α → CryptoGames.SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hevalLeak : ∀ o ∈ support oa,
      let spqr := LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K
      let Rspk := (D C K (ida o) (idb o) Dh encPt encT decT lam qep q).spk
      evalSpkLeakRed Rspk.spkLeakRed (s o) (Ak o) =
        spkLeakRed (paramsIdsWithSpqr C spqr (ida o) (idb o)) Dh encPt encT decT qep (s o) (Ak o))
    (hevalLeakU : ∀ o ∈ support oa,
      let spqr := LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K
      let Rspk := (D C K (ida o) (idb o) Dh encPt encT decT lam qep q).spk
      evalSpkLeakRedU Rspk.spkLeakRedU (fun x => evalSpkLeakRed Rspk.spkLeakRed x (Ak o)) =
        spkLeakRedU spkLeakRed (paramsIdsWithSpqr C spqr (ida o) (idb o)) Dh encPt encT decT qep
          (Ak o))
    (hevalPrg : ∀ o ∈ support oa, ∀ j < spkSwapHybridCount,
      let spqr := LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K
      let Rspk := (D C K (ida o) (idb o) Dh encPt encT decT lam qep q).spk
      evalSpkSwapPrgHybrid (Rspk.hop2PrgRedK j) (s o) (Ak o) =
        hop2PrgRedK (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ Dh encPt encT decT qep
          (s o) j (Ak o))
    (hevalPrf : ∀ o ∈ support oa, ∀ j < spkSwapHybridCount,
      let spqr := LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K
      let Rspk := (D C K (ida o) (idb o) Dh encPt encT decT lam qep q).spk
      evalSpkSwapPrfHybrid (Rspk.hop2PrfRedK j) (s o) (Ak o) =
        hop2PrfRedK (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ Dh encT decT qep
          (s o) j (Ak o)) :
    let spqr := LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K
    let R := fun o => D C K (ida o) (idb o) Dh encPt encT decT lam qep q
    let Rspk := fun o => (R o).spk
    (uniformStartMixtureBound C K ℓ Dh encPt encT decT lam qep q δ oa ida idb R Ak
      + 2 * (extractPRF C.F encPt).prfAdvantage
          (prefixPrfAvg oa (fun o =>
            evalSpkLeakRed (Rspk o).spkLeakRed (s o) (Ak o)))
      + 2 * (extractPRF C.F encPt).prfAdvantage
          (prefixPrfAvg oa (fun o =>
            evalSpkLeakRedU (Rspk o).spkLeakRedU
              (fun x => evalSpkLeakRed (Rspk o).spkLeakRed x (Ak o))))
      + 2 * (epoch0ChainForgeryTerm C.F q
          + (∑ j ∈ Finset.range spkSwapHybridCount,
              ((CryptoGames.Ratchet.expandPRG C.F).prgAdvantage
                  (prefixPrgAvg oa (fun o =>
                    evalSpkSwapPrgHybrid ((Rspk o).hop2PrgRedK j) (s o) (Ak o)))
                + (extractPRF C.F encPt).prfAdvantage
                  (prefixPrfAvg oa (fun o =>
                    evalSpkSwapPrfHybrid ((Rspk o).hop2PrfRedK j) (s o) (Ak o)))))
          + hop2CreateCollTerm Dh q + spkSwapSpuriousStepTerm C.F q + spkSwapCreationPointHitTerm Dh q
          + spkSwapHiddenScalarGuessTerm Dh q)) =
      uniformStartMixtureBound C K ℓ Dh encPt encT decT lam qep q δ oa ida idb R Ak
        + 2 * (extractPRF C.F encPt).prfAdvantage
            (Signed.leakAvgWithSpqr C spqr Dh encPt encT decT qep oa ida idb s Ak)
        + 2 * (extractPRF C.F encPt).prfAdvantage
            (Signed.leakUAvgWithSpqr C spqr Dh encPt encT decT qep oa ida idb Ak)
        + 2 * Signed.hop2TermAvgWithSpqr C spqr ℓ Dh encPt encT decT qep q oa ida idb s Ak := by
  intro spqr R Rspk
  have hl1 :
      (extractPRF C.F encPt).prfAdvantage
        (prefixPrfAvg oa (fun o => evalSpkLeakRed (Rspk o).spkLeakRed (s o) (Ak o))) =
      (extractPRF C.F encPt).prfAdvantage
        (Signed.leakAvgWithSpqr C spqr Dh encPt encT decT qep oa ida idb s Ak) :=
    Signed.prfAdvantage_prfAvg_congr_of_support' (extractPRF C.F encPt) oa _ _ hevalLeak
  have hl2 :
      (extractPRF C.F encPt).prfAdvantage
        (prefixPrfAvg oa (fun o =>
          evalSpkLeakRedU (Rspk o).spkLeakRedU
            (fun x => evalSpkLeakRed (Rspk o).spkLeakRed x (Ak o)))) =
      (extractPRF C.F encPt).prfAdvantage
        (Signed.leakUAvgWithSpqr C spqr Dh encPt encT decT qep oa ida idb Ak) :=
    Signed.prfAdvantage_prfAvg_congr_of_support' (extractPRF C.F encPt) oa _ _ hevalLeakU
  have hsum :
      (∑ j ∈ Finset.range spkSwapHybridCount,
        ((CryptoGames.Ratchet.expandPRG C.F).prgAdvantage
            (prefixPrgAvg oa (fun o =>
              evalSpkSwapPrgHybrid ((Rspk o).hop2PrgRedK j) (s o) (Ak o)))
          + (extractPRF C.F encPt).prfAdvantage
            (prefixPrfAvg oa (fun o =>
              evalSpkSwapPrfHybrid ((Rspk o).hop2PrfRedK j) (s o) (Ak o))))) =
      (∑ j ∈ Finset.range spkSwapHybridCount,
        ((CryptoGames.Ratchet.expandPRG C.F).prgAdvantage
            (Signed.hop2PrgAvgWithSpqr C spqr ℓ Dh encPt encT decT qep oa ida idb s j Ak)
          + (extractPRF C.F encPt).prfAdvantage
            (Signed.hop2PrfAvgWithSpqr C spqr ℓ Dh encT decT qep oa ida idb s j Ak))) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj_lt : j < spkSwapHybridCount := Finset.mem_range.mp hj
    have hprg :
        (CryptoGames.Ratchet.expandPRG C.F).prgAdvantage
          (prefixPrgAvg oa (fun o => evalSpkSwapPrgHybrid ((Rspk o).hop2PrgRedK j) (s o) (Ak o))) =
        (CryptoGames.Ratchet.expandPRG C.F).prgAdvantage
          (Signed.hop2PrgAvgWithSpqr C spqr ℓ Dh encPt encT decT qep oa ida idb s j Ak) :=
      Signed.prgAdvantage_prgAvg_congr_of_support' (CryptoGames.Ratchet.expandPRG C.F) oa _ _
        fun o ho => hevalPrg o ho j hj_lt
    have hprf :
        (extractPRF C.F encPt).prfAdvantage
          (prefixPrfAvg oa (fun o => evalSpkSwapPrfHybrid ((Rspk o).hop2PrfRedK j) (s o) (Ak o))) =
        (extractPRF C.F encPt).prfAdvantage
          (Signed.hop2PrfAvgWithSpqr C spqr ℓ Dh encT decT qep oa ida idb s j Ak) :=
      Signed.prfAdvantage_prfAvg_congr_of_support' (extractPRF C.F encPt) oa _ _
        fun o ho => hevalPrf o ho j hj_lt
    rw [hprg, hprf]
  unfold Signed.hop2TermAvgWithSpqr
  rw [hl1, hl2, hsum]

/-! ## Bridge propositions and `KeyIndRoGap` transfer -/

/-- CLI adapter coupling bridge bounding `CliPqxdhAdvantage` by the bias of `bhE2EExpWithKi true`
at `pqxdhKeyIndImpl1KeyReal` plus `kemDecapsFailureTerm`. -/
def CliPqAdapterBoundProp {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (S : SignalPqxdh.Setup) (ℓ : ℕ) : Prop :=
  ∀ (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (_hCli : CliSpecPqxdh run X W) (_hK_tot : MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds W.Q.K)
    (_hP : SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X W))
    (δ_kem : ℝ≥0∞) (_hKemBin : SignalPqxdh.KemDeltaCorrect (modelPrims X W) δ_kem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ) (_hℓ : ℓ < 10 ^ 6)
    (_hDh : Dh.Commutes) (_hX : X25519RealizesDh W.C Dh encPt encT)
    (_hdec : ∀ T, decT (encT T) = some T) (_hinj : Function.Injective encT)
    (_hdum : ∀ T, encT T ≠ dummyKey) (_hz : ∀ x, Dh.dh x 0 = 0)
    (_hD : ∀ k x, W.C.D k (W.C.E k x) = x)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (_hq32 : ∀ k < qStart, 2 * (qs k + 1) + 25002 < 2 ^ 32)
    (A : CliGameAdversary S ℓ (BitVec 512))
    (_hA : CliGameAdversaryPerInstanceBounded A b qStart qs),
    let P := modelPrims X W
    let B_A := (L_bh (S := S) (ℓ := ℓ) (PQC := BitVec 512) decT encT).eval (fun _ => cliGameAdversaryReassoc A) ()
    CliPqxdhAdvantage S run X W ℓ qep decT encT A ≤
      𝒟[bhE2EExpWithKi true S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) W.C W.Q.K ℓ qep
          decT encT B_A].boolBias +
        SignalPqxdh.Security.kemDecapsFailureTerm S δ_kem

/-- Prefix-hybrid bridge bounding the bias of `bhE2EExpWithKi false` at `pqxdhKeyIndImpl1KeyReal`
by the `qStart`-step mixture session bias sum of `Prefix1Key.bhPrefixRedWith`. -/
def CliPqPrefixBoundProp {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (S : SignalPqxdh.Setup) (ℓ : ℕ) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (_hK_tot : MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds W.Q.K)
    (_hP : SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X W))
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ) (_hℓ : ℓ < 10 ^ 6)
    (_hDh : Dh.Commutes) (_hX : X25519RealizesDh W.C Dh encPt encT)
    (_hdec : ∀ T, decT (encT T) = some T) (_hinj : Function.Injective encT)
    (_hdum : ∀ T, encT T ≠ dummyKey) (_hz : ∀ x, Dh.dh x 0 = 0)
    (_hD : ∀ k x, W.C.D k (W.C.E k x) = x)
    (qStart qTot : ℕ)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (_hQStart : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
      qStart)
    (_hQTot : B_A.IsQueryBoundP (ReductionDsl.isGameQuery (G := bhTargetGameSpec S ℓ (BitVec 512))) qTot),
    let P := modelPrims X W
    let spqr := LibsignalSpqrV1.spqrV1SessionUniformCoins W.C.F W.Q.K
    let prefRed :=
      Prefix1Key.bhPrefixRedWith S ℓ P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) W.C W.Q.K qep
        decT encT
    𝒟[bhE2EExpWithKi false S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) W.C W.Q.K ℓ qep
        decT encT B_A].boolBias ≤
      ∑ k ∈ Finset.range qStart, ⨆ flip : Bool,
        𝒟[do
          let o ← stageOneAsProbComp ((prefRed k).eval1 (fun _ => B_A) () qTot false)
          CryptoGames.SM.gameR
            (sessionSchemeFixedSpk (paramsIdsWithSpqr W.C spqr o.1.idA o.1.idB) ℓ o.1.spkCoins)
            (2 + 1) qep (configRefuseEarlyBobCorr decT encT)
            ((prefRed k).eval2 o.2 flip qTot false)].boolBias

theorem cliPqPrefixBoundProp_of_general
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (hGen : ∀ (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
      (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (qStart qTot : ℕ)
      (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool),
      B.IsQueryBoundP
        (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
        qStart →
      B.IsQueryBoundP (ReductionDsl.isGameQuery (G := bhTargetGameSpec S ℓ (BitVec 512))) qTot →
      let spqr := LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K
      let prefRed := Prefix1Key.bhPrefixRedWith S ℓ P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K qep
        decT encT
      𝒟[bhE2EExpWithKi false S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K ℓ qep
          decT encT B].boolBias ≤
        ∑ k ∈ Finset.range qStart, ⨆ flip : Bool,
          𝒟[stageOneAsProbComp ((prefRed k).eval1 (fun _ => B) () qTot false) >>=
            fun o =>
              CryptoGames.SM.gameR
                (sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr o.1.idA o.1.idB) ℓ o.1.spkCoins)
                (2 + 1) qep (configRefuseEarlyBobCorr decT encT)
                ((prefRed k).eval2 o.2 flip qTot false)].boolBias) :
    CliPqPrefixBoundProp (Pt := Pt) S ℓ :=
  fun X W _ _ _ _ encT decT qep _ _ _ _ _ _ _ _ qStart qTot B_A hQStart hQTot =>
    hGen (modelPrims X W) W.C W.Q.K qep decT encT qStart qTot B_A hQStart hQTot

/-- Transfers `PqxdhKeyIndReductionBoundδ` across `KeyIndRoGap` to bound `KeyInd1KeyRealAdvantage`. -/
theorem keyInd1KeyRealAdvantage_le_of_roGap
    (S : SignalPqxdh.Setup)
    (RK : SignalPqxdh.Security.KeyIndCostedReductionFamily S)
    (hKi : SignalPqxdh.Security.PqxdhKeyIndReductionBoundδ S RK.eval)
    (P : SignalPqxdh.Primitives)
    (hP : SignalPqxdh.CryptoWellFormedPrimitivesδ P)
    (δ_kem : ℝ≥0∞) (hKemBin : SignalPqxdh.KemDeltaCorrect P δ_kem)
    (b_ki : SignalPqxdh.QueryBudget)
    (advK : SignalPqxdh.KeyIndAdversary S)
    (hK : SignalPqxdh.QueryBounded advK b_ki)
    (ε_ro : ℝ≥0∞) (hRo : SignalPqxdh.KeyIndRoGap S P advK ε_ro) :
    SignalPqxdh.KeyInd1KeyRealAdvantage S P advK ≤
      (let R := RK.eval
       let Ab : SignalPqxdh.BoundedAdv (SignalPqxdh.KeyIndAdversary S) b_ki := ⟨advK, hK⟩
       SignalPqxdh.Security.pqxdhKeyIndAdvantageBoundActiveδ S b_ki.q_on δ_kem
         (SignalPqxdh.GapSigEufCma P P.isValidDhTriple (R.sig _ Ab))
         (SignalPqxdh.KemShCr P (R.shcr _ Ab))
         (SignalPqxdh.GapDhWithSign P P.isValidDhTriple P.pow8 (R.gdh _ Ab)) + ε_ro) :=
  SignalPqxdh.keyInd1KeyRealAdvantage_le_of_roGap_and_bound hRo
    (hKi P hP δ_kem hKemBin b_ki ⟨advK, hK⟩)

end CryptoVerification.E2E

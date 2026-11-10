/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.SignedRefine
public import Computational.Proofs.E2E.SignedFSBound
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Defs
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.HiddenSaltBound
public import Computational.Proofs.E2E.RefuseCorrB0Core
public import Computational.Proofs.E2E.SignedPrims
public import Computational.Proofs.SessionCostedFig8
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Encaps1Total
import Computational.Proofs.CryptoGames.CKA.DHProof
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.QueryBounds
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Queries
import Computational.Proofs.CryptoGames.SM.Theorem1
import Computational.Proofs.E2E.SignedFig8
import Computational.Proofs.E2E.SignedSession
import Computational.Proofs.E2E.SignedThm1
import Computational.Proofs.E2E.SignedThm8
import Computational.Proofs.HeadlineV1.SendShortC
import Computational.Proofs.SignalWireRoundTrip
import Computational.Proofs.SpqrV1Sync.SendTotal

/-!
# Mixture refinement bounds with SPQR V1

Integrates the U-hop, simulator refinement, epoch-0 PRG, hidden-salt, Fig. 8, and FS-AEAD bounds
over a prefix distribution `oa` for `paramsV1 Z K (ida o) (idb o)`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OracleComp OracleSpec MeasureTheory ENNReal

namespace CryptoVerification.E2E.Signed

open CryptoGames CryptoGames.SM CryptoGames.SM.Construction CryptoGames.Ratchet
  CryptoGames.Ratchet.LibsignalInst CryptoGames.LibsignalSM.Proofs CryptoVerification.E2E
  CryptoGames.LibsignalSession CryptoGames.CKA LibsignalProtoCodec CryptoGames.LibsignalSM
  CryptoGames.LibsignalSM.Proofs.Refinement CryptoGames.Ratchet.LibsignalSim
  CryptoGames.Ratchet.LibsignalSimC CryptoGames.SM.Construction.DeliverForge
  CryptoVerification.E2E.RefuseCorrB0 CryptoVerification.E2E.HeadlineU
  CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1Sync.SendTotal
  CryptoVerification.LibsignalSession.HeadlineV1

/-! ## `paramsV1` and `KemFailFind` mixture averaging -/

/-- Session `Params` for identity keys `(idA, idB)` with `spqrV1SessionUniformCoins Z.F K`. -/
abbrev paramsV1 (Z : Crypto) (K : MlKem) (idA idB : IdentityKey) :
    LibsignalSession.Params Bytes (BitVec 512) :=
  paramsIdsWithSpqr Z (spqrV1SessionUniformCoins Z.F K) idA idB

@[simp] theorem paramsV1_C (Z : Crypto) (K : MlKem) (idA idB : IdentityKey) :
    (paramsV1 Z K idA idB).C = Z := rfl

@[simp] theorem paramsV1_codec (Z : Crypto) (K : MlKem) (idA idB : IdentityKey) :
    (paramsV1 Z K idA idB).codec = protoSignalCodec := rfl

/-- Averages a family of `KemFailFind` adversaries over a prefix distribution `oa`. -/
def kemFailAvg {α : Type} (oa : ProbComp α) (B : α → MlKem.KemFailFindAdversary) :
    MlKem.KemFailFindAdversary :=
  oa >>= B

theorem kemFailFindGame_avg {α : Type} (K : MlKem) (oa : ProbComp α)
    (B : α → MlKem.KemFailFindAdversary) :
    K.kemFailFindGame (kemFailAvg oa B) = (oa >>= fun o => K.kemFailFindGame (B o)) := by
  unfold MlKem.kemFailFindGame kemFailAvg
  simp only [bind_assoc]

/-- Expected `KemFailFind` advantage over `oa` equals the advantage of `kemFailAvg oa B`. -/
theorem lintegral_kemFailFindAdvantage {α : Type} (K : MlKem) (oa : ProbComp α)
    (B : α → MlKem.KemFailFindAdversary) :
    letI : MeasurableSpace α := ⊤
    ∫⁻ o, K.kemFailFindAdvantage (B o) ∂𝒟[oa] = K.kemFailFindAdvantage (kemFailAvg oa B) := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  unfold MlKem.kemFailFindAdvantage
  rw [kemFailFindGame_avg, evalDist_bind_apply_lintegral]

/-! ## U-mixture hop -/

@[simp] theorem sessionSchemeU_eq_libSessionU_poly {PQ PQC : Type} [Inhabited PQ]
    (P : Params PQ PQC) (ℓ : ℕ) :
    sessionSchemeU P ℓ = libSessionU P ℓ := rfl

/-- Mixture U-hop bound for `paramsV1` with a single uniform `rootKdfAsPrg` distinguisher. -/
theorem boolBias_mixU_le_v1 {Pt α : Type} (Z : Crypto) (K : MlKem) {ℓ : ℕ}
    (encPt : Pt → Bytes) (lam : Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes) :
    𝒟[oa >>= fun o => SM.gameR (sessionSchemeU (paramsV1 Z K (ida o) (idb o)) ℓ) 3 qep
        (configRefuseEarlyBobCorr decT encT) (A o)].boolBias ≤
      𝒟[oa >>= fun o => SM.gameR (libsignalSessionScheme (paramsV1 Z K (ida o) (idb o)) ℓ encPt lam) 3 qep
          (configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT))
          (A o).refuseCorrB0].boolBias
        + 2 * (LibsignalSim.rootKdfAsPrg Z.F (encPt lam)).prgAdvantage
          (prgAvg oa fun o => uniformStartDistinguisher (paramsV1 Z K (ida o) (idb o)) ℓ
            (configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT)) qep
            (A o).refuseCorrB0) := by
  have hU : 𝒟[oa >>= fun o => SM.gameR (sessionSchemeU (paramsV1 Z K (ida o) (idb o)) ℓ) 3 qep
        (configRefuseEarlyBobCorr decT encT) (A o)] =
      𝒟[PRGScheme.prgIdealExperiment
        (prgAvg oa fun o => uniformStartDistinguisher (paramsV1 Z K (ida o) (idb o)) ℓ
          (configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT)) qep
          (A o).refuseCorrB0)] := by
    rw [prgIdeal_avg]
    refine evalDist_bind_congr _ _ _ fun o => ?_
    rw [sessionSchemeU_eq_libSessionU_poly, ← evalDist_gameR_libSessionU_eq_prgIdeal]
    exact congrArg _ (gameR_withNoCorrB0_eq _ 3 qep
      (configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT)) rfl (A o))
  have hR : 𝒟[oa >>= fun o => SM.gameR (libsignalSessionScheme (paramsV1 Z K (ida o) (idb o)) ℓ encPt lam) 3
        qep (configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT))
        (A o).refuseCorrB0] =
      𝒟[(LibsignalSim.rootKdfAsPrg Z.F (encPt lam)).prgRealExperiment
        (prgAvg oa fun o => uniformStartDistinguisher (paramsV1 Z K (ida o) (idb o)) ℓ
          (configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT)) qep
          (A o).refuseCorrB0)] := by
    rw [prgReal_avg]
    exact evalDist_bind_congr _ _ _ fun o => evalDist_gameR_libSessionR_eq_prgReal _ ℓ encPt lam _
      qep _
  unfold PRGScheme.prgAdvantage
  rw [hU, hR, Measure.boolDist_comm
    𝒟[(LibsignalSim.rootKdfAsPrg Z.F (encPt lam)).prgRealExperiment _]]
  exact SM.Construction.boolBias_le_add_two_mul_boolDist _ _

theorem boolDist_bind_le_add3 {α : Type} (oa : ProbComp α) (f g h₁ h₂ h₃ : α → ProbComp Bool)
    (c : ℝ≥0∞)
    (H : ∀ a, 𝒟[f a].boolDist 𝒟[g a] ≤
      c + (𝒟[h₁ a] {true} + 𝒟[h₂ a] {true} + 𝒟[h₃ a] {true})) :
    𝒟[oa >>= f].boolDist 𝒟[oa >>= g] ≤
      c + (𝒟[oa >>= h₁] {true} + 𝒟[oa >>= h₂] {true} + 𝒟[oa >>= h₃] {true}) := by
  refine Measure.boolDist_le_of_apply_le _ _ fun v => ?_
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  rw [evalDist_bind_apply_lintegral, evalDist_bind_apply_lintegral,
    evalDist_bind_apply_lintegral, evalDist_bind_apply_lintegral,
    evalDist_bind_apply_lintegral]
  calc ∫⁻ a, 𝒟[f a] {v} ∂𝒟[oa]
      ≤ ∫⁻ a, (𝒟[g a] {v} + (c + (𝒟[h₁ a] {true} + 𝒟[h₂ a] {true} + 𝒟[h₃ a] {true}))) ∂𝒟[oa] :=
        lintegral_mono fun a => (apply_le_add_boolDist _ _ v).trans (add_le_add le_rfl (H a))
    _ = ∫⁻ a, 𝒟[g a] {v} ∂𝒟[oa] +
          (c + (∫⁻ a, 𝒟[h₁ a] {true} ∂𝒟[oa] + ∫⁻ a, 𝒟[h₂ a] {true} ∂𝒟[oa] +
            ∫⁻ a, 𝒟[h₃ a] {true} ∂𝒟[oa])) := by
      rw [lintegral_add_left Measurable.of_discrete, lintegral_add_left measurable_const,
        lintegral_const, evalDist_apply_univ_eq_one, mul_one,
        lintegral_add_left Measurable.of_discrete, lintegral_add_left Measurable.of_discrete]

/-! ## Mixture refinement, epoch-0, and hidden-salt bounds -/

section RefineV1

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

/-- Mixture simulator refinement bound for `paramsV1`. -/
theorem boolBias_mixR_le_v1 {α : Type} (Z : Crypto) (K : MlKem) (hK_tot : Encaps1Total K)
    {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh Z Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hD : ∀ k x, Z.D k (Z.E k x) = x) (hinj : Function.Injective encT)
    (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0) (lam : Pt) (qep q : ℕ)
    (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (oa : ProbComp α) (ida idb : α → IdentityKey)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : ∀ o, SM.MakesAtMostQueries (A o) q) :
    𝒟[oa >>= fun o => SM.gameR (libsignalSessionScheme (paramsV1 Z K (ida o) (idb o)) ℓ encPt lam) 3 qep
        (configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT)) (A o)].boolBias ≤
      𝒟[oa >>= fun o => SM.game (lFig8 Dh encPt Z protoSignalCodec ℓ encT
          (idsOf (ida o) (idb o)) 25000 lam) 3 (qep + 1) SM.Config.h1
          (Refine.libsignalToModularSchemeSim (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT
            (idsOf (ida o) (idb o)) lam qep (A o))].boolBias
        + 2 * (refineConst Z Dh encPt q qep δ +
          (𝒟[oa >>= fun o => simCNoneWinEvent (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT
              (idsOf (ida o) (idb o)) lam qep (A o)] {true} +
           𝒟[oa >>= fun o => eps0Event (paramsV1 Z K (ida o) (idb o)) ℓ encPt lam
              (ratchetKeyAdmissible protoSignalCodec decT encT) qep (A o)] {true} +
           𝒟[oa >>= fun o => hiddenSaltGame (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT
              (idsOf (ida o) (idb o)) lam qep (A o)] {true})) := by
  refine (SM.Construction.boolBias_le_add_two_mul_boolDist _ _).trans (add_le_add le_rfl ?_)
  refine mul_le_mul_right ?_ 2
  refine boolDist_bind_le_add3 _ _ _ _ _ _ _ fun o => ?_
  have hL : LengthsOk (paramsV1 Z K (ida o) (idb o)) ℓ :=
    lengthsOk_paramsIdsWithSpqr_v1 Z K (ida o) (idb o) ℓ hℓ
  have hrt : RoundTrip.RtHyp (paramsV1 Z K (ida o) (idb o)) ℓ :=
    ⟨CryptoVerification.LibsignalSession.signalRoundTripShort_proto, hL,
      CryptoVerification.LibsignalSession.signalEncodeFits32_proto⟩
  have hS : Corr.SpqrSendCorrectQ (paramsV1 Z K (ida o) (idb o)).spqr q :=
    spqrV1SessionB_sendCorrectQ Z.F K hK_tot q (by omega)
  refine (sim_game_boolDist_le_C (paramsV1 Z K (ida o) (idb o)) ℓ Dh hDh encPt encT decT hX hdec
    hD hrt hinj hdum hz (idsOf (ida o) (idb o)) ⟨rfl, rfl⟩ lam qep q hS (by omega) δ hδ (A o)
    (hq o)).trans_eq ?_
  have hC : (paramsV1 Z K (ida o) (idb o)).C = Z := rfl
  have hcod : (paramsV1 Z K (ida o) (idb o)).codec = protoSignalCodec := rfl
  rw [hC, hcod]
  unfold refineConst hiddenSaltTerm
  ring

/-- Mixture epoch-0 bound for `paramsV1` with a single uniform `rootKdfAsPrg` distinguisher. -/
theorem evalDist_mixEps0_le_v1 {α : Type} (Z : Crypto) (K : MlKem) {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (hX : X25519RealizesDh Z Dh encPt encT)
    (hdec : ∀ T, decT (encT T) = some T) (hinj : Function.Injective encT)
    (hdum : ∀ T, encT T ≠ dummyKey) (lam : Pt) (qep q : ℕ)
    (oa : ProbComp α) (ida idb : α → IdentityKey)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : ∀ o, SM.MakesAtMostQueries (A o) q) :
    𝒟[oa >>= fun o => eps0Event (paramsV1 Z K (ida o) (idb o)) ℓ encPt lam
        (ratchetKeyAdmissible protoSignalCodec decT encT) qep (A o)] {true} ≤
      (rootKdfAsPrg Z.F (encPt lam)).prgAdvantage
          (prgAvg oa fun o => epoch0Distinguisher (paramsV1 Z K (ida o) (idb o)) ℓ
            (ratchetKeyAdmissible protoSignalCodec decT encT) qep (A o))
        + q * eps0IdealUnit Z.F := by
  have hR : 𝒟[oa >>= fun o => eps0Event (paramsV1 Z K (ida o) (idb o)) ℓ encPt lam
        (ratchetKeyAdmissible protoSignalCodec decT encT) qep (A o)] =
      𝒟[(rootKdfAsPrg Z.F (encPt lam)).prgRealExperiment
          (prgAvg oa fun o => epoch0Distinguisher (paramsV1 Z K (ida o) (idb o)) ℓ
            (ratchetKeyAdmissible protoSignalCodec decT encT) qep (A o))] := by
    rw [prgReal_avg]
    exact evalDist_bind_congr _ _ _ fun o => evalDist_eps0Event_eq_prgReal _ ℓ encPt lam _ qep _
  rw [hR]
  refine (Refinement.prgReal_true_le _ _).trans (add_le_add le_rfl ?_)
  rw [prgIdeal_avg]
  refine evalDist_bind_apply_le_const _ _ _ true fun o => ?_
  have hrt : RoundTrip.RtHyp (paramsV1 Z K (ida o) (idb o)) ℓ :=
    ⟨CryptoVerification.LibsignalSession.signalRoundTripShort_proto,
      lengthsOk_paramsIdsWithSpqr_v1 Z K (ida o) (idb o) ℓ hℓ,
      CryptoVerification.LibsignalSession.signalEncodeFits32_proto⟩
  exact eps0_ideal_le (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT hX hdec hinj hdum hrt
    qep q (A o) (hq o)

end RefineV1

/-! ## Mixture Fig. 8 bounds -/

section Fig8V1

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

/-- Authenticity term of the mixture Fig. 8 bound for `libsignalToModularSchemeSim` on `paramsV1`. -/
noncomputable def fig8MixAuth_v1 {α : Type} (Z : Crypto) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) (oa : ProbComp α)
    (ida idb : α → IdentityKey)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes) : ℝ≥0∞ :=
  letI : MeasurableSpace α := ⊤
  2 * ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) t,
    (CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
        (advAvg oa fun o => redCKAAuth (dhScheme Dh) (rootPRNG Z.F encPt)
          (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL t
          (Thm1.challSim (2 + 1) (qep + 1)
            (Refine.libsignalToModularSchemeSim (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT
              (idsOf (ida o) (idb o)) lam qep (A o))))
      + PRFPRNG.advantage (rootPRNG Z.F encPt)
        (advAvg oa fun o => redPRNGAuth (dhScheme Dh) (rootPRNG Z.F encPt)
          (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL t
          (Thm1.challSim (2 + 1) (qep + 1)
            (Refine.libsignalToModularSchemeSim (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT
              (idsOf (ida o) (idb o)) lam qep (A o))))
      + ∫⁻ o, ∑ j ∈ Finset.range q,
          FSAEAD.advantage (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000)
            (redFSAuth (dhScheme Dh) (rootPRNG Z.F encPt)
              (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) j
              tL t (Thm1.challSim (2 + 1) (qep + 1)
                (Refine.libsignalToModularSchemeSim (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT
                  (idsOf (ida o) (idb o)) lam qep (A o))))
          ∂𝒟[oa])

/-- Privacy term of the mixture Fig. 8 bound for `libsignalToModularSchemeSim` on `paramsV1`. -/
noncomputable def fig8MixPriv_v1 {α : Type} (Z : Crypto) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep : ℕ) (oa : ProbComp α)
    (ida idb : α → IdentityKey)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes) : ℝ≥0∞ :=
  letI : MeasurableSpace α := ⊤
  2 * ∑ i ∈ Finset.range ((qep + 1) + 1), ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) i,
    (2 * CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
        (advAvg oa fun o => redCKAPriv (dhScheme Dh) (rootPRNG Z.F encPt)
          (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL i
          (ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ)
            (Refine.libsignalToModularSchemeSim (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT
              (idsOf (ida o) (idb o)) lam qep (A o))))
      + 2 * PRFPRNG.advantage (rootPRNG Z.F encPt)
        (advAvg oa fun o => redPRNGPriv (dhScheme Dh) (rootPRNG Z.F encPt)
          (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL i
          (ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ)
            (Refine.libsignalToModularSchemeSim (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT
              (idsOf (ida o) (idb o)) lam qep (A o))))
      + 𝒟[oa >>= fun o =>
          FSAEAD.game (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000)
            (redFSPriv (dhScheme Dh) (rootPRNG Z.F encPt)
              (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL i
              (ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ)
                (Refine.libsignalToModularSchemeSim (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT
                  (idsOf (ida o) (idb o)) lam qep (A o))))].boolBias
      + 2 * ∫⁻ o,
          FSAEAD.advantage (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000)
            (redFSPrivCoin (dhScheme Dh) (rootPRNG Z.F encPt)
              (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL i
              (ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ)
                (Refine.libsignalToModularSchemeSim (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT
                  (idsOf (ida o) (idb o)) lam qep (A o))))
          ∂𝒟[oa])

/-- Mixture Fig. 8 H1 bias bound for `libsignalToModularSchemeSim`. -/
theorem boolBias_mixFig8_le_v1 {α : Type} (Z : Crypto) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ)
    (oa : ProbComp α) (ida idb : α → IdentityKey)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : ∀ o, SM.MakesAtMostQueries (A o) q) :
    𝒟[oa >>= fun o => SM.game (lFig8 Dh encPt Z protoSignalCodec ℓ encT
        (idsOf (ida o) (idb o)) 25000 lam) 3 (qep + 1) SM.Config.h1
        (Refine.libsignalToModularSchemeSim (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT
          (idsOf (ida o) (idb o)) lam qep (A o))].boolBias ≤
      fig8MixAuth_v1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb A
        + fig8MixPriv_v1 Z K ℓ Dh encPt encT decT lam qep oa ida idb A := by
  exact theorem6_h1_blank_mix (dhScheme Dh) (rootPRNG Z.F encPt)
    (fun o => lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1)
    (dhScheme_correct Dh hDh) (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => m.1) (lBlank ℓ)
    (fun _ _ h => by simp [lBlank, h]) oa
    (fun o => Refine.libsignalToModularSchemeSim (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT
      (idsOf (ida o) (idb o)) lam qep (A o))
    (fun o => Proofs.Refinement.simC_equalPub_proof (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT
      decT (idsOf (ida o) (idb o)) lam qep (A o)) q
    (fun o => Proofs.Refinement.simC_queries_proof (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT
      decT (idsOf (ida o) (idb o)) lam qep q (A o) (hq o))

theorem evalDist_mixSimCNoneWin_le_v1 {α : Type} (Z : Crypto) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep : ℕ) (oa : ProbComp α)
    (ida idb : α → IdentityKey)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes) :
    𝒟[oa >>= fun o => simCNoneWinEvent (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT
        (idsOf (ida o) (idb o)) lam qep (A o)] {true} ≤
      ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) t,
        𝒟[oa >>= fun o => authGame (lFig8 Dh encPt Z protoSignalCodec ℓ encT
          (idsOf (ida o) (idb o)) 25000 lam) (2 + 1) (qep + 1) tL t
          (Thm1.challSim (2 + 1) (qep + 1)
            (Refine.libsignalToModularSchemeSim (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT
              (idsOf (ida o) (idb o)) lam qep (A o)))]
          {true} :=
  evalDist_bind_apply_le_sum_sum oa _ _ _ _ fun o =>
    simCNoneWinEvent_le_auth (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT
      (idsOf (ida o) (idb o)) lam qep (A o)

/-- Bounds twice the mixture `simCNoneWinEvent` probability by `fig8MixAuth_v1`. -/
theorem evalDist_mixSimCNoneWin_le_auth_v1 {α : Type} (Z : Crypto) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ)
    (oa : ProbComp α) (ida idb : α → IdentityKey)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : ∀ o, SM.MakesAtMostQueries (A o) q) :
    2 * 𝒟[oa >>= fun o => simCNoneWinEvent (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT
        (idsOf (ida o) (idb o)) lam qep (A o)] {true} ≤
      fig8MixAuth_v1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb A := by
  refine (mul_le_mul_right
    (evalDist_mixSimCNoneWin_le_v1 Z K ℓ Dh encPt encT decT lam qep oa ida idb A) 2).trans ?_
  unfold fig8MixAuth_v1
  gcongr with t _ tL _
  exact theorem8_mix (dhScheme Dh) (rootPRNG Z.F encPt)
    (fun o => lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1)
    (dhScheme_correct Dh hDh) tL t q oa _ fun o => Thm1.challSim_queries _ _ _ q
      (Proofs.Refinement.simC_queries_proof (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT
        (idsOf (ida o) (idb o)) lam qep q (A o) (hq o))

end Fig8V1

/-! ## Mixture FS-AEAD bound -/

section ShortMixV1

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

omit [Zero Pt] [SampleableType Pt] in
/-- Mixture FS-AEAD bound from `FsOk`. -/
theorem lFS_bound_mix_of_fsOk_v1 {α : Type} (C : Crypto) (hD : ∀ k x, C.D k (C.E k x) = x)
    (ℓ : ℕ) (hℓ : ℓ < 2 ^ 31)
    (encT : Pt → PublicKey) (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (oa : ProbComp α) (idOf : α → Party → IdentityKey)
    (A : α → FSAEAD.RatchetAdversary (BitVec 256) (BitVec 256) (Header Pt) (LibsignalMsgPublicPart × CBC.Plain ℓ)
      LibsignalCiphertextWithSalt32) (q qd : ℕ) (hq32 : q + 25002 < 2 ^ 32)
    (hok : ∀ o, CryptoVerification.LibsignalSession.FsOk ℓ q qd (A o)) :
    𝒟[oa >>= fun o => FSAEAD.game (lFS C protoSignalCodec ℓ encT (idOf o) 25000) (A o)].boolBias ≤
      FSMix.fsShortBoundMix C protoSignalCodec ℓ encT oa idOf 25000 q qd A :=
  FSMix.lFS_bound_mix C hD protoSignalCodec
    CryptoVerification.LibsignalSession.signalRoundTripShort_proto
    CryptoVerification.LibsignalSession.signalEncodeFits32_proto ℓ
    (by omega) encT hinj hdum oa idOf 25000 le_rfl A q qd
    (fun o => (hok o).1) (fun o => (hok o).2.1) hq32 (fun o => (hok o).2.2.1)
    (fun o => (hok o).2.2.2.1) (fun o => (hok o).2.2.2.2.1) (fun o => (hok o).2.2.2.2.2)

end ShortMixV1

/-! ## Generic simulator-family Fig. 8 mixture bounds -/

section Fig8GenV1

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

/-- Authenticity term of the mixture Fig. 8 bound for a simulator family `simH`. -/
noncomputable def fig8MixAuthGen_v1 {α : Type} (Z : Crypto) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (lam : Pt) (qep q : ℕ) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (simH : α → Fig8Adv Pt ℓ) : ℝ≥0∞ :=
  letI : MeasurableSpace α := ⊤
  2 * ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) t,
    (CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
        (advAvg oa fun o => redCKAAuth (dhScheme Dh) (rootPRNG Z.F encPt)
          (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL t
          (Thm1.challSim (2 + 1) (qep + 1) (simH o)))
      + PRFPRNG.advantage (rootPRNG Z.F encPt)
        (advAvg oa fun o => redPRNGAuth (dhScheme Dh) (rootPRNG Z.F encPt)
          (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL t
          (Thm1.challSim (2 + 1) (qep + 1) (simH o)))
      + ∫⁻ o, ∑ j ∈ Finset.range q,
          FSAEAD.advantage (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000)
            (redFSAuth (dhScheme Dh) (rootPRNG Z.F encPt)
              (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) j
              tL t (Thm1.challSim (2 + 1) (qep + 1) (simH o)))
          ∂𝒟[oa])

/-- Privacy term of the mixture Fig. 8 bound for a simulator family `simH`. -/
noncomputable def fig8MixPrivGen_v1 {α : Type} (Z : Crypto) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (lam : Pt) (qep : ℕ) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (simH : α → Fig8Adv Pt ℓ) : ℝ≥0∞ :=
  letI : MeasurableSpace α := ⊤
  2 * ∑ i ∈ Finset.range ((qep + 1) + 1), ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) i,
    (2 * CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
        (advAvg oa fun o => redCKAPriv (dhScheme Dh) (rootPRNG Z.F encPt)
          (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL i
          (ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simH o)))
      + 2 * PRFPRNG.advantage (rootPRNG Z.F encPt)
        (advAvg oa fun o => redPRNGPriv (dhScheme Dh) (rootPRNG Z.F encPt)
          (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL i
          (ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simH o)))
      + 𝒟[oa >>= fun o =>
          FSAEAD.game (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000)
            (redFSPriv (dhScheme Dh) (rootPRNG Z.F encPt)
              (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL i
              (ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simH o)))].boolBias
      + 2 * ∫⁻ o,
          FSAEAD.advantage (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000)
            (redFSPrivCoin (dhScheme Dh) (rootPRNG Z.F encPt)
              (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL i
              (ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simH o)))
          ∂𝒟[oa])

theorem boolBias_mixFig8Gen_le_v1 {α : Type} (Z : Crypto) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (qep q : ℕ)
    (oa : ProbComp α) (ida idb : α → IdentityKey) (simH : α → Fig8Adv Pt ℓ)
    (heqPub : ∀ o, SM.EqualPubChalls (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => m.1) (simH o))
    (hqSim : ∀ o, SM.MakesAtMostQueries (simH o) q) :
    𝒟[oa >>= fun o => SM.game (lFig8 Dh encPt Z protoSignalCodec ℓ encT
        (idsOf (ida o) (idb o)) 25000 lam) 3 (qep + 1) SM.Config.h1 (simH o)].boolBias ≤
      fig8MixAuthGen_v1 Z ℓ Dh encPt encT lam qep q oa ida idb simH
        + fig8MixPrivGen_v1 Z ℓ Dh encPt encT lam qep oa ida idb simH :=
  theorem6_h1_blank_mix (dhScheme Dh) (rootPRNG Z.F encPt)
    (fun o => lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1)
    (dhScheme_correct Dh hDh) (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => m.1) (lBlank ℓ)
    (fun _ _ h => by simp [lBlank, h]) oa simH heqPub q hqSim

theorem evalDist_mixWinGen_le_auth_v1 {α : Type} (Z : Crypto) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (qep q : ℕ)
    (oa : ProbComp α) (ida idb : α → IdentityKey) (simH : α → Fig8Adv Pt ℓ)
    (hqSim : ∀ o, SM.MakesAtMostQueries (simH o) q) :
    2 * 𝒟[oa >>= fun o => do
        let b ← $ᵗ Bool
        let sm := lFig8 Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000 lam
        let (_, s) ← SM.run sm 3 (qep + 1) SM.Config.h1 b (simH o)
        return s.win] {true} ≤
      fig8MixAuthGen_v1 Z ℓ Dh encPt encT lam qep q oa ida idb simH := by
  have h1 :
      𝒟[oa >>= fun o => do
          let b ← $ᵗ Bool
          let sm := lFig8 Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000 lam
          let (_, s) ← SM.run sm 3 (qep + 1) SM.Config.h1 b (simH o)
          return s.win] {true} ≤
        ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) t,
          𝒟[oa >>= fun o => authGame (lFig8 Dh encPt Z protoSignalCodec ℓ encT
            (idsOf (ida o) (idb o)) 25000 lam) (2 + 1) (qep + 1) tL t
            (Thm1.challSim (2 + 1) (qep + 1) (simH o))] {true} :=
    evalDist_bind_apply_le_sum_sum oa _ _ _ _ fun o =>
      run_win_prob_le_auth (lFig8 Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000 lam)
        (2 + 1) (qep + 1) (by omega) (simH o)
  refine (mul_le_mul_right h1 2).trans ?_
  unfold fig8MixAuthGen_v1
  gcongr with t _ tL _
  exact theorem8_mix (dhScheme Dh) (rootPRNG Z.F encPt)
    (fun o => lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1)
    (dhScheme_correct Dh hDh) tL t q oa _ fun o => Thm1.challSim_queries _ _ _ q (hqSim o)

theorem fig8MixAuthGen_eq_fig8MixAuth_v1 {α : Type} (Z : Crypto) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) (oa : ProbComp α)
    (ida idb : α → IdentityKey)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes) :
    fig8MixAuthGen_v1 Z ℓ Dh encPt encT lam qep q oa ida idb
      (fun o => Refine.libsignalToModularSchemeSim (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT
        (idsOf (ida o) (idb o)) lam qep (A o)) =
    fig8MixAuth_v1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb A := rfl

theorem fig8MixPrivGen_eq_fig8MixPriv_v1 {α : Type} (Z : Crypto) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep : ℕ) (oa : ProbComp α)
    (ida idb : α → IdentityKey)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes) :
    fig8MixPrivGen_v1 Z ℓ Dh encPt encT lam qep oa ida idb
      (fun o => Refine.libsignalToModularSchemeSim (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT
        (idsOf (ida o) (idb o)) lam qep (A o)) =
    fig8MixPriv_v1 Z K ℓ Dh encPt encT decT lam qep oa ida idb A := rfl

end Fig8GenV1

/-! ## Tracker-halted simulator Fig. 8 mixture bounds -/

section Fig8TrackHaltedV1

open CryptoGames.Ratchet.LibsignalSimC

private def srh_QBC {PQ Pt : Type} {ℓ : ℕ}
    (Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop) [DecidablePred Q]
    {α : Type} (x : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α)
    (n : ℕ) : Prop :=
  ∀ sC : LibsignalToModularSchemeSimState PQ Pt ℓ, IsQueryBoundP (x.run sC) Q n

private theorem srh_qbc_pure {PQ Pt : Type} {ℓ : ℕ}
    {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {α : Type} (a : α) (n : ℕ) : srh_QBC (PQ := PQ) Q (pure a) n :=
  fun _ => by simp

private theorem srh_qbc_bind {PQ Pt : Type} {ℓ : ℕ}
    {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {α β : Type} {x : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α}
    {f : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) β} {n m : ℕ}
    (hx : srh_QBC Q x n) (hf : ∀ a, srh_QBC Q (f a) m) : srh_QBC Q (x >>= f) (n + m) :=
  fun sC => by
    rw [StateT.run_bind]
    exact isQueryBoundP_bind (hx sC) fun p _ => hf p.1 p.2

private theorem srh_qbc_bind0 {PQ Pt : Type} {ℓ : ℕ}
    {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {α β : Type} {x : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α}
    {f : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) β} {m : ℕ}
    (hx : srh_QBC Q x 0) (hf : ∀ a, srh_QBC Q (f a) m) : srh_QBC Q (x >>= f) m := by
  simpa using srh_qbc_bind hx hf

private theorem srh_qbc_bind_r {PQ Pt : Type} {ℓ : ℕ}
    {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {α β : Type} {x : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α}
    {f : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) β} {n : ℕ}
    (hx : srh_QBC Q x n) (hf : ∀ a, srh_QBC Q (f a) 0) : srh_QBC Q (x >>= f) n := by
  simpa using srh_qbc_bind hx hf

private theorem srh_qbc_ite {PQ Pt : Type} {ℓ : ℕ}
    {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {c : Prop} [Decidable c] {α : Type}
    {x y : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α} {n : ℕ}
    (hx : srh_QBC Q x n) (hy : srh_QBC Q y n) : srh_QBC Q (if c then x else y) n := by
  by_cases hc : c <;> simp [hc, hx, hy]

private theorem srh_qbc_ite_pure {PQ Pt : Type} {ℓ : ℕ}
    {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {c : Prop} [Decidable c] {α : Type} {a : α}
    {y : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α} {n : ℕ}
    (hy : srh_QBC Q y n) : srh_QBC Q (if c then pure a else y) n :=
  srh_qbc_ite (srh_qbc_pure a n) hy

private theorem srh_qbc_get {PQ Pt : Type} {ℓ : ℕ}
    {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q] :
    srh_QBC (PQ := PQ) Q
      (get : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ)
        (LibsignalToModularSchemeSimState PQ Pt ℓ)) 0 :=
  fun _ => by simp

private theorem srh_qbc_set {PQ Pt : Type} {ℓ : ℕ}
    {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    (sC' : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    srh_QBC Q (set sC' : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) PUnit) 0 :=
  fun _ => by simp

private theorem srh_qbc_modify {PQ Pt : Type} {ℓ : ℕ}
    {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    (f : LibsignalToModularSchemeSimState PQ Pt ℓ → LibsignalToModularSchemeSimState PQ Pt ℓ) :
    srh_QBC Q (modify f : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) PUnit) 0 :=
  fun _ => by simp

private theorem srh_qbc_zoomB {PQ Pt : Type} {ℓ : ℕ}
    {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {α : Type} {x : QueryBounds.SimM PQ Pt ℓ α} {n : ℕ} (hx : QueryBounds.QB Q x n) :
    srh_QBC Q (runOnBaseState idHook x) n := fun sC => by
  show IsQueryBoundP (x.run sC.base >>= fun p => pure (p.1, { sC with base := p.2 })) Q n
  simpa using hx sC.base

private theorem srh_qbc_liftC {PQ Pt : Type} {ℓ : ℕ}
    {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {α : Type} {x : Fig8Comp Pt ℓ α} {n : ℕ} (hx : IsQueryBoundP x Q n) :
    srh_QBC (PQ := PQ) Q (liftC idHook x) n := fun sC => by
  show IsQueryBoundP (x >>= fun a => pure (a, sC)) Q n
  simpa using isQueryBoundP_bind hx (fun a _ => isQueryBoundP_pure Q (a, sC) 0)

private theorem srh_qbc_liftC_query {PQ Pt : Type} {ℓ : ℕ}
    {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {t : (QueryBounds.FSpec Pt ℓ).Domain} {d : ℕ} (hd : Q t → 0 < d) :
    srh_QBC (PQ := PQ) Q (liftC idHook (query (spec := QueryBounds.FSpec Pt ℓ) t)) d :=
  srh_qbc_liftC ((isQueryBoundP_query_iff Q t d).2 hd)

private theorem srh_qbc_probe {PQ Pt : Type} {ℓ : ℕ}
    {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    (R : Party) (c' : Fig8C Pt) (d : ℕ) :
    srh_QBC (PQ := PQ) Q (StateT.lift ((idHook (ℓ := ℓ)).probe R c')) d := fun sC => by
  show IsQueryBoundP (pure () >>= fun a => pure (a, sC)) Q d
  simp

private theorem srh_qbc_fwdAnswerC {PQ Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] {ℓ : ℕ} (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × CBC.Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × CBC.Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q] (d : ℕ)
    (hQd : ∀ R c, Q (.inr (.inl (.inl (.inr (R, c))))) → 0 < d)
    (hQi : ∀ R c, Q (.inr (.inl (.inr (R, c)))) → 0 < d)
    (R : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ) (T : PublicKey)
    (pq' : PQ) (c' : Fig8C Pt) :
    srh_QBC Q (fwdAnswerC qep fig fs idHook R w isDel ci? T pq' c') d := by
  unfold fwdAnswerC
  refine srh_qbc_bind_r (srh_qbc_zoomB (QueryBounds.qb_fwd d hQd hQi R c')) fun res => ?_
  cases res with
  | none => exact srh_qbc_zoomB (QueryBounds.qb_onAnswer qep R w isDel ci? T pq' none)
  | some rr =>
    cases rr with
    | rejected => exact srh_qbc_zoomB (QueryBounds.qb_onAnswer qep R w isDel ci? T pq' (some .rejected))
    | accepted t i pm =>
      exact srh_qbc_bind0 (srh_qbc_modify _) fun _ =>
        srh_qbc_zoomB (QueryBounds.qb_onAnswer qep R w isDel ci? T pq' (some (.accepted t i pm)))

private theorem srh_qbc_resyncC {PQ Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] {ℓ : ℕ} (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × CBC.Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × CBC.Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q] (d : ℕ)
    (hQd : ∀ R c, Q (.inr (.inl (.inl (.inr (R, c))))) → 0 < d)
    (R : Party) (w : List (BitVec 8)) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (c : Fig8C Pt) (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × CBC.Plain ℓ))) :
    srh_QBC Q (resyncC qep fig fs idHook R w ci? T pq' c r) d := by
  unfold resyncC
  cases r with
  | none => exact srh_qbc_pure (some RecvResult.rejected) d
  | some tipm =>
    rcases tipm with ⟨t, i, pm⟩
    refine srh_qbc_bind_r (srh_qbc_liftC_query (hQd R c)) fun res => ?_
    cases res with
    | none => exact srh_qbc_pure (some RecvResult.rejected) 0
    | some rr =>
      cases rr with
      | rejected => exact srh_qbc_pure (some RecvResult.rejected) 0
      | accepted _ _ _ =>
        exact srh_qbc_bind0 (srh_qbc_modify _) fun _ =>
          srh_qbc_zoomB (QueryBounds.qb_onAccept qep R w true t i pm.2 ci? T pq')

private theorem srh_qbc_fwdC {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ PQC) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × CBC.Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × CBC.Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q] (d : ℕ)
    (hQd : ∀ R c, Q (.inr (.inl (.inl (.inr (R, c))))) → 0 < d)
    (hQi : ∀ R c, Q (.inr (.inl (.inr (R, c)))) → 0 < d)
    (R : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ) (T : PublicKey)
    (pq' : PQ) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt) :
    srh_QBC Q (fwdC P qep fig fs idHook R w isDel ci? T pq' honestC c') d := by
  unfold fwdC
  refine srh_qbc_bind0 srh_qbc_get fun sC => ?_
  cases honestC with
  | none => exact srh_qbc_fwdAnswerC qep fig fs d hQd hQi R w isDel ci? T pq' c'
  | some c =>
    dsimp only
    refine srh_qbc_ite ?_ (srh_qbc_fwdAnswerC qep fig fs d hQd hQi R w isDel ci? T pq' c')
    cases predictReceiveWithSnapshots fig fs P sC R w c c' with
    | some r => exact srh_qbc_resyncC qep fig fs d hQd R w ci? T pq' c r
    | none => exact srh_qbc_bind0 (srh_qbc_probe R c' 0) fun _ => srh_qbc_pure (some RecvResult.rejected) d

private theorem srh_qbc_fwdEvictC {PQ Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] {ℓ : ℕ} (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × CBC.Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × CBC.Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q] (d : ℕ)
    (hQd : ∀ R c, Q (.inr (.inl (.inl (.inr (R, c))))) → 0 < d)
    (hQi : ∀ R c, Q (.inr (.inl (.inr (R, c)))) → 0 < d)
    (R : Party) (w : List (BitVec 8)) (isDel : Bool) (T : PublicKey)
    (pq' : PQ) (c' : Fig8C Pt) :
    srh_QBC Q (fwdEvictC qep fig fs idHook R w isDel T pq' c') d := by
  unfold fwdEvictC
  refine srh_qbc_bind0 srh_qbc_get fun sC => ?_
  refine srh_qbc_ite ?_ (srh_qbc_fwdAnswerC qep fig fs d hQd hQi R w isDel none T pq' c')
  exact srh_qbc_bind0 (srh_qbc_probe R c' 0) fun _ => srh_qbc_pure (some RecvResult.rejected) d

private theorem srh_qbc_simRecvC {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ PQC) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × CBC.Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × CBC.Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q] (d : ℕ)
    (hQd : ∀ R c, Q (.inr (.inl (.inl (.inr (R, c))))) → 0 < d)
    (hQi : ∀ R c, Q (.inr (.inl (.inr (R, c)))) → 0 < d)
    (R : Party) (w : List (BitVec 8)) (isDel : Bool) :
    srh_QBC Q (simRecvC P encT decT qep fig fs idHook R w isDel) d := by
  unfold simRecvC
  refine srh_qbc_bind0 srh_qbc_get fun sC => ?_
  dsimp only
  refine srh_qbc_ite_pure (srh_qbc_ite_pure (srh_qbc_ite_pure (srh_qbc_ite_pure ?_)))
  cases (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => exact srh_qbc_pure (some RecvResult.rejected) d
  | some hp =>
    dsimp only
    refine srh_qbc_ite_pure (srh_qbc_ite_pure ?_)
    cases P.spqr.recv (sC.base.pq R) hp.1.pqRatchet with
    | error _ => exact srh_qbc_pure (some RecvResult.rejected) d
    | ok ps =>
      dsimp only
      cases (sC.base.chains R).findIdx? (fun g => g.key == some hp.1.senderRatchetKey) with
      | some ci =>
        dsimp only
        exact srh_qbc_ite_pure
          (srh_qbc_fwdC P qep fig fs d hQd hQi R w isDel (some ci) hp.1.senderRatchetKey ps.1 _ _)
      | none =>
        dsimp only
        refine srh_qbc_ite_pure (srh_qbc_ite_pure ?_)
        refine srh_qbc_ite (srh_qbc_bind0 (srh_qbc_modify _) fun _ => ?_) ?_ <;>
        · refine srh_qbc_ite_pure ?_
          cases decT hp.1.senderRatchetKey with
          | none => exact srh_qbc_pure (some RecvResult.rejected) d
          | some T =>
            exact srh_qbc_ite
              (srh_qbc_fwdEvictC qep fig fs d hQd hQi R w isDel hp.1.senderRatchetKey ps.1 _)
              (srh_qbc_fwdC P qep fig fs d hQd hQi R w isDel none hp.1.senderRatchetKey ps.1 _ _)

private theorem srh_qbc_simCorrC {PQ PQC Pt : Type} [Inhabited PQ] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q] (d : ℕ)
    (hQcorr : ∀ R, Q (.inr (.inr R)) → 0 < d) (R : Party) :
    srh_QBC Q (LibsignalSimC.simCorrC P encT idHook Dh R) d := by
  unfold LibsignalSimC.simCorrC
  refine srh_qbc_bind0 srh_qbc_get fun sC => ?_
  dsimp only
  refine srh_qbc_ite_pure ?_
  refine srh_qbc_bind_r (srh_qbc_liftC_query (hQcorr R)) fun res => ?_
  cases res with
  | none => exact srh_qbc_pure none 0
  | some st => exact srh_qbc_bind0 (srh_qbc_set _) fun _ => srh_qbc_pure _ 0

private theorem srh_qbc_guardC {PQ Pt : Type} {ℓ : ℕ}
    {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {α : Type} {x : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) (Option α)}
    {n : ℕ} (hx : srh_QBC Q x n) : srh_QBC Q (guardC x) n := by
  unfold guardC
  refine srh_qbc_bind0 srh_qbc_get fun sC => ?_
  split
  · exact srh_qbc_pure none n
  · exact hx

private abbrev SimCMPair (PQ Pt τ : Type) (ℓ : ℕ) :=
  StateT (LibsignalToModularSchemeSimState PQ Pt ℓ × τ) (Fig8Comp Pt ℓ)

private def srh_qbcP {PQ Pt τ : Type} {ℓ : ℕ}
    (Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop) [DecidablePred Q]
    {α : Type} (x : SimCMPair PQ Pt τ ℓ α) (n : ℕ) : Prop :=
  ∀ st : LibsignalToModularSchemeSimState PQ Pt ℓ × τ, IsQueryBoundP (x.run st) Q n

private theorem srh_qbcP_pure {PQ Pt τ : Type} {ℓ : ℕ}
    {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {α : Type} (a : α) (n : ℕ) : srh_qbcP (PQ := PQ) (τ := τ) Q (pure a) n :=
  fun _ => by simp

private theorem srh_qbcP_get {PQ Pt τ : Type} {ℓ : ℕ}
    {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q] :
    srh_qbcP (PQ := PQ) (τ := τ) Q
      (get : SimCMPair PQ Pt τ ℓ (LibsignalToModularSchemeSimState PQ Pt ℓ × τ)) 0 :=
  fun _ => by simp

private theorem srh_qbcP_set {PQ Pt τ : Type} {ℓ : ℕ}
    {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    (st' : LibsignalToModularSchemeSimState PQ Pt ℓ × τ) :
    srh_qbcP Q (set st' : SimCMPair PQ Pt τ ℓ PUnit) 0 :=
  fun _ => by simp

private theorem srh_qbcP_modify {PQ Pt τ : Type} {ℓ : ℕ}
    {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    (f : LibsignalToModularSchemeSimState PQ Pt ℓ × τ →
      LibsignalToModularSchemeSimState PQ Pt ℓ × τ) :
    srh_qbcP Q (modify f : SimCMPair PQ Pt τ ℓ PUnit) 0 :=
  fun _ => by simp

private theorem srh_qbcP_bind {PQ Pt τ : Type} {ℓ : ℕ}
    {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {α β : Type} {x : SimCMPair PQ Pt τ ℓ α}
    {f : α → SimCMPair PQ Pt τ ℓ β} {n m : ℕ}
    (hx : srh_qbcP Q x n) (hf : ∀ a, srh_qbcP Q (f a) m) : srh_qbcP Q (x >>= f) (n + m) :=
  fun st => by
    rw [StateT.run_bind]
    exact isQueryBoundP_bind (hx st) fun p _ => hf p.1 p.2

private theorem srh_qbcP_bind0 {PQ Pt τ : Type} {ℓ : ℕ}
    {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {α β : Type} {x : SimCMPair PQ Pt τ ℓ α}
    {f : α → SimCMPair PQ Pt τ ℓ β} {m : ℕ}
    (hx : srh_qbcP Q x 0) (hf : ∀ a, srh_qbcP Q (f a) m) : srh_qbcP Q (x >>= f) m := by
  simpa using srh_qbcP_bind hx hf

private theorem srh_qbcP_bind_r {PQ Pt τ : Type} {ℓ : ℕ}
    {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {α β : Type} {x : SimCMPair PQ Pt τ ℓ α}
    {f : α → SimCMPair PQ Pt τ ℓ β} {n : ℕ}
    (hx : srh_qbcP Q x n) (hf : ∀ a, srh_qbcP Q (f a) 0) : srh_qbcP Q (x >>= f) n := by
  simpa using srh_qbcP_bind hx hf

private theorem srh_qbcP_liftF {PQ Pt τ : Type} {ℓ : ℕ}
    {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {α : Type} {x : Fig8Comp Pt ℓ α} {n : ℕ} (hx : IsQueryBoundP x Q n) :
    srh_qbcP (PQ := PQ) (τ := τ) Q (StateT.lift x) n := fun st => by
  show IsQueryBoundP (x >>= fun a => pure (a, st)) Q n
  simpa using isQueryBoundP_bind hx (fun a _ => isQueryBoundP_pure Q (a, st) 0)

private theorem srh_qbcP_liftF_query {PQ Pt τ : Type} {ℓ : ℕ}
    {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {t : (QueryBounds.FSpec Pt ℓ).Domain} {d : ℕ} (hd : Q t → 0 < d) :
    srh_qbcP (PQ := PQ) (τ := τ) Q
      (StateT.lift (query (spec := QueryBounds.FSpec Pt ℓ) t)) d :=
  srh_qbcP_liftF ((isQueryBoundP_query_iff Q t d).2 hd)

private theorem srh_qbcP_liftS {PQ Pt τ : Type} {ℓ : ℕ}
    {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {α : Type} {m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α} {n : ℕ}
    (hm : srh_QBC Q m n) :
    srh_qbcP (τ := τ) Q (do
      let (sC, tr) ← get
      let (a, sC') ← StateT.lift (m.run sC)
      set (sC', tr)
      return a) n := by
  refine srh_qbcP_bind0 srh_qbcP_get fun ⟨sC, tr⟩ => ?_
  refine srh_qbcP_bind_r (srh_qbcP_liftF (hm sC)) fun ⟨a, sC'⟩ => ?_
  exact srh_qbcP_bind0 (srh_qbcP_set (sC', tr)) fun _ => srh_qbcP_pure a 0

private theorem srh_qbcP_simSendCTrackHalted {PQ Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × CBC.Plain ℓ) (BitVec 256) (Fig8C Pt))
    {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q] (d : ℕ)
    (hQu : ∀ u, ¬ Q (.inl u))
    (hQt : ∀ R pm rc, Q (.inr (.inl (.inl (.inl (.inl (R, pm, rc)))))) → 0 < d)
    (hQc : ∀ R pub m₀ m₁ rc, Q (.inr (.inl (.inl (.inl (.inr (R, (pub, m₀), (pub, m₁), rc)))))) → 0 < d)
    (R : Party) (m₀ : CBC.Plain ℓ) (chal : Option (CBC.Plain ℓ)) (r : Option (BitVec 512)) :
    srh_qbcP Q (simSendCTrackHalted P K qep fig idHook R m₀ chal r) d := by
  unfold simSendCTrackHalted
  generalize ($ᵗ BitVec 512 : ProbComp (BitVec 512)) = p512
  generalize ($ᵗ BitVec 256 : ProbComp (BitVec 256)) = p256
  refine srh_qbcP_bind0 srh_qbcP_get fun ⟨sC, tr⟩ => ?_
  dsimp only
  split
  · exact srh_qbcP_pure none d
  · cases sC.base.mir.epMgmt 3 qep R r.isSome with
    | none => exact srh_qbcP_pure none d
    | some s₁ =>
      dsimp only
      split
      · exact srh_qbcP_pure none d
      · refine srh_qbcP_bind0 ?_ fun rq => ?_
        · cases r with
          | some rq => exact srh_qbcP_liftF (isQueryBoundP_pure Q rq 0)
          | none => exact srh_qbcP_liftF (QueryBounds.isQueryBoundP_liftProb hQu p512)
        · split
          · exact srh_qbcP_bind0 (srh_qbcP_set _) fun _ => srh_qbcP_pure none d
          · refine srh_qbcP_bind0 ?_ fun rc => ?_
            · cases r with
              | some _ =>
                exact srh_qbcP_liftF
                  ((isQueryBoundP_map_iff _ _ _).mpr
                    (QueryBounds.isQueryBoundP_liftProb hQu p256))
              | none => exact srh_qbcP_liftF (isQueryBoundP_pure Q none 0)
            · cases mkPub (P := P) sC.base R rq
                  (if s₁.epoch R ≠ sC.base.mir.epoch R then BitVec.ofNat 32 (sC.base.mir.idx R - 1)
                   else sC.base.pn R) with
              | none => exact srh_qbcP_bind0 (srh_qbcP_set _) fun _ => srh_qbcP_pure none d
              | some pp =>
                rcases pp with ⟨pq', pub⟩
                dsimp only
                refine srh_qbcP_bind_r ?_ fun res => ?_
                · cases chal with
                  | none => exact srh_qbcP_liftF_query (hQt R (pub, m₀) rc)
                  | some m₁ => exact srh_qbcP_liftF_query (hQc R pub m₀ m₁ rc)
                · cases res with
                  | none => exact srh_qbcP_bind0 (srh_qbcP_set _) fun _ => srh_qbcP_pure none 0
                  | some c => exact srh_qbcP_bind0 (srh_qbcP_set _) fun _ => srh_qbcP_pure _ 0

private theorem srh_qbcP_simDeliverCTrackHalted {PQ Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × CBC.Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × CBC.Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q] (d : ℕ)
    (hQd : ∀ R c, Q (.inr (.inl (.inl (.inr (R, c))))) → 0 < d)
    (hQi : ∀ R c, Q (.inr (.inl (.inr (R, c)))) → 0 < d)
    (R : Party) (w : List (BitVec 8)) :
    srh_qbcP (τ := KemFailTrackState P.C.F) Q (
      let liftS {α : Type} (m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α) :
          SimCMPair PQ Pt (KemFailTrackState P.C.F) ℓ α := do
        let (sC, tr) ← get; let (a, sC') ← StateT.lift (m.run sC); set (sC', tr); return a
      do
        let (sC, _) ← get
        let j? := sC.base.honest.reverse.findIdx?
          (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == R.other)
        let res ← liftS (guardC (simRecvC (P := P) (encT := encT) (decT := decT)
          (qep := qep) (fig := fig) (fs := fs) (H := idHook) R w true))
        match res, j? with
        | some (.accepted _ _ _), some j =>
          modify fun (sC', tr) => (sC', stepKemFailDeliver P.C.F K tr R j)
        | _, _ => pure ()
        return res) d := by
  refine srh_qbcP_bind0 srh_qbcP_get fun ⟨sC, _⟩ => ?_
  refine srh_qbcP_bind_r
    (srh_qbcP_liftS (srh_qbc_guardC (srh_qbc_simRecvC P encT decT qep fig fs d hQd hQi R w true)))
    fun res => ?_
  cases res with
  | none => exact srh_qbcP_pure none 0
  | some rr =>
    cases rr with
    | rejected => exact srh_qbcP_pure (some RecvResult.rejected) 0
    | accepted t i m =>
      cases sC.base.honest.reverse.findIdx?
          (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == R.other) with
      | none => exact srh_qbcP_pure (some (RecvResult.accepted t i m)) 0
      | some j =>
        exact srh_qbcP_bind0 (srh_qbcP_modify _) fun _ => srh_qbcP_pure (some (RecvResult.accepted t i m)) 0

/-- `runLibsignalToModularSchemeSimTrackHalted` makes at most `q` queries when `A` does. -/
theorem simCTrackHalted_queries_proof {PQ Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (A : SM.Adversary (GhostState PQ) (CBC.Plain ℓ) (BitVec 512) (List (BitVec 8)))
    (hq : SM.MakesAtMostQueries A q) :
    SM.MakesAtMostQueries
      (runLibsignalToModularSchemeSimTrackHalted P K Dh encPt encT decT idOf lam qep A) q := by
  unfold SM.MakesAtMostQueries runLibsignalToModularSchemeSimTrackHalted simRunCTrackHaltedWith
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let fs := lFS P.C P.codec ℓ encT idOf 25000
  refine QueryBounds.isQueryBoundP_congr (p := QueryBounds.QInr Pt ℓ) (by rintro (_ | _) <;> rfl) ?_
  rw [← Nat.zero_add q]
  refine isQueryBoundP_bind
    (QueryBounds.isQueryBoundP_liftProb (Pt := Pt) (ℓ := ℓ) QueryBounds.hQu_QInr ($ᵗ BitVec 256))
    fun pqrKey _ => ?_
  have hsim : IsQueryBoundP
      ((simulateQ (simImplCTrackHalted P K encT decT qep fig fs idHook Dh) A).run
        (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
          initKemFailTrack P.C.F pqrKey)) (QueryBounds.QInr Pt ℓ) q := by
    refine IsQueryBoundP.simulateQ_run_of_step hq ?_ ?_ _
    · rintro (n | o) hp st
      · cases hp
      · rcases o with ((((⟨R, m, r⟩ | ⟨R, m₀, m₁, r⟩) | ⟨R, w⟩) | ⟨R, w⟩) | R)
        · exact srh_qbcP_simSendCTrackHalted P K qep fig 1 QueryBounds.hQu_QInr
            (fun _ _ _ _ => Nat.zero_lt_one) (fun _ _ _ _ _ _ => Nat.zero_lt_one) R m none r st
        · exact srh_qbcP_simSendCTrackHalted P K qep fig 1 QueryBounds.hQu_QInr
            (fun _ _ _ _ => Nat.zero_lt_one) (fun _ _ _ _ _ _ => Nat.zero_lt_one) R m₀ (some m₁) r st
        · exact srh_qbcP_simDeliverCTrackHalted P K encT decT qep fig fs 1
            (fun _ _ _ => Nat.zero_lt_one) (fun _ _ _ => Nat.zero_lt_one) R w st
        · exact srh_qbcP_liftS (srh_qbc_guardC (srh_qbc_simRecvC P encT decT qep fig fs 1
            (fun _ _ _ => Nat.zero_lt_one) (fun _ _ _ => Nat.zero_lt_one) R w false)) st
        · exact srh_qbcP_liftS
            (srh_qbc_guardC (srh_qbc_simCorrC P Dh encT 1 (fun _ _ => Nat.zero_lt_one) R)) st
    · rintro (n | o) hnp st
      · exact srh_qbcP_liftF (QueryBounds.isQueryBoundP_liftProb QueryBounds.hQu_QInr
          (query (spec := unifSpec) n)) st
      · exact absurd rfl hnp
  rw [StateT.run'_eq]
  exact (isQueryBoundP_map_iff _ _ _).mpr hsim

/-- `runLibsignalToModularSchemeSimTrackHalted` issues equal-public-part challenges. -/
theorem simCTrackHalted_equalPub_proof {PQ Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (A : SM.Adversary (GhostState PQ) (CBC.Plain ℓ) (BitVec 512) (List (BitVec 8))) :
    SM.EqualPubChalls (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => m.1)
      (runLibsignalToModularSchemeSimTrackHalted P K Dh encPt encT decT idOf lam qep A) := by
  unfold SM.EqualPubChalls runLibsignalToModularSchemeSimTrackHalted simRunCTrackHaltedWith
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let fs := lFS P.C P.codec ℓ encT idOf 25000
  change IsQueryBoundP _ (QueryBounds.QEq Pt ℓ) 0
  rw [← Nat.zero_add 0]
  refine isQueryBoundP_bind
    (QueryBounds.isQueryBoundP_liftProb (Pt := Pt) (ℓ := ℓ) QueryBounds.hQu_QEq ($ᵗ BitVec 256))
    fun pqrKey _ => ?_
  have hQt : ∀ R pm rc,
      QueryBounds.QEq Pt ℓ (.inr (.inl (.inl (.inl (.inl (R, pm, rc)))))) → 0 < 0 := fun _ _ _ h => nomatch h
  have hQc : ∀ R pub m₀ m₁ rc,
      QueryBounds.QEq Pt ℓ (.inr (.inl (.inl (.inl (.inr (R, (pub, m₀), (pub, m₁), rc)))))) →
        0 < 0 := by intro _ _ _ _ _ h; simp [QueryBounds.QEq, SM.unequalPubChall] at h
  have hQd : ∀ R c, QueryBounds.QEq Pt ℓ (.inr (.inl (.inl (.inr (R, c))))) → 0 < 0 := fun _ _ h => nomatch h
  have hQi : ∀ R c, QueryBounds.QEq Pt ℓ (.inr (.inl (.inr (R, c)))) → 0 < 0 := fun _ _ h => nomatch h
  have hQcorr : ∀ R, QueryBounds.QEq Pt ℓ (.inr (.inr R)) → 0 < 0 := fun _ h => nomatch h
  have hsim : IsQueryBoundP
      ((simulateQ (simImplCTrackHalted P K encT decT qep fig fs idHook Dh) A).run
        (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
          initKemFailTrack P.C.F pqrKey)) (QueryBounds.QEq Pt ℓ) 0 := by
    refine QueryBounds.isQueryBoundP_simulateQ_run_zero A (fun t st => ?_) _
    rcases t with (n | ((((⟨R, m, r⟩ | ⟨R, m₀, m₁, r⟩) | ⟨R, w⟩) | ⟨R, w⟩) | R))
    · exact srh_qbcP_liftF (QueryBounds.isQueryBoundP_liftProb QueryBounds.hQu_QEq
        (query (spec := unifSpec) n)) st
    · exact srh_qbcP_simSendCTrackHalted P K qep fig 0 QueryBounds.hQu_QEq hQt hQc R m none r st
    · exact srh_qbcP_simSendCTrackHalted P K qep fig 0 QueryBounds.hQu_QEq hQt hQc R m₀ (some m₁) r st
    · exact srh_qbcP_simDeliverCTrackHalted P K encT decT qep fig fs 0 hQd hQi R w st
    · exact srh_qbcP_liftS (srh_qbc_guardC (srh_qbc_simRecvC P encT decT qep fig fs 0 hQd hQi R w false)) st
    · exact srh_qbcP_liftS (srh_qbc_guardC (srh_qbc_simCorrC P Dh encT 0 hQcorr R)) st
  rw [StateT.run'_eq]
  exact (isQueryBoundP_map_iff _ _ _).mpr hsim

/-- Fig. 8 `win` event for `runLibsignalToModularSchemeSimTrackHalted`. -/
def simCNoneWinEventTrackHalted {PQ Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (lam : Pt) (qep : ℕ)
    (A : SM.Adversary (GhostState PQ) (CBC.Plain ℓ) (BitVec 512) (List (BitVec 8))) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let (_, s) ← SM.run sm 3 (qep + 1) SM.Config.h1 b
    (runLibsignalToModularSchemeSimTrackHalted P K Dh encPt encT decT idOf lam qep A)
  return s.win

noncomputable def fig8MixAuthTrackHalted_v1 {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] {α : Type} (Z : Crypto) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) (oa : ProbComp α)
    (ida idb : α → IdentityKey)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes) : ℝ≥0∞ :=
  fig8MixAuthGen_v1 Z ℓ Dh encPt encT lam qep q oa ida idb
    (fun o => runLibsignalToModularSchemeSimTrackHalted (paramsV1 Z K (ida o) (idb o)) K Dh encPt
      encT decT (idsOf (ida o) (idb o)) lam qep (A o))

noncomputable def fig8MixPrivTrackHalted_v1 {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] {α : Type} (Z : Crypto) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep : ℕ) (oa : ProbComp α)
    (ida idb : α → IdentityKey)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes) : ℝ≥0∞ :=
  fig8MixPrivGen_v1 Z ℓ Dh encPt encT lam qep oa ida idb
    (fun o => runLibsignalToModularSchemeSimTrackHalted (paramsV1 Z K (ida o) (idb o)) K Dh encPt
      encT decT (idsOf (ida o) (idb o)) lam qep (A o))

/-- Mixture Fig. 8 H1 bias bound for `runLibsignalToModularSchemeSimTrackHalted`. -/
theorem boolBias_mixFig8TrackHalted_le_v1 {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] {α : Type} (Z : Crypto) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ)
    (oa : ProbComp α) (ida idb : α → IdentityKey)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : ∀ o, SM.MakesAtMostQueries (A o) q) :
    𝒟[oa >>= fun o => SM.game (lFig8 Dh encPt Z protoSignalCodec ℓ encT
        (idsOf (ida o) (idb o)) 25000 lam) 3 (qep + 1) SM.Config.h1
        (runLibsignalToModularSchemeSimTrackHalted (paramsV1 Z K (ida o) (idb o)) K Dh encPt encT
          decT (idsOf (ida o) (idb o)) lam qep (A o))].boolBias ≤
      fig8MixAuthTrackHalted_v1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb A
        + fig8MixPrivTrackHalted_v1 Z K ℓ Dh encPt encT decT lam qep oa ida idb A :=
  boolBias_mixFig8Gen_le_v1 Z ℓ Dh hDh encPt encT lam qep q oa ida idb _
    (fun o => simCTrackHalted_equalPub_proof (paramsV1 Z K (ida o) (idb o)) K ℓ Dh encPt encT decT
      (idsOf (ida o) (idb o)) lam qep (A o))
    (fun o => simCTrackHalted_queries_proof (paramsV1 Z K (ida o) (idb o)) K ℓ Dh encPt encT decT
      (idsOf (ida o) (idb o)) lam qep q (A o) (hq o))

/-- Bounds twice the mixture `simCNoneWinEventTrackHalted` probability by `fig8MixAuthTrackHalted_v1`. -/
theorem evalDist_mixSimCNoneWinTrackHalted_le_auth_v1 {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] {α : Type} (Z : Crypto) (K : MlKem)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ)
    (oa : ProbComp α) (ida idb : α → IdentityKey)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : ∀ o, SM.MakesAtMostQueries (A o) q) :
    2 * 𝒟[oa >>= fun o => simCNoneWinEventTrackHalted (paramsV1 Z K (ida o) (idb o)) K ℓ Dh encPt
        encT decT (idsOf (ida o) (idb o)) lam qep (A o)] {true} ≤
      fig8MixAuthTrackHalted_v1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb A :=
  evalDist_mixWinGen_le_auth_v1 Z ℓ Dh hDh encPt encT lam qep q oa ida idb _
    (fun o => simCTrackHalted_queries_proof (paramsV1 Z K (ida o) (idb o)) K ℓ Dh encPt encT decT
      (idsOf (ida o) (idb o)) lam qep q (A o) (hq o))

end Fig8TrackHaltedV1

end CryptoVerification.E2E.Signed

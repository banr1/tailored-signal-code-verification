/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.HiddenSaltBound
public import Computational.Proofs.E2E.HeadlineComposed
public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECell
public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEReds
import Computational.Proofs.CryptoGames.CKA.DHProof
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperDir2
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperSim
import Computational.Proofs.E2E.ComposedPrefixHelpers
import Computational.Proofs.E2E.HeadlineSpkSession
import Computational.Proofs.E2E.SpkCostedAndHeadlineSlice
import Computational.Proofs.Game.PromotedCostedReds.Epoch0DistinguisherProg
import Computational.Proofs.HeadlineV1.DeliverForgePaperChallSim
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEClamp2
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEHaltedCouple
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEHaltedEvict
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNESkeleton
import Computational.Proofs.SessionCostedHalt
import Computational.Proofs.SignalPqxdh.Delta.Statements

/-!
# Headline Composed Security from `SessionCostedReductions`

Lifts per-session `SessionCostedReductions` families to `SessionCostedReductionFamily`, bounds the
`sessionSchemeU` and `sessionSchemeFixedSpk` mixture biases, and establishes the session and
composed `hiddenSaltBoundV1` bridges.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal BigOperators
open ReductionDsl OracleComp OracleSpec MeasureTheory
open CryptoGames CryptoGames.LibsignalSM CryptoGames.LibsignalSM.Inst
open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst
open CryptoGames.Ratchet.LibsignalSim CryptoGames.LibsignalSM.Proofs
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal
open CryptoVerification.LibsignalSession.HeadlineV1
open CryptoVerification.E2E.Signed
open CryptoGames.SM.Construction.AuthL11
open HMAC HKDF CBC LibsignalAead AEADScheme MACScheme WireAEAD FSAEAD

namespace CryptoVerification.E2E

attribute [local irreducible] CryptoVerification.E2E.HeadlineSpk.mkSpkCostedReds
attribute [local irreducible] Computational.Proofs.E2E.SpkCostedAndHeadlineSlice.spkCostedRedsInst

/-! ## Reduction family packaging -/

/-- Lifts a per-session `SessionCostedReductions` constructor family to `SessionCostedReductionFamily Pt ℓ`. -/
def spkSlotRedsWithSpqrOfV1SessionReds
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (v1Reds :
      (C : Crypto) → (K : MlKem) → (idA idB : IdentityKey) →
      (Dh : DHFun (BitVec 256) Pt) → (encPt : Pt → Bytes) →
      (encT : Pt → PublicKey) → (decT : PublicKey → Option Pt) →
      (lam : Pt) → (qep q : ℕ) →
      SessionCostedReductions Pt ℓ C K idA idB Dh encPt encT decT lam) :
    SessionCostedReductionFamily Pt ℓ :=
  fun C K idA idB Dh encPt encT decT lam qep q =>
    v1Reds C K idA idB Dh encPt encT decT lam qep q

theorem spkSlotRedsWithSpqrOfV1SessionReds_bounds
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (v1Reds :
      (C : Crypto) → (K : MlKem) → (idA idB : IdentityKey) →
      (Dh : DHFun (BitVec 256) Pt) → (encPt : Pt → Bytes) →
      (encT : Pt → PublicKey) → (decT : PublicKey → Option Pt) →
      (lam : Pt) → (qep q : ℕ) →
      SessionCostedReductions Pt ℓ C K idA idB Dh encPt encT decT lam)
    (hv1_bounds :
      ∀ (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
        (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
        (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ),
        sessionCostedReductionsBounded ℓ C K idA idB Dh encPt encT decT lam qep q
          (v1Reds C K idA idB Dh encPt encT decT lam qep q)) :
    SessionCostedReductionFamilyBounded ℓ (spkSlotRedsWithSpqrOfV1SessionReds v1Reds) :=
  hv1_bounds

/-! ## Uniform-start mixture bias -/

/-- Bounds the `sessionSchemeU` mixture bias by `uniformStartMixtureBound` from a session-level
`hiddenSaltBoundV1` bound on `support oa`. -/
theorem boolBias_mixU_le_uTermShortMix_of_v1SessionReds
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {α : Type} (Z : Crypto) (K : MlKem)
    (hK_tot : Encaps1Total K) (hD : ∀ k x, Z.D k (Z.E k x) = x)
    {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh Z Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (lam : Pt) (qep q : ℕ) (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt,
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o,
      SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : ∀ o ∈ support oa, SM.MakesAtMostQueries (A o) q)
    (hHid : ∀ o ∈ support oa,
      let P := paramsV1 Z K (ida o) (idb o)
      LibsignalSimC.hiddenSaltTerm P ℓ Dh encPt encT decT (idsOf (ida o) (idb o)) lam qep
          (RefuseB0.refuseCorrB0 (A o)) ≤
        hiddenSaltBoundV1 Z K ℓ Dh encPt encT decT (ida o) (idb o) lam qep q δ (R o)
          (RefuseB0.refuseCorrB0 (A o)))
    (hfig8 : ∀ o, (R o).fig8 =
      (v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).fig8 := by
      intros; rfl)
    (hfs : ∀ o, (R o).fs =
      (v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).fs := by
      intros; rfl)
    (hsimFig8 : ∀ o, (R o).simFig8 =
      (v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).simFig8 := by
      intros; rfl)
    (hepoch0Red : ∀ o, (R o).epoch0Red =
      (v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).epoch0Red := by
      intros; rfl)
    (huniformStartRed : ∀ o, (R o).uniformStartRed =
      (v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).uniformStartRed := by
      intros; rfl) :
    𝒟[oa >>= fun o => SM.gameR (sessionSchemeU (paramsV1 Z K (ida o) (idb o)) ℓ) 3 qep
        (configRefuseEarlyBobCorr decT encT) (A o)].boolBias ≤
      uniformStartMixtureBound Z K ℓ Dh encPt encT decT lam qep q δ oa ida idb R A := by
  let _ : MeasurableSpace α := ⊤
  obtain ⟨A', hsup, hq'⟩ :
      ∃ A' : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes,
        (∀ o ∈ support oa, A' o = A o) ∧ (∀ o, SM.MakesAtMostQueries (A' o) q) := by
    classical
    refine ⟨fun o => if o ∈ support oa then A o
      else (pure false : OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes) Bool),
      fun o ho => ?_, fun o => ?_⟩
    · dsimp only; split_ifs; rfl
    · dsimp only
      split_ifs with ho
      · exact hq o ho
      · unfold SM.MakesAtMostQueries; simp
  have hqR : ∀ o, SM.MakesAtMostQueries (RefuseB0.refuseCorrB0 (A' o)) q := fun o => by
    rw [refuseCorrB0_eq]
    exact RefuseCorrB0.refuseCorrB0_queries (A' o) q (hq' o)
  have hU := boolBias_mixU_le_v1 Z K encPt lam encT decT qep oa ida idb A'
  simp only [← refuseCorrB0_eq] at hU
  have hUsEq :
      (prgAvg oa fun o => uniformStartDistinguisher (paramsV1 Z K (ida o) (idb o)) ℓ
        (configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT)) qep
        (RefuseB0.refuseCorrB0 (A' o))) =
      (prefixPrgAvg oa fun o rc =>
        (R o).uniformStartRed.eval (fun _ => RefuseB0.refuseCorrB0 (A' o)) rc) := by
    funext rc
    unfold prgAvg CryptoVerification.E2E.prefixPrgAvg
    congr 1; funext o
    dsimp only
    rw [huniformStartRed o, v1SessionReds_uniformStartRed]
    exact
      (Computational.Proofs.Game.PromotedCostedReds.UniformStartDistinguisherProg.uniformStartRed_eval
        Z K Dh encPt encT decT (ida o) (idb o) lam ℓ q qep
        (RefuseB0.refuseCorrB0 (A' o)) rc (hqR o) hℓ).symm
  rw [hUsEq] at hU
  have hR := boolBias_mixR_le_v1 Z K hK_tot hℓ Dh hDh encPt encT decT hX hdec hD hinj hdum
    hz lam qep q hq32 δ hδ oa ida idb (fun o => RefuseB0.refuseCorrB0 (A' o)) hqR
  have hAuthEq :
      fig8MixShortAuthV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb
        (fun o => v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q)
        (fun o => RefuseB0.refuseCorrB0 (A' o)) =
      fig8MixShortAuthV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R
        (fun o => RefuseB0.refuseCorrB0 (A' o)) := by
    unfold fig8MixShortAuthV1
    simp only [← hfig8, ← hfs, ← hsimFig8]
  have hPrivEq :
      fig8MixShortPrivV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb
        (fun o => v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q)
        (fun o => RefuseB0.refuseCorrB0 (A' o)) =
      fig8MixShortPrivV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R
        (fun o => RefuseB0.refuseCorrB0 (A' o)) := by
    unfold fig8MixShortPrivV1
    simp only [← hfig8, ← hfs, ← hsimFig8]
  have h1 := boolBias_mixFig8_le_fig8MixShortV1 Z K hD hℓ Dh hDh encPt encT decT hinj hdum lam qep q
    (by omega) oa ida idb (fun o => RefuseB0.refuseCorrB0 (A' o)) hqR
  rw [hAuthEq, hPrivEq] at h1
  have h2 := evalDist_mixSimCNoneWin_le_fig8MixShortAuthV1 Z K hD hℓ Dh hDh encPt encT decT hinj hdum
    lam qep q (by omega) oa ida idb (fun o => RefuseB0.refuseCorrB0 (A' o)) hqR
  rw [hAuthEq] at h2
  have h3 := evalDist_mixEps0_le_v1 Z K hℓ Dh encPt encT decT hX hdec hinj hdum
    lam qep q oa ida idb (fun o => RefuseB0.refuseCorrB0 (A' o)) hqR
  have hEps0Eq :
      (prgAvg oa fun o => epoch0Distinguisher (paramsV1 Z K (ida o) (idb o)) ℓ
        (ratchetKeyAdmissible protoSignalCodec decT encT) qep
        (RefuseB0.refuseCorrB0 (A' o))) =
      (prefixPrgAvg oa fun o rc =>
        (R o).epoch0Red.eval (fun _ => RefuseB0.refuseCorrB0 (A' o)) rc) := by
    funext rc
    unfold prgAvg CryptoVerification.E2E.prefixPrgAvg
    congr 1; funext o
    dsimp only
    rw [hepoch0Red o, v1SessionReds_epoch0Red]
    exact
      (Computational.Proofs.Game.PromotedCostedReds.Epoch0DistinguisherProg.epoch0Red_eval
        Z K Dh encPt encT decT (ida o) (idb o) lam ℓ q qep
        (RefuseB0.refuseCorrB0 (A' o)) rc (hqR o) hℓ).symm
  rw [hEps0Eq] at h3
  have h4 := evalDist_mixHiddenSalt_le_v1_of_support Z K ℓ Dh encPt encT decT lam qep q δ
    oa ida idb R (fun o => RefuseB0.refuseCorrB0 (A' o))
    (fun o ho => by rw [hsup o ho]; exact hHid o ho)
  have hle :
      𝒟[oa >>= fun o => SM.gameR (sessionSchemeU (paramsV1 Z K (ida o) (idb o)) ℓ) 3 qep
          (configRefuseEarlyBobCorr decT encT) (A' o)].boolBias ≤
        uniformStartMixtureBound Z K ℓ Dh encPt encT decT lam qep q δ oa ida idb R A' := by
    refine hU.trans ((add_le_add hR le_rfl).trans ?_)
    rw [mul_add, mul_add, mul_add]
    refine (add_le_add (add_le_add h1 (add_le_add le_rfl (add_le_add
      (add_le_add h2 (mul_le_mul_right h3 2)) (mul_le_mul_right h4 2)))) le_rfl).trans_eq ?_
    unfold CryptoVerification.E2E.uniformStartMixtureBound
      Signed.refineConst CryptoVerification.E2E.refineConst
    ring
  have hg :
      𝒟[oa >>= fun o => SM.gameR (sessionSchemeU (paramsV1 Z K (ida o) (idb o)) ℓ) 3 qep
        (configRefuseEarlyBobCorr decT encT) (A' o)] =
      𝒟[oa >>= fun o => SM.gameR (sessionSchemeU (paramsV1 Z K (ida o) (idb o)) ℓ) 3 qep
        (configRefuseEarlyBobCorr decT encT) (A o)] :=
    OracleComp.evalDist_bind_congr_of_support oa _ _ fun o ho => by
      rw [hsup o ho]
  rw [hg, uTermShortMixV1_congr_of_support Z K ℓ Dh encPt encT decT lam qep q δ oa ida idb R _ _
    hsup] at hle
  exact hle

/-! ## Per-SPK-slot mixture bias -/

/-- Bounds the per-SPK-slot `sessionSchemeFixedSpk` mixture bias by `uniformStartMixtureBound` plus
the `Signed` PQXDH hop terms. -/
theorem boolBias_mixSpk_v1_le_of_v1SessionReds
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {α : Type} (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (hK_tot : Encaps1Total K) (hD : ∀ k x, C.D k (C.E k x) = x)
    {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (lam : Pt) (qep q : ℕ) (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt,
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256)
    (R : ∀ o, SessionCostedReductions Pt ℓ C K (ida o) (idb o)
      Dh encPt encT decT lam)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hker : ∀ o (x : BitVec 256) (P₁ P₂ : Pt),
      Dh.dh x P₁ = Dh.dh x P₂ ↔ Dh.dh (s o) P₁ = Dh.dh (s o) P₂)
    (hq : ∀ o ∈ support oa, SM.MakesAtMostQueries (A o) q)
    (hHid : ∀ o ∈ support oa,
      let P := paramsV1 C K (ida o) (idb o)
      LibsignalSimC.hiddenSaltTerm P ℓ Dh encPt encT decT (idsOf (ida o) (idb o)) lam qep
          (RefuseB0.refuseCorrB0 (A o)) ≤
        hiddenSaltBoundV1 C K ℓ Dh encPt encT decT (ida o) (idb o) lam qep q δ (R o)
          (RefuseB0.refuseCorrB0 (A o)))
    (hfig8 : ∀ o, (R o).fig8 =
      (v1SessionReds ℓ C K (ida o) (idb o) Dh encPt encT decT lam qep q).fig8 := by
      intros; rfl)
    (hfs : ∀ o, (R o).fs =
      (v1SessionReds ℓ C K (ida o) (idb o) Dh encPt encT decT lam qep q).fs := by
      intros; rfl)
    (hsimFig8 : ∀ o, (R o).simFig8 =
      (v1SessionReds ℓ C K (ida o) (idb o) Dh encPt encT decT lam qep q).simFig8 := by
      intros; rfl)
    (hepoch0Red : ∀ o, (R o).epoch0Red =
      (v1SessionReds ℓ C K (ida o) (idb o) Dh encPt encT decT lam qep q).epoch0Red := by
      intros; rfl)
    (huniformStartRed : ∀ o, (R o).uniformStartRed =
      (v1SessionReds ℓ C K (ida o) (idb o) Dh encPt encT decT lam qep q).uniformStartRed := by
      intros; rfl) :
    let spqr := LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K
    𝒟[oa >>= fun o =>
        SM.gameR (sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ (s o)) 3 qep
          (configRefuseEarlyBobCorr decT encT) (A o)].boolBias ≤
      uniformStartMixtureBound C K ℓ Dh encPt encT decT lam qep q δ oa ida idb R A
        + 2 * (extractPRF C.F encPt).prfAdvantage
            (Signed.leakAvgWithSpqr C spqr Dh encPt encT decT qep oa ida idb s A)
        + 2 * (extractPRF C.F encPt).prfAdvantage
            (Signed.leakUAvgWithSpqr C spqr Dh encPt encT decT qep oa ida idb A)
        + 2 * Signed.hop2TermAvgWithSpqr C spqr ℓ Dh encPt encT decT qep q oa ida idb s A := by
  intro spqr
  have hSpk := Signed.boolBias_mixSpkWithSpqr_le_of_support C spqr Dh encPt encT decT
    (by omega)
    (fun st rq st' salt msg h =>
      Nat.lt_of_le_of_lt (spqrV1Send_msg_len_le C.F K st rq st' salt msg h) (by decide))
    hDh hX hdec hz qep q oa ida idb s A hker hq
  have hU := boolBias_mixU_le_uTermShortMix_of_v1SessionReds C K hK_tot hD hℓ Dh hDh encPt encT
    decT hX hdec hinj hdum hz lam qep q hq32 δ hδ oa ida idb R A hq hHid hfig8 hfs hsimFig8
    hepoch0Red huniformStartRed
  exact hSpk.trans (add_le_add (add_le_add (add_le_add hU le_rfl) le_rfl) le_rfl)

/-! ## Composed headline bounds -/

/-- Packages a bounded `SessionCostedReductions` family satisfying the session-level
`hiddenSaltTerm` bound into `HiddenSaltBoundV1HoldsEx`. -/
theorem hiddenSaltBoundV1HoldsEx_of_v1SessionReds
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ)
    (v1Reds :
      (C : Crypto) → (K : LibsignalSpqrV1.MlKem) → (idA idB : IdentityKey) →
      (Dh : DHFun (BitVec 256) Pt) → (encPt : Pt → Bytes) →
      (encT : Pt → PublicKey) → (decT : PublicKey → Option Pt) →
      (lam : Pt) → (qep q : ℕ) →
      SessionCostedReductions Pt ℓ C K idA idB Dh encPt encT decT lam)
    (hv1_bounds :
      ∀ (C : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey)
        (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
        (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ),
        qep ≤ q + 4 →
          sessionCostedReductionsBounded ℓ C K idA idB Dh encPt encT decT lam qep q
            (v1Reds C K idA idB Dh encPt encT decT lam qep q))
    (hHid :
      ∀ (C : Crypto) (K : LibsignalSpqrV1.MlKem) (_hK_tot : Encaps1Total K)
        (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
        (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
        (lam : Pt) (qep q : ℕ) (_hℓ : ℓ < 10 ^ 6)
        (_hDh : Dh.Commutes) (_hX : X25519RealizesDh C Dh encPt encT)
        (_hdec : ∀ T, decT (encT T) = some T) (_hinj : Function.Injective encT)
        (_hdum : ∀ T, encT T ≠ dummyKey)
        (_hz : ∀ x, Dh.dh x 0 = 0) (_hD : ∀ k x, C.D k (C.E k x) = x)
        (_hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) (δ : ℝ≥0∞)
        (_hδ : ∀ Q : Pt,
          𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
        (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
        (_hq : SM.MakesAtMostQueries A q),
        let P := paramsV1 C K idA idB
        LibsignalSimC.hiddenSaltTerm P ℓ Dh encPt encT decT (idsOf idA idB) lam qep
            (RefuseB0.refuseCorrB0 A) ≤
          hiddenSaltBoundV1 C K ℓ Dh encPt encT decT idA idB lam qep q δ
            (v1Reds C K idA idB Dh encPt encT decT lam qep q)
            (RefuseB0.refuseCorrB0 A))
    (hspk :
      ∀ C K idA idB Dh encPt encT decT lam qep q,
        (v1Reds C K idA idB Dh encPt encT decT lam qep q).spk =
          Computational.Proofs.E2E.SpkCostedAndHeadlineSlice.spkCostedRedsInst
            ℓ C K idA idB Dh encPt encT decT lam q qep := by
      intros; rfl)
    (hfig8 :
      ∀ C K idA idB Dh encPt encT decT lam qep q,
        (v1Reds C K idA idB Dh encPt encT decT lam qep q).fig8 =
          (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).fig8 := by
      intros; rfl)
    (hfs :
      ∀ C K idA idB Dh encPt encT decT lam qep q,
        (v1Reds C K idA idB Dh encPt encT decT lam qep q).fs =
          (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).fs := by
      intros; rfl)
    (hsimFig8 :
      ∀ C K idA idB Dh encPt encT decT lam qep q,
        (v1Reds C K idA idB Dh encPt encT decT lam qep q).simFig8 =
          (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).simFig8 := by
      intros; rfl)
    (hepoch0Red :
      ∀ C K idA idB Dh encPt encT decT lam qep q,
        (v1Reds C K idA idB Dh encPt encT decT lam qep q).epoch0Red =
          (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).epoch0Red := by
      intros; rfl)
    (huniformStartRed :
      ∀ C K idA idB Dh encPt encT decT lam qep q,
        (v1Reds C K idA idB Dh encPt encT decT lam qep q).uniformStartRed =
          (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).uniformStartRed := by
      intros; rfl) :
    HiddenSaltBoundV1HoldsEx (Pt := Pt) ℓ := by
  intro C K idA idB Dh encPt encT decT lam qep q
  refine ⟨Computational.Proofs.SessionCostedHalt.clampSessionCostedReductionFamily ℓ v1Reds
      C K idA idB Dh encPt encT decT lam qep q,
    Computational.Proofs.SessionCostedHalt.clampSessionCostedReductionFamily_bounded ℓ v1Reds
      hv1_bounds C K idA idB Dh encPt encT decT lam qep q,
    ?_, ?_⟩
  · rw [Computational.Proofs.SessionCostedHalt.clampSessionCostedReductionFamily_fs, hfs]
    simp only [v1SessionReds_fs]
  · intro hqep
    rw [Computational.Proofs.SessionCostedHalt.clampSessionCostedReductionFamily_of_le ℓ v1Reds
      C K idA idB Dh encPt encT decT lam hqep]
    refine ⟨?_,
      hfig8 C K idA idB Dh encPt encT decT lam qep q,
      hsimFig8 C K idA idB Dh encPt encT decT lam qep q,
      hepoch0Red C K idA idB Dh encPt encT decT lam qep q,
      huniformStartRed C K idA idB Dh encPt encT decT lam qep q,
      ?_⟩
    · rw [hspk]
      intro hℓ hdec A hq
      exact
        ⟨fun s =>
          Computational.Proofs.E2E.SpkCostedAndHeadlineSlice.spkCostedRedsInst_evalSpkLeakRed
            (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam q qep s A hq hℓ,
         Computational.Proofs.E2E.SpkCostedAndHeadlineSlice.spkCostedRedsInst_evalSpkLeakRedU
            (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam q qep A hq hℓ,
         fun s j hj =>
          Computational.Proofs.E2E.SpkCostedAndHeadlineSlice.spkCostedRedsInst_evalHop2PrgRedK
            (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam q qep s j A hdec hj hq hℓ,
         fun s j hj =>
          Computational.Proofs.E2E.SpkCostedAndHeadlineSlice.spkCostedRedsInst_evalHop2PrfRedK
            (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam q qep s j A hdec hj hq hℓ⟩
    · intro hK_tot hℓ hDh hX hdec hinj hdum hz hD hq32 δ hδ A hq
      exact hHid C K hK_tot idA idB Dh encPt encT decT lam qep q hℓ hDh hX hdec hinj hdum hz hD
        hq32 δ hδ A hq

open CryptoVerification.E2E.RefuseCorrB0 CryptoVerification.E2E.HeadlineU

theorem forgeGuessedAdvantagePaper_le_hiddenSaltCellTermPaperDF
    {Pt PQ PQC : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [SampleableType PQC]
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    {t : ℕ} (_ht : t ∈ Finset.range ((qep + 1) + 2))
    {tL : Option ℕ} (_htL : tL ∈ admissibleLastLeakGuesses 2 t)
    (dfAdv : DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hc : (dhScheme Dh).Correct)
    (hq : DeliverForge.MakesAtMostQueriesDF
      (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv) q) :
    DeliverForge.forgeGuessedAdvantageCellPaper
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (qep + 1) DeliverForge.sameHdrScheme tL t
        (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv) ≤
      Proofs.Refinement.hiddenSaltCellTermPaperDF P ℓ Dh encPt encT idOf lam qep q tL t dfAdv := by
  by_cases h2 : 2 ≤ t ∧ tL = some (t - 2)
  · rcases h2 with ⟨ht2, rfl⟩
    unfold DeliverForge.forgeGuessedAdvantageCellPaper
      Proofs.Refinement.hiddenSaltCellTermPaperDF
      Proofs.Refinement.redCKAHiddenSaltPaperDF
      Proofs.Refinement.redPRNGHiddenSaltPaperDF
      Proofs.Refinement.redFSHiddenSaltPaperDF
    simp only [ht2, and_self, ↓reduceIte]
    exact DeliverForge.forgeGuessedAdvantageShiftedDir2Paper_le_reds
      (dhScheme Dh) (Ratchet.rootPRNG P.C.F encPt) (lFS P.C P.codec ℓ encT idOf 25000) lam
      (qep + 1) t q hc ht2
      (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv)
      (DeliverForge.noBadCoinsDF_challSimDF'Paper (2 + 1) (qep + 1) _) hq
  · by_cases h3 : 3 ≤ t ∧ tL = some (t - 3)
    · rcases h3 with ⟨ht3, rfl⟩
      have hne : t - 3 ≠ t - 2 := by omega
      unfold DeliverForge.forgeGuessedAdvantageCellPaper
        Proofs.Refinement.hiddenSaltCellTermPaperDF
        Proofs.Refinement.redCKAHiddenSaltPaperDF
        Proofs.Refinement.redPRNGHiddenSaltPaperDF
        Proofs.Refinement.redFSHiddenSaltPaperDF
      simp only [Option.some.injEq, hne, and_false, ht3, and_self, ↓reduceIte]
      exact DeliverForge.forgeGuessedAdvantageShiftedPaper_le_reds
        (dhScheme Dh) (Ratchet.rootPRNG P.C.F encPt) (lFS P.C P.codec ℓ encT idOf 25000) lam
        (qep + 1) t q hc ht3
        (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv)
        (DeliverForge.noBadCoinsDF_challSimDF'Paper (2 + 1) (qep + 1) _) hq
    · unfold DeliverForge.forgeGuessedAdvantageCellPaper
        Proofs.Refinement.hiddenSaltCellTermPaperDF
        Proofs.Refinement.redCKAHiddenSaltPaperDF
        Proofs.Refinement.redPRNGHiddenSaltPaperDF
        Proofs.Refinement.redFSHiddenSaltPaperDF
      simp only [h2, h3, ↓reduceIte]
      exact DeliverForge.theorem8_df_paper (dhScheme Dh) (Ratchet.rootPRNG P.C.F encPt)
        (lFS P.C P.codec ℓ encT idOf 25000) lam 1 (qep + 1) hc tL t q
        (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv) hq

theorem sum_forgeGuessedAdvantageCellPaper_le_sum_hiddenSaltCellTermPaperDF
    {Pt PQ PQC : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [SampleableType PQC]
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (dfAdv : DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hc : (dhScheme Dh).Correct)
    (hq : DeliverForge.MakesAtMostQueriesDF dfAdv q) :
    (∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses 2 t,
      DeliverForge.forgeGuessedAdvantageCellPaper
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (qep + 1) DeliverForge.sameHdrScheme tL t
        (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv)) ≤
    (∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses 2 t,
      Proofs.Refinement.hiddenSaltCellTermPaperDF P ℓ Dh encPt encT idOf lam qep q tL t dfAdv) := by
  have hqDF : DeliverForge.MakesAtMostQueriesDF
      (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv) q :=
    HeadlineV1.challSimDF'Paper_queries (2 + 1) (qep + 1) dfAdv hq
  exact Finset.sum_le_sum (fun t ht => Finset.sum_le_sum (fun tL htL =>
    forgeGuessedAdvantagePaper_le_hiddenSaltCellTermPaperDF
      P ℓ Dh encPt encT idOf lam qep q ht htL dfAdv hc hqDF))

/-- Bounds `hiddenSaltTerm` on `RefuseB0.refuseCorrB0 A` by `hiddenSaltBoundV1` plus
`K.kemFailFindAdvantage`. -/
theorem hiddenSaltTerm_le_hiddenSaltBoundV1
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ}
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (hK_tot : Encaps1Total K)
    (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) (hℓ : ℓ < 10 ^ 6)
    (hDh : Dh.Commutes) (hX : X25519RealizesDh C Dh encPt encT)
    (hdec : ∀ T, decT (encT T) = some T) (hinj : Function.Injective encT)
    (hdum : ∀ T, encT T ≠ dummyKey)
    (hz : ∀ x, Dh.dh x 0 = 0) (hD : ∀ k x, C.D k (C.E k x) = x)
    (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : SM.MakesAtMostQueries A q) :
    let P := paramsV1 C K idA idB
    LibsignalSimC.hiddenSaltTerm P ℓ Dh encPt encT decT (idsOf idA idB) lam qep
        (RefuseB0.refuseCorrB0 A) ≤
      hiddenSaltBoundV1 C K ℓ Dh encPt encT decT idA idB lam qep q δ
        (v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT
          lam qep q)
        (RefuseB0.refuseCorrB0 A) +
      K.kemFailFindAdvantage
        (Proofs.Refinement.redKemFailHiddenSalt P K ℓ Dh encPt encT decT (idsOf idA idB) lam qep
          (RefuseB0.refuseCorrB0 A)) := by
  intro P
  let idOf := idsOf idA idB
  let R := v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam qep q
  let dfAdv := R.simDeliverForge.eval (fun _ => A.refuseCorrB0) ()
  have hqR : SM.MakesAtMostQueries A.refuseCorrB0 q :=
    RefuseCorrB0.refuseCorrB0_queries A q hq
  have hq_df : DeliverForge.MakesAtMostQueriesDF dfAdv q :=
    Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeProg.simDeliverForgeRedProg_makesAtMostQueriesDF
      ℓ C K idA idB Dh encPt encT decT lam qep q A.refuseCorrB0 hqR
  have hclamp :
      (∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses 2 t,
        DeliverForge.forgeGuessedAdvantageCellPaper
          (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
          (qep + 1) DeliverForge.sameHdrScheme tL t
          (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
            (Proofs.Refinement.simDeliverForge P ℓ Dh encPt encT decT idOf lam qep
              A.refuseCorrB0))) =
      ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses 2 t,
        DeliverForge.forgeGuessedAdvantageCellPaper
          (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
          (qep + 1) DeliverForge.sameHdrScheme tL t
          (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv) := by
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun tL _ => ?_
    exact
      (Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeProg.forgeGuessedAdvantageCellPaper_challSimDF'Paper_simDeliverForgeRedProg_eq
        hℓ C K idA idB Dh encPt encT decT lam qep q tL t A.refuseCorrB0 hqR hq32).symm
  have hsum := sum_forgeGuessedAdvantageCellPaper_le_sum_hiddenSaltCellTermPaperDF
    P ℓ Dh encPt encT idOf lam qep q dfAdv (dhScheme_correct Dh hDh) hq_df
  have hlazy := hiddenSaltTerm_le_add_spuriousStepTerm_v1_refuseCorrB0_lazy'
    C K hK_tot idA idB Dh encPt encT decT lam qep q hℓ hDh hX hdec hinj hdum hz hD hq32
    (∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses 2 t,
      Proofs.Refinement.hiddenSaltCellTermPaperDF P ℓ Dh encPt encT idOf lam qep q tL t dfAdv)
    δ hδ A hq (fun InvPQ _ hInv_top =>
      (evalDist_simulateQ_firstNESimImpl'_le_sum_cells P K rfl InvPQ hInv_top ℓ Dh hDh encPt encT
        decT idOf ⟨rfl, rfl⟩ hX hinj hdec lam qep q A.refuseCorrB0).trans
        (hclamp.le.trans hsum))
  have hreds := sum_hiddenSaltCellTermPaperDF_le_hiddenSaltBoundV1_paper
    C K hD hℓ Dh encPt encT decT hinj hdum idA idB lam qep q hq32 δ A.refuseCorrB0 hqR
  rw [refuseCorrB0_eq]
  exact hlazy.trans (add_le_add hreds le_rfl)

/-- Establishes `HiddenSaltBoundV1HoldsEx` under zero `kemFailFindAdvantage`. -/
theorem hiddenSaltBoundV1HoldsEx
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ)
    (hK_zero : ∀ (C : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey)
      (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
      (decT : PublicKey → Option Pt) (lam : Pt) (qep : ℕ)
      (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes),
      K.kemFailFindAdvantage
        (Proofs.Refinement.redKemFailHiddenSalt (paramsV1 C K idA idB) K ℓ Dh encPt encT decT
          (idsOf idA idB) lam qep (RefuseB0.refuseCorrB0 A)) = 0) :
    HiddenSaltBoundV1HoldsEx (Pt := Pt) ℓ :=
  hiddenSaltBoundV1HoldsEx_of_v1SessionReds ℓ
    (v1SessionRedsPaper ℓ)
    (fun C K idA idB Dh encPt encT decT lam qep q hqep =>
      v1SessionRedsPaper_bounded ℓ C K idA idB Dh encPt encT decT lam qep q (by omega))
    (fun C K hK_tot idA idB Dh encPt encT decT lam qep q hℓ hDh hX hdec hinj hdum hz hD hq32 δ hδ
        A hq => by
      refine (hiddenSaltTerm_le_hiddenSaltBoundV1 C K hK_tot idA idB Dh encPt encT decT lam qep q
        hℓ hDh hX hdec hinj hdum hz hD hq32 δ hδ A hq).trans_eq ?_
      rw [hK_zero, add_zero])

open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB)
open Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEHaltedEvict
open Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEHaltedCouple

theorem sum_hiddenSaltCellTermPaperDF_le_hiddenSaltBoundV1_of_dfReds
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (Z : Crypto) (K : LibsignalSpqrV1.MlKem) (hD : ∀ k x, Z.D k (Z.E k x) = x)
    {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idA idB : IdentityKey) (lam : Pt) (qep q : ℕ) (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32)
    (δ : ℝ≥0∞)
    (R : SessionCostedReductions Pt ℓ Z K idA idB Dh encPt encT decT lam)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq_df : DeliverForge.MakesAtMostQueriesDF (R.simDeliverForge.eval (fun _ => A) ()) q)
    (hsh_df : SendMsgsOkDF
      (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => atomicShortPubB m.1)
      (R.simDeliverForge.eval (fun _ => A) ()))
    (hg_df : GuardedSMDFShort (R.simDeliverForge.eval (fun _ => A) ()))
    (hchall : R.challSimDF.eval (fun _ => R.simDeliverForge.eval (fun _ => A) ()) () =
      DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
        (R.simDeliverForge.eval (fun _ => A) ()))
    (hfs : R.fs = (v1SessionRedsPaper ℓ Z K idA idB Dh encPt encT decT lam qep q).fs)
    (hcka : ∀ t ∈ Finset.range ((qep + 1) + 2), ∀ tL ∈ admissibleLastLeakGuesses 2 t,
      (R.B_cka tL t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => A) ())) () =
      ((v1SessionRedsPaper ℓ Z K idA idB Dh encPt encT decT lam qep q).B_cka tL t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => A) ())) ())
    (hprng : ∀ t ∈ Finset.range ((qep + 1) + 2), ∀ tL ∈ admissibleLastLeakGuesses 2 t,
      (R.B_prng tL t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => A) ())) () =
      ((v1SessionRedsPaper ℓ Z K idA idB Dh encPt encT decT lam qep q).B_prng tL t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => A) ())) ())
    (hbfs : ∀ j ∈ Finset.range q, ∀ t ∈ Finset.range ((qep + 1) + 2),
      ∀ tL ∈ admissibleLastLeakGuesses 2 t,
      (R.B_fs j tL t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => A) ())) () =
      ((v1SessionRedsPaper ℓ Z K idA idB Dh encPt encT decT lam qep q).B_fs j tL t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => A) ())) ()) :
    let P := paramsV1 Z K idA idB
    let dfAdv := R.simDeliverForge.eval (fun _ => A) ()
    (∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses 2 t,
      Proofs.Refinement.hiddenSaltCellTermPaperDF P ℓ Dh encPt encT (idsOf idA idB) lam qep q
        tL t dfAdv) +
      spuriousStepTerm Z.F encPt Dh q qep + (qep + 1) * (qep + 2) * δ ≤
    hiddenSaltBoundV1 Z K ℓ Dh encPt encT decT idA idB lam qep q δ R A := by
  intro P dfAdv
  unfold hiddenSaltBoundV1; dsimp only
  rw [hchall, hfs]
  gcongr with t ht tL htL
  have hcell := hiddenSaltCellTermPaperDF_le_v1SessionRedsPaper Z K hD hℓ Dh encPt encT decT
    hinj hdum idA idB lam qep q hq32 tL t dfAdv hq_df hsh_df hg_df
  have hsum_fs :
      (∑ j ∈ Finset.range q, fsAeadSlotSumBound Z (min (2 * q) (q + 2))
        (v1SessionRedsPaper ℓ Z K idA idB Dh encPt encT decT lam qep q).fs
        ((R.B_fs j tL t).eval (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv)
          ())) =
      ∑ j ∈ Finset.range q, fsAeadSlotSumBound Z (min (2 * q) (q + 2))
        (v1SessionRedsPaper ℓ Z K idA idB Dh encPt encT decT lam qep q).fs
        (((v1SessionRedsPaper ℓ Z K idA idB Dh encPt encT decT lam qep q).B_fs j tL t).eval
          (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv) ()) :=
    Finset.sum_congr rfl fun j hj => by rw [hbfs j hj t ht tL htL]
  refine hcell.trans (le_of_eq ?_)
  rw [← hcka t ht tL htL, ← hprng t ht tL htL, ← hsum_fs]

/-- Bounds `hiddenSaltTermTrackHalted` on `RefuseB0.refuseCorrB0 A` by `hiddenSaltBoundV1` with no
`kemFailFindAdvantage` error term. -/
theorem hiddenSaltTermTrackHalted_le_hiddenSaltBoundV1_of_dfReds
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ}
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (hK_tot : Encaps1Total K)
    (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) (hℓ : ℓ < 10 ^ 6)
    (hDh : Dh.Commutes) (hX : X25519RealizesDh C Dh encPt encT)
    (hdec : ∀ T, decT (encT T) = some T) (hinj : Function.Injective encT)
    (hdum : ∀ T, encT T ≠ dummyKey)
    (hz : ∀ x, Dh.dh x 0 = 0) (hD : ∀ k x, C.D k (C.E k x) = x)
    (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (R : SessionCostedReductions Pt ℓ C K idA idB Dh encPt encT decT lam)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : SM.MakesAtMostQueries A q)
    (hq_df : DeliverForge.MakesAtMostQueriesDF
      (R.simDeliverForge.eval (fun _ => RefuseB0.refuseCorrB0 A) ()) q)
    (hsh_df : SendMsgsOkDF
      (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => atomicShortPubB m.1)
      (R.simDeliverForge.eval (fun _ => RefuseB0.refuseCorrB0 A) ()))
    (hg_df : GuardedSMDFShort (R.simDeliverForge.eval (fun _ => RefuseB0.refuseCorrB0 A) ()))
    (hcell_le : ∀ t ∈ Finset.range ((qep + 1) + 2), ∀ tL ∈ admissibleLastLeakGuesses 2 t,
      DeliverForge.forgeGuessedAdvantageCellPaper
        (lFig8 Dh encPt C protoSignalCodec ℓ encT (idsOf idA idB) 25000 lam)
        (qep + 1) DeliverForge.sameHdrScheme tL t
        (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (Proofs.Refinement.simDeliverForgeTrackHalted (paramsV1 C K idA idB) K ℓ Dh encPt encT
            decT (idsOf idA idB) lam qep (RefuseB0.refuseCorrB0 A))) ≤
      DeliverForge.forgeGuessedAdvantageCellPaper
        (lFig8 Dh encPt C protoSignalCodec ℓ encT (idsOf idA idB) 25000 lam)
        (qep + 1) DeliverForge.sameHdrScheme tL t
        (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => RefuseB0.refuseCorrB0 A) ())))
    (hchall : R.challSimDF.eval
        (fun _ => R.simDeliverForge.eval (fun _ => RefuseB0.refuseCorrB0 A) ()) () =
      DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
        (R.simDeliverForge.eval (fun _ => RefuseB0.refuseCorrB0 A) ()))
    (hfs : R.fs = (v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam qep q).fs)
    (hcka : ∀ t ∈ Finset.range ((qep + 1) + 2), ∀ tL ∈ admissibleLastLeakGuesses 2 t,
      (R.B_cka tL t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => RefuseB0.refuseCorrB0 A) ())) () =
      ((v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam qep q).B_cka tL t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => RefuseB0.refuseCorrB0 A) ())) ())
    (hprng : ∀ t ∈ Finset.range ((qep + 1) + 2), ∀ tL ∈ admissibleLastLeakGuesses 2 t,
      (R.B_prng tL t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => RefuseB0.refuseCorrB0 A) ())) () =
      ((v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam qep q).B_prng tL t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => RefuseB0.refuseCorrB0 A) ())) ())
    (hbfs : ∀ j ∈ Finset.range q, ∀ t ∈ Finset.range ((qep + 1) + 2),
      ∀ tL ∈ admissibleLastLeakGuesses 2 t,
      (R.B_fs j tL t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => RefuseB0.refuseCorrB0 A) ())) () =
      ((v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam qep q).B_fs j tL t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => RefuseB0.refuseCorrB0 A) ())) ()) :
    let P := paramsV1 C K idA idB
    Proofs.Refinement.hiddenSaltTermTrackHalted P K ℓ Dh encPt encT decT (idsOf idA idB) lam qep
        (RefuseB0.refuseCorrB0 A) ≤
      hiddenSaltBoundV1 C K ℓ Dh encPt encT decT idA idB lam qep q δ R
        (RefuseB0.refuseCorrB0 A) := by
  intro P
  let idOf := idsOf idA idB
  let dfAdv := R.simDeliverForge.eval (fun _ => RefuseB0.refuseCorrB0 A) ()
  have hsum_cell :
      (∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses 2 t,
        DeliverForge.forgeGuessedAdvantageCellPaper
          (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
          (qep + 1) DeliverForge.sameHdrScheme tL t
          (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
            (Proofs.Refinement.simDeliverForgeTrackHalted P K ℓ Dh encPt encT decT idOf lam qep
              A.refuseCorrB0))) ≤
      ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses 2 t,
        DeliverForge.forgeGuessedAdvantageCellPaper
          (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
          (qep + 1) DeliverForge.sameHdrScheme tL t
          (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv) := by
    refine Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun tL htL => ?_
    rw [← refuseCorrB0_eq]
    exact hcell_le t ht tL htL
  have hsum := sum_forgeGuessedAdvantageCellPaper_le_sum_hiddenSaltCellTermPaperDF
    P ℓ Dh encPt encT idOf lam qep q dfAdv (dhScheme_correct Dh hDh) hq_df
  have hlazy := hiddenSaltTermTrackHalted_le_add_spuriousStepTerm_v1_refuseCorrB0_lazy'
    C K hK_tot idA idB Dh encPt encT decT lam qep q hℓ hDh hX hdec hinj hdum hz hD hq32
    (∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses 2 t,
      Proofs.Refinement.hiddenSaltCellTermPaperDF P ℓ Dh encPt encT idOf lam qep q tL t dfAdv)
    δ hδ A hq (fun InvPQ _ hInv_top =>
      (evalDist_simulateQ_firstNEHalted'_le_sum_cells P K rfl InvPQ hInv_top ℓ Dh hDh encPt encT
        decT idOf ⟨rfl, rfl⟩ hX hinj hdec lam qep q A.refuseCorrB0).trans
        (hsum_cell.trans hsum))
  have hreds := sum_hiddenSaltCellTermPaperDF_le_hiddenSaltBoundV1_of_dfReds
    C K hD hℓ Dh encPt encT decT hinj hdum idA idB lam qep q hq32 δ R (RefuseB0.refuseCorrB0 A)
    hq_df hsh_df hg_df hchall hfs hcka hprng hbfs
  rw [← refuseCorrB0_eq] at hlazy
  exact hlazy.trans hreds

end CryptoVerification.E2E

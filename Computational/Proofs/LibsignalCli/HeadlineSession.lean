/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.StatementSession
public import Computational.Proofs.SpecLemmas.Session.GameRCoinLogged
public import Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge
public import Computational.Proofs.SpecLemmas.Session.KemFailTrackEpochClamp
public import Computational.Proofs.E2E.SignedSession
public import Computational.Proofs.SessionCostedDF
public import Computational.Proofs.SessionCostedHalt
public import Computational.Proofs.E2E.HeadlineComposed
public import Computational.Proofs.E2E.HeadlineSpkSession
public import Computational.Proofs.Game.PromotedCostedReds.HaltedSpkLeakProg
public import Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2RInProg
public import Computational.Proofs.Game.PromotedCostedReds.HaltedEpoch0Prog
public import Computational.Proofs.Game.PromotedCostedReds.HaltedUniformEpoch0Prog
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8Halted
public import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHalted
public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEReds
import Computational.Proofs.E2E.RefuseCorrB0Core
import Computational.Proofs.E2E.HaltedSpkSession
import Computational.Proofs.E2E.HaltedSessionChain
import Computational.Proofs.Game.PromotedCostedReds.SimFig8HaltedEval
import Computational.Proofs.HeadlineV1.SignedRefineC
import Computational.Proofs.HeadlineV1.SendShortC
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEHeadline
import Computational.Proofs.SignalWireRoundTrip
import Computational.Proofs.SpqrV1Sync.SendTotal
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.TrackHaltedRefinesC

/-!
# Lemma 2: single-session security with costed reductions

**Checked by Lean.** Proves `GameRCoinLoggedFaithful` (`gameRCoinLogged_faithful`) and
`SessionSecure ℓ` (`session_secure_proof`) by splitting the `SM.gameR` mixture bias into the
tracker-halted `gameRTrackHalted` bias plus `2 * sessionKemFailProb` and bounding the halted game
via the clamped costed reduction family `v1SessionRedsHaltedClamped`.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal BigOperators
open ReductionDsl OracleComp OracleSpec MeasureTheory

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme WireAEAD FSAEAD
  CryptoGames.Ratchet.LibsignalSim
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.E2E.Signed

local instance instInhabitedOfZeroHeadlineSession {Pt : Type} [Zero Pt] : Inhabited Pt := ⟨0⟩

/-! ## Epoch-cap clamping and generic session bound -/

/-- Clamps `qep` to `min qep (q + 4)` in `gameRTrackHalted` when every `A o` makes at most `q`
queries. -/
theorem evalDist_mixGameRTrackHalted_min_eq {α PQ : Type} [Inhabited PQ]
    (pqrOf : SampledSessionKey → BitVec 256)
    (F : ShaCompress) (K : LibsignalSpqrV1.MlKem)
    (P : α → Params PQ (BitVec 512)) (hF : ∀ o, (P o).C.F = F)
    (ℓ Δ qep q : ℕ) (s : α → BitVec 256)
    (cfg : SM.ConfigR (GhostState PQ) (CBC.Plain ℓ) Bytes)
    (oa : ProbComp α)
    (A : α → SM.Adversary (GhostState PQ) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : ∀ o ∈ support oa, SM.MakesAtMostQueries (A o) q) :
    𝒟[oa >>= fun o =>
        Prod.fst <$>
          Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.gameRTrackHalted pqrOf F K
            (sessionSchemeFixedSpk (P o) ℓ (s o)) Δ qep cfg (A o)] =
      𝒟[oa >>= fun o =>
        Prod.fst <$>
          Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.gameRTrackHalted pqrOf F K
            (sessionSchemeFixedSpk (P o) ℓ (s o)) Δ (min qep (q + 4)) cfg (A o)] :=
  Computational.Proofs.SpecLemmas.Session.KemFailTrackEpochClamp.evalDist_mixGameRTrackHalted_min_eq
    pqrOf F K P hF ℓ Δ qep q s cfg oa A hq

/-- Forgetting the send-coin log recovers `SM.gameR`. -/
theorem gameRCoinLogged_faithful : GameRCoinLoggedFaithful :=
  Computational.Proofs.SpecLemmas.Session.GameRCoinLogged.gameRCoinLogged_faithful

theorem sessBound_eq_gen
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {α : Type}
    (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (D : SessionCostedReductionFamily Pt ℓ)
    (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (spkLeakT : α → BitVec 256 →
      SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes →
      MACScheme.PRFAdversary Pt (BitVec 256))
    (spkLeakUT : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes →
      MACScheme.PRFAdversary Pt (BitVec 256))
    (hop2PrgT : α → BitVec 256 → ℕ →
      SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes →
      PRGScheme.PRGAdversary (BitVec 256 × BitVec 256))
    (hop2PrfT : α → BitVec 256 → ℕ →
      SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes →
      MACScheme.PRFAdversary Pt (BitVec 256))
    (hdec : ∀ T, decT (encT T) = some T)
    (hq : ∀ o ∈ support oa, SM.MakesAtMostQueries (A o) q)
    (hspk : ∀ o ∈ support oa,
      SpkCostedEvalAgreesGen C K ℓ Dh encPt encT decT 0 q
        (spkLeakT o) (spkLeakUT o) (hop2PrgT o) (hop2PrfT o)
        (D C K (ida o) (idb o) Dh encPt encT decT 0 qep q).spk) :
    let R := fun o => D C K (ida o) (idb o) Dh encPt encT decT 0 qep q
    sessionAdvantageBound ℓ D C K Dh encPt encT decT qep q δ oa ida idb s A =
      uniformStartMixtureBound C K ℓ Dh encPt encT decT 0 qep q δ oa ida idb R A
        + 2 * (extractPRF C.F encPt).prfAdvantage
            (prefixPrfAvg oa (fun o => spkLeakT o (s o) (A o)))
        + 2 * (extractPRF C.F encPt).prfAdvantage
            (prefixPrfAvg oa (fun o => spkLeakUT o (A o)))
        + 2 * (epoch0ChainForgeryTerm C.F q
            + (∑ j ∈ Finset.range spkSwapHybridCount,
                ((Ratchet.expandPRG C.F).prgAdvantage
                    (prefixPrgAvg oa (fun o => hop2PrgT o (s o) j (A o)))
                  + (extractPRF C.F encPt).prfAdvantage
                    (prefixPrfAvg oa (fun o => hop2PrfT o (s o) j (A o)))))
            + hop2CreateCollTerm Dh q + spkSwapSpuriousStepTerm C.F q
            + spkSwapCreationPointHitTerm Dh q + spkSwapHiddenScalarGuessTerm Dh q) := by
  set R := fun o => D C K (ida o) (idb o) Dh encPt encT decT 0 qep q
  set Rspk := fun o => (R o).spk
  have hl1 :
      (extractPRF C.F encPt).prfAdvantage
        (prefixPrfAvg oa (fun o => evalSpkLeakRed (Rspk o).spkLeakRed (s o) (A o))) =
      (extractPRF C.F encPt).prfAdvantage
        (prefixPrfAvg oa (fun o => spkLeakT o (s o) (A o))) :=
    Signed.prfAdvantage_prfAvg_congr_of_support' (extractPRF C.F encPt) oa _ _
      fun o ho => (hspk o ho hℓ hdec (A o) (hq o ho)).1 (s o)
  have hl2 :
      (extractPRF C.F encPt).prfAdvantage
        (prefixPrfAvg oa (fun o =>
          evalSpkLeakRedU (Rspk o).spkLeakRedU
            (fun x => evalSpkLeakRed (Rspk o).spkLeakRed x (A o)))) =
      (extractPRF C.F encPt).prfAdvantage
        (prefixPrfAvg oa (fun o => spkLeakUT o (A o))) :=
    Signed.prfAdvantage_prfAvg_congr_of_support' (extractPRF C.F encPt) oa _ _
      fun o ho => (hspk o ho hℓ hdec (A o) (hq o ho)).2.1
  have hsum :
      (∑ j ∈ Finset.range spkSwapHybridCount,
        ((Ratchet.expandPRG C.F).prgAdvantage
            (prefixPrgAvg oa (fun o =>
              evalSpkSwapPrgHybrid ((Rspk o).hop2PrgRedK j) (s o) (A o)))
          + (extractPRF C.F encPt).prfAdvantage
            (prefixPrfAvg oa (fun o =>
              evalSpkSwapPrfHybrid ((Rspk o).hop2PrfRedK j) (s o) (A o))))) =
      (∑ j ∈ Finset.range spkSwapHybridCount,
        ((Ratchet.expandPRG C.F).prgAdvantage
            (prefixPrgAvg oa (fun o => hop2PrgT o (s o) j (A o)))
          + (extractPRF C.F encPt).prfAdvantage
            (prefixPrfAvg oa (fun o => hop2PrfT o (s o) j (A o))))) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj_lt : j < spkSwapHybridCount := Finset.mem_range.mp hj
    have hprg :
        (Ratchet.expandPRG C.F).prgAdvantage
          (prefixPrgAvg oa (fun o =>
            evalSpkSwapPrgHybrid ((Rspk o).hop2PrgRedK j) (s o) (A o))) =
        (Ratchet.expandPRG C.F).prgAdvantage
          (prefixPrgAvg oa (fun o => hop2PrgT o (s o) j (A o))) :=
      Signed.prgAdvantage_prgAvg_congr_of_support' (Ratchet.expandPRG C.F) oa _ _
        fun o ho => (hspk o ho hℓ hdec (A o) (hq o ho)).2.2.1 (s o) j hj_lt
    have hprf :
        (extractPRF C.F encPt).prfAdvantage
          (prefixPrfAvg oa (fun o =>
            evalSpkSwapPrfHybrid ((Rspk o).hop2PrfRedK j) (s o) (A o))) =
        (extractPRF C.F encPt).prfAdvantage
          (prefixPrfAvg oa (fun o => hop2PrfT o (s o) j (A o))) :=
      Signed.prfAdvantage_prfAvg_congr_of_support' (extractPRF C.F encPt) oa _ _
        fun o ho => (hspk o ho hℓ hdec (A o) (hq o ho)).2.2.2 (s o) j hj_lt
    rw [hprg, hprf]
  unfold sessionAdvantageBound
  dsimp only at hl1 hl2 hsum ⊢
  rw [hl1, hl2, hsum]

theorem sessBound_eq_signed
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {α : Type}
    (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (D : SessionCostedReductionFamily Pt ℓ)
    (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hdec : ∀ T, decT (encT T) = some T)
    (hq : ∀ o ∈ support oa, SM.MakesAtMostQueries (A o) q)
    (hspk : ∀ o ∈ support oa,
      SpkCostedEvalAgrees C K (ida o) (idb o) ℓ Dh encPt encT decT 0 qep q
        (D C K (ida o) (idb o) Dh encPt encT decT 0 qep q).spk) :
    let spqr := LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K
    let R := fun o => D C K (ida o) (idb o) Dh encPt encT decT 0 qep q
    sessionAdvantageBound ℓ D C K Dh encPt encT decT qep q δ oa ida idb s A =
      uniformStartMixtureBound C K ℓ Dh encPt encT decT 0 qep q δ oa ida idb R A
        + 2 * (extractPRF C.F encPt).prfAdvantage
            (Signed.leakAvgWithSpqr C spqr Dh encPt encT decT qep oa ida idb s A)
        + 2 * (extractPRF C.F encPt).prfAdvantage
            (Signed.leakUAvgWithSpqr C spqr Dh encPt encT decT qep oa ida idb A)
        + 2 * Signed.hop2TermAvgWithSpqr C spqr ℓ Dh encPt encT decT qep q oa ida idb s A :=
  let spqr := LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K
  sessBound_eq_gen ℓ hℓ D C K Dh encPt encT decT qep q δ oa ida idb s A
    (fun o s' A' => spkLeakRed (paramsIdsWithSpqr C spqr (ida o) (idb o)) Dh encPt encT decT qep s' A')
    (fun o A' => spkLeakRedU spkLeakRed (paramsIdsWithSpqr C spqr (ida o) (idb o)) Dh encPt encT decT qep A')
    (fun o s' j A' => hop2PrgRedK (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ Dh encPt encT decT qep s' j A')
    (fun o s' j A' => hop2PrfRedK (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ Dh encT decT qep s' j A')
    hdec hq (fun o ho => (spkCostedEvalAgrees_iff_gen C K (ida o) (idb o) ℓ Dh encPt encT decT 0 qep q _).mp (hspk o ho))

/-- Five-hop session bias bound into `sessionAdvantageBound` for any `SessionCostedReductionFamily`
whose outer reductions satisfy the evaluation-agreement hypotheses. -/
theorem boolBias_mixSpkGen_le_sessionAdvantageBound
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {α : Type}
    (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (D : SessionCostedReductionFamily Pt ℓ)
    (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (hD : ∀ k x, C.D k (C.E k x) = x)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hdec : ∀ T, decT (encT T) = some T)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (qep q : ℕ) (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) (δ : ℝ≥0∞)
    (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256)
    (gameFixedSpk gameU gameR : α →
      SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes → ProbComp Bool)
    (spkLeakT : α → BitVec 256 →
      SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes →
      MACScheme.PRFAdversary Pt (BitVec 256))
    (spkLeakUT : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes →
      MACScheme.PRFAdversary Pt (BitVec 256))
    (hop2PrgT : α → BitVec 256 → ℕ →
      SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes →
      PRGScheme.PRGAdversary (BitVec 256 × BitVec 256))
    (hop2PrfT : α → BitVec 256 → ℕ →
      SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes →
      MACScheme.PRFAdversary Pt (BitVec 256))
    (uniformStartT epoch0T : α →
      SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes →
      (Ratchet.RootKey × BitVec 256) → ProbComp Bool)
    (simT : α →
      SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes → Fig8Adv Pt ℓ)
    (winT eps0Game hidGame : α →
      SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes → ProbComp Bool)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : ∀ o ∈ support oa, SM.MakesAtMostQueries (A o) q)
    (hSpkChain :
      𝒟[oa >>= fun o => gameFixedSpk o (A o)].boolBias ≤
        𝒟[oa >>= fun o => gameU o (A o)].boolBias
          + 2 * (extractPRF C.F encPt).prfAdvantage
              (prefixPrfAvg oa (fun o => spkLeakT o (s o) (A o)))
          + 2 * (extractPRF C.F encPt).prfAdvantage
              (prefixPrfAvg oa (fun o => spkLeakUT o (A o)))
          + 2 * (epoch0ChainForgeryTerm C.F q
              + (∑ j ∈ Finset.range spkSwapHybridCount,
                  ((Ratchet.expandPRG C.F).prgAdvantage
                      (prefixPrgAvg oa (fun o => hop2PrgT o (s o) j (A o)))
                    + (extractPRF C.F encPt).prfAdvantage
                      (prefixPrfAvg oa (fun o => hop2PrfT o (s o) j (A o)))))
              + hop2CreateCollTerm Dh q + spkSwapSpuriousStepTerm C.F q
              + spkSwapCreationPointHitTerm Dh q + spkSwapHiddenScalarGuessTerm Dh q))
    (hspk : ∀ o ∈ support oa,
      SpkCostedEvalAgreesGen C K ℓ Dh encPt encT decT 0 q
        (spkLeakT o) (spkLeakUT o) (hop2PrgT o) (hop2PrfT o)
        (D C K (ida o) (idb o) Dh encPt encT decT 0 qep q).spk)
    (hUR : ∀ B : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes,
      (∀ o, SM.MakesAtMostQueries (B o) q) →
      𝒟[oa >>= fun o => gameU o (B o)].boolBias ≤
        𝒟[oa >>= fun o => gameR o (RefuseB0.refuseCorrB0 (B o))].boolBias
          + 2 * (rootKdfAsPrg C.F (encPt 0)).prgAdvantage
              (prefixPrgAvg oa fun o rc => uniformStartT o (RefuseB0.refuseCorrB0 (B o)) rc))
    (hRSim : ∀ B : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes,
      (∀ o, SM.MakesAtMostQueries (B o) q) →
      𝒟[oa >>= fun o => gameR o (B o)].boolBias ≤
        𝒟[oa >>= fun o => SM.game (lFig8 Dh encPt C protoSignalCodec ℓ encT
            (idsOf (ida o) (idb o)) 25000 0) 3 (qep + 1) SM.Config.h1 (simT o (B o))].boolBias
          + 2 * (refineConst C Dh encPt q qep δ +
            (𝒟[oa >>= fun o => winT o (B o)] {true} +
             𝒟[oa >>= fun o => eps0Game o (B o)] {true} +
             𝒟[oa >>= fun o => hidGame o (B o)] {true})))
    (hEps0 : ∀ B : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes,
      (∀ o, SM.MakesAtMostQueries (B o) q) →
      𝒟[oa >>= fun o => eps0Game o (B o)] {true} ≤
        (rootKdfAsPrg C.F (encPt 0)).prgAdvantage
          (prefixPrgAvg oa fun o rc => epoch0T o (B o) rc) + q * eps0IdealUnit C.F)
    (hHid : ∀ o ∈ support oa,
      𝒟[hidGame o (RefuseB0.refuseCorrB0 (A o))] {true} ≤
        hiddenSaltBoundV1 C K ℓ Dh encPt encT decT (ida o) (idb o) 0 qep q δ
          (D C K (ida o) (idb o) Dh encPt encT decT 0 qep q)
          (RefuseB0.refuseCorrB0 (A o)))
    (hUE : ∀ o, UniformEpoch0CostedEvalAgreesGen C K (ida o) (idb o) ℓ Dh encPt encT decT 0 q
      (uniformStartT o) (epoch0T o) (D C K (ida o) (idb o) Dh encPt encT decT 0 qep q))
    (hSim : ∀ o, SimFig8CostedEvalAgreesGen C K (ida o) (idb o) ℓ Dh encPt encT decT 0 qep q
      (simT o) (winT o) (D C K (ida o) (idb o) Dh encPt encT decT 0 qep q))
    (hfig8 : ∀ o, (D C K (ida o) (idb o) Dh encPt encT decT 0 qep q).fig8 =
      (v1SessionReds ℓ C K (ida o) (idb o) Dh encPt encT decT 0 qep q).fig8)
    (hfs : ∀ o, (D C K (ida o) (idb o) Dh encPt encT decT 0 qep q).fs =
      (v1SessionReds ℓ C K (ida o) (idb o) Dh encPt encT decT 0 qep q).fs) :
    𝒟[oa >>= fun o => gameFixedSpk o (A o)].boolBias ≤
      sessionAdvantageBound ℓ D C K Dh encPt encT decT qep q δ oa ida idb s A := by
  have hU := boolBias_mixUGen_le_uTermShortMix C K hD hℓ Dh hDh encPt encT decT hinj hdum (0 : Pt)
    qep q hq32 δ oa ida idb (fun o => D C K (ida o) (idb o) Dh encPt encT decT 0 qep q)
    gameU gameR uniformStartT epoch0T simT winT eps0Game hidGame A hq
    hUR hRSim hEps0 hHid hUE hSim hfig8 hfs
  have heq := sessBound_eq_gen ℓ hℓ D C K Dh encPt encT decT qep q δ oa ida idb s A
    spkLeakT spkLeakUT hop2PrgT hop2PrfT hdec hq hspk
  exact (hSpkChain.trans (add_le_add (add_le_add (add_le_add hU le_rfl) le_rfl) le_rfl)).trans_eq
    heq.symm

/-! ## Clamped tracker-halted reduction family -/

/-- Unclamped tracker-halted session reduction family wiring halted outer reductions onto
`v1SessionRedsPaper`. -/
noncomputable def v1SessionRedsHaltedRaw
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) : SessionCostedReductionFamily Pt ℓ :=
  fun C K idA idB Dh encPt encT decT lam qep q =>
    { v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam qep q with
      spk := Computational.Proofs.SessionCostedHalt.mkSpkCostedRedsHalted
        (Computational.Proofs.Game.PromotedCostedReds.HaltedSpkLeakProg.spkLeakRedRInProgHalted
          (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep)
        (CryptoVerification.E2E.HeadlineSpk.spkLeakRedUAtomicProg (Pt := Pt) ℓ)
        (fun k =>
          Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2RInProg.spkHop2PrgProgHalted
            (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
        (fun k =>
          Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2RInProg.spkHop2PrfProgHalted
            (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
      simFig8 :=
        Computational.Proofs.Game.PromotedCostedReds.SimFig8Halted.simFig8RedProgHalted
          (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q
      simDeliverForge :=
        Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHalted.simDeliverForgeRedProgHalted
          (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q
      epoch0Red :=
        Computational.Proofs.Game.PromotedCostedReds.HaltedEpoch0Prog.epoch0DistinguisherProgHalted
          C K Dh encPt encT decT idA idB lam ℓ q qep
      uniformStartRed :=
        Computational.Proofs.Game.PromotedCostedReds.HaltedUniformEpoch0Prog.uniformStartRedHalted
          C K Dh encPt encT decT idA idB lam ℓ q qep }

/-- Epoch-clamped tracker-halted session reduction family. -/
noncomputable def v1SessionRedsHaltedClamped
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) : SessionCostedReductionFamily Pt ℓ :=
  Computational.Proofs.SessionCostedHalt.clampSessionCostedReductionFamily ℓ
    (v1SessionRedsHaltedRaw ℓ)

private theorem v1SessionRedsHaltedRaw_bounded_of_le
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) (hqep : qep ≤ q + 4) :
    sessionCostedReductionsBounded ℓ C K idA idB Dh encPt encT decT lam qep q
      (v1SessionRedsHaltedRaw ℓ C K idA idB Dh encPt encT decT lam qep q) := by
  have hqep10 : qep ≤ q + 10 := by omega
  have hp := v1SessionRedsPaper_bounded ℓ C K idA idB Dh encPt encT decT lam qep q hqep10
  refine ⟨?_, hp.2.1, hp.2.2.1, ?_, ?_, ?_, ?_,
    hp.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2⟩
  · exact Computational.Proofs.SessionCostedHalt.mkSpkCostedRedsHalted_bounds
      (Computational.Proofs.Game.PromotedCostedReds.HaltedSpkLeakProg.spkLeakRedRInProgHalted_gRedBounded_tight
        (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep hqep10)
      (CryptoVerification.E2E.HeadlineSpk.spkLeakRedUAtomicProg_gRedBounded_tight (Pt := Pt) ℓ q)
      (fun k _ =>
        Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2RInProg.spkHop2PrgProgHalted_gRedBounded_tight
          (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k hqep10)
      (fun k _ =>
        Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2RInProg.spkHop2PrfProgHalted_gRedBounded_tight
          (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k hqep10)
  · exact Computational.Proofs.Game.PromotedCostedReds.SimFig8Halted.simFig8RedProgHalted_gRedBounded
      (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q hqep10
  · exact Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHalted.simDeliverForgeRedProgHalted_gRedBounded
      (Pt := Pt) (ℓ := ℓ) C K idA idB Dh encPt encT decT lam qep q hqep10
  · exact Computational.Proofs.Game.PromotedCostedReds.HaltedEpoch0Prog.epoch0DistinguisherProgHalted_gRedBounded_succ
      C K Dh encPt encT decT idA idB lam ℓ q qep hqep10
  · exact Computational.Proofs.Game.PromotedCostedReds.HaltedUniformEpoch0Prog.uniformStartRedHalted_gRedBounded_succ
      C K Dh encPt encT decT idA idB lam ℓ q qep hqep10

theorem v1SessionRedsHaltedClamped_bounded
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) :
    SessionCostedReductionFamilyBounded ℓ (v1SessionRedsHaltedClamped (Pt := Pt) ℓ) :=
  Computational.Proofs.SessionCostedHalt.clampSessionCostedReductionFamily_bounded ℓ
    (v1SessionRedsHaltedRaw ℓ) (v1SessionRedsHaltedRaw_bounded_of_le ℓ)

private theorem spkCostedEvalAgreesGen_v1SessionRedsHaltedRaw
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) :
    let spqr := LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K
    let P_s := paramsIdsWithSpqr C spqr idA idB
    SpkCostedEvalAgreesGen C K ℓ Dh encPt encT decT lam q
      (fun s' A' =>
        Computational.Proofs.E2E.HaltedSpkDefs.spkLeakRedTrackHalted K P_s Dh encPt encT decT qep
          s' A')
      (fun A' =>
        spkLeakRedU (Computational.Proofs.E2E.HaltedSpkDefs.spkLeakRedTrackHalted K)
          P_s Dh encPt encT decT qep A')
      (fun s' j A' =>
        Computational.Proofs.E2E.HaltedSpkDefs.hop2PrgRedKTrackHalted P_s K ℓ Dh encPt encT decT
          qep s' j A')
      (fun s' j A' =>
        Computational.Proofs.E2E.HaltedSpkDefs.hop2PrfRedKTrackHalted P_s K ℓ Dh encT decT qep s'
          j A')
      (v1SessionRedsHaltedRaw ℓ C K idA idB Dh encPt encT decT lam qep q).spk := by
  dsimp only
  intro hℓ hdec A hq
  have h1 : ∀ s' : BitVec 256,
      evalSpkLeakRed
        (v1SessionRedsHaltedRaw ℓ C K idA idB Dh encPt encT decT lam qep q).spk.spkLeakRed s' A =
      Computational.Proofs.E2E.HaltedSpkDefs.spkLeakRedTrackHalted K
        (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) idA idB)
        Dh encPt encT decT qep s' A :=
    fun s' =>
      Computational.Proofs.Game.PromotedCostedReds.HaltedSpkLeakProg.spkLeakRedRInProgHalted_eval
        (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep s' A hq hℓ
  refine ⟨h1, ?_, ?_, ?_⟩
  · have hfn :
        (fun x => evalSpkLeakRed
          (v1SessionRedsHaltedRaw ℓ C K idA idB Dh encPt encT decT lam qep q).spk.spkLeakRed x A) =
        (fun x => Computational.Proofs.E2E.HaltedSpkDefs.spkLeakRedTrackHalted K
          (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) idA idB)
          Dh encPt encT decT qep x A) :=
      funext h1
    rw [hfn]
    exact CryptoVerification.E2E.HeadlineSpk.spkLeakRedUAtomicProg_eval (Pt := Pt) ℓ
      (Computational.Proofs.E2E.HaltedSpkDefs.spkLeakRedTrackHalted K)
      (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) idA idB)
      Dh encPt encT decT qep A
  · intro s' j hj
    dsimp only [v1SessionRedsHaltedRaw]
    rw [Computational.Proofs.SessionCostedHalt.mkSpkCostedRedsHalted_hop2PrgRedK_of_lt _ _ _ _ hj]
    exact
      Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2RInProg.spkHop2PrgProgHalted_eval
        (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep j s' A hdec hj hq hℓ
  · intro s' j hj
    dsimp only [v1SessionRedsHaltedRaw]
    rw [Computational.Proofs.SessionCostedHalt.mkSpkCostedRedsHalted_hop2PrfRedK_of_lt _ _ _ _ hj]
    exact
      Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2RInProg.spkHop2PrfProgHalted_eval
        (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep j s' A hdec hj hq hℓ

private theorem uniformEpoch0CostedEvalAgreesGen_v1SessionRedsHaltedRaw
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) :
    let P_v1 := paramsV1 C K idA idB
    let adm := ratchetKeyAdmissible protoSignalCodec decT encT
    UniformEpoch0CostedEvalAgreesGen C K idA idB ℓ Dh encPt encT decT lam q
      (fun B rc =>
        Computational.Proofs.E2E.HaltedSessionChain.uniformStartDistinguisherTrackHalted
          P_v1 K ℓ (configR1OnCurve adm) qep B rc)
      (fun B rc =>
        Computational.Proofs.E2E.HaltedSessionChain.epoch0DistinguisherTrackHalted
          P_v1 K ℓ adm qep B rc)
      (v1SessionRedsHaltedRaw ℓ C K idA idB Dh encPt encT decT lam qep q) := by
  dsimp only
  intro hℓ B hq rc
  exact ⟨
    Computational.Proofs.Game.PromotedCostedReds.HaltedUniformEpoch0Prog.uniformStartRedHalted_eval_bridge
      C K Dh encPt encT decT idA idB lam ℓ q qep B rc hq hℓ,
    Computational.Proofs.Game.PromotedCostedReds.HaltedEpoch0Prog.epoch0DistinguisherProgHalted_eval_bridge
      C K Dh encPt encT decT idA idB lam ℓ q qep B rc hq hℓ⟩

private theorem simFig8CostedEvalAgreesGen_v1SessionRedsHaltedRaw
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) :
    let P_v1 := paramsV1 C K idA idB
    SimFig8CostedEvalAgreesGen C K idA idB ℓ Dh encPt encT decT lam qep q
      (fun B =>
        Computational.Proofs.Game.PromotedCostedReds.SimFig8Halted.libsignalToModularSchemeSimHalted
          P_v1 K ℓ Dh encPt encT decT (idsOf idA idB) lam qep B)
      (fun B =>
        Computational.Proofs.Game.PromotedCostedReds.SimFig8Halted.simCNoneWinEventHalted
          P_v1 K ℓ Dh encPt encT decT (idsOf idA idB) lam qep B)
      (v1SessionRedsHaltedRaw ℓ C K idA idB Dh encPt encT decT lam qep q) := by
  dsimp only
  intro hℓ B hq
  exact ⟨
    Computational.Proofs.Game.PromotedCostedReds.SimFig8HaltedEval.simFig8RedProgHalted_queries
      hℓ C K idA idB Dh encPt encT decT lam qep q B hq,
    Computational.Proofs.Game.PromotedCostedReds.SimFig8HaltedEval.simFig8RedProgHalted_equalPub
      hℓ C K idA idB Dh encPt encT decT lam qep q B hq,
    Computational.Proofs.Game.PromotedCostedReds.SimFig8HaltedEval.simFig8RedProgHalted_sendAtomicShort
      hℓ C K idA idB Dh encPt encT decT lam qep q B hq,
    Computational.Proofs.Game.PromotedCostedReds.SimFig8HaltedEval.simFig8RedProgHalted_guardedSMShort
      hℓ C K idA idB Dh encPt encT decT lam qep q B hq,
    (Computational.Proofs.Game.PromotedCostedReds.SimFig8HaltedEval.simFig8RedProgHalted_sm_game_eq
      hℓ C K idA idB Dh encPt encT decT lam qep q SM.Config.h1 B hq).symm,
    Computational.Proofs.Game.PromotedCostedReds.SimFig8HaltedEval.simFig8RedProgHalted_simCNoneWinEvent_eq
      hℓ C K idA idB Dh encPt encT decT lam qep q B hq⟩

private theorem hiddenSalt_v1SessionRedsHaltedRaw_le
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (hK_tot : Encaps1Total K)
    (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) (hℓ : ℓ < 10 ^ 6)
    (hDh : Dh.Commutes) (hX : X25519RealizesDh C Dh encPt encT)
    (hdec : ∀ T, decT (encT T) = some T) (hinj : Function.Injective encT)
    (hdum : ∀ T, encT T ≠ dummyKey)
    (hz : ∀ x, Dh.dh x 0 = 0) (hD : ∀ k x, C.D k (C.E k x) = x)
    (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : SM.MakesAtMostQueries A q) :
    let P_v1 := paramsV1 C K idA idB
    𝒟[Proofs.Refinement.hiddenSaltGameTrackHalted P_v1 K ℓ Dh encPt encT decT (idsOf idA idB)
        lam qep (RefuseB0.refuseCorrB0 A)] {true} ≤
      hiddenSaltBoundV1 C K ℓ Dh encPt encT decT idA idB lam qep q δ
        (v1SessionRedsHaltedRaw ℓ C K idA idB Dh encPt encT decT lam qep q)
        (RefuseB0.refuseCorrB0 A) := by
  have hA_ref : SM.MakesAtMostQueries (RefuseB0.refuseCorrB0 A) q := by
    rw [refuseCorrB0_eq]
    exact RefuseCorrB0.refuseCorrB0_queries A q hq
  have hq_df :=
    Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHalted.simDeliverForgeRedProgHalted_makesAtMostQueriesDF
      C K idA idB Dh encPt encT decT lam qep q (RefuseB0.refuseCorrB0 A) hA_ref
  exact hiddenSaltTermTrackHalted_le_hiddenSaltBoundV1_of_dfReds
    C K hK_tot idA idB Dh encPt encT decT lam qep q hℓ hDh hX hdec hinj hdum hz hD hq32 δ hδ
    (v1SessionRedsHaltedRaw ℓ C K idA idB Dh encPt encT decT lam qep q) A hq
    hq_df
    (Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHalted.simDeliverForgeRedProgHalted_sendAtomicShortDF
      hℓ C K idA idB Dh encPt encT decT lam qep q _ hA_ref)
    (Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHalted.simDeliverForgeRedProgHalted_guardedSMDFShort
      hℓ C K idA idB Dh encPt encT decT lam qep q _ hA_ref)
    (fun t _ tL _ => le_of_eq
      (Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHalted.forgeGuessedAdvantageCellPaper_challSimDF'Paper_simDeliverForgeRedProgHalted_eq
        hℓ C K idA idB Dh encPt encT decT lam qep q tL t _ hA_ref hq32).symm)
    (v1SessionRedsPaper_challSimDF_eval
      ℓ hℓ C K idA idB Dh encPt encT decT lam qep q _ hq_df)
    rfl
    (fun _ _ _ _ => rfl)
    (fun _ _ _ _ => rfl)
    (fun _ _ _ _ _ _ => rfl)

private theorem boolBias_mixRTrackHalted_le_v1
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {α : Type}
    (Z : Crypto) (K : LibsignalSpqrV1.MlKem)
    (hK_tot : Encaps1Total K)
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
    let adm := ratchetKeyAdmissible protoSignalCodec decT encT
    𝒟[oa >>= fun o =>
        Prod.fst <$>
          Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.gameRTrackHalted
            Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.libsignalSessionPqrOf
            Z.F K
            (libsignalSessionScheme (paramsV1 Z K (ida o) (idb o)) ℓ encPt lam)
            3 qep (configR1OnCurve adm) (A o)].boolBias ≤
      𝒟[oa >>= fun o =>
          SM.game (lFig8 Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000 lam)
            3 (qep + 1) SM.Config.h1
            (Computational.Proofs.Game.PromotedCostedReds.SimFig8Halted.libsignalToModularSchemeSimHalted
              (paramsV1 Z K (ida o) (idb o)) K ℓ Dh encPt encT decT
              (idsOf (ida o) (idb o)) lam qep (A o))].boolBias
        + 2 * (refineConst Z Dh encPt q qep δ +
          (𝒟[oa >>= fun o =>
              Computational.Proofs.Game.PromotedCostedReds.SimFig8Halted.simCNoneWinEventHalted
                (paramsV1 Z K (ida o) (idb o)) K ℓ Dh encPt encT decT
                (idsOf (ida o) (idb o)) lam qep (A o)] {true} +
           𝒟[oa >>= fun o =>
              Computational.Proofs.E2E.HaltedSessionChain.eps0EventTrackHalted
                (paramsV1 Z K (ida o) (idb o)) K ℓ encPt lam adm qep (A o)] {true} +
           𝒟[oa >>= fun o =>
              Proofs.Refinement.hiddenSaltGameTrackHalted
                (paramsV1 Z K (ida o) (idb o)) K ℓ Dh encPt encT decT
                (idsOf (ida o) (idb o)) lam qep (A o)] {true})) := by
  intro adm
  refine (boolBias_le_add_two_mul_boolDist _ _).trans (add_le_add le_rfl ?_)
  refine mul_le_mul_right ?_ 2
  refine Signed.boolDist_bind_le_add3 _ _ _ _ _ _ _ fun o => ?_
  have hL : LengthsOk (paramsV1 Z K (ida o) (idb o)) ℓ :=
    HeadlineV1.lengthsOk_paramsIdsWithSpqr_v1 Z K (ida o) (idb o) ℓ hℓ
  have hrt : Proofs.RoundTrip.RtHyp (paramsV1 Z K (ida o) (idb o)) ℓ :=
    ⟨signalRoundTripShort_proto, hL, signalEncodeFits32_proto⟩
  have hS : Corr.SpqrSendCorrectQ (paramsV1 Z K (ida o) (idb o)).spqr q :=
    CryptoVerification.SpqrV1Sync.SendTotal.spqrV1SessionB_sendCorrectQ Z.F K hK_tot q (by omega)
  refine (Proofs.Refinement.sim_game_boolDist_le_C_trackHalted
    (paramsV1 Z K (ida o) (idb o)) K ℓ Dh hDh encPt encT decT
    hX hdec hD hrt hinj hdum hz (idsOf (ida o) (idb o)) ⟨rfl, rfl⟩
    lam qep q hS (by omega) δ hδ (A o) (hq o)).trans_eq ?_
  have hwin :
      Proofs.Refinement.simCNoneWinEventTrackHalted (paramsV1 Z K (ida o) (idb o)) K ℓ Dh encPt
        encT decT (idsOf (ida o) (idb o)) lam qep (A o) =
      Computational.Proofs.Game.PromotedCostedReds.SimFig8Halted.simCNoneWinEventHalted
        (paramsV1 Z K (ida o) (idb o)) K ℓ Dh encPt encT decT (idsOf (ida o) (idb o)) lam qep
        (A o) := rfl
  have heps :
      Proofs.Refinement.eps0EventTrackHalted (paramsV1 Z K (ida o) (idb o)) K ℓ encPt lam
        (ratchetKeyAdmissible (paramsV1 Z K (ida o) (idb o)).codec decT encT) qep (A o) =
      Computational.Proofs.E2E.HaltedSessionChain.eps0EventTrackHalted
        (paramsV1 Z K (ida o) (idb o)) K ℓ encPt lam adm qep (A o) := rfl
  have hC : (paramsV1 Z K (ida o) (idb o)).C = Z := rfl
  rw [hwin, heps, hC]
  unfold refineConst Proofs.Refinement.hiddenSaltTermTrackHalted
  ring

/-- Bounds the tracker-halted single-session mixture bias by `sessionAdvantageBound` on
`v1SessionRedsHaltedClamped ℓ`. -/
theorem boolBias_gameRTrackHalted_session_le
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {α : Type}
    (ℓ : ℕ) (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt)
    (hK : Encaps1Total K) (hD : ∀ k x, C.D k (C.E k x) = x)
    (hℓ : ℓ < 10 ^ 6) (hDh : Dh.Commutes) (hX : X25519RealizesDh C Dh encPt encT)
    (hdec : ∀ T, decT (encT T) = some T) (hdum : ∀ T, encT T ≠ dummyKey)
    (hz : ∀ x, Dh.dh x 0 = 0) (hker : DhKerUniform Dh)
    (qep q : ℕ) (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hA : ∀ o ∈ support oa, SM.MakesAtMostQueries (A o) q) :
    𝒟[oa >>= fun o =>
        Prod.fst <$>
          Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.gameRTrackHalted
            Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.sampledSessionPqrOf
            C.F K
            (sessionSchemeFixedSpk
              (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) (ida o) (idb o))
              ℓ (s o))
            3 qep (configRefuseEarlyBobCorr decT encT) (A o)].boolBias ≤
      sessionAdvantageBound ℓ (v1SessionRedsHaltedClamped (Pt := Pt) ℓ)
        C K Dh encPt encT decT qep q δ oa ida idb s A := by
  let spqr := LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K
  let qep_c := Computational.Proofs.SessionCostedHalt.qepClamp qep q
  let adm := ratchetKeyAdmissible protoSignalCodec decT encT
  have hinj : Function.Injective encT := fun x y h =>
    Option.some.inj (by rw [← hdec x, ← hdec y, h])
  have hℓ31 : ℓ < 2 ^ 31 := by omega
  have h_clamp :
      𝒟[oa >>= fun o =>
        Prod.fst <$>
          Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.gameRTrackHalted
            Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.sampledSessionPqrOf
            C.F K
            (sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ (s o))
            3 qep (configRefuseEarlyBobCorr decT encT) (A o)] =
      𝒟[oa >>= fun o =>
        Prod.fst <$>
          Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.gameRTrackHalted
            Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.sampledSessionPqrOf
            C.F K
            (sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ (s o))
            3 qep_c (configRefuseEarlyBobCorr decT encT) (A o)] :=
    evalDist_mixGameRTrackHalted_min_eq
      Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.sampledSessionPqrOf
      C.F K (fun o => paramsIdsWithSpqr C spqr (ida o) (idb o)) (fun _ => rfl)
      ℓ 3 qep q s (configRefuseEarlyBobCorr decT encT) oa A hA
  rw [h_clamp]
  refine (boolBias_mixSpkGen_le_sessionAdvantageBound
    ℓ hℓ (v1SessionRedsHaltedRaw ℓ) C K hD Dh hDh encPt encT decT hdec hinj hdum
    qep_c q hq32 δ oa ida idb s
    (fun o B =>
      Prod.fst <$>
        Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.gameRTrackHalted
          Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.sampledSessionPqrOf
          C.F K
          (sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ (s o))
          3 qep_c (configRefuseEarlyBobCorr decT encT) B)
    (fun o B =>
      Prod.fst <$>
        Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.gameRTrackHalted
          Computational.Proofs.E2E.HaltedSessionChain.pqrOfSessionU
          C.F K
          (sessionSchemeU (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ)
          3 qep_c (configRefuseEarlyBobCorr decT encT) B)
    (fun o B =>
      Prod.fst <$>
        Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.gameRTrackHalted
          Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.libsignalSessionPqrOf
          C.F K
          (libsignalSessionScheme (paramsV1 C K (ida o) (idb o)) ℓ encPt 0)
          3 qep_c (configR1OnCurve adm) B)
    (fun o s' B =>
      Computational.Proofs.E2E.HaltedSpkDefs.spkLeakRedTrackHalted K
        (paramsIdsWithSpqr C spqr (ida o) (idb o)) Dh encPt encT decT qep_c s' B)
    (fun o B =>
      spkLeakRedU (Computational.Proofs.E2E.HaltedSpkDefs.spkLeakRedTrackHalted K)
        (paramsIdsWithSpqr C spqr (ida o) (idb o)) Dh encPt encT decT qep_c B)
    (fun o s' j B =>
      Computational.Proofs.E2E.HaltedSpkDefs.hop2PrgRedKTrackHalted
        (paramsIdsWithSpqr C spqr (ida o) (idb o)) K ℓ Dh encPt encT decT qep_c s' j B)
    (fun o s' j B =>
      Computational.Proofs.E2E.HaltedSpkDefs.hop2PrfRedKTrackHalted
        (paramsIdsWithSpqr C spqr (ida o) (idb o)) K ℓ Dh encT decT qep_c s' j B)
    (fun o B rc =>
      Computational.Proofs.E2E.HaltedSessionChain.uniformStartDistinguisherTrackHalted
        (paramsV1 C K (ida o) (idb o)) K ℓ (configR1OnCurve adm) qep_c B rc)
    (fun o B rc =>
      Computational.Proofs.E2E.HaltedSessionChain.epoch0DistinguisherTrackHalted
        (paramsV1 C K (ida o) (idb o)) K ℓ adm qep_c B rc)
    (fun o B =>
      Computational.Proofs.Game.PromotedCostedReds.SimFig8Halted.libsignalToModularSchemeSimHalted
        (paramsV1 C K (ida o) (idb o)) K ℓ Dh encPt encT decT (idsOf (ida o) (idb o)) 0 qep_c B)
    (fun o B =>
      Computational.Proofs.Game.PromotedCostedReds.SimFig8Halted.simCNoneWinEventHalted
        (paramsV1 C K (ida o) (idb o)) K ℓ Dh encPt encT decT (idsOf (ida o) (idb o)) 0 qep_c B)
    (fun o B =>
      Computational.Proofs.E2E.HaltedSessionChain.eps0EventTrackHalted
        (paramsV1 C K (ida o) (idb o)) K ℓ encPt (0 : Pt) adm qep_c B)
    (fun o B =>
      Proofs.Refinement.hiddenSaltGameTrackHalted
        (paramsV1 C K (ida o) (idb o)) K ℓ Dh encPt encT decT (idsOf (ida o) (idb o)) 0 qep_c B)
    A hA
    (Computational.Proofs.E2E.HaltedSpkSession.boolBias_mixSpkTrackHaltedWithSpqr_le_of_support
      C K hℓ31 Dh hDh encPt encT decT hX hdec hz qep_c q oa ida idb s A
      (fun o x P₁ P₂ => hker (s o) x P₁ P₂) hA)
    (fun o _ =>
      spkCostedEvalAgreesGen_v1SessionRedsHaltedRaw ℓ C K (ida o) (idb o) Dh encPt encT decT
        0 qep_c q)
    (fun B _ =>
      (Computational.Proofs.E2E.HaltedSessionChain.boolBias_mixUTrackHalted_le_v1
        C K encPt (0 : Pt) encT decT qep_c oa ida idb B).trans_eq (by
        simp only [refuseCorrB0_eq]; rfl))
    (fun B hB =>
      boolBias_mixRTrackHalted_le_v1 C K hK hℓ Dh hDh encPt encT decT
        hX hdec hD hinj hdum hz (0 : Pt) qep_c q hq32 δ hδ oa ida idb B hB)
    (fun B hB =>
      Computational.Proofs.E2E.HaltedSessionChain.evalDist_mixEps0TrackHalted_le_v1
        C K hℓ Dh encPt encT decT hX hdec hinj hdum (0 : Pt) qep_c q oa ida idb B hB)
    (fun o ho =>
      hiddenSalt_v1SessionRedsHaltedRaw_le ℓ C K hK (ida o) (idb o) Dh encPt encT
        decT (0 : Pt) qep_c q hℓ hDh hX hdec hinj hdum hz hD hq32 δ hδ (A o) (hA o ho))
    (fun o =>
      uniformEpoch0CostedEvalAgreesGen_v1SessionRedsHaltedRaw ℓ C K (ida o) (idb o) Dh encPt
        encT decT (0 : Pt) qep_c q)
    (fun o =>
      simFig8CostedEvalAgreesGen_v1SessionRedsHaltedRaw ℓ C K (ida o) (idb o) Dh encPt
        encT decT (0 : Pt) qep_c q)
    (fun _ => rfl)
    (fun _ => rfl)).trans ?_
  exact
    Computational.Proofs.SessionCostedHalt.sessionAdvantageBound_le_clampSessionCostedReductionFamily
      ℓ (v1SessionRedsHaltedRaw ℓ) C K Dh encPt encT decT qep q δ oa ida idb s A

/-- Single-session security (`SessionSecure ℓ`, Lemma 2) with costed reductions. -/
theorem session_secure_proof
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) :
    SessionSecure (Pt := Pt) ℓ := by
  refine ⟨v1SessionRedsHaltedClamped (Pt := Pt) ℓ, v1SessionRedsHaltedClamped_bounded ℓ, ?_⟩
  intro C K Dh encPt encT decT hK hD hℓ hDh hX hdec hdum hz hker qep q hq32 δ hδ
    α oa ida idb s A hA
  exact
    (Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.boolBias_session_le_trackHalted_add_two_mul_sessionKemFailProb
      C K ℓ decT encT qep oa ida idb s A).trans
      (add_le_add
        (boolBias_gameRTrackHalted_session_le ℓ C K Dh encPt encT decT
          hK hD hℓ hDh hX hdec hdum hz hker qep q hq32 δ hδ oa ida idb s A hA)
        le_rfl)

end CryptoVerification.E2E

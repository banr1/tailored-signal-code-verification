/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SessionCostedDF
public import Computational.Proofs.ReductionDsl.Fig8Atomic
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalSimC
public import Computational.Proofs.SpecLemmas.Session.StatementComposed
public import Computational.Proofs.E2E.SignedSession
import Computational.Proofs.E2E.ComposedPrefixHelpers
import Computational.Proofs.E2E.HeadlineSpkSession
import Computational.Proofs.CryptoGames.CKA.DHProof
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.PrivRedQueries
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Queries
import Computational.Proofs.CryptoGames.SM.Theorem1
import Computational.Proofs.E2E.SignedCoin
import Computational.Proofs.E2E.SignedFig8
import Computational.Proofs.E2E.SignedThm1
import Computational.Proofs.E2E.SignedThm8

/-!
# Composed PQXDH + Double Ratchet Security with SPQR V1

**Checked by Lean.** Defines semantic evaluation agreement predicates (`SpkCostedEvalAgrees`,
`SimFig8CostedEvalAgreesGen`) and the existential hidden-salt bound `HiddenSaltBoundV1HoldsEx`,
and assembles the mixture bounds for `ComposedSecurePrefixMixV1`.

**DEV-C5 (formalization): Bounded-query prefix-step hybrids and mixture reductions.**
`ComposedSecurePrefixMixV1` bounds the `qStart`-step prefix hybrid via prefix-step mixture
reductions over `support (composedPrefixWithSpqr ...)`, avoiding the `N_spk_tot * N_send_tot`
slot-hybrid multiplicity.
-/

@[expose] public section

open scoped ENNReal BigOperators
open ReductionDsl OracleComp OracleSpec MeasureTheory

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSM CryptoGames.LibsignalSM.Inst CryptoGames.LibsignalSM.Proofs
  Ratchet LibsignalInst LibsignalSession
  HMAC HKDF CBC LibsignalAead SM SM.Construction CryptoGames.SM.Thm1 CryptoGames.SM.ThmB
  CKA AEADScheme MACScheme WireAEAD FSAEAD
  CryptoGames.Ratchet.LibsignalSim
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.E2E.Signed CryptoVerification.E2E.HeadlineU
open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB)

local instance instInhabitedOfZeroHeadlineComposed {Pt : Type} [Zero Pt] : Inhabited Pt := ⟨0⟩

/-- Semantic evaluation agreement of `Rspk` with `spkLeakRed`, `spkLeakRedU`, `hop2PrgRedK`, and
`hop2PrfRedK` on `paramsV1 C K idA idB`. -/
def SpkCostedEvalAgrees {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ) (Rspk : SpkCostedReds Pt ℓ C K Dh encPt encT decT lam) : Prop :=
  ∀ (_hℓ : ℓ < 10 ^ 6)
    (_hdec : ∀ T, decT (encT T) = some T)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (_hq : SM.MakesAtMostQueries A q),
    let P := paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) idA idB
    (∀ s : BitVec 256,
      evalSpkLeakRed Rspk.spkLeakRed s A = spkLeakRed P Dh encPt encT decT qep s A) ∧
    (evalSpkLeakRedU Rspk.spkLeakRedU (fun x => evalSpkLeakRed Rspk.spkLeakRed x A) =
      spkLeakRedU spkLeakRed P Dh encPt encT decT qep A) ∧
    (∀ (s : BitVec 256) (j : ℕ), j < spkSwapHybridCount →
      evalSpkSwapPrgHybrid (Rspk.hop2PrgRedK j) s A =
        hop2PrgRedK P ℓ Dh encPt encT decT qep s j A) ∧
    (∀ (s : BitVec 256) (j : ℕ), j < spkSwapHybridCount →
      evalSpkSwapPrfHybrid (Rspk.hop2PrfRedK j) s A =
        hop2PrfRedK P ℓ Dh encT decT qep s j A)

/-- Semantic evaluation agreement of `Rspk` with target reductions `(spkLeakT, spkLeakUT, hop2PrgT,
hop2PrfT)`. -/
def SpkCostedEvalAgreesGen {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (q : ℕ)
    (spkLeakT : BitVec 256 →
      SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes →
      MACScheme.PRFAdversary Pt (BitVec 256))
    (spkLeakUT : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes →
      MACScheme.PRFAdversary Pt (BitVec 256))
    (hop2PrgT : BitVec 256 → ℕ →
      SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes →
      PRGScheme.PRGAdversary (BitVec 256 × BitVec 256))
    (hop2PrfT : BitVec 256 → ℕ →
      SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes →
      MACScheme.PRFAdversary Pt (BitVec 256))
    (Rspk : SpkCostedReds Pt ℓ C K Dh encPt encT decT lam) : Prop :=
  ∀ (_hℓ : ℓ < 10 ^ 6)
    (_hdec : ∀ T, decT (encT T) = some T)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (_hq : SM.MakesAtMostQueries A q),
    (∀ s : BitVec 256, evalSpkLeakRed Rspk.spkLeakRed s A = spkLeakT s A) ∧
    (evalSpkLeakRedU Rspk.spkLeakRedU (fun x => evalSpkLeakRed Rspk.spkLeakRed x A) =
      spkLeakUT A) ∧
    (∀ (s : BitVec 256) (j : ℕ), j < spkSwapHybridCount →
      evalSpkSwapPrgHybrid (Rspk.hop2PrgRedK j) s A = hop2PrgT s j A) ∧
    (∀ (s : BitVec 256) (j : ℕ), j < spkSwapHybridCount →
      evalSpkSwapPrfHybrid (Rspk.hop2PrfRedK j) s A = hop2PrfT s j A)

theorem spkCostedEvalAgrees_iff_gen {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ) (Rspk : SpkCostedReds Pt ℓ C K Dh encPt encT decT lam) :
    let P := paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) idA idB
    SpkCostedEvalAgrees C K idA idB ℓ Dh encPt encT decT lam qep q Rspk ↔
      SpkCostedEvalAgreesGen C K ℓ Dh encPt encT decT lam q
        (fun s A => spkLeakRed P Dh encPt encT decT qep s A)
        (fun A => spkLeakRedU spkLeakRed P Dh encPt encT decT qep A)
        (fun s j A => hop2PrgRedK P ℓ Dh encPt encT decT qep s j A)
        (fun s j A => hop2PrfRedK P ℓ Dh encT decT qep s j A)
        Rspk :=
  Iff.rfl

/-- Semantic evaluation agreement of `R.uniformStartRed` and `R.epoch0Red` with `(uniformStartT,
epoch0T)`. -/
def UniformEpoch0CostedEvalAgreesGen {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (q : ℕ)
    (uniformStartT epoch0T :
      SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes →
      (Ratchet.RootKey × BitVec 256) → ProbComp Bool)
    (R : SessionCostedReductions Pt ℓ C K idA idB Dh encPt encT decT lam) : Prop :=
  ∀ (_hℓ : ℓ < 10 ^ 6)
    (B : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (_hq : SM.MakesAtMostQueries B q) (rc : Ratchet.RootKey × BitVec 256),
    R.uniformStartRed.eval (fun _ => B) rc = uniformStartT B rc ∧
    R.epoch0Red.eval (fun _ => B) rc = epoch0T B rc

/-- Existential `SessionCostedReductions` witness satisfying `sessionCostedReductionsBounded`,
`SpkCostedEvalAgrees`, and `hiddenSaltTerm ≤ hiddenSaltBoundV1` for `qep ≤ q + 4`. -/
def HiddenSaltBoundV1HoldsEx {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) : Prop :=
  ∀ (C : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ),
    ∃ (R : SessionCostedReductions Pt ℓ C K idA idB Dh encPt encT decT lam),
      sessionCostedReductionsBounded ℓ C K idA idB Dh encPt encT decT lam qep q R ∧
      R.fs = (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).fs ∧
      (qep ≤ q + 4 →
        SpkCostedEvalAgrees C K idA idB ℓ Dh encPt encT decT lam qep q R.spk ∧
        R.fig8 = (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).fig8 ∧
        R.simFig8 = (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).simFig8 ∧
        R.epoch0Red = (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).epoch0Red ∧
        R.uniformStartRed =
          (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).uniformStartRed ∧
        ∀ (_hK_tot : Encaps1Total K)
          (_hℓ : ℓ < 10 ^ 6)
          (_hDh : Dh.Commutes) (_hX : X25519RealizesDh C Dh encPt encT)
          (_hdec : ∀ T, decT (encT T) = some T) (_hinj : Function.Injective encT)
          (_hdum : ∀ T, encT T ≠ dummyKey)
          (_hz : ∀ x, Dh.dh x 0 = 0) (_hD : ∀ k x, C.D k (C.E k x) = x)
          (_hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) (δ : ℝ≥0∞)
          (_hδ : ∀ Q : Pt,
            𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
          (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
          (_hq : SM.MakesAtMostQueries A q),
          let P := paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) idA idB
          LibsignalSimC.hiddenSaltTerm P ℓ Dh encPt encT decT (idsOf idA idB) lam qep
              (RefuseB0.refuseCorrB0 A) ≤
            hiddenSaltBoundV1 C K ℓ Dh encPt encT decT idA idB lam qep q δ R
              (RefuseB0.refuseCorrB0 A))

theorem evalDist_mixHiddenSaltGen_le_v1_of_support
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {α : Type}
    (Z : Crypto) (K : LibsignalSpqrV1.MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hidGame : α → ProbComp Bool)
    (hHid : ∀ o ∈ support oa,
      𝒟[hidGame o] {true} ≤
        hiddenSaltBoundV1 Z K ℓ Dh encPt encT decT (ida o) (idb o) lam qep q δ (R o) (A o)) :
    𝒟[oa >>= hidGame] {true} ≤
      hiddenSaltMixtureBound Z K ℓ Dh encPt encT decT lam qep q δ oa ida idb R A := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  rw [Signed.evalDist_bind_apply_lintegral]
  refine (lintegral_mono_of_support oa _ _ hHid).trans_eq ?_
  unfold hiddenSaltBoundV1 hiddenSaltMixtureBound
  change (∫⁻ o, _ ∂𝒟[oa]) = _
  simp only [lintegral_add_left Measurable.of_discrete,
    lintegral_finsetSum _ fun _ _ => Measurable.of_discrete,
    lintegral_const, evalDist_apply_univ_eq_one, mul_one]

/-- Semantic evaluation contract for `R.simFig8` against a Figure-8 simulator `simT` and win-event
game `winT`. -/
def SimFig8CostedEvalAgreesGen {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (Z : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ)
    (simT : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes → Fig8Adv Pt ℓ)
    (winT : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes → ProbComp Bool)
    (R : SessionCostedReductions Pt ℓ Z K idA idB Dh encPt encT decT lam) : Prop :=
  ∀ (_hℓ : ℓ < 10 ^ 6)
    (B : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (_hq : SM.MakesAtMostQueries B q),
    let simAdv := R.simFig8.eval (fun _ => B) ()
    let smFig8 := lFig8 Dh encPt Z protoSignalCodec ℓ encT (idsOf idA idB) 25000 lam
    SM.MakesAtMostQueries simAdv q ∧
    SM.EqualPubChalls (·.1) simAdv ∧
    SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => atomicShortPubB m.1) simAdv ∧
    SessionShort.GuardedSMShort simAdv ∧
    SM.game smFig8 3 (qep + 1) SM.Config.h1 simAdv =
      SM.game smFig8 3 (qep + 1) SM.Config.h1 (simT B) ∧
    winT B = (do
      let b ← $ᵗ Bool
      let (_, s) ← SM.run smFig8 3 (qep + 1) SM.Config.h1 b simAdv
      return s.win)

theorem fig8MixAuth_of_simFig8_le_fig8MixShortAuthV1
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {α : Type}
    (Z : Crypto) (K : LibsignalSpqrV1.MlKem)
    (hD : ∀ k x, Z.D k (Z.E k x) = x) {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (lam : Pt)
    (qep q : ℕ) (hq32 : 2 * q + 25002 < 2 ^ 32) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hqSim : ∀ o, SM.MakesAtMostQueries ((R o).simFig8.eval (fun _ => A o) ()) q)
    (hshSim : ∀ o, SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => atomicShortPubB m.1)
      ((R o).simFig8.eval (fun _ => A o) ()))
    (hgSim : ∀ o, SessionShort.GuardedSMShort ((R o).simFig8.eval (fun _ => A o) ()))
    (hfig8 : ∀ o, (R o).fig8 =
      (v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).fig8)
    (hfs : ∀ o, (R o).fs =
      (v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).fs) :
    letI : MeasurableSpace α := ⊤
    let simAdv : α → Fig8Adv Pt ℓ := fun o => (R o).simFig8.eval (fun _ => A o) ()
    2 * ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) t,
      (CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
          (advAvg oa fun o => redCKAAuth (dhScheme Dh) (rootPRNG Z.F encPt)
            (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL t
            (Thm1.challSim (2 + 1) (qep + 1) (simAdv o)))
        + PRFPRNG.advantage (rootPRNG Z.F encPt)
          (advAvg oa fun o => redPRNGAuth (dhScheme Dh) (rootPRNG Z.F encPt)
            (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL t
            (Thm1.challSim (2 + 1) (qep + 1) (simAdv o)))
        + ∫⁻ o, ∑ j ∈ Finset.range q,
            FSAEAD.advantage (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000)
              (redFSAuth (dhScheme Dh) (rootPRNG Z.F encPt)
                (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) j
                tL t (Thm1.challSim (2 + 1) (qep + 1) (simAdv o))) ∂𝒟[oa]) ≤
      fig8MixShortAuthV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R A := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  let simAdv : α → Fig8Adv Pt ℓ := fun o => (R o).simFig8.eval (fun _ => A o) ()
  have hChall : ∀ o,
      ((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
        lam (qep + 1) q).challSim.eval (fun _ => simAdv o) ()) =
      SM.Thm1.challSim (2 + 1) (qep + 1) (simAdv o) := fun o =>
    fig8RedsInst_challSim_eval Dh encPt Z protoSignalCodec ℓ hℓ encT (idsOf (ida o) (idb o))
      lam (qep + 1) q (simAdv o) (hqSim o)
  have hqChall : ∀ o,
      SM.MakesAtMostQueries (SM.Thm1.challSim (2 + 1) (qep + 1) (simAdv o)) q := fun o =>
    SM.Thm1.challSim_queries (2 + 1) (qep + 1) (simAdv o) q (hqSim o)
  have hshChall : ∀ o, SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => atomicShortPubB m.1)
      (SM.Thm1.challSim (2 + 1) (qep + 1) (simAdv o)) := fun o =>
    SessionShort.challSim_sendOk (2 + 1) (qep + 1)
      (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => atomicShortPubB m.1) (simAdv o) (hshSim o)
  have hAuthOk := fun o =>
    (fig8RedsInst_fsOk_and_encAtomicShort Dh encPt Z protoSignalCodec rfl ℓ hℓ encT
      (idsOf (ida o) (idb o)) lam (qep + 1) q (simAdv o) (hqSim o) (hshSim o) (hgSim o)).1
  unfold fig8MixShortAuthV1
  simp only [hfig8, hfs, v1SessionReds_fig8, v1SessionReds_fs]
  gcongr with t _ tL _
  · have hEq :
        (prefixAdvAvg oa fun o =>
          ((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
            lam (qep + 1) q).redCKAAuth tL t).eval
            (fun _ => ((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
              lam (qep + 1) q).challSim.eval (fun _ => simAdv o) ())) ()) =
        (advAvg oa fun o =>
          ((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
            lam (qep + 1) q).redCKAAuth tL t).eval
            (fun _ => SM.Thm1.challSim (2 + 1) (qep + 1) (simAdv o)) ()) := by
      unfold prefixAdvAvg advAvg
      exact congrArg _ (funext fun o => by rw [hChall o])
    exact le_of_eq ((fig8RedsInst_redCKAAuth_advAvg_advantage Dh encPt Z protoSignalCodec rfl ℓ hℓ
      encT oa (fun o => idsOf (ida o) (idb o)) lam (qep + 1) q (healEpoch tL) tL t
      _ hqChall hshChall).symm.trans
      (congrArg (CKA.advantage (dhScheme Dh) 1 (healEpoch tL)) hEq.symm))
  · have hEq :
        (prefixAdvAvg oa fun o =>
          ((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
            lam (qep + 1) q).redPRNGAuth tL t).eval
            (fun _ => ((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
              lam (qep + 1) q).challSim.eval (fun _ => simAdv o) ())) ()) =
        (advAvg oa fun o =>
          ((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
            lam (qep + 1) q).redPRNGAuth tL t).eval
            (fun _ => SM.Thm1.challSim (2 + 1) (qep + 1) (simAdv o)) ()) := by
      unfold prefixAdvAvg advAvg
      exact congrArg _ (funext fun o => by rw [hChall o])
    exact le_of_eq ((fig8RedsInst_redPRNGAuth_advAvg_advantage Dh encPt Z protoSignalCodec rfl ℓ hℓ
      encT oa (fun o => idsOf (ida o) (idb o)) lam (qep + 1) q tL t _ hqChall hshChall).symm.trans
      (congrArg (PRFPRNG.advantage (rootPRNG Z.F encPt)) hEq.symm))
  · rw [lintegral_finsetSum (Finset.range q) (fun _ _ => Measurable.of_discrete)]
    gcongr with j _
    have hbias := fig8RedsInst_redFSAuth_mix_boolBias Dh encPt Z protoSignalCodec rfl ℓ hℓ encT
      oa (fun o => idsOf (ida o) (idb o)) lam (qep + 1) q j tL t _ hqChall hshChall
    have hGame :
        (oa >>= fun o => FSAEAD.game (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) maxForwardJumps)
          (((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
            lam (qep + 1) q).redFSAuth j tL t).eval
            (fun _ => SM.Thm1.challSim (2 + 1) (qep + 1) (simAdv o)) ())) =
        (oa >>= fun o => FSAEAD.game (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000)
          (((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
            lam (qep + 1) q).redFSAuth j tL t).eval
            (fun _ => ((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
              lam (qep + 1) q).challSim.eval (fun _ => simAdv o) ())) ())) :=
      bind_congr fun o => by rw [hChall o]; rfl
    change (∫⁻ o, FSAEAD.advantage (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) maxForwardJumps)
      (redFSAuth (dhScheme Dh) (rootPRNG Z.F encPt)
        (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) maxForwardJumps) lam 1 (qep + 1) j
        tL t (Thm1.challSim (2 + 1) (qep + 1) (simAdv o))) ∂𝒟[oa]) ≤ _
    rw [hbias, hGame, fsShortBoundMixWith_inst_eq Z ℓ encT oa (fun o => idsOf (ida o) (idb o))
      (min (2 * q) (q + 2)) q hℓ hinj _ (fun o => (hAuthOk o j tL t).1.1) (fun o => (hAuthOk o j tL t).2)]
    exact lFS_bound_mix_of_fsOk_v1 Z hD ℓ (by omega) encT hinj hdum oa
      (fun o => idsOf (ida o) (idb o)) _ (min (2 * q) (q + 2)) q (by omega) (fun o => (hAuthOk o j tL t).1)

theorem fig8MixPriv_of_simFig8_le_fig8MixShortPrivV1
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {α : Type}
    (Z : Crypto) (K : LibsignalSpqrV1.MlKem)
    (hD : ∀ k x, Z.D k (Z.E k x) = x) {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (lam : Pt)
    (qep q : ℕ) (hq32 : 2 * q + 25002 < 2 ^ 32) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hqSim : ∀ o, SM.MakesAtMostQueries ((R o).simFig8.eval (fun _ => A o) ()) q)
    (hshSim : ∀ o, SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => atomicShortPubB m.1)
      ((R o).simFig8.eval (fun _ => A o) ()))
    (hgSim : ∀ o, SessionShort.GuardedSMShort ((R o).simFig8.eval (fun _ => A o) ()))
    (hfig8 : ∀ o, (R o).fig8 =
      (v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).fig8)
    (hfs : ∀ o, (R o).fs =
      (v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).fs) :
    letI : MeasurableSpace α := ⊤
    let simAdv : α → Fig8Adv Pt ℓ := fun o => (R o).simFig8.eval (fun _ => A o) ()
    2 * ∑ i ∈ Finset.range ((qep + 1) + 1), ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) i,
      (2 * CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
          (advAvg oa fun o => redCKAPriv (dhScheme Dh) (rootPRNG Z.F encPt)
            (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL i
            (ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simAdv o)))
        + 2 * PRFPRNG.advantage (rootPRNG Z.F encPt)
          (advAvg oa fun o => redPRNGPriv (dhScheme Dh) (rootPRNG Z.F encPt)
            (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL i
            (ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simAdv o)))
        + 𝒟[oa >>= fun o =>
            FSAEAD.game (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000)
              (redFSPriv (dhScheme Dh) (rootPRNG Z.F encPt)
                (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL i
                (ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simAdv o)))].boolBias
        + 2 * ∫⁻ o,
            FSAEAD.advantage (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000)
              (redFSPrivCoin (dhScheme Dh) (rootPRNG Z.F encPt)
                (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL i
                (ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simAdv o))) ∂𝒟[oa]) ≤
      fig8MixShortPrivV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R A := by
  let _ : MeasurableSpace α := ⊤
  let simAdv : α → Fig8Adv Pt ℓ := fun o => (R o).simFig8.eval (fun _ => A o) ()
  have hPriv : ∀ o i,
      (((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
        lam (qep + 1) q).privRedB i).eval (fun _ => simAdv o) ()) =
      SM.ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simAdv o) := fun o i =>
    fig8RedsInst_privRedB_eval Dh encPt Z protoSignalCodec ℓ hℓ encT (idsOf (ida o) (idb o))
      lam (qep + 1) q i (simAdv o) (hqSim o)
  have hqPriv : ∀ i o,
      SM.MakesAtMostQueries (SM.ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simAdv o)) q :=
    fun i o => PrivRedQueries.privRedB_queries (2 + 1) (qep + 1) i (lBlank ℓ) (simAdv o) q (hqSim o)
  have hshPriv : ∀ i o, SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => atomicShortPubB m.1)
      (SM.ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simAdv o)) := fun i o =>
    SessionShort.privRedB_sendOk (2 + 1) (qep + 1) i
      (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => atomicShortPubB m.1)
      (lBlank ℓ) (fun _ => rfl) (simAdv o) (hshSim o)
  have hPrivOk := fun o =>
    (fig8RedsInst_fsOk_and_encAtomicShort Dh encPt Z protoSignalCodec rfl ℓ hℓ encT
      (idsOf (ida o) (idb o)) lam (qep + 1) q (simAdv o) (hqSim o) (hshSim o) (hgSim o)).2
  unfold fig8MixShortPrivV1
  simp only [hfig8, hfs, v1SessionReds_fig8, v1SessionReds_fs]
  gcongr with i _ tL _
  · have hEq :
        (prefixAdvAvg oa fun o =>
          ((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
            lam (qep + 1) q).redCKAPriv tL i).eval
            (fun _ => (((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
              lam (qep + 1) q).privRedB i).eval (fun _ => simAdv o) ())) ()) =
        (advAvg oa fun o =>
          ((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
            lam (qep + 1) q).redCKAPriv tL i).eval
            (fun _ => SM.ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simAdv o)) ()) := by
      unfold prefixAdvAvg advAvg
      exact congrArg _ (funext fun o => by rw [hPriv o i])
    exact le_of_eq ((fig8RedsInst_redCKAPriv_advAvg_advantage Dh encPt Z protoSignalCodec rfl ℓ hℓ
      encT oa (fun o => idsOf (ida o) (idb o)) lam (qep + 1) q (healEpoch tL) tL i
      _ (hqPriv i) (hshPriv i)).symm.trans
      (congrArg (CKA.advantage (dhScheme Dh) 1 (healEpoch tL)) hEq.symm))
  · have hEq :
        (prefixAdvAvg oa fun o =>
          ((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
            lam (qep + 1) q).redPRNGPriv tL i).eval
            (fun _ => (((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
              lam (qep + 1) q).privRedB i).eval (fun _ => simAdv o) ())) ()) =
        (advAvg oa fun o =>
          ((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
            lam (qep + 1) q).redPRNGPriv tL i).eval
            (fun _ => SM.ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simAdv o)) ()) := by
      unfold prefixAdvAvg advAvg
      exact congrArg _ (funext fun o => by rw [hPriv o i])
    exact le_of_eq ((fig8RedsInst_redPRNGPriv_advAvg_advantage Dh encPt Z protoSignalCodec rfl ℓ hℓ
      encT oa (fun o => idsOf (ida o) (idb o)) lam (qep + 1) q tL i
      _ (hqPriv i) (hshPriv i)).symm.trans
      (congrArg (PRFPRNG.advantage (rootPRNG Z.F encPt)) hEq.symm))
  · have heq := (fig8RedsInst_redFSPriv_mix_evalDistEq Dh encPt Z protoSignalCodec rfl ℓ hℓ encT
      oa (fun o => idsOf (ida o) (idb o)) lam (qep + 1) q tL i _ (hqPriv i) (hshPriv i)).evalDist_eq
    have hGame :
        (oa >>= fun o => FSAEAD.game (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) maxForwardJumps)
          (((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
            lam (qep + 1) q).redFSPriv tL i).eval
            (fun _ => SM.ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simAdv o)) ())) =
        (oa >>= fun o => FSAEAD.game (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000)
          (((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
            lam (qep + 1) q).redFSPriv tL i).eval
            (fun _ => (((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
              lam (qep + 1) q).privRedB i).eval (fun _ => simAdv o) ())) ())) :=
      bind_congr fun o => by rw [hPriv o i]; rfl
    change 𝒟[oa >>= fun o => FSAEAD.game (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) maxForwardJumps)
      (redFSPriv (dhScheme Dh) (rootPRNG Z.F encPt)
        (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) maxForwardJumps) lam 1 (qep + 1) tL i
        (ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simAdv o)))].boolBias ≤ _
    rw [← heq, hGame, fsShortBoundMixWith_inst_eq Z ℓ encT oa (fun o => idsOf (ida o) (idb o))
      (min (2 * q) (q + 2)) q hℓ hinj _ (fun o => ((hPrivOk o i).1 tL).1.1) (fun o => ((hPrivOk o i).1 tL).2)]
    exact lFS_bound_mix_of_fsOk_v1 Z hD ℓ (by omega) encT hinj hdum oa
      (fun o => idsOf (ida o) (idb o)) _ (min (2 * q) (q + 2)) q (by omega) (fun o => ((hPrivOk o i).1 tL).1)
  · have hbias := fig8RedsInst_redFSPrivCoin_mix_boolBias Dh encPt Z protoSignalCodec rfl ℓ hℓ
      encT oa (fun o => idsOf (ida o) (idb o)) lam (qep + 1) q tL i _ (hqPriv i) (hshPriv i)
    have hGame :
        (oa >>= fun o => FSAEAD.game (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) maxForwardJumps)
          (((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
            lam (qep + 1) q).redFSPrivCoin tL i).eval
            (fun _ => SM.ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simAdv o)) ())) =
        (oa >>= fun o => FSAEAD.game (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000)
          (((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
            lam (qep + 1) q).redFSPrivCoin tL i).eval
            (fun _ => (((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
              lam (qep + 1) q).privRedB i).eval (fun _ => simAdv o) ())) ())) :=
      bind_congr fun o => by rw [hPriv o i]; rfl
    change (∫⁻ o, FSAEAD.advantage (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) maxForwardJumps)
      (redFSPrivCoin (dhScheme Dh) (rootPRNG Z.F encPt)
        (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) maxForwardJumps) lam 1 (qep + 1) tL i
        (ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simAdv o))) ∂𝒟[oa]) ≤ _
    rw [hbias, hGame, fsShortBoundMixWith_inst_eq Z ℓ encT oa (fun o => idsOf (ida o) (idb o))
      (min (2 * q) (q + 2)) q hℓ hinj _ (fun o => ((hPrivOk o i).2 tL).1.1) (fun o => ((hPrivOk o i).2 tL).2)]
    exact lFS_bound_mix_of_fsOk_v1 Z hD ℓ (by omega) encT hinj hdum oa
      (fun o => idsOf (ida o) (idb o)) _ (min (2 * q) (q + 2)) q (by omega) (fun o => ((hPrivOk o i).2 tL).1)

theorem boolBias_mixFig8_of_simFig8_le_fig8MixShortV1
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {α : Type}
    (Z : Crypto) (K : LibsignalSpqrV1.MlKem)
    (hD : ∀ k x, Z.D k (Z.E k x) = x) {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (Dh : DHFun (BitVec 256) Pt)
    (hDh : Dh.Commutes) (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (lam : Pt)
    (qep q : ℕ) (hq32 : 2 * q + 25002 < 2 ^ 32) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (simT : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes → Fig8Adv Pt ℓ)
    (winT : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes → ProbComp Bool)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : ∀ o, SM.MakesAtMostQueries (A o) q)
    (hSim : ∀ o, SimFig8CostedEvalAgreesGen Z K (ida o) (idb o) ℓ Dh encPt encT decT lam qep q
      (simT o) (winT o) (R o))
    (hfig8 : ∀ o, (R o).fig8 =
      (v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).fig8)
    (hfs : ∀ o, (R o).fs =
      (v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).fs) :
    𝒟[oa >>= fun o => SM.game (lFig8 Dh encPt Z protoSignalCodec ℓ encT
        (idsOf (ida o) (idb o)) 25000 lam) 3 (qep + 1) SM.Config.h1 (simT o (A o))].boolBias ≤
      fig8MixShortAuthV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R A +
      fig8MixShortPrivV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R A := by
  let _ : MeasurableSpace α := ⊤
  let simAdv : α → Fig8Adv Pt ℓ := fun o => (R o).simFig8.eval (fun _ => A o) ()
  have hS := fun o => hSim o hℓ (A o) (hq o)
  have hGame :
      (oa >>= fun o => SM.game (lFig8 Dh encPt Z protoSignalCodec ℓ encT
        (idsOf (ida o) (idb o)) 25000 lam) 3 (qep + 1) SM.Config.h1 (simT o (A o))) =
      (oa >>= fun o => SM.game (lFig8 Dh encPt Z protoSignalCodec ℓ encT
        (idsOf (ida o) (idb o)) 25000 lam) 3 (qep + 1) SM.Config.h1 (simAdv o)) :=
    bind_congr fun o => (hS o).2.2.2.2.1.symm
  rw [hGame]
  have h6 := theorem6_h1_blank_mix (dhScheme Dh) (rootPRNG Z.F encPt)
    (fun o => lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1)
    (dhScheme_correct Dh hDh) (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => m.1) (lBlank ℓ)
    (fun _ _ h => by simp [lBlank, h]) oa simAdv
    (fun o => (hS o).2.1) q (fun o => (hS o).1)
  exact h6.trans (add_le_add
    (fig8MixAuth_of_simFig8_le_fig8MixShortAuthV1 Z K hD hℓ Dh encPt encT decT hinj hdum lam qep q
      hq32 oa ida idb R A (fun o => (hS o).1) (fun o => (hS o).2.2.1) (fun o => (hS o).2.2.2.1)
      hfig8 hfs)
    (fig8MixPriv_of_simFig8_le_fig8MixShortPrivV1 Z K hD hℓ Dh encPt encT decT hinj hdum lam qep q
      hq32 oa ida idb R A (fun o => (hS o).1) (fun o => (hS o).2.2.1) (fun o => (hS o).2.2.2.1)
      hfig8 hfs))

theorem evalDist_mixWin_of_simFig8_le_fig8MixShortAuthV1
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {α : Type}
    (Z : Crypto) (K : LibsignalSpqrV1.MlKem)
    (hD : ∀ k x, Z.D k (Z.E k x) = x) {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (Dh : DHFun (BitVec 256) Pt)
    (hDh : Dh.Commutes) (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (lam : Pt)
    (qep q : ℕ) (hq32 : 2 * q + 25002 < 2 ^ 32) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (simT : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes → Fig8Adv Pt ℓ)
    (winT : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes → ProbComp Bool)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : ∀ o, SM.MakesAtMostQueries (A o) q)
    (hSim : ∀ o, SimFig8CostedEvalAgreesGen Z K (ida o) (idb o) ℓ Dh encPt encT decT lam qep q
      (simT o) (winT o) (R o))
    (hfig8 : ∀ o, (R o).fig8 =
      (v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).fig8)
    (hfs : ∀ o, (R o).fs =
      (v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).fs) :
    2 * 𝒟[oa >>= fun o => winT o (A o)] {true} ≤
      fig8MixShortAuthV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R A := by
  let _ : MeasurableSpace α := ⊤
  let simAdv : α → Fig8Adv Pt ℓ := fun o => (R o).simFig8.eval (fun _ => A o) ()
  have hS := fun o => hSim o hℓ (A o) (hq o)
  have hWin :
      𝒟[oa >>= fun o => winT o (A o)] {true} ≤
        ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) t,
          𝒟[oa >>= fun o => authGame (lFig8 Dh encPt Z protoSignalCodec ℓ encT
            (idsOf (ida o) (idb o)) 25000 lam) (2 + 1) (qep + 1) tL t
            (Thm1.challSim (2 + 1) (qep + 1) (simAdv o))] {true} :=
    evalDist_bind_apply_le_sum_sum oa _ _ _ _ fun o => by
      rw [(hS o).2.2.2.2.2]
      exact Proofs.Refinement.run_win_prob_le_auth
        (lFig8 Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000 lam)
        (2 + 1) (qep + 1) (by omega) (simAdv o)
  have h8 :
      2 * (∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) t,
          𝒟[oa >>= fun o => authGame (lFig8 Dh encPt Z protoSignalCodec ℓ encT
            (idsOf (ida o) (idb o)) 25000 lam) (2 + 1) (qep + 1) tL t
            (Thm1.challSim (2 + 1) (qep + 1) (simAdv o))] {true}) ≤
        2 * ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) t,
          (CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
              (advAvg oa fun o => redCKAAuth (dhScheme Dh) (rootPRNG Z.F encPt)
                (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL t
                (Thm1.challSim (2 + 1) (qep + 1) (simAdv o)))
            + PRFPRNG.advantage (rootPRNG Z.F encPt)
              (advAvg oa fun o => redPRNGAuth (dhScheme Dh) (rootPRNG Z.F encPt)
                (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL t
                (Thm1.challSim (2 + 1) (qep + 1) (simAdv o)))
            + ∫⁻ o, ∑ j ∈ Finset.range q,
                FSAEAD.advantage (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000)
                  (redFSAuth (dhScheme Dh) (rootPRNG Z.F encPt)
                    (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) j
                    tL t (Thm1.challSim (2 + 1) (qep + 1) (simAdv o))) ∂𝒟[oa]) := by
    gcongr with t _ tL _
    exact theorem8_mix (dhScheme Dh) (rootPRNG Z.F encPt)
      (fun o => lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1)
      (dhScheme_correct Dh hDh) tL t q oa _ fun o => Thm1.challSim_queries _ _ _ q (hS o).1
  exact (mul_le_mul_right hWin 2).trans (h8.trans
    (fig8MixAuth_of_simFig8_le_fig8MixShortAuthV1 Z K hD hℓ Dh encPt encT decT hinj hdum lam qep q
      hq32 oa ida idb R A (fun o => (hS o).1) (fun o => (hS o).2.2.1) (fun o => (hS o).2.2.2.1)
      hfig8 hfs))

/-- Bounds the `boolBias` of `oa >>= gameU` by `uniformStartMixtureBound` across Uniform-Start,
Figure-8, epoch-0, and hidden-salt hops. -/
theorem boolBias_mixUGen_le_uTermShortMix
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {α : Type}
    (Z : Crypto) (K : LibsignalSpqrV1.MlKem)
    (hD : ∀ k x, Z.D k (Z.E k x) = x)
    {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (lam : Pt) (qep q : ℕ) (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) (δ : ℝ≥0∞)
    (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (gameU gameR : α →
      SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes → ProbComp Bool)
    (uniformStartT epoch0T : α →
      SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes →
      (Ratchet.RootKey × BitVec 256) → ProbComp Bool)
    (simT : α →
      SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes → Fig8Adv Pt ℓ)
    (winT eps0Game hidGame : α →
      SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes → ProbComp Bool)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : ∀ o ∈ support oa, SM.MakesAtMostQueries (A o) q)
    (hUR : ∀ B : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes,
      (∀ o, SM.MakesAtMostQueries (B o) q) →
      𝒟[oa >>= fun o => gameU o (B o)].boolBias ≤
        𝒟[oa >>= fun o => gameR o (RefuseB0.refuseCorrB0 (B o))].boolBias
          + 2 * (rootKdfAsPrg Z.F (encPt lam)).prgAdvantage
              (prefixPrgAvg oa fun o rc => uniformStartT o (RefuseB0.refuseCorrB0 (B o)) rc))
    (hRSim : ∀ B : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes,
      (∀ o, SM.MakesAtMostQueries (B o) q) →
      𝒟[oa >>= fun o => gameR o (B o)].boolBias ≤
        𝒟[oa >>= fun o => SM.game (lFig8 Dh encPt Z protoSignalCodec ℓ encT
            (idsOf (ida o) (idb o)) 25000 lam) 3 (qep + 1) SM.Config.h1 (simT o (B o))].boolBias
          + 2 * (refineConst Z Dh encPt q qep δ +
            (𝒟[oa >>= fun o => winT o (B o)] {true} +
             𝒟[oa >>= fun o => eps0Game o (B o)] {true} +
             𝒟[oa >>= fun o => hidGame o (B o)] {true})))
    (hEps0 : ∀ B : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes,
      (∀ o, SM.MakesAtMostQueries (B o) q) →
      𝒟[oa >>= fun o => eps0Game o (B o)] {true} ≤
        (rootKdfAsPrg Z.F (encPt lam)).prgAdvantage
          (prefixPrgAvg oa fun o rc => epoch0T o (B o) rc) + q * eps0IdealUnit Z.F)
    (hHid : ∀ o ∈ support oa,
      𝒟[hidGame o (RefuseB0.refuseCorrB0 (A o))] {true} ≤
        hiddenSaltBoundV1 Z K ℓ Dh encPt encT decT (ida o) (idb o) lam qep q δ (R o)
          (RefuseB0.refuseCorrB0 (A o)))
    (hUE : ∀ o, UniformEpoch0CostedEvalAgreesGen Z K (ida o) (idb o) ℓ Dh encPt encT decT lam q
      (uniformStartT o) (epoch0T o) (R o))
    (hSim : ∀ o, SimFig8CostedEvalAgreesGen Z K (ida o) (idb o) ℓ Dh encPt encT decT lam qep q
      (simT o) (winT o) (R o))
    (hfig8 : ∀ o, (R o).fig8 =
      (v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).fig8)
    (hfs : ∀ o, (R o).fs =
      (v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).fs) :
    𝒟[oa >>= fun o => gameU o (A o)].boolBias ≤
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
  have hU := hUR A' hq'
  have hUsEq :
      (prefixPrgAvg oa fun o rc => uniformStartT o (RefuseB0.refuseCorrB0 (A' o)) rc) =
      (prefixPrgAvg oa fun o rc =>
        (R o).uniformStartRed.eval (fun _ => RefuseB0.refuseCorrB0 (A' o)) rc) := by
    funext rc
    unfold prefixPrgAvg
    congr 1; funext o
    exact ((hUE o hℓ (RefuseB0.refuseCorrB0 (A' o)) (hqR o) rc).1).symm
  rw [hUsEq] at hU
  have hR := hRSim (fun o => RefuseB0.refuseCorrB0 (A' o)) hqR
  have h1 := boolBias_mixFig8_of_simFig8_le_fig8MixShortV1 Z K hD hℓ Dh hDh encPt encT decT hinj
    hdum lam qep q (by omega) oa ida idb R simT winT (fun o => RefuseB0.refuseCorrB0 (A' o)) hqR
    hSim hfig8 hfs
  have h2 := evalDist_mixWin_of_simFig8_le_fig8MixShortAuthV1 Z K hD hℓ Dh hDh encPt encT decT hinj
    hdum lam qep q (by omega) oa ida idb R simT winT (fun o => RefuseB0.refuseCorrB0 (A' o)) hqR
    hSim hfig8 hfs
  have h3 := hEps0 (fun o => RefuseB0.refuseCorrB0 (A' o)) hqR
  have hEps0Eq :
      (prefixPrgAvg oa fun o rc => epoch0T o (RefuseB0.refuseCorrB0 (A' o)) rc) =
      (prefixPrgAvg oa fun o rc =>
        (R o).epoch0Red.eval (fun _ => RefuseB0.refuseCorrB0 (A' o)) rc) := by
    funext rc
    unfold prefixPrgAvg
    congr 1; funext o
    exact ((hUE o hℓ (RefuseB0.refuseCorrB0 (A' o)) (hqR o) rc).2).symm
  rw [hEps0Eq] at h3
  have h4 := evalDist_mixHiddenSaltGen_le_v1_of_support Z K ℓ Dh encPt encT decT lam qep q δ
    oa ida idb R (fun o => RefuseB0.refuseCorrB0 (A' o))
    (fun o => hidGame o (RefuseB0.refuseCorrB0 (A' o)))
    (fun o ho => by rw [hsup o ho]; exact hHid o ho)
  have hle :
      𝒟[oa >>= fun o => gameU o (A' o)].boolBias ≤
        uniformStartMixtureBound Z K ℓ Dh encPt encT decT lam qep q δ oa ida idb R A' := by
    refine hU.trans ((add_le_add hR le_rfl).trans ?_)
    rw [mul_add, mul_add, mul_add]
    refine (add_le_add (add_le_add h1 (add_le_add le_rfl (add_le_add
      (add_le_add h2 (mul_le_mul_right h3 2)) (mul_le_mul_right h4 2)))) le_rfl).trans_eq ?_
    unfold uniformStartMixtureBound
    ring
  have hg :
      𝒟[oa >>= fun o => gameU o (A' o)] =
      𝒟[oa >>= fun o => gameU o (A o)] :=
    OracleComp.evalDist_bind_congr_of_support oa _ _ fun o ho => by
      rw [hsup o ho]
  rw [hg, uTermShortMixV1_congr_of_support Z K ℓ Dh encPt encT decT lam qep q δ oa ida idb R _ _
    hsup] at hle
  exact hle

end CryptoVerification.E2E

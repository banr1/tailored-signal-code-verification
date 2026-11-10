/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.StatementSession
public import Computational.Proofs.E2E.SpkHop2Red
public import Computational.Proofs.E2E.SpkLeakRedModel
public import Computational.Proofs.E2E.SpkCostedEval
public import Computational.Proofs.E2E.HeadlineSpkSession
public import Computational.Proofs.E2E.SignedSession
public import Computational.Proofs.Game.PromotedCostedReds.SpkLeakRedRInProg
public import Computational.Proofs.Game.PromotedCostedReds.SpkHop2RInProg
import Computational.Proofs.SpqrV1Sync.SendTotalExtras
import Computational.Proofs.E2E.ComposedPrefixHelpers
import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds

/-!
# Costed SPK Reductions and Headline Session SPK Slice

Packages the costed SPK reduction bundle `spkCostedRedsInst` over `atomicSessionOps`, proves its
`spkCostedBounds` and `.eval` agreement bridges, and establishes the costed leaked-SPK mixture
advantage rewrites and 3-hop bias bound `boolBias_mixSpkV1_costed_le`.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal BigOperators
open OracleComp OracleSpec

namespace Computational.Proofs.E2E.SpkCostedAndHeadlineSlice

open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.Ratchet (extractPRF expandPRG)
open CryptoGames.Ratchet.LibsignalInst (X25519RealizesDh)
open CryptoGames.SM (MakesAtMostQueries gameR Adversary)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey GhostState)
open CryptoVerification.LibsignalSession (GRedBounded ratchetCostBudget)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal (spqrV1Send_msg_len_le)
open CryptoVerification.E2E (Bytes SpkCostedReds spkCostedBounds spkSwapHybridCount
  spkLeakRedUBudget spkTier1Budget spkTier2Budget spkHopBudget
  evalSpkLeakRed evalSpkLeakRedU evalSpkSwapPrgHybrid evalSpkSwapPrfHybrid
  spkLeakRed spkLeakRedU hop2PrgRedK hop2PrfRedK
  paramsIdsWithSpqr sessionSchemeFixedSpk sessionSchemeU configRefuseEarlyBobCorr
  SessionCostedReductionFamily sessionAdvantageBound uniformStartMixtureBound
  prefixPrfAvg prefixPrgAvg epoch0ChainForgeryTerm hop2CreateCollTerm spkSwapSpuriousStepTerm
  spkSwapCreationPointHitTerm spkSwapHiddenScalarGuessTerm)
open CryptoVerification.E2E.HeadlineSpk (mkSpkCostedReds mkSpkCostedReds_bounds
  mkSpkCostedReds_evalSpkLeakRed mkSpkCostedReds_evalSpkLeakRedU
  mkSpkCostedReds_evalHop2PrgRedK mkSpkCostedReds_evalHop2PrfRedK
  mkSpkCostedReds_evalHop2PrgRedK_of_dec mkSpkCostedReds_evalHop2PrfRedK_of_dec)
open CryptoVerification.E2E.Signed (leakAvgWithSpqr leakUAvgWithSpqr
  hop2PrgAvgWithSpqr hop2PrfAvgWithSpqr hop2TermAvgWithSpqr
  prfAdvantage_prfAvg_congr_of_support' prgAdvantage_prgAvg_congr_of_support'
  boolBias_mixSpkWithSpqr_le_of_support)

/-! ## Canonical `SpkCostedReds` instance and bounds -/

/-- Canonical `SpkCostedReds` bundle over `atomicSessionOps`. -/
def spkCostedRedsInst {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (q qep : ℕ) :
    SpkCostedReds Pt ℓ C K Dh encPt encT decT lam :=
  mkSpkCostedReds ℓ C K idA idB Dh encPt encT decT lam q qep

theorem hop2PrfRedK_queryBudget_le_old (q : ℕ) :
    q ≤ 2 * q := by
  omega

private theorem spkHopBudget_le_ratchet (q qep ℓ : ℕ) :
    spkHopBudget q qep ℓ ≤ ratchetCostBudget q qep := by
  refine (Nat.min_le_left _ _).trans ?_
  have hmfj : CryptoGames.LibsignalSession.maxForwardJumps = 25000 := rfl
  unfold spkTier1Budget ratchetCostBudget
  rw [hmfj]
  have hq : q + 1 ≤ (q + 1) ^ 2 := by nlinarith
  have hqb : (q + 1) * ReductionDsl.bits qep ≤ (q + 1) ^ 2 * ReductionDsl.bits qep :=
    Nat.mul_le_mul_right (ReductionDsl.bits qep) hq
  nlinarith

private theorem spkLeakRedUBudget_le_ratchet (q qep : ℕ) :
    spkLeakRedUBudget q ≤ ratchetCostBudget q qep := by
  have hmfj : CryptoGames.LibsignalSession.maxForwardJumps = 25000 := rfl
  unfold spkLeakRedUBudget ratchetCostBudget
  rw [hmfj]
  have hq : q + 1 ≤ (q + 1) ^ 2 := by nlinarith
  nlinarith

private theorem gRedBounded_mono {S : ReductionDsl.Sig} {O : ReductionDsl.Ops S} {ι κ : Type}
    {T : OracleSpec ι} {I : ReductionDsl.Iface S T} {G : OracleSpec κ}
    {C : ReductionDsl.GameCodec S G} {rIn aIn aOut out : ReductionDsl.Ty S}
    {R : ReductionDsl.CostedReduction O I G C rIn aIn aOut out}
    {wTag : I.Tag → ℕ} {wSamp : I.smp.Samp → ℕ}
    {q qOut qOut' b1 b2 : ℕ}
    (hb : GRedBounded R wTag wSamp q qOut b1) (hqOut : qOut ≤ qOut') (hcost : b1 ≤ b2) :
    GRedBounded R wTag wSamp q qOut' b2 :=
  CryptoVerification.E2E.Costed.gRedBounded_of_bounds R wTag wSamp q qOut' b2
    (hb.1.trans hcost)
    (hb.2.1.trans (Nat.add_le_add_left (Nat.mul_le_mul_left (2 ^ 12) (ReductionDsl.bits_mono hcost)) _))
    (hb.2.2.1.trans hqOut)
    hb.2.2.2.1
    hb.2.2.2.2.1

theorem spkCostedBounds_imp_old {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} {C : Crypto} {K : MlKem}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    (q qep : ℕ) (R : SpkCostedReds Pt ℓ C K Dh encPt encT decT lam)
    (h : spkCostedBounds q qep R) :
    GRedBounded R.spkLeakRed (fun _ => 1) (fun _ => 0)
      q (q + 1) (ratchetCostBudget q qep) ∧
    GRedBounded R.spkLeakRedU (fun _ => 1) (fun _ => 0)
      (q + 1) (q + 1) (ratchetCostBudget q qep) ∧
    (∀ k : ℕ, k < spkSwapHybridCount →
      GRedBounded (R.hop2PrgRedK k) Empty.elim (fun _ => 0)
        q 0 (ratchetCostBudget q qep)) ∧
    (∀ k : ℕ, k < spkSwapHybridCount →
      GRedBounded (R.hop2PrfRedK k) (fun _ => 1) (fun _ => 0)
        q (2 * q) (ratchetCostBudget q qep)) :=
  ⟨gRedBounded_mono h.1 (Nat.le_refl _) (spkHopBudget_le_ratchet q qep ℓ),
   gRedBounded_mono h.2.1 (Nat.le_refl _) (spkLeakRedUBudget_le_ratchet q qep),
   fun k hk => gRedBounded_mono (h.2.2.1 k hk) (Nat.le_refl _) (spkHopBudget_le_ratchet q qep ℓ),
   fun k hk => gRedBounded_mono (h.2.2.2 k hk) (hop2PrfRedK_queryBudget_le_old q)
     (spkHopBudget_le_ratchet q qep ℓ)⟩

theorem spkCostedRedsInst_bounds {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (q qep : ℕ)
    (hqep : qep ≤ q + 10) :
    spkCostedBounds q qep
      (spkCostedRedsInst ℓ C K idA idB Dh encPt encT decT lam q qep) :=
  mkSpkCostedReds_bounds ℓ C K idA idB Dh encPt encT decT lam q qep hqep

/-! ## Evaluation bridges -/

theorem spkCostedRedsInst_evalSpkLeakRed
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (q qep : ℕ)
    (s : BitVec 256)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    evalSpkLeakRed
        (spkCostedRedsInst ℓ C K idA idB Dh encPt encT decT lam q qep).spkLeakRed s A =
      spkLeakRed
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
        Dh encPt encT decT qep s A :=
  mkSpkCostedReds_evalSpkLeakRed ℓ C K idA idB Dh encPt encT decT lam q qep s A hq hℓ

theorem spkCostedRedsInst_evalSpkLeakRedU
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (q qep : ℕ)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    evalSpkLeakRedU
        (spkCostedRedsInst ℓ C K idA idB Dh encPt encT decT lam q qep).spkLeakRedU
        (fun x =>
          evalSpkLeakRed
            (spkCostedRedsInst ℓ C K idA idB Dh encPt encT decT lam q qep).spkLeakRed
            x A) =
      spkLeakRedU spkLeakRed
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
        Dh encPt encT decT qep A :=
  mkSpkCostedReds_evalSpkLeakRedU ℓ C K idA idB Dh encPt encT decT lam q qep A hq hℓ

theorem spkCostedRedsInst_evalHop2PrgRedK_of_dec
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (q qep : ℕ)
    (s : BitVec 256) (k : ℕ)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hdec : ∀ T, decT (encT T) = some T)
    (hk : k < spkSwapHybridCount) (hq : MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    evalSpkSwapPrgHybrid
        ((spkCostedRedsInst ℓ C K idA idB Dh encPt encT decT lam q qep).hop2PrgRedK k)
        s A =
      hop2PrgRedK
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
        ℓ Dh encPt encT decT qep s k A :=
  mkSpkCostedReds_evalHop2PrgRedK_of_dec ℓ C K idA idB Dh encPt encT decT lam q qep s k A hdec hk hq hℓ

theorem spkCostedRedsInst_evalHop2PrfRedK_of_dec
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (q qep : ℕ)
    (s : BitVec 256) (k : ℕ)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hdec : ∀ T, decT (encT T) = some T)
    (hk : k < spkSwapHybridCount) (hq : MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    evalSpkSwapPrfHybrid
        ((spkCostedRedsInst ℓ C K idA idB Dh encPt encT decT lam q qep).hop2PrfRedK k)
        s A =
      hop2PrfRedK
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
        ℓ Dh encT decT qep s k A :=
  mkSpkCostedReds_evalHop2PrfRedK_of_dec ℓ C K idA idB Dh encPt encT decT lam q qep s k A hdec hk hq hℓ

theorem spkCostedRedsInst_evalHop2PrgRedK
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (q qep : ℕ)
    (s : BitVec 256) (k : ℕ)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hdec : ∀ T, decT (encT T) = some T)
    (hk : k < spkSwapHybridCount) (hq : MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    evalSpkSwapPrgHybrid
        ((spkCostedRedsInst ℓ C K idA idB Dh encPt encT decT lam q qep).hop2PrgRedK k)
        s A =
      hop2PrgRedK
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
        ℓ Dh encPt encT decT qep s k A :=
  spkCostedRedsInst_evalHop2PrgRedK_of_dec ℓ C K idA idB Dh encPt encT decT lam q qep s k A hdec hk hq hℓ

theorem spkCostedRedsInst_evalHop2PrfRedK
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (q qep : ℕ)
    (s : BitVec 256) (k : ℕ)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hdec : ∀ T, decT (encT T) = some T)
    (hk : k < spkSwapHybridCount) (hq : MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    evalSpkSwapPrfHybrid
        ((spkCostedRedsInst ℓ C K idA idB Dh encPt encT decT lam q qep).hop2PrfRedK k)
        s A =
      hop2PrfRedK
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
        ℓ Dh encT decT qep s k A :=
  spkCostedRedsInst_evalHop2PrfRedK_of_dec ℓ C K idA idB Dh encPt encT decT lam q qep s k A hdec hk hq hℓ

/-! ## Costed SPK mixture advantage rewrites -/

/-- The leaked-SPK Hop-1, Hop-3, and Hop-2 mixture advantage terms evaluated on a per-context
family `Rspk` of `SpkCostedReds` witnesses. -/
noncomputable def spkMixCostedTerm {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {α : Type} (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    (q : ℕ) (oa : ProbComp α) (s : α → BitVec 256)
    (Rspk : α → SpkCostedReds Pt ℓ C K Dh encPt encT decT lam)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) : ℝ≥0∞ :=
  2 * (extractPRF C.F encPt).prfAdvantage
      (prefixPrfAvg oa (fun o =>
        evalSpkLeakRed (Rspk o).spkLeakRed (s o) (A o)))
    + 2 * (extractPRF C.F encPt).prfAdvantage
      (prefixPrfAvg oa (fun o =>
        evalSpkLeakRedU (Rspk o).spkLeakRedU
          (fun x => evalSpkLeakRed (Rspk o).spkLeakRed x (A o))))
    + 2 * (epoch0ChainForgeryTerm C.F q
        + (∑ j ∈ Finset.range spkSwapHybridCount,
            ((expandPRG C.F).prgAdvantage
                (prefixPrgAvg oa (fun o =>
                  evalSpkSwapPrgHybrid ((Rspk o).hop2PrgRedK j) (s o) (A o)))
              + (extractPRF C.F encPt).prfAdvantage
                (prefixPrfAvg oa (fun o =>
                  evalSpkSwapPrfHybrid ((Rspk o).hop2PrfRedK j) (s o) (A o)))))
        + hop2CreateCollTerm Dh q + spkSwapSpuriousStepTerm C.F q
        + spkSwapCreationPointHitTerm Dh q + spkSwapHiddenScalarGuessTerm Dh q)

theorem spkMixCostedTerm_eq_signed_of_dec
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {α : Type}
    (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ)
    (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256)
    (Rspk : α → SpkCostedReds Pt ℓ C K Dh encPt encT decT lam)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hdec : ∀ T, decT (encT T) = some T)
    (hℓ : ℓ < 10 ^ 6)
    (hq : ∀ o ∈ support oa, MakesAtMostQueries (A o) q)
    (hspk : ∀ o ∈ support oa,
      Rspk o = spkCostedRedsInst ℓ C K (ida o) (idb o) Dh encPt encT decT lam q qep) :
    let spqr := spqrV1SessionUniformCoins C.F K
    spkMixCostedTerm ℓ C K Dh encPt (encT := encT) (decT := decT) (lam := lam) q oa s Rspk A =
      2 * (extractPRF C.F encPt).prfAdvantage
          (leakAvgWithSpqr C spqr Dh encPt encT decT qep oa ida idb s A)
        + 2 * (extractPRF C.F encPt).prfAdvantage
          (leakUAvgWithSpqr C spqr Dh encPt encT decT qep oa ida idb A)
        + 2 * hop2TermAvgWithSpqr C spqr ℓ Dh encPt encT decT qep q oa ida idb s A := by
  set spqr := spqrV1SessionUniformCoins C.F K
  have hl1 :
      (extractPRF C.F encPt).prfAdvantage
        (prefixPrfAvg oa (fun o => evalSpkLeakRed (Rspk o).spkLeakRed (s o) (A o))) =
      (extractPRF C.F encPt).prfAdvantage
        (leakAvgWithSpqr C spqr Dh encPt encT decT qep oa ida idb s A) :=
    prfAdvantage_prfAvg_congr_of_support' (extractPRF C.F encPt) oa _ _
      fun o ho => by
        rw [hspk o ho]
        exact spkCostedRedsInst_evalSpkLeakRed
          ℓ C K (ida o) (idb o) Dh encPt encT decT lam q qep (s o) (A o) (hq o ho) hℓ
  have hl2 :
      (extractPRF C.F encPt).prfAdvantage
        (prefixPrfAvg oa (fun o =>
          evalSpkLeakRedU (Rspk o).spkLeakRedU
            (fun x => evalSpkLeakRed (Rspk o).spkLeakRed x (A o)))) =
      (extractPRF C.F encPt).prfAdvantage
        (leakUAvgWithSpqr C spqr Dh encPt encT decT qep oa ida idb A) :=
    prfAdvantage_prfAvg_congr_of_support' (extractPRF C.F encPt) oa _ _
      fun o ho => by
        rw [hspk o ho]
        exact spkCostedRedsInst_evalSpkLeakRedU
          ℓ C K (ida o) (idb o) Dh encPt encT decT lam q qep (A o) (hq o ho) hℓ
  have hsum :
      (∑ j ∈ Finset.range spkSwapHybridCount,
        ((expandPRG C.F).prgAdvantage
            (prefixPrgAvg oa (fun o =>
              evalSpkSwapPrgHybrid ((Rspk o).hop2PrgRedK j) (s o) (A o)))
          + (extractPRF C.F encPt).prfAdvantage
            (prefixPrfAvg oa (fun o =>
              evalSpkSwapPrfHybrid ((Rspk o).hop2PrfRedK j) (s o) (A o))))) =
      (∑ j ∈ Finset.range spkSwapHybridCount,
        ((expandPRG C.F).prgAdvantage
            (hop2PrgAvgWithSpqr C spqr ℓ Dh encPt encT decT qep oa ida idb s j A)
          + (extractPRF C.F encPt).prfAdvantage
            (hop2PrfAvgWithSpqr C spqr ℓ Dh encT decT qep oa ida idb s j A))) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjk : j < spkSwapHybridCount := Finset.mem_range.mp hj
    have hprg :
        (expandPRG C.F).prgAdvantage
          (prefixPrgAvg oa (fun o =>
            evalSpkSwapPrgHybrid ((Rspk o).hop2PrgRedK j) (s o) (A o))) =
        (expandPRG C.F).prgAdvantage
          (hop2PrgAvgWithSpqr C spqr ℓ Dh encPt encT decT qep oa ida idb s j A) :=
      prgAdvantage_prgAvg_congr_of_support' (expandPRG C.F) oa _ _
        fun o ho => by
          rw [hspk o ho]
          exact spkCostedRedsInst_evalHop2PrgRedK_of_dec
            ℓ C K (ida o) (idb o) Dh encPt encT decT lam q qep (s o) j (A o) hdec hjk (hq o ho) hℓ
    have hprf :
        (extractPRF C.F encPt).prfAdvantage
          (prefixPrfAvg oa (fun o =>
            evalSpkSwapPrfHybrid ((Rspk o).hop2PrfRedK j) (s o) (A o))) =
        (extractPRF C.F encPt).prfAdvantage
          (hop2PrfAvgWithSpqr C spqr ℓ Dh encT decT qep oa ida idb s j A) :=
      prfAdvantage_prfAvg_congr_of_support' (extractPRF C.F encPt) oa _ _
        fun o ho => by
          rw [hspk o ho]
          exact spkCostedRedsInst_evalHop2PrfRedK_of_dec
            ℓ C K (ida o) (idb o) Dh encPt encT decT lam q qep (s o) j (A o) hdec hjk (hq o ho) hℓ
    rw [hprg, hprf]
  unfold spkMixCostedTerm hop2TermAvgWithSpqr
  dsimp only [spqr]
  rw [hl1, hl2, hsum]

theorem spkMixCostedTerm_eq_signed
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {α : Type}
    (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ)
    (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256)
    (Rspk : α → SpkCostedReds Pt ℓ C K Dh encPt encT decT lam)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hdec : ∀ T, decT (encT T) = some T)
    (hℓ : ℓ < 10 ^ 6)
    (hq : ∀ o ∈ support oa, MakesAtMostQueries (A o) q)
    (hspk : ∀ o ∈ support oa,
      Rspk o = spkCostedRedsInst ℓ C K (ida o) (idb o) Dh encPt encT decT lam q qep) :
    let spqr := spqrV1SessionUniformCoins C.F K
    spkMixCostedTerm ℓ C K Dh encPt (encT := encT) (decT := decT) (lam := lam) q oa s Rspk A =
      2 * (extractPRF C.F encPt).prfAdvantage
          (leakAvgWithSpqr C spqr Dh encPt encT decT qep oa ida idb s A)
        + 2 * (extractPRF C.F encPt).prfAdvantage
          (leakUAvgWithSpqr C spqr Dh encPt encT decT qep oa ida idb A)
        + 2 * hop2TermAvgWithSpqr C spqr ℓ Dh encPt encT decT qep q oa ida idb s A :=
  spkMixCostedTerm_eq_signed_of_dec ℓ C K Dh encPt encT decT lam qep q oa ida idb s Rspk A
    hdec hℓ hq hspk

/-- Decomposes `sessionAdvantageBound` into `uniformStartMixtureBound` plus the `Signed` Hop-1,
Hop-3, and Hop-2 mixture terms when `.spk` agrees with `spkCostedRedsInst`. -/
theorem sessBound_eq_signed
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {α : Type}
    (ℓ : ℕ) (D : SessionCostedReductionFamily Pt ℓ)
    (C : Crypto) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hdec : ∀ T, decT (encT T) = some T)
    (hℓ : ℓ < 10 ^ 6)
    (hq : ∀ o ∈ support oa, MakesAtMostQueries (A o) q)
    (hspk : ∀ idA idB,
      (D C K idA idB Dh encPt encT decT 0 qep q).spk =
      spkCostedRedsInst ℓ C K idA idB Dh encPt encT decT 0 q qep) :
    let spqr := spqrV1SessionUniformCoins C.F K
    let R := fun o => D C K (ida o) (idb o) Dh encPt encT decT 0 qep q
    sessionAdvantageBound ℓ D C K Dh encPt encT decT qep q δ oa ida idb s A =
      uniformStartMixtureBound C K ℓ Dh encPt encT decT 0 qep q δ oa ida idb R A
        + 2 * (extractPRF C.F encPt).prfAdvantage
            (leakAvgWithSpqr C spqr Dh encPt encT decT qep oa ida idb s A)
        + 2 * (extractPRF C.F encPt).prfAdvantage
            (leakUAvgWithSpqr C spqr Dh encPt encT decT qep oa ida idb A)
        + 2 * hop2TermAvgWithSpqr C spqr ℓ Dh encPt encT decT qep q oa ida idb s A := by
  intro spqr R
  have hterm := spkMixCostedTerm_eq_signed ℓ C K Dh encPt encT decT 0 qep q oa ida idb s
    (fun o => (R o).spk) A hdec hℓ hq (fun o _ => hspk (ida o) (idb o))
  dsimp only at hterm
  have hdef :
      sessionAdvantageBound ℓ D C K Dh encPt encT decT qep q δ oa ida idb s A =
      uniformStartMixtureBound C K ℓ Dh encPt encT decT 0 qep q δ oa ida idb R A +
        spkMixCostedTerm ℓ C K Dh encPt (encT := encT) (decT := decT) (lam := 0)
          q oa s (fun o => (R o).spk) A := by
    unfold sessionAdvantageBound spkMixCostedTerm
    dsimp only [R]
    ac_rfl
  rw [hdef, hterm]
  ac_rfl

theorem prefixFullBoundMix_generic_eq
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {α : Type}
    (ℓ : ℕ) (D : SessionCostedReductionFamily Pt ℓ)
    (C : Crypto) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256)
    (Ak : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hdec : ∀ T, decT (encT T) = some T)
    (hℓ : ℓ < 10 ^ 6)
    (hq : ∀ o ∈ support oa, MakesAtMostQueries (Ak o) q)
    (hspk : ∀ idA idB,
      (D C K idA idB Dh encPt encT decT 0 qep q).spk =
      spkCostedRedsInst ℓ C K idA idB Dh encPt encT decT 0 q qep) :
    let spqr := spqrV1SessionUniformCoins C.F K
    let R := fun o => D C K (ida o) (idb o) Dh encPt encT decT 0 qep q
    let Rspk := fun o => (R o).spk
    (uniformStartMixtureBound C K ℓ Dh encPt encT decT 0 qep q δ oa ida idb R Ak
      + 2 * (extractPRF C.F encPt).prfAdvantage
          (prefixPrfAvg oa (fun o =>
            evalSpkLeakRed (Rspk o).spkLeakRed (s o) (Ak o)))
      + 2 * (extractPRF C.F encPt).prfAdvantage
          (prefixPrfAvg oa (fun o =>
            evalSpkLeakRedU (Rspk o).spkLeakRedU
              (fun x => evalSpkLeakRed (Rspk o).spkLeakRed x (Ak o))))
      + 2 * (epoch0ChainForgeryTerm C.F q
          + (∑ j ∈ Finset.range spkSwapHybridCount,
              ((expandPRG C.F).prgAdvantage
                  (prefixPrgAvg oa (fun o =>
                    evalSpkSwapPrgHybrid ((Rspk o).hop2PrgRedK j) (s o) (Ak o)))
                + (extractPRF C.F encPt).prfAdvantage
                  (prefixPrfAvg oa (fun o =>
                    evalSpkSwapPrfHybrid ((Rspk o).hop2PrfRedK j) (s o) (Ak o)))))
          + hop2CreateCollTerm Dh q + spkSwapSpuriousStepTerm C.F q
          + spkSwapCreationPointHitTerm Dh q + spkSwapHiddenScalarGuessTerm Dh q)) =
      uniformStartMixtureBound C K ℓ Dh encPt encT decT 0 qep q δ oa ida idb R Ak
        + 2 * (extractPRF C.F encPt).prfAdvantage
            (leakAvgWithSpqr C spqr Dh encPt encT decT qep oa ida idb s Ak)
        + 2 * (extractPRF C.F encPt).prfAdvantage
            (leakUAvgWithSpqr C spqr Dh encPt encT decT qep oa ida idb Ak)
        + 2 * hop2TermAvgWithSpqr C spqr ℓ Dh encPt encT decT qep q oa ida idb s Ak :=
  sessBound_eq_signed ℓ D C K Dh encPt encT decT qep q δ oa ida idb s Ak hdec hℓ hq hspk

/-! ## Standalone costed 3-hop leaked-SPK mixture bound -/

/-- Costed 3-hop leaked-SPK mixture bias bound from `sessionSchemeFixedSpk` to `sessionSchemeU`
via `spkCostedRedsInst`. -/
theorem boolBias_mixSpkV1_costed_le
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {α : Type}
    (C : Crypto) (K : MlKem) {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh C Dh encPt encT)
    (hdec : ∀ T, decT (encT T) = some T)
    (hz : ∀ x, Dh.dh x 0 = 0)
    (lam : Pt) (qep q : ℕ)
    (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hker : ∀ o (x : BitVec 256) (P₁ P₂ : Pt),
      Dh.dh x P₁ = Dh.dh x P₂ ↔ Dh.dh (s o) P₁ = Dh.dh (s o) P₂)
    (hq : ∀ o ∈ support oa, MakesAtMostQueries (A o) q) :
    let spqr := spqrV1SessionUniformCoins C.F K
    let Rspk := fun o => spkCostedRedsInst ℓ C K (ida o) (idb o) Dh encPt encT decT lam q qep
    𝒟[oa >>= fun o =>
        gameR (sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ (s o)) 3 qep
          (configRefuseEarlyBobCorr decT encT) (A o)].boolBias ≤
      𝒟[oa >>= fun o =>
          gameR (sessionSchemeU (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ) 3 qep
            (configRefuseEarlyBobCorr decT encT) (A o)].boolBias
        + spkMixCostedTerm ℓ C K Dh encPt (encT := encT) (decT := decT) (lam := lam)
            q oa s Rspk A := by
  intro spqr Rspk
  have hSpk := boolBias_mixSpkWithSpqr_le_of_support C spqr Dh encPt encT decT
    (by omega) (fun st rq st' salt msg h =>
      Nat.lt_of_le_of_lt (spqrV1Send_msg_len_le C.F K st rq st' salt msg h) (by decide))
    hDh hX hdec hz qep q oa ida idb s A hker hq
  have hCosted := spkMixCostedTerm_eq_signed_of_dec ℓ C K Dh encPt encT decT lam qep q oa ida idb s
    Rspk A hdec hℓ hq (fun _ _ => rfl)
  refine hSpk.trans_eq ?_
  rw [hCosted]
  dsimp only [spqr]
  ac_rfl

end Computational.Proofs.E2E.SpkCostedAndHeadlineSlice

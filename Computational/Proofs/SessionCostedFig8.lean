/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.SessionShort
public import Computational.Proofs.CryptoGames.Ratchet.LibsignalSessionStatements
public import Computational.Proofs.ReductionDsl.SM.RedCKA
public import Computational.Proofs.ReductionDsl.SM.RedFS
public import Computational.Proofs.ReductionDsl.SM.RedPRNG
public import Computational.Proofs.ReductionDsl.SM.Theorem1
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalBound
public import Computational.Proofs.ReductionDsl.Fig8SourceCosts
public import Computational.Proofs.SessionCostedFig8.QuerySubsumes
public import Computational.Proofs.SessionCostedFig8.Bundles
public import Computational.Proofs.SessionCostedFig8.ProgBounds
public import Computational.Proofs.SessionCostedFig8.FsAtomicBSwap
public import Computational.Proofs.SessionCostedFig8.BundlesEval
public import Computational.Proofs.E2E.SignedPrims
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.PrivRedQueries
import Computational.Proofs.CryptoGames.SM.Theorem1
import Computational.Proofs.SessionCostedBase
import Computational.Proofs.SignalWireRoundTrip
import Computational.Proofs.SignalWireShortProto
import Computational.Proofs.ReductionDsl.AtomicTablesHonest
import Computational.Proofs.GameHop.ReductionDsl.CostUB
import Computational.Proofs.E2E.SignedCoin

/-!
# Costed Figure 8 Reduction Bundle and Advantage Bridges

Instantiates the atomic `Fig8CostedReds` bundle `fig8RedsInst` with `fig8CostedBounds` and bridges
its single-instance and mixture (`advAvg`) advantages to `fig8ShortBoundWith`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalSession

open OracleComp OracleSpec CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst
  LibsignalSession LibsignalProtoCodec HMAC HKDF CBC LibsignalAead SM SM.Construction SM.Engine
  CKA AEADScheme MACScheme WireAEAD FSAEAD ReductionDsl ENNReal MeasureTheory
open Computational.Proofs.GameHop.ReductionDsl.CostUB
open Computational.Proofs.ReductionDsl.PureAuxMacroLift (CoinSimEquiv
  ckaAdvantage_congr prngAdvantage_congr fsaeadGame_evalDistEq_of_coinSimEquiv)
open Computational.Proofs.ReductionDsl.Fig8Atomic (dhSchemeFb atomicShortPubB
  atomicShortPubB_imp_shortB fsAtomicB fsAtomicB_send_eq)
open CryptoVerification.LibsignalSession.Fig8SchemeBridge (ckaBranch_dhSchemeFb_eq)
open CryptoVerification.E2E.Signed (advAvg ckaBranch_avg prngBranch_avg boolBias_mix_coin)
open Computational.Proofs.SessionCostedFig8
open Computational.Proofs.SessionCostedFig8.QuerySubsumes
open CryptoGames.LibsignalSM.Proofs.RestrictedReds (SafePost validQ_unequalPubChall validQ_offClass
  safePost_redFSAuth safePost_redFSPriv safePost_redFSPrivCoin challSim_equalPub
  privRedB_equalPub_local)
open CryptoGames.LibsignalSM.Proofs.SessionShort

export Computational.Proofs.ReductionDsl.Fig8SourceCosts (v0_cost v1_cost v2_cost v3_cost
  v4_cost v5_cost v6_cost v7_cost bits_succ_le bits_le_bits_qep_add HooksCostBounded
  fig8_poly_le_ratchetCostBudget add_mul_le_ratchetCostBudget)

abbrev fig8StepBound (q qep : ℕ) : ℕ :=
  let L := q + 1
  let B := (q + 1) * (maxForwardJumps + 1)
  2000 * (L * L) + 2700 * L + L * (3 * ReductionDsl.bits qep + 60) + 3 * B +
    200 * ReductionDsl.bits qep + 350000

section Fig8Costed

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

local instance : Inhabited Pt := ⟨0⟩

omit [Zero Pt] [SampleableType Pt] in
lemma fig8C_heqCt :
    (fun x1 x2 : LibsignalSim.Fig8C Pt => x1 == x2) =
    @BEq.beq (LibsignalSim.Fig8C Pt) instBEqOfDecidableEq := by
  funext x1 x2
  exact Bool.eq_iff_iff.mpr (beq_iff_eq.trans decide_eq_true_iff.symm)

omit [Zero Pt] [SampleableType Pt] in
/-- Well-formedness hypotheses on an FS-AEAD reduction `R` required by `lFS_full_bound_short_proto`. -/
def FsOk (ℓ : ℕ) (qR qd : ℕ)
    (R : FSAEAD.RatchetAdversary (BitVec 256) (BitVec 256) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      LibsignalCiphertextWithSalt32) : Prop :=
  FSAEAD.MakesAtMostQueries R qR ∧ FSAEAD.MakesAtMostDecQueries R qd ∧
    FSAEAD.EqualPubChallenges R ∧
    FSAEAD.AllQueriesInOneADClass (fun h : Header Pt => h.1) R ∧
    FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB) R ∧
    GuardedFSInjectShort R

omit [Zero Pt] [SampleableType Pt] in
theorem fs_le_fsShortBound (C : LibsignalSession.Crypto) (hD : ∀ k x, C.D k (C.E k x) = x)
    (codec : SignalMessageProtoCodec) (hc : codec = protoSignalCodec) (ℓ : ℕ) (hℓ : ℓ + 16 < 2 ^ 31 + 16)
    (encT : Pt → PublicKey) (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idOf : Party → IdentityKey) (qR qd : ℕ) (hq32 : qR + 25002 < 2 ^ 32)
    (R : FSAEAD.RatchetAdversary (BitVec 256) (BitVec 256) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      LibsignalCiphertextWithSalt32) (hR : FsOk ℓ qR qd R) :
    FSAEAD.advantage (lFS C codec ℓ encT idOf 25000) R ≤
      fsShortBound C codec ℓ encT idOf qR qd R := by
  obtain ⟨hq, hqd, heq, hcls, hshort, hinj_short⟩ := hR
  exact lFS_full_bound_short_proto C hD codec hc ℓ hℓ encT hinj hdum idOf 25000 le_rfl
    R qR qd hq hqd hq32 heq hcls hshort hinj_short

theorem fig8Reds_fsOk_of_eval (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : LibsignalSession.Crypto) (codec : SignalMessageProtoCodec)
    (hc : codec = protoSignalCodec) (ℓ : ℕ) (hℓ : ℓ + 16 < 2 ^ 31 + 16)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (R : Fig8CostedReds Dh encPt C codec ℓ encT idOf lam)
    (B_adv : Fig8Adv Pt ℓ) (hqB : SM.MakesAtMostQueries B_adv q)
    (hshB : LibsignalSM.Proofs.SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB) B_adv)
    (hgB : LibsignalSM.Proofs.SessionShort.GuardedSMShort B_adv)
    (hChall : R.challSim.eval (fun _ => B_adv) () = SM.Thm1.challSim (2 + 1) qep B_adv)
    (hPriv : ∀ i, (R.privRedB i).eval (fun _ => B_adv) () =
      SM.ThmB.privRedB (2 + 1) qep i (lBlank ℓ) B_adv)
    (hFSAuth : ∀ j tL t (A : Fig8Adv Pt ℓ), SM.MakesAtMostQueries A q →
      (R.redFSAuth j tL t).eval (fun _ => A) () =
        SM.Construction.redFSAuth (dhScheme Dh) (rootPRNG C.F encPt)
          (SM.Construction.fsClamp ((q + 1) * (maxForwardJumps + 1))
            (lFS C codec ℓ encT idOf maxForwardJumps)) lam 1 qep j tL t A)
    (hFSPriv : ∀ tL i (A : Fig8Adv Pt ℓ), SM.MakesAtMostQueries A q →
      (R.redFSPriv tL i).eval (fun _ => A) () =
        SM.Construction.redFSPriv (dhScheme Dh) (rootPRNG C.F encPt)
          (SM.Construction.fsClamp ((q + 1) * (maxForwardJumps + 1))
            (lFS C codec ℓ encT idOf maxForwardJumps)) lam 1 qep tL i A)
    (hFSPrivCoin : ∀ tL i (A : Fig8Adv Pt ℓ), SM.MakesAtMostQueries A q →
      (R.redFSPrivCoin tL i).eval (fun _ => A) () =
        SM.Construction.redFSPrivCoin (dhScheme Dh) (rootPRNG C.F encPt)
          (SM.Construction.fsClamp ((q + 1) * (maxForwardJumps + 1))
            (lFS C codec ℓ encT idOf maxForwardJumps)) lam 1 qep tL i A) :
    let challAdv := R.challSim.eval (fun _ => B_adv) ()
    (∀ j tL t, FsOk ℓ (2 * q) q ((R.redFSAuth j tL t).eval (fun _ => challAdv) ())) ∧
    (∀ i,
      let privAdv := (R.privRedB i).eval (fun _ => B_adv) ()
      (∀ tL, FsOk ℓ (2 * q) q ((R.redFSPriv tL i).eval (fun _ => privAdv) ())) ∧
      (∀ tL, FsOk ℓ (2 * q) q ((R.redFSPrivCoin tL i).eval (fun _ => privAdv) ()))) := by
  intro challAdv
  have hqChall := SM.Thm1.challSim_queries (2 + 1) qep B_adv q hqB
  have heqChall := challSim_equalPub (2 + 1) qep (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1) B_adv
  have hshChall : FSAEADRed.SendMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB)
      (SM.Thm1.challSim (2 + 1) qep B_adv) :=
    LibsignalSM.Proofs.QueryBounds.isQueryBoundP_congr
      (by rintro (_ | ((((_ | _) | _) | _) | _)) <;> rfl)
      (challSim_sendOk (2 + 1) qep (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB) B_adv hshB)
  have hgChall := challSim_guardedSMShort (2 + 1) qep B_adv hgB
  let cka := dhScheme Dh; let prng := rootPRNG C.F encPt
  let fs' := SM.Construction.fsClamp ((q + 1) * (maxForwardJumps + 1))
    (lFS C codec ℓ encT idOf maxForwardJumps)
  have hfsShort : FSAEADRed.FsSendShort (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB) fs' :=
    FSAEADRed.lFS_fsSendShort C codec (hc ▸ signalEncodeFits32_proto) ℓ hℓ encT idOf maxForwardJumps
  refine ⟨fun j tL t => ?_, fun i => ?_⟩
  · dsimp only [challAdv]; rw [hChall, hFSAuth j tL t _ hqChall]
    exact ⟨SM.Construction.redFSAuth_queries cka prng fs' lam 1 qep j tL t _ hqChall,
      SM.Construction.redFSAuth_dec_queries cka prng fs' lam 1 qep j tL t _ hqChall,
      SafePost.to_isQueryBoundP (safePost_redFSAuth cka prng fs' lam 1 qep j tL t
        (validQ_unequalPubChall ⟨true, tL, t⟩) _ heqChall),
      ⟨t, SafePost.to_isQueryBoundP (safePost_redFSAuth cka prng fs' lam 1 qep j tL t
        (validQ_offClass ⟨true, tL, t⟩ (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1)) _ heqChall)⟩,
      SafePost.to_isQueryBoundP (FSAEADRed.safePost_redFSAuth cka prng fs' lam 1 qep j tL t
        (FSAEADRed.validQ_encBadMsg ⟨true, tL, t⟩ (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB))
        _ hshChall),
      FSAEADRed.guardedFSInjectShort_redFSAuth cka prng fs' hfsShort lam 1 qep j tL t _ hshChall hgChall⟩
  · intro privAdv
    have hqPriv := LibsignalSM.Proofs.PrivRedQueries.privRedB_queries (2 + 1) qep i (lBlank ℓ) B_adv q hqB
    have heqPriv := privRedB_equalPub_local (2 + 1) qep i
      (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1) (lBlank ℓ) (fun _ => rfl) B_adv
    have hshPriv : FSAEADRed.SendMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB)
        (SM.ThmB.privRedB (2 + 1) qep i (lBlank ℓ) B_adv) :=
      LibsignalSM.Proofs.QueryBounds.isQueryBoundP_congr
        (by rintro (_ | ((((_ | _) | _) | _) | _)) <;> rfl)
        (privRedB_sendOk (2 + 1) qep i (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB)
          (lBlank ℓ) (fun _ => rfl) B_adv hshB)
    have hgPriv := privRedB_guardedSMShort (2 + 1) qep i (lBlank ℓ) B_adv hgB
    refine ⟨fun tL => ?_, fun tL => ?_⟩
    · dsimp only [privAdv]; rw [hPriv i, hFSPriv tL i _ hqPriv]
      exact ⟨SM.Construction.redFSPriv_queries cka prng fs' lam 1 qep tL i _ hqPriv,
        SM.Construction.redFSPriv_dec_queries cka prng fs' lam 1 qep tL i _ hqPriv,
        SafePost.to_isQueryBoundP (safePost_redFSPriv cka prng fs' lam 1 qep tL i
          (validQ_unequalPubChall ⟨false, tL, i⟩) _ heqPriv),
        ⟨i, SafePost.to_isQueryBoundP (safePost_redFSPriv cka prng fs' lam 1 qep tL i
          (validQ_offClass ⟨false, tL, i⟩ (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1)) _ heqPriv)⟩,
        SafePost.to_isQueryBoundP (FSAEADRed.safePost_redFSPriv cka prng fs' lam 1 qep tL i
          (FSAEADRed.validQ_encBadMsg ⟨false, tL, i⟩ (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB))
          _ hshPriv),
        FSAEADRed.guardedFSInjectShort_redFSPriv cka prng fs' hfsShort lam 1 qep tL i _ hshPriv hgPriv⟩
    · dsimp only [privAdv]; rw [hPriv i, hFSPrivCoin tL i _ hqPriv]
      exact ⟨SM.Construction.redFSPrivCoin_queries cka prng fs' lam 1 qep tL i _ hqPriv,
        SM.Construction.redFSPrivCoin_dec_queries cka prng fs' lam 1 qep tL i _ hqPriv,
        SafePost.to_isQueryBoundP (safePost_redFSPrivCoin cka prng fs' lam 1 qep tL i
          (validQ_unequalPubChall ⟨false, tL, i⟩) _ heqPriv),
        ⟨i, SafePost.to_isQueryBoundP (safePost_redFSPrivCoin cka prng fs' lam 1 qep tL i
          (validQ_offClass ⟨false, tL, i⟩ (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1)) _ heqPriv)⟩,
        SafePost.to_isQueryBoundP (FSAEADRed.safePost_redFSPrivCoin cka prng fs' lam 1 qep tL i
          (FSAEADRed.validQ_encBadMsg ⟨false, tL, i⟩ (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB))
          _ hshPriv),
        FSAEADRed.guardedFSInjectShort_redFSPrivCoin cka prng fs' hfsShort lam 1 qep tL i _ hshPriv hgPriv⟩

theorem fig8H1Bound_le_fig8ShortBoundWith_of_eval (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : LibsignalSession.Crypto)
    (hD : ∀ k x, C.D k (C.E k x) = x) (codec : SignalMessageProtoCodec)
    (hc : codec = protoSignalCodec) (ℓ : ℕ) (hℓ : ℓ + 16 < 2 ^ 31 + 16)
    (encT : Pt → PublicKey) (hinj : Function.Injective encT)
    (hdum : ∀ T, encT T ≠ dummyKey) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (hq32 : 2 * q + 25002 < 2 ^ 32)
    (R : Fig8CostedReds Dh encPt C codec ℓ encT idOf lam) (Rfs : FsCostedReds C codec ℓ encT idOf)
    (hFs : ∀ (A : FsAdv Pt ℓ), FsOk ℓ (min (2 * q) (q + 2)) q A →
      fsShortBound C codec ℓ encT idOf (min (2 * q) (q + 2)) q A ≤
        fsShortBoundWith C codec ℓ (min (2 * q) (q + 2)) q Rfs A)
    (B_adv : Fig8Adv Pt ℓ) (hqB : SM.MakesAtMostQueries B_adv q)
    (hChall : R.challSim.eval (fun _ => B_adv) () = SM.Thm1.challSim (2 + 1) qep B_adv)
    (hPriv : ∀ i, (R.privRedB i).eval (fun _ => B_adv) () =
      SM.ThmB.privRedB (2 + 1) qep i (lBlank ℓ) B_adv)
    (hAuthOk : ∀ j tL t,
      FsOk ℓ (min (2 * q) (q + 2)) q
        ((R.redFSAuth j tL t).eval (fun _ => R.challSim.eval (fun _ => B_adv) ()) ()))
    (hPrivOk : ∀ i,
      (∀ tL, FsOk ℓ (min (2 * q) (q + 2)) q
        ((R.redFSPriv tL i).eval (fun _ => (R.privRedB i).eval (fun _ => B_adv) ()) ())) ∧
      (∀ tL, FsOk ℓ (min (2 * q) (q + 2)) q
        ((R.redFSPrivCoin tL i).eval (fun _ => (R.privRedB i).eval (fun _ => B_adv) ()) ())))
    (hCKAAuth : ∀ tL t (A : Fig8Adv Pt ℓ), SM.MakesAtMostQueries A q →
      (R.redCKAAuth tL t).eval (fun _ => A) () =
        SM.Construction.redCKAAuth (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C codec ℓ encT idOf maxForwardJumps) lam 1 qep tL t A)
    (hPRNGAuth : ∀ tL t (A : Fig8Adv Pt ℓ), SM.MakesAtMostQueries A q →
      PRFPRNG.advantage (rootPRNG C.F encPt) ((R.redPRNGAuth tL t).eval (fun _ => A) ()) =
        PRFPRNG.advantage (rootPRNG C.F encPt)
          (SM.Construction.redPRNGAuth (dhScheme Dh) (rootPRNG C.F encPt)
            (lFS C codec ℓ encT idOf maxForwardJumps) lam 1 qep tL t A))
    (hFSAuthAdv : ∀ j tL t (A : Fig8Adv Pt ℓ), SM.MakesAtMostQueries A q →
      FSAEAD.advantage (lFS C codec ℓ encT idOf maxForwardJumps)
        ((R.redFSAuth j tL t).eval (fun _ => A) ()) =
      FSAEAD.advantage (lFS C codec ℓ encT idOf maxForwardJumps)
        (SM.Construction.redFSAuth (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C codec ℓ encT idOf maxForwardJumps) lam 1 qep j tL t A))
    (hCKAPriv : ∀ tL i (A : Fig8Adv Pt ℓ), SM.MakesAtMostQueries A q →
      (R.redCKAPriv tL i).eval (fun _ => A) () =
        SM.Construction.redCKAPriv (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C codec ℓ encT idOf maxForwardJumps) lam 1 qep tL i A)
    (hPRNGPriv : ∀ tL i (A : Fig8Adv Pt ℓ), SM.MakesAtMostQueries A q →
      PRFPRNG.advantage (rootPRNG C.F encPt) ((R.redPRNGPriv tL i).eval (fun _ => A) ()) =
        PRFPRNG.advantage (rootPRNG C.F encPt)
          (SM.Construction.redPRNGPriv (dhScheme Dh) (rootPRNG C.F encPt)
            (lFS C codec ℓ encT idOf maxForwardJumps) lam 1 qep tL i A))
    (hFSPrivAdv : ∀ tL i (A : Fig8Adv Pt ℓ), SM.MakesAtMostQueries A q →
      FSAEAD.advantage (lFS C codec ℓ encT idOf maxForwardJumps)
        ((R.redFSPriv tL i).eval (fun _ => A) ()) =
      FSAEAD.advantage (lFS C codec ℓ encT idOf maxForwardJumps)
        (SM.Construction.redFSPriv (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C codec ℓ encT idOf maxForwardJumps) lam 1 qep tL i A))
    (hFSPrivCoinAdv : ∀ tL i (A : Fig8Adv Pt ℓ), SM.MakesAtMostQueries A q →
      FSAEAD.advantage (lFS C codec ℓ encT idOf maxForwardJumps)
        ((R.redFSPrivCoin tL i).eval (fun _ => A) ()) =
      FSAEAD.advantage (lFS C codec ℓ encT idOf maxForwardJumps)
        (SM.Construction.redFSPrivCoin (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C codec ℓ encT idOf maxForwardJumps) lam 1 qep tL i A)) :
    fig8H1Bound Dh encPt C codec ℓ encT idOf lam qep q B_adv ≤
      fig8ShortBoundWith Dh encPt C codec ℓ encT idOf lam qep q R Rfs B_adv := by
  have hqChall : SM.MakesAtMostQueries (R.challSim.eval (fun _ => B_adv) ()) q := by
    rw [hChall]; exact SM.Thm1.challSim_queries (2 + 1) qep B_adv q hqB
  have hqPriv : ∀ i, SM.MakesAtMostQueries ((R.privRedB i).eval (fun _ => B_adv) ()) q := fun i => by
    rw [hPriv i]; exact LibsignalSM.Proofs.PrivRedQueries.privRedB_queries (2 + 1) qep i (lBlank ℓ) B_adv q hqB
  have h25k : (25000 : ℕ) = maxForwardJumps := rfl
  unfold fig8H1Bound fig8ShortBoundWith; dsimp only; simp only [h25k, ← hChall, ← hPriv]
  gcongr with t _ tL _ j _ i _ tL _
  · rw [hCKAAuth tL t _ hqChall]
  · rw [hPRNGAuth tL t _ hqChall]
  · rw [← hFSAuthAdv j tL t _ hqChall]
    exact (fs_le_fsShortBound C hD codec hc ℓ hℓ encT hinj hdum idOf (min (2 * q) (q + 2)) q
      (by omega) _ (hAuthOk j tL t)).trans (hFs _ (hAuthOk j tL t))
  · rw [hCKAPriv tL i _ (hqPriv i)]
  · rw [hPRNGPriv tL i _ (hqPriv i)]
  · rw [← hFSPrivAdv tL i _ (hqPriv i)]
    exact (fs_le_fsShortBound C hD codec hc ℓ hℓ encT hinj hdum idOf (min (2 * q) (q + 2)) q
      (by omega) _ ((hPrivOk i).1 tL)).trans (hFs _ ((hPrivOk i).1 tL))
  · rw [← hFSPrivCoinAdv tL i _ (hqPriv i)]
    exact (fs_le_fsShortBound C hD codec hc ℓ hℓ encT hinj hdum idOf (min (2 * q) (q + 2)) q
      (by omega) _ ((hPrivOk i).2 tL)).trans (hFs _ ((hPrivOk i).2 tL))

def fig8CostedRedsBoundedWitness (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : LibsignalSession.Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) :
    Fig8CostedReds Dh encPt C codec ℓ encT idOf lam where
  challSim := { σ := .unit, init := .ret (.pair .unit .unit), handle := .ret (.pair (.inl .none) .unit), finish := .ret (.bool false) }
  privRedB _ := { σ := .unit, init := .ret (.pair .unit .unit), handle := .ret (.pair (.inl .none) .unit), finish := .ret (.bool false) }
  redCKAAuth _ _ := { σ := .unit, init := .ret (.pair .unit .unit), handle := .ret (.pair (.inl .none) .unit), finish := .ret (.bool false) }
  redPRNGAuth _ _ := { σ := .unit, init := .ret (.pair .unit .unit), handle := .ret (.pair (.inl .none) .unit), finish := .ret (.bool false) }
  redFSAuth _ _ _ := { σ := .unit, init := .ret (.pair .unit .unit), handle := .ret (.pair (.inl .none) .unit), finish := .ret (.bool false) }
  redCKAPriv _ _ := { σ := .unit, init := .ret (.pair .unit .unit), handle := .ret (.pair (.inl .none) .unit), finish := .ret (.bool false) }
  redPRNGPriv _ _ := { σ := .unit, init := .ret (.pair .unit .unit), handle := .ret (.pair (.inl .none) .unit), finish := .ret (.bool false) }
  redFSPriv _ _ := { σ := .unit, init := .ret (.pair .unit .unit), handle := .ret (.pair (.inl .none) .unit), finish := .ret (.bool false) }
  redFSPrivCoin _ _ := { σ := .unit, init := .ret (.pair .unit .unit), handle := .ret (.pair (.inl .none) .unit), finish := .ret (.bool false) }

private theorem pureRetRed_isQueryBoundP
    {S : Sig} {O : Ops S} {ι κ : Type} {T₀ : OracleSpec.{0, 0} ι}
    {I : Iface S (unifSpec + T₀)} {G : OracleSpec.{0, 0} κ} {C : _root_.ReductionDsl.GameCodec S G}
    {rIn aIn aOut out σ : Ty S} (initE : Expr O [rIn] (.prod aIn σ))
    (handleE : Expr O [σ, C.Q] (.prod C.R σ)) (finishE : Expr O [σ, aOut] out)
    {P : (unifSpec + T₀).Domain → Prop} [DecidablePred P]
    (hFwdU : ∀ n, I.fwdU n = liftM (OracleSpec.query (spec := unifSpec + T₀) (.inl n)))
    (hP : ∀ n, ¬ P (.inl n))
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote) (x : rIn.denote) (k : ℕ) :
    (({ σ := σ, init := .ret initE, handle := .ret handleE, finish := .ret finishE } :
        CostedReduction O I G C rIn aIn aOut out).eval A x).IsQueryBoundP P k := by
  let R : CostedReduction O I G C rIn aIn aOut out :=
    { σ := σ, init := .ret initE, handle := .ret handleE, finish := .ret finishE }
  suffices hSim : ∀ (oa : OracleComp (unifSpec + G) aOut.denote) (s : σ.denote),
      (((simulateQ R.impl oa).run s) >>= fun bs =>
        pure (finishE.eval (.cons bs.2 (.cons bs.1 .nil)))).IsQueryBoundP P k by
    change (R.eval A x).IsQueryBoundP P k; unfold CostedReduction.eval
    simp only [R, Comp.eval, pure_bind]
    exact hSim (A (initE.eval (.cons x .nil)).1) (initE.eval (.cons x .nil)).2
  intro oa; induction oa using OracleComp.inductionOn with
  | pure b => intro s; simp [simulateQ_pure, StateT.run_pure]
  | query_bind q mx ih =>
    intro s; rcases q with n | t
    · have hStep : ((simulateQ R.impl
          (liftM (OracleSpec.query (spec := unifSpec + G) (.inl n)) >>= mx)).run s) >>=
            (fun bs => pure (finishE.eval (.cons bs.2 (.cons bs.1 .nil)))) =
          liftM (OracleSpec.query (spec := unifSpec + T₀) (.inl n)) >>= fun u =>
            (((simulateQ R.impl (mx u)).run s) >>=
              fun bs => pure (finishE.eval (.cons bs.2 (.cons bs.1 .nil)))) := by
        simp [R, CostedReduction.impl, _root_.ReductionDsl.handlerImpl,
          StateT.run_bind, StateT.run_lift, hFwdU, map_eq_bind_pure_comp, bind_assoc]
      rw [hStep, isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (hP n), fun u => by simpa [hP n] using ih u s⟩
    · have hStep : ((simulateQ R.impl
          (liftM (OracleSpec.query (spec := unifSpec + G) (.inr t)) >>= mx)).run s) >>=
            (fun bs => pure (finishE.eval (.cons bs.2 (.cons bs.1 .nil)))) =
          (((simulateQ R.impl
              (mx (C.rdec t (handleE.eval (.cons s (.cons (C.qenc t) .nil))).1))).run
            (handleE.eval (.cons s (.cons (C.qenc t) .nil))).2) >>=
              fun bs => pure (finishE.eval (.cons bs.2 (.cons bs.1 .nil)))) := by
        simp [R, CostedReduction.impl, _root_.ReductionDsl.handlerImpl, Comp.eval,
          StateT.run_bind, StateT.run_mk, pure_bind]
      rw [hStep]; exact ih _ _

theorem fig8CostedRedsBoundedWitness_bounds (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : LibsignalSession.Crypto) (codec : SignalMessageProtoCodec)
    (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) :
    fig8CostedBounds q qep (fig8CostedRedsBoundedWitness Dh encPt C codec ℓ encT idOf lam) := by
  have hbud := ratchetCostBudget_pos q qep; have hmax37 : max 1 37 = 37 := rfl
  have hOps := ReductionDsl.atomicFig8Ops_sizeHonest ℓ Pt C Dh encPt encT lam
  have hSamp := ReductionDsl.atomicSamplers_sizeHonest ℓ Pt
  refine ⟨?_, fun _ _ => ?_, fun _ _ _ _ => ?_, fun _ _ _ _ => ?_, fun _ _ _ _ _ _ => ?_,
    fun _ _ _ _ => ?_, fun _ _ _ _ => ?_, fun _ _ _ _ => ?_, fun _ _ _ _ => ?_, ?mamq⟩
  case mamq =>
    refine ⟨fun _ _ _ _ _ _ => ?_, fun _ _ _ _ _ _ => ?_, fun _ _ _ _ _ _ => ?_,
      fun _ _ _ _ _ _ => ?_, fun _ _ _ _ _ _ _ _ => ?_, fun _ _ _ _ _ _ => ?_,
      fun _ _ _ _ _ _ => ?_⟩ <;>
    · dsimp only [fig8CostedRedsBoundedWitness]
      exact pureRetRed_isQueryBoundP _ _ _ (fun _ => rfl) (fun _ h => nomatch h) _ _ _
  all_goals
    refine gredBounded_of_bounds ?_ ?_ ?_ hOps hSamp
    · simp only [ReductionDsl.CostedReduction.totalCost, fig8CostedRedsBoundedWitness, Comp.cost,
        Expr.cost, fig8SmIface, ckaTargetIface, prngTargetIface, fsaeadHeaderIface, fig8SmCodec,
        Nat.reduceAdd, hmax37]; omega
    · simp only [CostedReduction.size, fig8CostedRedsBoundedWitness, Comp.size, Expr.size,
        reductionSizeBudget, Nat.reduceAdd]; omega
    · simp only [CostedReduction.totalQueries, fig8CostedRedsBoundedWitness, Comp.queries]; omega

end Fig8Costed

/-! ## Concrete atomic bundle and bridges -/

section ConcreteAtomicFig8

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

local instance : Inhabited Pt := ⟨0⟩

abbrev fig8RedsInst := @Bundles.fig8RedsInst

abbrev challSimDFAtomicProg := @Bundles.challSimDFAtomicProg
abbrev redCKAAuthDFAtomicProg := @Bundles.redCKAAuthDFAtomicProg
abbrev redPRNGAuthDFAtomicProg := @Bundles.redPRNGAuthDFAtomicProg
abbrev redFSAuthDFAtomicProg := @Bundles.redFSAuthDFAtomicProg

theorem fig8RedsInst_bounds (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : LibsignalSession.Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    fig8CostedBounds q qep (fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q) :=
  ProgBounds.fig8RedsInst_bounds Dh encPt C codec ℓ encT idOf lam qep q hqep

theorem fig8RedsInst_challSim_eval (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : LibsignalSession.Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (A : Fig8Adv Pt ℓ) (hqA : SM.MakesAtMostQueries A q) :
    ((fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).challSim.eval (fun _ => A) ()) =
      SM.Thm1.challSim (2 + 1) qep A :=
  BundlesEval.fig8RedsInst_challSim_eval Dh encPt C codec ℓ hℓ encT idOf lam qep q A hqA

theorem fig8RedsInst_privRedB_eval (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : LibsignalSession.Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qep q i : ℕ)
    (A : Fig8Adv Pt ℓ) (hqA : SM.MakesAtMostQueries A q) :
    (((fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).privRedB i).eval (fun _ => A) ()) =
      SM.ThmB.privRedB (2 + 1) qep i (lBlank ℓ) A :=
  BundlesEval.fig8RedsInst_privRedB_eval Dh encPt C codec ℓ hℓ encT idOf lam qep q i A hqA

omit [DecidableEq Pt] in
theorem ckaAdvantage_dhSchemeFb_eq (Dh : DHFun (BitVec 256) Pt) (Δ tStar : ℕ)
    (A : CKA.Adversary (CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt) :
    CKA.advantage (dhSchemeFb Dh) Δ tStar A = CKA.advantage (dhScheme Dh) Δ tStar A := by
  rw [CKA.advantage_eq_boolDist, CKA.advantage_eq_boolDist,
    ckaBranch_dhSchemeFb_eq Dh Δ tStar true A, ckaBranch_dhSchemeFb_eq Dh Δ tStar false A]

theorem fig8RedsInst_redCKAAuth_advantage (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : LibsignalSession.Crypto) (codec : SignalMessageProtoCodec)
    (hc : codec = protoSignalCodec) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (tStar : ℕ) (tL : Option ℕ) (t : ℕ) (A : Fig8Adv Pt ℓ) (hqA : SM.MakesAtMostQueries A q)
    (hshA : LibsignalSM.Proofs.SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    CKA.advantage (dhScheme Dh) 1 tStar
      (((fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redCKAAuth tL t).eval
        (fun _ => A) ()) =
    CKA.advantage (dhScheme Dh) 1 tStar
      (SM.Construction.redCKAAuth (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C codec ℓ encT idOf maxForwardJumps) lam 1 qep tL t A) := by
  subst hc
  rw [ckaAdvantage_congr (dhScheme Dh) 1 tStar
      (BundlesEval.fig8RedsInst_redCKAAuth_coinSimEquiv Dh encPt C protoSignalCodec
        ℓ hℓ encT idOf lam qep q tL t A hqA),
    ← ckaAdvantage_dhSchemeFb_eq]
  exact FsAtomicBSwap.ckaAdvantage_redCKAAuth_atomic_eq Dh (rootPRNG C.F encPt) C ℓ encT idOf lam
    ((q + 1) * (maxForwardJumps + 1)) q 1 tStar qep tL t (Nat.le_refl _) A q hqA (Nat.le_refl q)
    hshA

theorem fig8RedsInst_redCKAPriv_advantage (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : LibsignalSession.Crypto) (codec : SignalMessageProtoCodec)
    (hc : codec = protoSignalCodec) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (tStar : ℕ) (tL : Option ℕ) (i : ℕ) (A : Fig8Adv Pt ℓ) (hqA : SM.MakesAtMostQueries A q)
    (hshA : LibsignalSM.Proofs.SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    CKA.advantage (dhScheme Dh) 1 tStar
      (((fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redCKAPriv tL i).eval
        (fun _ => A) ()) =
    CKA.advantage (dhScheme Dh) 1 tStar
      (SM.Construction.redCKAPriv (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C codec ℓ encT idOf maxForwardJumps) lam 1 qep tL i A) := by
  subst hc
  rw [ckaAdvantage_congr (dhScheme Dh) 1 tStar
      (BundlesEval.fig8RedsInst_redCKAPriv_coinSimEquiv Dh encPt C protoSignalCodec
        ℓ hℓ encT idOf lam qep q tL i A hqA),
    ← ckaAdvantage_dhSchemeFb_eq]
  exact FsAtomicBSwap.ckaAdvantage_redCKAPriv_atomic_eq Dh (rootPRNG C.F encPt) C ℓ encT idOf lam
    ((q + 1) * (maxForwardJumps + 1)) q 1 tStar qep tL i (Nat.le_refl _) A q hqA (Nat.le_refl q)
    hshA

theorem fig8RedsInst_redPRNGAuth_advantage (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : LibsignalSession.Crypto) (codec : SignalMessageProtoCodec)
    (hc : codec = protoSignalCodec) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (tL : Option ℕ) (t : ℕ) (A : Fig8Adv Pt ℓ) (hqA : SM.MakesAtMostQueries A q)
    (hshA : LibsignalSM.Proofs.SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    PRFPRNG.advantage (rootPRNG C.F encPt)
      (((fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redPRNGAuth tL t).eval
        (fun _ => A) ()) =
    PRFPRNG.advantage (rootPRNG C.F encPt)
      (SM.Construction.redPRNGAuth (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C codec ℓ encT idOf maxForwardJumps) lam 1 qep tL t A) := by
  subst hc
  rw [prngAdvantage_congr (rootPRNG C.F encPt)
      (BundlesEval.fig8RedsInst_redPRNGAuth_prog_coinSimEquiv Dh encPt C protoSignalCodec
        ℓ hℓ encT idOf lam qep q tL t A),
    BundlesEval.redPRNGAuthProg_advantage_atomic Dh encPt C ℓ encT idOf lam qep q tL t A hqA]
  exact FsAtomicBSwap.prngAdvantage_redPRNGAuth_atomic_eq Dh (rootPRNG C.F encPt) C ℓ encT idOf lam
    ((q + 1) * (maxForwardJumps + 1)) q 1 qep tL t (Nat.le_refl _) A q hqA (Nat.le_refl q) hshA

theorem fig8RedsInst_redPRNGPriv_advantage (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : LibsignalSession.Crypto) (codec : SignalMessageProtoCodec)
    (hc : codec = protoSignalCodec) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (tL : Option ℕ) (i : ℕ) (A : Fig8Adv Pt ℓ) (hqA : SM.MakesAtMostQueries A q)
    (hshA : LibsignalSM.Proofs.SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    PRFPRNG.advantage (rootPRNG C.F encPt)
      (((fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redPRNGPriv tL i).eval
        (fun _ => A) ()) =
    PRFPRNG.advantage (rootPRNG C.F encPt)
      (SM.Construction.redPRNGPriv (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C codec ℓ encT idOf maxForwardJumps) lam 1 qep tL i A) := by
  subst hc
  rw [prngAdvantage_congr (rootPRNG C.F encPt)
      (BundlesEval.fig8RedsInst_redPRNGPriv_prog_coinSimEquiv Dh encPt C protoSignalCodec
        ℓ hℓ encT idOf lam qep q tL i A),
    BundlesEval.redPRNGPrivProg_advantage_atomic Dh encPt C ℓ encT idOf lam qep q tL i A hqA]
  exact FsAtomicBSwap.prngAdvantage_redPRNGPriv_atomic_eq Dh (rootPRNG C.F encPt) C ℓ encT idOf lam
    ((q + 1) * (maxForwardJumps + 1)) q 1 qep tL i (Nat.le_refl _) A q hqA (Nat.le_refl q) hshA

theorem fig8RedsInst_redFSAuth_game_evalDistEq (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : LibsignalSession.Crypto) (codec : SignalMessageProtoCodec)
    (hc : codec = protoSignalCodec) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (j : ℕ) (tL : Option ℕ) (t : ℕ) (A : Fig8Adv Pt ℓ) (hqA : SM.MakesAtMostQueries A q)
    (hshA : LibsignalSM.Proofs.SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    FSAEAD.game (lFS C codec ℓ encT idOf maxForwardJumps)
      (((fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redFSAuth j tL t).eval
        (fun _ => A) ()) =ᵈ
    FSAEAD.game (lFS C codec ℓ encT idOf maxForwardJumps)
      (SM.Construction.redFSAuth (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C codec ℓ encT idOf maxForwardJumps) lam 1 qep j tL t A) := by
  subst hc
  have h1 := fsaeadGame_evalDistEq_of_coinSimEquiv
    (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
    (BundlesEval.fig8RedsInst_redFSAuth_coinSimEquiv Dh encPt C protoSignalCodec
      ℓ hℓ encT idOf lam qep q j tL t A hqA)
  have h2 := FsAtomicBSwap.fsaeadGame_redFSAuth_atomic_eq Dh (rootPRNG C.F encPt) C ℓ encT idOf lam
    ((q + 1) * (maxForwardJumps + 1)) ((q + 1) * (maxForwardJumps + 1)) q 1 qep j tL t
    (Nat.le_refl _) (Nat.le_refl _) A q hqA (Nat.le_refl q) hshA
  rwa [h2] at h1

theorem fig8RedsInst_redFSAuth_advantage (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : LibsignalSession.Crypto) (codec : SignalMessageProtoCodec)
    (hc : codec = protoSignalCodec) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (j : ℕ) (tL : Option ℕ) (t : ℕ) (A : Fig8Adv Pt ℓ) (hqA : SM.MakesAtMostQueries A q)
    (hshA : LibsignalSM.Proofs.SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    FSAEAD.advantage (lFS C codec ℓ encT idOf maxForwardJumps)
      (((fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redFSAuth j tL t).eval
        (fun _ => A) ()) =
    FSAEAD.advantage (lFS C codec ℓ encT idOf maxForwardJumps)
      (SM.Construction.redFSAuth (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C codec ℓ encT idOf maxForwardJumps) lam 1 qep j tL t A) := by
  unfold FSAEAD.advantage
  rw [(fig8RedsInst_redFSAuth_game_evalDistEq Dh encPt C codec hc ℓ hℓ encT idOf lam qep q
    j tL t A hqA hshA).evalDist_eq]

theorem fig8RedsInst_redFSPriv_game_evalDistEq (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : LibsignalSession.Crypto) (codec : SignalMessageProtoCodec)
    (hc : codec = protoSignalCodec) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (tL : Option ℕ) (i : ℕ) (A : Fig8Adv Pt ℓ) (hqA : SM.MakesAtMostQueries A q)
    (hshA : LibsignalSM.Proofs.SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    FSAEAD.game (lFS C codec ℓ encT idOf maxForwardJumps)
      (((fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redFSPriv tL i).eval
        (fun _ => A) ()) =ᵈ
    FSAEAD.game (lFS C codec ℓ encT idOf maxForwardJumps)
      (SM.Construction.redFSPriv (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C codec ℓ encT idOf maxForwardJumps) lam 1 qep tL i A) := by
  subst hc
  have h1 := fsaeadGame_evalDistEq_of_coinSimEquiv
    (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
    (BundlesEval.fig8RedsInst_redFSPriv_coinSimEquiv Dh encPt C protoSignalCodec
      ℓ hℓ encT idOf lam qep q tL i A hqA)
  have h2 := FsAtomicBSwap.fsaeadGame_redFSPriv_atomic_eq Dh (rootPRNG C.F encPt) C ℓ encT idOf lam
    ((q + 1) * (maxForwardJumps + 1)) ((q + 1) * (maxForwardJumps + 1)) q 1 qep tL i
    (Nat.le_refl _) (Nat.le_refl _) A q hqA (Nat.le_refl q) hshA
  rwa [h2] at h1

theorem fig8RedsInst_redFSPriv_advantage (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : LibsignalSession.Crypto) (codec : SignalMessageProtoCodec)
    (hc : codec = protoSignalCodec) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (tL : Option ℕ) (i : ℕ) (A : Fig8Adv Pt ℓ) (hqA : SM.MakesAtMostQueries A q)
    (hshA : LibsignalSM.Proofs.SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    FSAEAD.advantage (lFS C codec ℓ encT idOf maxForwardJumps)
      (((fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redFSPriv tL i).eval
        (fun _ => A) ()) =
    FSAEAD.advantage (lFS C codec ℓ encT idOf maxForwardJumps)
      (SM.Construction.redFSPriv (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C codec ℓ encT idOf maxForwardJumps) lam 1 qep tL i A) := by
  unfold FSAEAD.advantage
  rw [(fig8RedsInst_redFSPriv_game_evalDistEq Dh encPt C codec hc ℓ hℓ encT idOf lam qep q
    tL i A hqA hshA).evalDist_eq]

theorem fig8RedsInst_redFSPrivCoin_game_evalDistEq (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : LibsignalSession.Crypto) (codec : SignalMessageProtoCodec)
    (hc : codec = protoSignalCodec) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (tL : Option ℕ) (i : ℕ) (A : Fig8Adv Pt ℓ) (hqA : SM.MakesAtMostQueries A q)
    (hshA : LibsignalSM.Proofs.SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    FSAEAD.game (lFS C codec ℓ encT idOf maxForwardJumps)
      (((fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redFSPrivCoin tL i).eval
        (fun _ => A) ()) =ᵈ
    FSAEAD.game (lFS C codec ℓ encT idOf maxForwardJumps)
      (SM.Construction.redFSPrivCoin (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C codec ℓ encT idOf maxForwardJumps) lam 1 qep tL i A) := by
  subst hc
  have h1 := fsaeadGame_evalDistEq_of_coinSimEquiv
    (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
    (BundlesEval.fig8RedsInst_redFSPrivCoin_coinSimEquiv Dh encPt C protoSignalCodec
      ℓ hℓ encT idOf lam qep q tL i A hqA)
  have h2 := FsAtomicBSwap.fsaeadGame_redFSPrivCoin_atomic_eq Dh (rootPRNG C.F encPt) C ℓ encT
    idOf lam ((q + 1) * (maxForwardJumps + 1)) ((q + 1) * (maxForwardJumps + 1)) q 1 qep tL i
    (Nat.le_refl _) (Nat.le_refl _) A q hqA (Nat.le_refl q) hshA
  rwa [h2] at h1

theorem fig8RedsInst_redFSPrivCoin_advantage (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : LibsignalSession.Crypto) (codec : SignalMessageProtoCodec)
    (hc : codec = protoSignalCodec) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (tL : Option ℕ) (i : ℕ) (A : Fig8Adv Pt ℓ) (hqA : SM.MakesAtMostQueries A q)
    (hshA : LibsignalSM.Proofs.SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    FSAEAD.advantage (lFS C codec ℓ encT idOf maxForwardJumps)
      (((fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redFSPrivCoin tL i).eval
        (fun _ => A) ()) =
    FSAEAD.advantage (lFS C codec ℓ encT idOf maxForwardJumps)
      (SM.Construction.redFSPrivCoin (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C codec ℓ encT idOf maxForwardJumps) lam 1 qep tL i A) := by
  unfold FSAEAD.advantage
  rw [(fig8RedsInst_redFSPrivCoin_game_evalDistEq Dh encPt C codec hc ℓ hℓ encT idOf lam qep q
    tL i A hqA hshA).evalDist_eq]

/-! ## Mixture advantage bridges -/

theorem fig8RedsInst_redCKAAuth_advAvg_advantage {α : Type} (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : LibsignalSession.Crypto) (codec : SignalMessageProtoCodec)
    (hc : codec = protoSignalCodec) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (oa : ProbComp α) (idOf : α → Party → IdentityKey)
    (lam : Pt) (qep q tStar : ℕ) (tL : Option ℕ) (t : ℕ) (A : α → Fig8Adv Pt ℓ)
    (hqA : ∀ o, SM.MakesAtMostQueries (A o) q)
    (hshA : ∀ o, LibsignalSM.Proofs.SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) (A o)) :
    CKA.advantage (dhScheme Dh) 1 tStar
      (advAvg oa fun o =>
        ((fig8RedsInst Dh encPt C codec ℓ encT (idOf o) lam qep q).redCKAAuth tL t).eval
          (fun _ => A o) ()) =
    CKA.advantage (dhScheme Dh) 1 tStar
      (advAvg oa fun o =>
        SM.Construction.redCKAAuth (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C codec ℓ encT (idOf o) maxForwardJumps) lam 1 qep tL t (A o)) := by
  subst hc
  rw [QuerySubsumes.ckaAdvantage_advAvg_congr (dhScheme Dh) 1 tStar oa fun o =>
      BundlesEval.fig8RedsInst_redCKAAuth_coinSimEquiv Dh encPt C protoSignalCodec
        ℓ hℓ encT (idOf o) lam qep q tL t (A o) (hqA o)]
  rw [CKA.advantage_eq_boolDist, CKA.advantage_eq_boolDist,
    ckaBranch_avg, ckaBranch_avg, ckaBranch_avg, ckaBranch_avg]
  have hBr : ∀ b,
      (oa >>= fun o => CKA.branch (dhScheme Dh) 1 tStar b
        (SM.Construction.redCKAAuth (dhSchemeFb Dh) (rootPRNG C.F encPt)
          (fsAtomicB C ℓ encT (idOf o) ((q + 1) * (maxForwardJumps + 1)))
          lam 1 qep tL t (A o))) =
      (oa >>= fun o => CKA.branch (dhScheme Dh) 1 tStar b
        (SM.Construction.redCKAAuth (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT (idOf o) maxForwardJumps) lam 1 qep tL t (A o))) :=
    fun b => bind_congr fun o => by
      rw [← ckaBranch_dhSchemeFb_eq]
      exact FsAtomicBSwap.ckaBranch_redCKAAuth_atomic_eq Dh (rootPRNG C.F encPt) C ℓ encT (idOf o)
        lam ((q + 1) * (maxForwardJumps + 1)) q 1 tStar qep tL t b (Nat.le_refl _)
        (A o) q (hqA o) (Nat.le_refl q) (hshA o)
  rw [hBr true, hBr false]

theorem fig8RedsInst_redCKAPriv_advAvg_advantage {α : Type} (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : LibsignalSession.Crypto) (codec : SignalMessageProtoCodec)
    (hc : codec = protoSignalCodec) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (oa : ProbComp α) (idOf : α → Party → IdentityKey)
    (lam : Pt) (qep q tStar : ℕ) (tL : Option ℕ) (i : ℕ) (A : α → Fig8Adv Pt ℓ)
    (hqA : ∀ o, SM.MakesAtMostQueries (A o) q)
    (hshA : ∀ o, LibsignalSM.Proofs.SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) (A o)) :
    CKA.advantage (dhScheme Dh) 1 tStar
      (advAvg oa fun o =>
        ((fig8RedsInst Dh encPt C codec ℓ encT (idOf o) lam qep q).redCKAPriv tL i).eval
          (fun _ => A o) ()) =
    CKA.advantage (dhScheme Dh) 1 tStar
      (advAvg oa fun o =>
        SM.Construction.redCKAPriv (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C codec ℓ encT (idOf o) maxForwardJumps) lam 1 qep tL i (A o)) := by
  subst hc
  rw [QuerySubsumes.ckaAdvantage_advAvg_congr (dhScheme Dh) 1 tStar oa fun o =>
      BundlesEval.fig8RedsInst_redCKAPriv_coinSimEquiv Dh encPt C protoSignalCodec
        ℓ hℓ encT (idOf o) lam qep q tL i (A o) (hqA o)]
  rw [CKA.advantage_eq_boolDist, CKA.advantage_eq_boolDist,
    ckaBranch_avg, ckaBranch_avg, ckaBranch_avg, ckaBranch_avg]
  have hBr : ∀ b,
      (oa >>= fun o => CKA.branch (dhScheme Dh) 1 tStar b
        (SM.Construction.redCKAPriv (dhSchemeFb Dh) (rootPRNG C.F encPt)
          (fsAtomicB C ℓ encT (idOf o) ((q + 1) * (maxForwardJumps + 1)))
          lam 1 qep tL i (A o))) =
      (oa >>= fun o => CKA.branch (dhScheme Dh) 1 tStar b
        (SM.Construction.redCKAPriv (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT (idOf o) maxForwardJumps) lam 1 qep tL i (A o))) :=
    fun b => bind_congr fun o => by
      rw [← ckaBranch_dhSchemeFb_eq]
      exact FsAtomicBSwap.ckaBranch_redCKAPriv_atomic_eq Dh (rootPRNG C.F encPt) C ℓ encT (idOf o)
        lam ((q + 1) * (maxForwardJumps + 1)) q 1 tStar qep tL i b (Nat.le_refl _)
        (A o) q (hqA o) (Nat.le_refl q) (hshA o)
  rw [hBr true, hBr false]

private abbrev fig8PrngShallowIface (ℓ : ℕ) :=
  PRFPRNG.prngIface (BitVec 256) (CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
    (BitVec 256) (BitVec 256) (BitVec 256) (RatchetSenderState (BitVec 256))
    (RatchetReceiverState (BitVec 256) (BitVec 256)) (LibsignalMsgPublicPart × Plain ℓ)
    (ℕ × LibsignalCiphertextWithSalt32) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256))
    ($ᵗ Pt) ($ᵗ (BitVec 256))

theorem fig8RedsInst_redPRNGAuth_advAvg_advantage {α : Type} (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : LibsignalSession.Crypto) (codec : SignalMessageProtoCodec)
    (hc : codec = protoSignalCodec) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (oa : ProbComp α) (idOf : α → Party → IdentityKey)
    (lam : Pt) (qep q : ℕ) (tL : Option ℕ) (t : ℕ) (A : α → Fig8Adv Pt ℓ)
    (hqA : ∀ o, SM.MakesAtMostQueries (A o) q)
    (hshA : ∀ o, LibsignalSM.Proofs.SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) (A o)) :
    PRFPRNG.advantage (rootPRNG C.F encPt)
      (advAvg oa fun o =>
        ((fig8RedsInst Dh encPt C codec ℓ encT (idOf o) lam qep q).redPRNGAuth tL t).eval
          (fun _ => A o) ()) =
    PRFPRNG.advantage (rootPRNG C.F encPt)
      (advAvg oa fun o =>
        SM.Construction.redPRNGAuth (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C codec ℓ encT (idOf o) maxForwardJumps) lam 1 qep tL t (A o)) := by
  subst hc
  rw [QuerySubsumes.prngAdvantage_advAvg_congr (rootPRNG C.F encPt) oa fun o =>
      BundlesEval.fig8RedsInst_redPRNGAuth_prog_coinSimEquiv Dh encPt C protoSignalCodec
        ℓ hℓ encT (idOf o) lam qep q tL t (A o)]
  rw [PRFPRNG.advantage_eq_boolDist, PRFPRNG.advantage_eq_boolDist,
    prngBranch_avg, prngBranch_avg, prngBranch_avg, prngBranch_avg]
  have hBr : ∀ b,
      (oa >>= fun o => PRFPRNG.branch (rootPRNG C.F encPt) b
        ((SM.Construction.redPRNGAuthProg (q + 1) ((q + 1) * (maxForwardJumps + 1))
          1 qep maxForwardJumps tL t :
          CostedReduction (Bundles.fig8CkaOpsShallow ℓ Pt C Dh encPt encT (idOf o) lam
            ((q + 1) * (maxForwardJumps + 1)))
            (fig8PrngShallowIface ℓ)
            _ _ .unit .unit .bool .bool).eval (fun _ => A o) ())) =
      (oa >>= fun o => PRFPRNG.branch (rootPRNG C.F encPt) b
        (SM.Construction.redPRNGAuth (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT (idOf o) maxForwardJumps) lam 1 qep tL t (A o))) :=
    fun b => bind_congr fun o => by
      rw [BundlesEval.redPRNGAuthProg_branch_eval_atomic Dh encPt C ℓ encT (idOf o)
        lam qep q tL t (A o) (hqA o) b,
        FsAtomicBSwap.redPRNGAuth_atomic_eq Dh (rootPRNG C.F encPt) C ℓ encT (idOf o) lam
          ((q + 1) * (maxForwardJumps + 1)) q 1 qep tL t (Nat.le_refl _) (A o) q (hqA o)
          (Nat.le_refl q) (hshA o)]
  rw [hBr true, hBr false]

theorem fig8RedsInst_redPRNGPriv_advAvg_advantage {α : Type} (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : LibsignalSession.Crypto) (codec : SignalMessageProtoCodec)
    (hc : codec = protoSignalCodec) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (oa : ProbComp α) (idOf : α → Party → IdentityKey)
    (lam : Pt) (qep q : ℕ) (tL : Option ℕ) (i : ℕ) (A : α → Fig8Adv Pt ℓ)
    (hqA : ∀ o, SM.MakesAtMostQueries (A o) q)
    (hshA : ∀ o, LibsignalSM.Proofs.SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) (A o)) :
    PRFPRNG.advantage (rootPRNG C.F encPt)
      (advAvg oa fun o =>
        ((fig8RedsInst Dh encPt C codec ℓ encT (idOf o) lam qep q).redPRNGPriv tL i).eval
          (fun _ => A o) ()) =
    PRFPRNG.advantage (rootPRNG C.F encPt)
      (advAvg oa fun o =>
        SM.Construction.redPRNGPriv (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C codec ℓ encT (idOf o) maxForwardJumps) lam 1 qep tL i (A o)) := by
  subst hc
  rw [QuerySubsumes.prngAdvantage_advAvg_congr (rootPRNG C.F encPt) oa fun o =>
      BundlesEval.fig8RedsInst_redPRNGPriv_prog_coinSimEquiv Dh encPt C protoSignalCodec
        ℓ hℓ encT (idOf o) lam qep q tL i (A o)]
  rw [PRFPRNG.advantage_eq_boolDist, PRFPRNG.advantage_eq_boolDist,
    prngBranch_avg, prngBranch_avg, prngBranch_avg, prngBranch_avg]
  have hBr : ∀ b,
      (oa >>= fun o => PRFPRNG.branch (rootPRNG C.F encPt) b
        ((SM.Construction.redPRNGPrivProg (q + 1) ((q + 1) * (maxForwardJumps + 1))
          1 qep maxForwardJumps tL i :
          CostedReduction (Bundles.fig8CkaOpsShallow ℓ Pt C Dh encPt encT (idOf o) lam
            ((q + 1) * (maxForwardJumps + 1)))
            (fig8PrngShallowIface ℓ)
            _ _ .unit .unit .bool .bool).eval (fun _ => A o) ())) =
      (oa >>= fun o => PRFPRNG.branch (rootPRNG C.F encPt) b
        (SM.Construction.redPRNGPriv (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT (idOf o) maxForwardJumps) lam 1 qep tL i (A o))) :=
    fun b => bind_congr fun o => by
      rw [BundlesEval.redPRNGPrivProg_branch_eval_atomic Dh encPt C ℓ encT (idOf o)
        lam qep q tL i (A o) (hqA o) b,
        FsAtomicBSwap.redPRNGPriv_atomic_eq Dh (rootPRNG C.F encPt) C ℓ encT (idOf o) lam
          ((q + 1) * (maxForwardJumps + 1)) q 1 qep tL i (Nat.le_refl _) (A o) q (hqA o)
          (Nat.le_refl q) (hshA o)]
  rw [hBr true, hBr false]

theorem fig8RedsInst_redFSAuth_mix_evalDistEq {α : Type} (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : LibsignalSession.Crypto) (codec : SignalMessageProtoCodec)
    (hc : codec = protoSignalCodec) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (oa : ProbComp α) (idOf : α → Party → IdentityKey)
    (lam : Pt) (qep q : ℕ) (j : ℕ) (tL : Option ℕ) (t : ℕ) (A : α → Fig8Adv Pt ℓ)
    (hqA : ∀ o, SM.MakesAtMostQueries (A o) q)
    (hshA : ∀ o, LibsignalSM.Proofs.SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) (A o)) :
    (oa >>= fun o => FSAEAD.game (lFS C codec ℓ encT (idOf o) maxForwardJumps)
      (((fig8RedsInst Dh encPt C codec ℓ encT (idOf o) lam qep q).redFSAuth j tL t).eval
        (fun _ => A o) ())) =ᵈ
    (oa >>= fun o => FSAEAD.game (lFS C codec ℓ encT (idOf o) maxForwardJumps)
      (SM.Construction.redFSAuth (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C codec ℓ encT (idOf o) maxForwardJumps) lam 1 qep j tL t (A o))) :=
  EvalDistEq.rfl.bind fun o =>
    fig8RedsInst_redFSAuth_game_evalDistEq Dh encPt C codec hc ℓ hℓ encT (idOf o) lam qep q
      j tL t (A o) (hqA o) (hshA o)

theorem fig8RedsInst_redFSAuth_mix_boolBias {α : Type} (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : LibsignalSession.Crypto) (codec : SignalMessageProtoCodec)
    (hc : codec = protoSignalCodec) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (oa : ProbComp α) (idOf : α → Party → IdentityKey)
    (lam : Pt) (qep q : ℕ) (j : ℕ) (tL : Option ℕ) (t : ℕ) (A : α → Fig8Adv Pt ℓ)
    (hqA : ∀ o, SM.MakesAtMostQueries (A o) q)
    (hshA : ∀ o, LibsignalSM.Proofs.SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) (A o)) :
    letI : MeasurableSpace α := ⊤
    (∫⁻ o, FSAEAD.advantage (lFS C codec ℓ encT (idOf o) maxForwardJumps)
      (SM.Construction.redFSAuth (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C codec ℓ encT (idOf o) maxForwardJumps) lam 1 qep j tL t (A o)) ∂𝒟[oa]) =
    𝒟[oa >>= fun o => FSAEAD.game (lFS C codec ℓ encT (idOf o) maxForwardJumps)
      (((fig8RedsInst Dh encPt C codec ℓ encT (idOf o) lam qep q).redFSAuth j tL t).eval
        (fun _ => A o) ())].boolBias := by
  let _ : MeasurableSpace α := ⊤
  rw [(fig8RedsInst_redFSAuth_mix_evalDistEq Dh encPt C codec hc ℓ hℓ encT oa idOf lam qep q
    j tL t A hqA hshA).evalDist_eq]
  exact (boolBias_mix_coin oa (fun o => lFS C codec ℓ encT (idOf o) maxForwardJumps) fun o =>
    SM.Construction.runFS (dhScheme Dh) (rootPRNG C.F encPt)
      (lFS C codec ℓ encT (idOf o) maxForwardJumps) lam 1 qep ⟨true, tL, t⟩ j false (A o)).symm

theorem fig8RedsInst_redFSPriv_mix_evalDistEq {α : Type} (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : LibsignalSession.Crypto) (codec : SignalMessageProtoCodec)
    (hc : codec = protoSignalCodec) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (oa : ProbComp α) (idOf : α → Party → IdentityKey)
    (lam : Pt) (qep q : ℕ) (tL : Option ℕ) (i : ℕ) (A : α → Fig8Adv Pt ℓ)
    (hqA : ∀ o, SM.MakesAtMostQueries (A o) q)
    (hshA : ∀ o, LibsignalSM.Proofs.SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) (A o)) :
    (oa >>= fun o => FSAEAD.game (lFS C codec ℓ encT (idOf o) maxForwardJumps)
      (((fig8RedsInst Dh encPt C codec ℓ encT (idOf o) lam qep q).redFSPriv tL i).eval
        (fun _ => A o) ())) =ᵈ
    (oa >>= fun o => FSAEAD.game (lFS C codec ℓ encT (idOf o) maxForwardJumps)
      (SM.Construction.redFSPriv (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C codec ℓ encT (idOf o) maxForwardJumps) lam 1 qep tL i (A o))) :=
  EvalDistEq.rfl.bind fun o =>
    fig8RedsInst_redFSPriv_game_evalDistEq Dh encPt C codec hc ℓ hℓ encT (idOf o) lam qep q
      tL i (A o) (hqA o) (hshA o)

theorem fig8RedsInst_redFSPrivCoin_mix_evalDistEq {α : Type} (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : LibsignalSession.Crypto) (codec : SignalMessageProtoCodec)
    (hc : codec = protoSignalCodec) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (oa : ProbComp α) (idOf : α → Party → IdentityKey)
    (lam : Pt) (qep q : ℕ) (tL : Option ℕ) (i : ℕ) (A : α → Fig8Adv Pt ℓ)
    (hqA : ∀ o, SM.MakesAtMostQueries (A o) q)
    (hshA : ∀ o, LibsignalSM.Proofs.SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) (A o)) :
    (oa >>= fun o => FSAEAD.game (lFS C codec ℓ encT (idOf o) maxForwardJumps)
      (((fig8RedsInst Dh encPt C codec ℓ encT (idOf o) lam qep q).redFSPrivCoin tL i).eval
        (fun _ => A o) ())) =ᵈ
    (oa >>= fun o => FSAEAD.game (lFS C codec ℓ encT (idOf o) maxForwardJumps)
      (SM.Construction.redFSPrivCoin (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C codec ℓ encT (idOf o) maxForwardJumps) lam 1 qep tL i (A o))) :=
  EvalDistEq.rfl.bind fun o =>
    fig8RedsInst_redFSPrivCoin_game_evalDistEq Dh encPt C codec hc ℓ hℓ encT (idOf o) lam qep q
      tL i (A o) (hqA o) (hshA o)

theorem fig8RedsInst_redFSPrivCoin_mix_boolBias {α : Type} (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : LibsignalSession.Crypto) (codec : SignalMessageProtoCodec)
    (hc : codec = protoSignalCodec) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (oa : ProbComp α) (idOf : α → Party → IdentityKey)
    (lam : Pt) (qep q : ℕ) (tL : Option ℕ) (i : ℕ) (A : α → Fig8Adv Pt ℓ)
    (hqA : ∀ o, SM.MakesAtMostQueries (A o) q)
    (hshA : ∀ o, LibsignalSM.Proofs.SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) (A o)) :
    letI : MeasurableSpace α := ⊤
    (∫⁻ o, FSAEAD.advantage (lFS C codec ℓ encT (idOf o) maxForwardJumps)
      (SM.Construction.redFSPrivCoin (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C codec ℓ encT (idOf o) maxForwardJumps) lam 1 qep tL i (A o)) ∂𝒟[oa]) =
    𝒟[oa >>= fun o => FSAEAD.game (lFS C codec ℓ encT (idOf o) maxForwardJumps)
      (((fig8RedsInst Dh encPt C codec ℓ encT (idOf o) lam qep q).redFSPrivCoin tL i).eval
        (fun _ => A o) ())].boolBias := by
  let _ : MeasurableSpace α := ⊤
  rw [(fig8RedsInst_redFSPrivCoin_mix_evalDistEq Dh encPt C codec hc ℓ hℓ encT oa idOf lam qep q
    tL i A hqA hshA).evalDist_eq]
  exact (boolBias_mix_coin oa (fun o => lFS C codec ℓ encT (idOf o) maxForwardJumps) fun o =>
    SM.Construction.runFS (dhScheme Dh) (rootPRNG C.F encPt)
      (lFS C codec ℓ encT (idOf o) maxForwardJumps) lam 1 qep ⟨false, tL, i⟩ 0 false (A o)).symm


private theorem isQueryBoundP_zero_mono {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {oa : OracleComp spec α} {p q : ι → Prop} [DecidablePred p] [DecidablePred q]
    (hqp : ∀ x, q x → p x) (h : IsQueryBoundP oa p 0) : IsQueryBoundP oa q 0 := by
  induction oa using OracleComp.inductionOn with
  | pure _ => trivial
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h ⊢
    have hnp : ¬ p t := h.1.resolve_right (Nat.not_lt_zero 0)
    have hnq : ¬ q t := mt (hqp t) hnp
    exact ⟨Or.inl hnq, fun u => by
      have hu := h.2 u
      simp only [hnp, ite_false] at hu
      simpa [hnq] using ih u hu⟩

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem encMsgsOk_shortB_of_atomicShortPubB {SS RS AD C : Type} {ℓ : ℕ}
    {R : FSAEAD.Adversary SS RS AD (LibsignalMsgPublicPart × Plain ℓ) C}
    (h : FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) R) :
    FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB) R := by
  refine isQueryBoundP_zero_mono (fun t ht => ?_) h
  rcases t with _ | (((((⟨_, m⟩ | ⟨_, m₀, m₁⟩) | _) | _) | _) | _)
  · cases ht
  · simp only [FSAEAD.encBadMsg, Bool.not_eq_true'] at ht ⊢
    cases hat : atomicShortPubB m.1
    · rfl
    · rw [atomicShortPubB_imp_shortB hat] at ht; cases ht
  · simp only [FSAEAD.encBadMsg, Bool.or_eq_true, Bool.not_eq_true'] at ht ⊢
    rcases ht with ht₀ | ht₁
    · left
      cases hat : atomicShortPubB m₀.1
      · rfl
      · rw [atomicShortPubB_imp_shortB hat] at ht₀; cases ht₀
    · right
      cases hat : atomicShortPubB m₁.1
      · rfl
      · rw [atomicShortPubB_imp_shortB hat] at ht₁; cases ht₁
  all_goals cases ht

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem fsClamp_fsAtomicB_fsSendShort (C : LibsignalSession.Crypto) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (B B0 : ℕ) :
    LibsignalSM.Proofs.SessionShort.FSAEADRed.FsSendShort
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
      (SM.Construction.fsClamp B (fsAtomicB C ℓ encT idOf B0)) := by
  intro ss hdr m hm
  change ((fsAtomicB C ℓ encT idOf B0).send ss hdr m).2.2.1.1.length + 8 < 2 ^ 32
  rw [fsAtomicB_send_eq C ℓ encT idOf B0 ss hdr m hm]
  exact LibsignalSM.Proofs.SessionShort.FSAEADRed.lFS_fsSendShort C protoSignalCodec
    signalEncodeFits32_proto ℓ (by omega) encT idOf maxForwardJumps ss hdr m
    (atomicShortPubB_imp_shortB hm)

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem fsOk_and_encAtomicShort_of_querySubsumes (ℓ qR qd : ℕ)
    {D C_uncached : FsAdv Pt ℓ} (hMakes : FSAEAD.MakesAtMostQueries D qR)
    (hSub : QuerySubsumes D C_uncached) (hqd : FSAEAD.MakesAtMostDecQueries C_uncached qd)
    (heq : FSAEAD.EqualPubChallenges C_uncached)
    (hcls : FSAEAD.AllQueriesInOneADClass (fun h : Header Pt => h.1) C_uncached)
    (hEnc : FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
      C_uncached)
    (hGuard : GuardedFSInjectShort C_uncached) :
    FsOk ℓ qR qd D ∧
      FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) D := by
  have hEncAt := QuerySubsumes.fsaeadEncMsgsOk_of_querySubsumes hSub hEnc
  exact ⟨⟨hMakes, QuerySubsumes.fsaeadMakesAtMostDecQueries_of_querySubsumes hSub hqd,
    QuerySubsumes.fsaeadEqualPubChallenges_of_querySubsumes hSub heq,
    QuerySubsumes.fsaeadAllQueriesInOneADClass_of_querySubsumes hSub hcls,
    encMsgsOk_shortB_of_atomicShortPubB hEncAt,
    QuerySubsumes.guardedFSInjectShort_of_querySubsumes hSub hGuard⟩, hEncAt⟩

theorem fig8RedsInst_fsOk_and_encAtomicShort (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : LibsignalSession.Crypto) (codec : SignalMessageProtoCodec)
    (_hc : codec = protoSignalCodec) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (B_adv : Fig8Adv Pt ℓ) (hqB : SM.MakesAtMostQueries B_adv q)
    (hshB : LibsignalSM.Proofs.SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) B_adv)
    (hgB : LibsignalSM.Proofs.SessionShort.GuardedSMShort B_adv) :
    let R := fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q
    let challAdv := R.challSim.eval (fun _ => B_adv) ()
    (∀ j tL t,
      FsOk ℓ (min (2 * q) (q + 2)) q ((R.redFSAuth j tL t).eval (fun _ => challAdv) ()) ∧
      FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
        ((R.redFSAuth j tL t).eval (fun _ => challAdv) ())) ∧
    (∀ i,
      let privAdv := (R.privRedB i).eval (fun _ => B_adv) ()
      (∀ tL,
        FsOk ℓ (min (2 * q) (q + 2)) q ((R.redFSPriv tL i).eval (fun _ => privAdv) ()) ∧
        FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
          ((R.redFSPriv tL i).eval (fun _ => privAdv) ())) ∧
      (∀ tL,
        FsOk ℓ (min (2 * q) (q + 2)) q ((R.redFSPrivCoin tL i).eval (fun _ => privAdv) ()) ∧
        FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
          ((R.redFSPrivCoin tL i).eval (fun _ => privAdv) ()))) := by
  intro R challAdv
  have hChall : challAdv = SM.Thm1.challSim (2 + 1) qep B_adv :=
    fig8RedsInst_challSim_eval Dh encPt C codec ℓ hℓ encT idOf lam qep q B_adv hqB
  have hPriv : ∀ i, (R.privRedB i).eval (fun _ => B_adv) () =
      SM.ThmB.privRedB (2 + 1) qep i (lBlank ℓ) B_adv := fun i =>
    fig8RedsInst_privRedB_eval Dh encPt C codec ℓ hℓ encT idOf lam qep q i B_adv hqB
  let cka := dhSchemeFb Dh; let prng := rootPRNG C.F encPt
  let B0 := (q + 1) * (maxForwardJumps + 1)
  let fs' := SM.Construction.fsClamp B0 (fsAtomicB C ℓ encT idOf B0)
  have hfsShort := fsClamp_fsAtomicB_fsSendShort C ℓ hℓ encT idOf B0 B0
  refine ⟨fun j tL t => ?_, fun i => ?_⟩
  · have hqChall := SM.Thm1.challSim_queries (2 + 1) qep B_adv q hqB
    have heqChall := challSim_equalPub (2 + 1) qep (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1) B_adv
    have hshChall : FSAEADRed.SendMsgsOk
        (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
        (SM.Thm1.challSim (2 + 1) qep B_adv) :=
      LibsignalSM.Proofs.QueryBounds.isQueryBoundP_congr
        (by rintro (_ | ((((_ | _) | _) | _) | _)) <;> rfl)
        (challSim_sendOk (2 + 1) qep
          (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) B_adv hshB)
    have hgChall := challSim_guardedSMShort (2 + 1) qep B_adv hgB
    have hSub : QuerySubsumes ((R.redFSAuth j tL t).eval (fun _ => challAdv) ())
        (SM.Construction.redFSAuth cka prng fs' lam 1 qep j tL t
          (SM.Thm1.challSim (2 + 1) qep B_adv)) := by
      dsimp only [R]; rw [hChall]
      exact BundlesEval.fig8RedsInst_redFSAuth_querySubsumes Dh encPt C codec ℓ hℓ encT idOf
        lam qep q j tL t _ hqChall
    have hMakes : FSAEAD.MakesAtMostQueries ((R.redFSAuth j tL t).eval (fun _ => challAdv) ())
        (min (2 * q) (q + 2)) := by
      dsimp only [R]; rw [hChall]
      exact ProgBounds.fig8RedsInst_redFSAuth_makesAtMostQueries Dh encPt C codec ℓ encT
        idOf lam qep q j tL t _ hqChall
    exact fsOk_and_encAtomicShort_of_querySubsumes ℓ (min (2 * q) (q + 2)) q hMakes hSub
      (SM.Construction.redFSAuth_dec_queries cka prng fs' lam 1 qep j tL t _ hqChall)
      (SafePost.to_isQueryBoundP (safePost_redFSAuth cka prng fs' lam 1 qep j tL t
        (validQ_unequalPubChall ⟨true, tL, t⟩) _ heqChall))
      ⟨t, SafePost.to_isQueryBoundP (safePost_redFSAuth cka prng fs' lam 1 qep j tL t
        (validQ_offClass ⟨true, tL, t⟩ (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1)) _ heqChall)⟩
      (SafePost.to_isQueryBoundP (FSAEADRed.safePost_redFSAuth cka prng fs' lam 1 qep j tL t
        (FSAEADRed.validQ_encBadMsg ⟨true, tL, t⟩
          (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)) _ hshChall))
      (FSAEADRed.guardedFSInjectShort_redFSAuth cka prng fs' hfsShort lam 1 qep j tL t _ hshChall hgChall)
  · intro privAdv
    have hqPriv := LibsignalSM.Proofs.PrivRedQueries.privRedB_queries (2 + 1) qep i (lBlank ℓ) B_adv q hqB
    have heqPriv := privRedB_equalPub_local (2 + 1) qep i
      (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1) (lBlank ℓ) (fun _ => rfl) B_adv
    have hshPriv : FSAEADRed.SendMsgsOk
        (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
        (SM.ThmB.privRedB (2 + 1) qep i (lBlank ℓ) B_adv) :=
      LibsignalSM.Proofs.QueryBounds.isQueryBoundP_congr
        (by rintro (_ | ((((_ | _) | _) | _) | _)) <;> rfl)
        (privRedB_sendOk (2 + 1) qep i
          (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
          (lBlank ℓ) (fun _ => rfl) B_adv hshB)
    have hgPriv := privRedB_guardedSMShort (2 + 1) qep i (lBlank ℓ) B_adv hgB
    refine ⟨fun tL => ?_, fun tL => ?_⟩
    · have hSub : QuerySubsumes ((R.redFSPriv tL i).eval (fun _ => privAdv) ())
          (SM.Construction.redFSPriv cka prng fs' lam 1 qep tL i
            (SM.ThmB.privRedB (2 + 1) qep i (lBlank ℓ) B_adv)) := by
        dsimp only [privAdv, R]; rw [hPriv i]
        exact BundlesEval.fig8RedsInst_redFSPriv_querySubsumes Dh encPt C codec ℓ hℓ encT idOf
          lam qep q tL i _ hqPriv
      have hMakes : FSAEAD.MakesAtMostQueries ((R.redFSPriv tL i).eval (fun _ => privAdv) ())
          (min (2 * q) (q + 2)) := by
        dsimp only [privAdv, R]; rw [hPriv i]
        exact ProgBounds.fig8RedsInst_redFSPriv_makesAtMostQueries Dh encPt C codec ℓ encT
          idOf lam qep q tL i _ hqPriv
      exact fsOk_and_encAtomicShort_of_querySubsumes ℓ (min (2 * q) (q + 2)) q hMakes hSub
        (SM.Construction.redFSPriv_dec_queries cka prng fs' lam 1 qep tL i _ hqPriv)
        (SafePost.to_isQueryBoundP (safePost_redFSPriv cka prng fs' lam 1 qep tL i
          (validQ_unequalPubChall ⟨false, tL, i⟩) _ heqPriv))
        ⟨i, SafePost.to_isQueryBoundP (safePost_redFSPriv cka prng fs' lam 1 qep tL i
          (validQ_offClass ⟨false, tL, i⟩ (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1)) _ heqPriv)⟩
        (SafePost.to_isQueryBoundP (FSAEADRed.safePost_redFSPriv cka prng fs' lam 1 qep tL i
          (FSAEADRed.validQ_encBadMsg ⟨false, tL, i⟩
            (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)) _ hshPriv))
        (FSAEADRed.guardedFSInjectShort_redFSPriv cka prng fs' hfsShort lam 1 qep tL i _ hshPriv hgPriv)
    · have hSub : QuerySubsumes ((R.redFSPrivCoin tL i).eval (fun _ => privAdv) ())
          (SM.Construction.redFSPrivCoin cka prng fs' lam 1 qep tL i
            (SM.ThmB.privRedB (2 + 1) qep i (lBlank ℓ) B_adv)) := by
        dsimp only [privAdv, R]; rw [hPriv i]
        exact BundlesEval.fig8RedsInst_redFSPrivCoin_querySubsumes Dh encPt C codec ℓ hℓ encT idOf
          lam qep q tL i _ hqPriv
      have hMakes : FSAEAD.MakesAtMostQueries ((R.redFSPrivCoin tL i).eval (fun _ => privAdv) ())
          (min (2 * q) (q + 2)) := by
        dsimp only [privAdv, R]; rw [hPriv i]
        exact ProgBounds.fig8RedsInst_redFSPrivCoin_makesAtMostQueries Dh encPt C codec ℓ encT
          idOf lam qep q tL i _ hqPriv
      exact fsOk_and_encAtomicShort_of_querySubsumes ℓ (min (2 * q) (q + 2)) q hMakes hSub
        (SM.Construction.redFSPrivCoin_dec_queries cka prng fs' lam 1 qep tL i _ hqPriv)
        (SafePost.to_isQueryBoundP (safePost_redFSPrivCoin cka prng fs' lam 1 qep tL i
          (validQ_unequalPubChall ⟨false, tL, i⟩) _ heqPriv))
        ⟨i, SafePost.to_isQueryBoundP (safePost_redFSPrivCoin cka prng fs' lam 1 qep tL i
          (validQ_offClass ⟨false, tL, i⟩ (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1)) _ heqPriv)⟩
        (SafePost.to_isQueryBoundP (FSAEADRed.safePost_redFSPrivCoin cka prng fs' lam 1 qep tL i
          (FSAEADRed.validQ_encBadMsg ⟨false, tL, i⟩
            (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)) _ hshPriv))
        (FSAEADRed.guardedFSInjectShort_redFSPrivCoin cka prng fs' hfsShort lam 1 qep tL i _ hshPriv hgPriv)

theorem fig8RedsInst_fsOk (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : LibsignalSession.Crypto) (codec : SignalMessageProtoCodec)
    (hc : codec = protoSignalCodec) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (B_adv : Fig8Adv Pt ℓ) (hqB : SM.MakesAtMostQueries B_adv q)
    (hshB : LibsignalSM.Proofs.SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) B_adv)
    (hgB : LibsignalSM.Proofs.SessionShort.GuardedSMShort B_adv) :
    let R := fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q
    let challAdv := R.challSim.eval (fun _ => B_adv) ()
    (∀ j tL t, FsOk ℓ (min (2 * q) (q + 2)) q ((R.redFSAuth j tL t).eval (fun _ => challAdv) ())) ∧
    (∀ i,
      let privAdv := (R.privRedB i).eval (fun _ => B_adv) ()
      (∀ tL, FsOk ℓ (min (2 * q) (q + 2)) q ((R.redFSPriv tL i).eval (fun _ => privAdv) ())) ∧
      (∀ tL, FsOk ℓ (min (2 * q) (q + 2)) q ((R.redFSPrivCoin tL i).eval (fun _ => privAdv) ()))) := by
  obtain ⟨hA, hP⟩ := fig8RedsInst_fsOk_and_encAtomicShort Dh encPt C codec hc ℓ hℓ encT idOf
    lam qep q B_adv hqB hshB hgB
  exact ⟨fun j tL t => (hA j tL t).1,
    fun i => ⟨fun tL => ((hP i).1 tL).1, fun tL => ((hP i).2 tL).1⟩⟩

/-- Bounds `fig8H1Bound` by `fig8ShortBoundWith` at `fig8RedsInst`. -/
theorem fig8H1Bound_le_fig8ShortBoundWith (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : LibsignalSession.Crypto)
    (hD : ∀ k x, C.D k (C.E k x) = x) (codec : SignalMessageProtoCodec)
    (hc : codec = protoSignalCodec) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (hinj : Function.Injective encT)
    (hdum : ∀ T, encT T ≠ dummyKey) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (hq32 : 2 * q + 25002 < 2 ^ 32)
    (Rfs : FsCostedReds C codec ℓ encT idOf)
    (hFs : ∀ (A : FsAdv Pt ℓ), FsOk ℓ (min (2 * q) (q + 2)) q A →
      FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A →
      fsShortBound C codec ℓ encT idOf (min (2 * q) (q + 2)) q A ≤
        fsShortBoundWith C codec ℓ (min (2 * q) (q + 2)) q Rfs A)
    (B_adv : Fig8Adv Pt ℓ) (hqB : SM.MakesAtMostQueries B_adv q)
    (hshB : LibsignalSM.Proofs.SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) B_adv)
    (hgB : LibsignalSM.Proofs.SessionShort.GuardedSMShort B_adv) :
    fig8H1Bound Dh encPt C codec ℓ encT idOf lam qep q B_adv ≤
      fig8ShortBoundWith Dh encPt C codec ℓ encT idOf lam qep q
        (fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q) Rfs B_adv := by
  let R := fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q
  have hChall : R.challSim.eval (fun _ => B_adv) () = SM.Thm1.challSim (2 + 1) qep B_adv :=
    fig8RedsInst_challSim_eval Dh encPt C codec ℓ hℓ encT idOf lam qep q B_adv hqB
  have hPriv : ∀ i, (R.privRedB i).eval (fun _ => B_adv) () =
      SM.ThmB.privRedB (2 + 1) qep i (lBlank ℓ) B_adv := fun i =>
    fig8RedsInst_privRedB_eval Dh encPt C codec ℓ hℓ encT idOf lam qep q i B_adv hqB
  have hqChall : SM.MakesAtMostQueries (R.challSim.eval (fun _ => B_adv) ()) q := by
    rw [hChall]; exact SM.Thm1.challSim_queries (2 + 1) qep B_adv q hqB
  have hshChall : LibsignalSM.Proofs.SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
      (R.challSim.eval (fun _ => B_adv) ()) := by
    rw [hChall]
    exact LibsignalSM.Proofs.SessionShort.challSim_sendOk (2 + 1) qep
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) B_adv hshB
  have hqPriv : ∀ i, SM.MakesAtMostQueries ((R.privRedB i).eval (fun _ => B_adv) ()) q := fun i => by
    rw [hPriv i]; exact LibsignalSM.Proofs.PrivRedQueries.privRedB_queries (2 + 1) qep i (lBlank ℓ) B_adv q hqB
  have hshPriv : ∀ i, LibsignalSM.Proofs.SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
      ((R.privRedB i).eval (fun _ => B_adv) ()) := fun i => by
    rw [hPriv i]; exact LibsignalSM.Proofs.SessionShort.privRedB_sendOk (2 + 1) qep i
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) (lBlank ℓ) (fun _ => rfl) B_adv hshB
  obtain ⟨hAuthOk, hPrivOk⟩ := fig8RedsInst_fsOk_and_encAtomicShort Dh encPt C codec hc ℓ hℓ
    encT idOf lam qep q B_adv hqB hshB hgB
  have hℓ31 : ℓ + 16 < 2 ^ 31 + 16 := by omega
  have h25k : (25000 : ℕ) = maxForwardJumps := rfl
  change fig8H1Bound Dh encPt C codec ℓ encT idOf lam qep q B_adv ≤
    fig8ShortBoundWith Dh encPt C codec ℓ encT idOf lam qep q R Rfs B_adv
  unfold fig8H1Bound fig8ShortBoundWith; dsimp only; simp only [h25k, ← hChall, ← hPriv]
  gcongr with t _ tL _ j _ i _ tL _
  · rw [fig8RedsInst_redCKAAuth_advantage Dh encPt C codec hc ℓ hℓ encT idOf lam qep q
      (healEpoch tL) tL t _ hqChall hshChall]
  · rw [fig8RedsInst_redPRNGAuth_advantage Dh encPt C codec hc ℓ hℓ encT idOf lam qep q
      tL t _ hqChall hshChall]
  · rw [← fig8RedsInst_redFSAuth_advantage Dh encPt C codec hc ℓ hℓ encT idOf lam qep q
      j tL t _ hqChall hshChall]
    exact (fs_le_fsShortBound C hD codec hc ℓ hℓ31 encT hinj hdum idOf (min (2 * q) (q + 2)) q
      (by omega) _ (hAuthOk j tL t).1).trans (hFs _ (hAuthOk j tL t).1 (hAuthOk j tL t).2)
  · rw [fig8RedsInst_redCKAPriv_advantage Dh encPt C codec hc ℓ hℓ encT idOf lam qep q
      (healEpoch tL) tL i _ (hqPriv i) (hshPriv i)]
  · rw [fig8RedsInst_redPRNGPriv_advantage Dh encPt C codec hc ℓ hℓ encT idOf lam qep q
      tL i _ (hqPriv i) (hshPriv i)]
  · rw [← fig8RedsInst_redFSPriv_advantage Dh encPt C codec hc ℓ hℓ encT idOf lam qep q
      tL i _ (hqPriv i) (hshPriv i)]
    exact (fs_le_fsShortBound C hD codec hc ℓ hℓ31 encT hinj hdum idOf (min (2 * q) (q + 2)) q
      (by omega) _ (((hPrivOk i).1 tL).1)).trans (hFs _ (((hPrivOk i).1 tL).1) (((hPrivOk i).1 tL).2))
  · rw [← fig8RedsInst_redFSPrivCoin_advantage Dh encPt C codec hc ℓ hℓ encT idOf lam qep q
      tL i _ (hqPriv i) (hshPriv i)]
    exact (fs_le_fsShortBound C hD codec hc ℓ hℓ31 encT hinj hdum idOf (min (2 * q) (q + 2)) q
      (by omega) _ (((hPrivOk i).2 tL).1)).trans (hFs _ (((hPrivOk i).2 tL).1) (((hPrivOk i).2 tL).2))

end ConcreteAtomicFig8

end CryptoVerification.LibsignalSession

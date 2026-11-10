/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Delta.KeyIndDefs

/-!
# PQXDH δ key indistinguishability: lazy stop event

**Checked by Lean.** Proves `kiStop` (`KIStopStmt`, DEV-PQ21), showing that a lazy stop implies the
Gap-DH bad event, an abort, or the KEM correctness bad event `hasBadKemCorrRecords`.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory
open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security
open Proofs.SignalPqxdh.Security
open Proofs.SignalPqxdh.Security.FgGapDh
open Proofs.SignalPqxdh.Security.FgGapDh.Ik
open Proofs.SignalPqxdh.Security.FgGapDh.Opk

namespace Proofs.SignalPqxdh.Security.PqxdhDelta

namespace KIStop

theorem badKeyIndFgAny4_of_resp_stillFresh_ro5KeyInViewδ {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (maxLen : ℕ) (adv : KeyIndAdvCutoffState S)
    (hValid : ValidTagState P maxLen adv)
    (hNoEc : hasEcPkCollisionKeyInd P adv.shCr.base = false)
    (hNoBadSig : hasBadSigKeyInd adv.shCr.base = false)
    (hNoKem : hasKemPkCollisionKeyInd adv.shCr.base = false)
    (hNoBadKem : hasBadKemShCrRecords S P adv.shCr.initKemRecs adv.shCr.recvKemRecs = false)
    (hNoCorr : hasBadKemCorrRecords S P adv.shCr.initKemRecs adv.shCr.recvKemRecs = false)
    {r : KeyIndRespEntry S} (hrMem : r ∈ adv.shCr.base.respSessions)
    (hRespFresh : isKeyIndRespStillFresh P true adv.shCr.base.principals adv.shCr.base.spkBundles
      adv.shCr.base.sessions r = true)
    (hRo5 : ro5KeyInView adv r.drKeyReal.rootKey = true) :
    badKeyIndFgAny4 P maxLen adv.shCr.base adv.advRoLog = true := by
  rcases hValid with ⟨hRoLen, hSendLe, hKS, hRand, hSessBoth, hRespValid⟩
  have hSessValid : ∀ s' ∈ adv.shCr.base.sessions, ValidInitSession S P adv.shCr s' :=
    fun s' hs' => (hSessBoth s' hs').1
  unfold isKeyIndRespStillFresh at hRespFresh
  simp only [Bool.and_assoc] at hRespFresh
  rcases Bool.and_eq_true_iff.mp hRespFresh with ⟨hNotRevR, hRest⟩
  rcases Bool.and_eq_true_iff.mp hRest with ⟨hSenderHonR, hMatch⟩
  cases hAny : adv.shCr.base.sessions.any (fun s => keyIndPartner P s r) with
  | true =>
    rw [hAny] at hMatch
    simp only [↓reduceIte] at hMatch
    obtain ⟨s, hsMem, hPart⟩ := List.any_eq_true.mp hAny
    have hClauseS := List.all_eq_true.mp hMatch s hsMem
    rw [hPart] at hClauseS
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at hClauseS
    rcases hClauseS with ⟨hNotRevS, hStillFreshS⟩
    have hKeySR : s.drKeyReal.rootKey = r.drKeyReal.rootKey :=
      keyIndPartner_imp_drKeyReal_eqδ P hP adv.shCr hKS hSendLe hNoCorr
        (hSessValid s hsMem) (hRespValid r hrMem) hPart
    have hFreshS : s.fresh = true := by
      unfold keyIndInitCorruptionClause at hStillFreshS
      exact (Bool.and_eq_true _ _).mp hStillFreshS |>.1
    have hPqHonS : s.pqspkHonest = true :=
      (fresh_imp_spkHonest_and_pqspkHonest_of_hasBadSigKeyInd_false hNoBadSig hsMem hFreshS).2
    unfold ro5KeyInView at hRo5
    simp only [Bool.or_eq_true, List.contains_iff_mem, List.any_eq_true, Bool.and_eq_true,
      beq_iff_eq] at hRo5
    rcases hRo5 with (hMemLog | ⟨s', hs'Mem, hUnfOrRev, hKeyEq⟩) | ⟨r', hr'Mem, hDishonOrRev,
      hKeyEq⟩
    · have hTake : s.drKeyReal.rootKey ∈ adv.advRoLog.take maxLen := by
        rw [hKeySR, List.take_of_length_le hRoLen]; exact hMemLog
      exact badKeyIndFgAny4_of_isSessionStillFreshKeyInd_mem_advRoLog P hP maxLen adv.shCr
        adv.advRoLog
        hKS hRand.sid_nodup hSessValid hsMem hStillFreshS hTake
    · have hsEq : s' = s :=
        init_eq_of_drKeyReal_eq P hP adv.shCr hNoEc hs'Mem hsMem (hSessValid s' hs'Mem) (hSessValid
          s hsMem)
          (hKeyEq.trans hKeySR.symm)
      subst hsEq
      exfalso
      rcases hUnfOrRev with hUnf | hRev
      · rw [hFreshS] at hUnf; nomatch hUnf
      · rw [hRev] at hNotRevS; nomatch hNotRevS
    · have hPart' : keyIndPartner P s r' = true :=
        drKeyReal_eq_imp_keyIndPartner_of_pqspkHonest P hP adv.shCr hKS hNoBadKem hNoKem hSendLe
          (hSessValid s hsMem) (hRespValid r' hr'Mem) hPqHonS (hKeySR.trans hKeyEq.symm)
      have hrEq : r' = r :=
        keyIndPartner_inj_right P adv.shCr hNoKem hRand.resp_bundle_nodup hr'Mem hrMem
          (hRespValid r' hr'Mem) (hRespValid r hrMem) hPart' hPart
      subst hrEq
      exfalso
      rcases hDishonOrRev with hDishon | hRev
      · rw [hSenderHonR] at hDishon; nomatch hDishon
      · rw [hRev] at hNotRevR; nomatch hNotRevR
  | false =>
    rw [hAny] at hMatch
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, Bool.true_and] at hMatch
    rcases hMatch with ⟨hPeerR, hNotSpkRevR⟩
    unfold ro5KeyInView at hRo5
    simp only [Bool.or_eq_true, List.contains_iff_mem, List.any_eq_true, Bool.and_eq_true,
      beq_iff_eq] at hRo5
    rcases hRo5 with (hMemLog | ⟨s', hs'Mem, _, hKeyEq⟩) | ⟨r', hr'Mem, hDishonOrRev, hKeyEq⟩
    · have hTake : r.drKeyReal.rootKey ∈ adv.advRoLog.take maxLen := by
        rw [List.take_of_length_le hRoLen]; exact hMemLog
      exact badKeyIndFgAny_imp_badKeyIndFgAny4 P maxLen adv.shCr.base adv.advRoLog
        (badKeyIndFgAny_of_resp_mem_advRoLog P hP maxLen adv.shCr adv.advRoLog hKS
          (hRespValid r hrMem) hPeerR hNotSpkRevR hTake)
    · have hNotPart : keyIndPartner P s' r = false := by
        by_contra hNeF
        have hTrue : keyIndPartner P s' r = true := Bool.eq_true_of_not_eq_false hNeF
        have hAnyT : adv.shCr.base.sessions.any (fun s => keyIndPartner P s r) = true :=
          List.any_eq_true.mpr ⟨s', hs'Mem, hTrue⟩
        rw [hAny] at hAnyT; nomatch hAnyT
      exact badKeyIndFgAny_imp_badKeyIndFgAny4 P maxLen adv.shCr.base adv.advRoLog
        (badKeyIndFgAny_of_resp_init_drKeyReal_eq P hP maxLen adv.shCr adv.advRoLog
          hKS hRand.sid_nodup hSessValid hNoBadKem hSendLe hs'Mem (hSessBoth s' hs'Mem).2
          (hRespValid r hrMem) hPeerR hNotSpkRevR hNotPart hKeyEq)
    · have hNe : r ≠ r' := by
        rintro rfl
        rcases hDishonOrRev with hDishon | hRev
        · rw [hSenderHonR] at hDishon; nomatch hDishon
        · rw [hRev] at hNotRevR; nomatch hNotRevR
      exact badKeyIndFgAny_imp_badKeyIndFgAny4 P maxLen adv.shCr.base adv.advRoLog
        (badKeyIndFgAny_of_resp_resp_drKeyReal_eq P hP maxLen adv.shCr adv.advRoLog
          hKS hNoEc hRand.resp_sid_nodup hRand.resp_bundle_nodup hrMem hr'Mem
          (hRespValid r hrMem) (hRespValid r' hr'Mem) hPeerR hNotSpkRevR hNe hKeyEq.symm)

end KIStop

/-- A lazy stop in a valid tag state implies `badKeyIndFgAny4`, an abort, or `hasBadKemCorrRecords`. -/
theorem kiStop (S : Setup) : KIStopStmt S := by
  intro P hP maxLen adv hValid hStop
  by_cases hAbort : isKeyIndG3Abort P adv.shCr = true
  · exact Or.inr (Or.inl hAbort)
  · by_cases hCorr : hasBadKemCorrRecords S P adv.shCr.initKemRecs adv.shCr.recvKemRecs = true
    · exact Or.inr (Or.inr hCorr)
    · left
      have hNoCorr : hasBadKemCorrRecords S P adv.shCr.initKemRecs adv.shCr.recvKemRecs = false :=
        Bool.eq_false_iff.mpr hCorr
      have hAbortF : isKeyIndG3Abort P adv.shCr = false := Bool.eq_false_iff.mpr hAbort
      unfold isKeyIndG3Abort at hAbortF
      dsimp only at hAbortF
      simp only [Bool.or_eq_false_iff, Bool.not_eq_false', Bool.and_eq_true, List.all_eq_true]
        at hAbortF
      rcases hAbortF with ⟨⟨⟨⟨⟨hInitClean, hRespClean⟩, hNoEc⟩, hNoBadSig⟩, hNoKem⟩, hNoBadKem⟩
      rcases hValid with ⟨hRoLen, hSendLe, hKS, hRand, hSessBoth, hRespValid⟩
      have hSessValid : ∀ s' ∈ adv.shCr.base.sessions, ValidInitSession S P adv.shCr s' :=
        fun s' hs' => (hSessBoth s' hs').1
      have hValid' : ValidTagState P maxLen adv := ⟨hRoLen, hSendLe, hKS, hRand, hSessBoth,
        hRespValid⟩
      unfold lazyStop at hStop
      simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true] at hStop
      rcases hStop with ((⟨s, hsMem, hsTest, hRo5⟩ | ⟨r, hrMem, hrTest, hRo5⟩) |
        ⟨s1, hs1Mem, hs1Test, (⟨s2, hs2Mem, hs2Test, hDis | ⟨hSidEq, hKeyNe⟩⟩ | ⟨r2, hr2Mem, hr2Test,
          hDis⟩)⟩) |
        ⟨r1, hr1Mem, hr1Test, ⟨r2, hr2Mem, hr2Test, hDis | ⟨hSidEq, hKeyNe⟩⟩⟩
      · have hClean := hInitClean s hsMem
        simp only [hsTest, Bool.not_true, Bool.false_or] at hClean
        exact badKeyIndFgAny4_of_init_stillFresh_ro5KeyInView P hP maxLen adv hValid'
          hNoEc hNoBadSig hNoKem hNoBadKem hsMem hClean hRo5
      · have hClean := hRespClean r hrMem
        simp only [hrTest, Bool.not_true, Bool.false_or] at hClean
        exact KIStop.badKeyIndFgAny4_of_resp_stillFresh_ro5KeyInViewδ P hP maxLen adv hValid'
          hNoEc hNoBadSig hNoKem hNoBadKem hNoCorr hrMem hClean hRo5
      · exfalso
        have hIff : (s1.drKeyReal.rootKey == s2.drKeyReal.rootKey) = (s1.drKeyRand.rootKey ==
          s2.drKeyRand.rootKey) := by
          apply Bool.eq_iff_iff.mpr
          simp only [beq_iff_eq]
          constructor
          · intro hReal
            have hsEq := init_eq_of_drKeyReal_eq P hP adv.shCr hNoEc hs1Mem hs2Mem
              (hSessValid s1 hs1Mem) (hSessValid s2 hs2Mem) hReal
            rw [hsEq]
          · intro hRandEq
            have hsEq := init_eq_of_drKeyRand_eq P adv.shCr hRand hNoEc hNoKem hRespValid hs1Mem
              hs2Mem hRandEq
            rw [hsEq]
        rw [hIff, bne_self_eq_false] at hDis
        nomatch hDis
      · exfalso
        have hsEq : s1 = s2 := eq_of_nodup_map (·.sid) hRand.sid_nodup hs1Mem hs2Mem (beq_iff_eq.mp
          hSidEq)
        subst hsEq
        simp at hKeyNe
      · exfalso
        have hClean1 := hInitClean s1 hs1Mem
        simp only [hs1Test, Bool.not_true, Bool.false_or] at hClean1
        have hFresh1 : s1.fresh = true := by
          unfold isKeyIndInitStillFresh keyIndInitCorruptionClause at hClean1
          simp only [Bool.and_eq_true] at hClean1
          exact hClean1.1.1.1
        have hPqHon1 : s1.pqspkHonest = true :=
          (fresh_imp_spkHonest_and_pqspkHonest_of_hasBadSigKeyInd_false hNoBadSig hs1Mem hFresh1).2
        have hIff : (s1.drKeyReal.rootKey == r2.drKeyReal.rootKey) = (s1.drKeyRand.rootKey ==
          r2.drKeyRand.rootKey) := by
          apply Bool.eq_iff_iff.mpr
          simp only [beq_iff_eq]
          constructor
          · intro hReal
            have hPart := drKeyReal_eq_imp_keyIndPartner_of_pqspkHonest P hP adv.shCr hKS hNoBadKem
              hNoKem hSendLe
              (hSessValid s1 hs1Mem) (hRespValid r2 hr2Mem) hPqHon1 hReal
            exact keyIndPartner_imp_drKeyRand_eq P adv.shCr hRand hNoEc hNoKem hRespValid hs1Mem
              hr2Mem hPart
          · intro hRandEq
            have hPart := keyIndPartner_of_drKeyRand_eq P adv.shCr hRand hNoEc hNoKem hRespValid
              hs1Mem hr2Mem hRandEq
            exact keyIndPartner_imp_drKeyReal_eqδ P hP adv.shCr hKS hSendLe hNoCorr
              (hSessValid s1 hs1Mem) (hRespValid r2 hr2Mem) hPart
        rw [hIff, bne_self_eq_false] at hDis
        nomatch hDis
      · by_cases hRandEq : (r1.drKeyRand.rootKey == r2.drKeyRand.rootKey) = true
        · exfalso
          have hrEq := resp_eq_of_drKeyRand_eq P adv.shCr hRand hNoEc hNoKem hRespValid hr1Mem hr2Mem
            (beq_iff_eq.mp hRandEq)
          subst hrEq
          simp at hDis
        · have hRandF : (r1.drKeyRand.rootKey == r2.drKeyRand.rootKey) = false :=
            Bool.eq_false_iff.mpr hRandEq
          rw [hRandF] at hDis
          have hRealEq : r1.drKeyReal.rootKey = r2.drKeyReal.rootKey := by
            cases hR : (r1.drKeyReal.rootKey == r2.drKeyReal.rootKey)
            · rw [hR] at hDis; nomatch hDis
            · exact beq_iff_eq.mp hR
          have hNe : r1 ≠ r2 := fun hEq => by subst hEq; simp at hRandF
          have hClean1 := hRespClean r1 hr1Mem
          simp only [hr1Test, Bool.not_true, Bool.false_or] at hClean1
          unfold isKeyIndRespStillFresh at hClean1
          simp only [Bool.and_assoc] at hClean1
          rcases Bool.and_eq_true_iff.mp hClean1 with ⟨_, hRest1⟩
          rcases Bool.and_eq_true_iff.mp hRest1 with ⟨_, hMatch1⟩
          cases hAny1 : adv.shCr.base.sessions.any (fun s => keyIndPartner P s r1) with
          | true =>
            exfalso
            rw [hAny1] at hMatch1
            simp only [↓reduceIte] at hMatch1
            obtain ⟨s, hsMem, hPart1⟩ := List.any_eq_true.mp hAny1
            have hClause1 := List.all_eq_true.mp hMatch1 s hsMem
            rw [hPart1] at hClause1
            simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at hClause1
            have hFreshS : s.fresh = true := by
              unfold keyIndInitCorruptionClause at hClause1
              exact (Bool.and_eq_true _ _).mp hClause1.2 |>.1
            have hPqHonS : s.pqspkHonest = true :=
              (fresh_imp_spkHonest_and_pqspkHonest_of_hasBadSigKeyInd_false hNoBadSig hsMem hFreshS).2
            have hKeySR1 : s.drKeyReal.rootKey = r1.drKeyReal.rootKey :=
              keyIndPartner_imp_drKeyReal_eqδ P hP adv.shCr hKS hSendLe hNoCorr
                (hSessValid s hsMem) (hRespValid r1 hr1Mem) hPart1
            have hPart2 : keyIndPartner P s r2 = true :=
              drKeyReal_eq_imp_keyIndPartner_of_pqspkHonest P hP adv.shCr hKS hNoBadKem hNoKem hSendLe
                (hSessValid s hsMem) (hRespValid r2 hr2Mem) hPqHonS (hKeySR1.trans hRealEq)
            exact hNe (keyIndPartner_inj_right P adv.shCr hNoKem hRand.resp_bundle_nodup hr1Mem hr2Mem
              (hRespValid r1 hr1Mem) (hRespValid r2 hr2Mem) hPart1 hPart2)
          | false =>
            rw [hAny1] at hMatch1
            simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, Bool.true_and] at hMatch1
            rcases hMatch1 with ⟨hPeer1, hNotSpkRev1⟩
            exact badKeyIndFgAny_imp_badKeyIndFgAny4 P maxLen adv.shCr.base adv.advRoLog
              (badKeyIndFgAny_of_resp_resp_drKeyReal_eq P hP maxLen adv.shCr adv.advRoLog
                hKS hNoEc hRand.resp_sid_nodup hRand.resp_bundle_nodup hr1Mem hr2Mem
                (hRespValid r1 hr1Mem) (hRespValid r2 hr2Mem) hPeer1 hNotSpkRev1 hNe hRealEq)
      · exfalso
        have hrEq : r1 = r2 := eq_of_nodup_map (·.sid) hRand.resp_sid_nodup hr1Mem hr2Mem
          (beq_iff_eq.mp hSidEq)
        subst hrEq
        simp at hKeyNe

end Proofs.SignalPqxdh.Security.PqxdhDelta

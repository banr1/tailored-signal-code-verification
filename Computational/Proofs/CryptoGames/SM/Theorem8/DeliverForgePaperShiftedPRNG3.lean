/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperShiftedPRNG2
public import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma10
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma9
import ProofLib.SepLogic.WP.StateNorm

/-!
# Shifted-Paper Hop 2, Part 3

New-epoch `transmitE` step lemma, main induction, and shifted-paper Lemma 10 bounds
(`lemma10_df_shifted_paper` and `lemma10_df_shifted_dir2_paper`).
-/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory OracleComp OracleSpec

namespace CryptoGames.SM.Construction.DeliverForge

open CryptoGames.SM
open CryptoGames.SM.Engine
open CryptoGames.SM.Construction
open CryptoGames.SM.Construction.AuthL9
open CryptoGames.SM.Construction.AuthL10
open CryptoGames.SM.Construction.DeliverForge.AuthL10DF
open CryptoGames.LibsignalSM.Proofs.Refinement

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

namespace AuthL10ShiftedPaper

omit [SampleableType KC] in
theorem startSendP_coins_DFShiftedPaper_le (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δ_off : ℕ) (b_auth : Bool) (qep l t : ℕ)
    (hvalid : SM.lastLeakGuessAdmissible (2 + Δ_off) (some (l - 1)) t = true)
    (P : Party) (m_msg : M) (bad : Bool)
    (k : Option (Header T × E) → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T} {esP : EStateP Γ T Sig SS RS M E K}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp)
    (ih : ∀ r esS' sc' esP' sp',
      Sync10ShiftedPaper prng Δ_off l t esS' sc' esP' sp' →
      𝒟[runRDFShiftedPaper cka prng fs Δ_off b_auth qep l t (k r) esS' sc'] {true} ≤
        𝒟[runRDFShifted10Paper cka prng fs Δ_off b_auth qep l t (k r) esP' sp'] {true})
    (coins : CCoins) (sc' : CKA.GameState Γ T)
    (hsend : P.sendsIn (esS.g.epoch P + 1) = true)
    (hnot_tH : ((some (l - 1)).isSome &&
      decide (esS.g.epoch P + 1 = (⟨true, some (l - 1), t⟩ : Mode).tH)) = false)
    (hb_sc' : sc'.b = true)
    (hcka' : localCKA ⟨true, some (l - 1), t⟩ 1 (esS.g.epoch P) = false →
      sc'.st P = (cka.send (esP.g.st P).γ coins).1 ∧ sc'.epoch P = esS.g.epoch P + 1 ∧
      sc'.st P.other = (esP.g.st P.other).γ ∧ sc'.epoch P.other = esS.g.epoch P ∧
      sc'.lastMsg = some (cka.send (esP.g.st P).γ coins).2.1) :
    let mo : Mode := ⟨true, some (l - 1), t⟩
    let m := esS.g.epoch P + 1
    let c_cka := cka.send (esP.g.st P).γ coins
    let p := prng.up (esS.g.st P).root c_cka.2.2
    let resC : Option (Option Γ × T × Sig × SS) × CKAStateShifted Γ T I :=
      (some (if localCKA mo 1 m then some c_cka.1 else none, c_cka.2.1, p.1, fs.initSender p.2),
        { base := { cache := Function.update esS.h.base.cache m (some (c_cka.2.1, c_cka.2.2)) }
          γPre := if m + 1 ≤ l then Function.update esS.h.γPre P (some c_cka.1) else esS.h.γPre })
    let outC := postSendCShiftedPaper fs Δ_off P m_msg bad esS resC
    𝒟[runRDFShiftedPaper cka prng fs Δ_off b_auth qep l t (k outC.1) outC.2 sc'] {true} ≤
      𝒟[(simulateQ (pImpl prng)
          ((startSendP_body cka prng fs mo m (esP.g.st P).γ (esP.g.st P).root coins).run
            esP.h)).run sp >>=
        fun out =>
          let outP := postSendP fs Δ_off P m_msg bad esP out.1
          runRDFShifted10Paper cka prng fs Δ_off b_auth qep l t (k outP.1) outP.2 out.2]
        {true} := by
  intro mo m c_cka p resC outC
  have htL_eq : mo.tL = some (l - 1) := rfl
  have htStar_eq : mo.tStar = t := rfl
  change (mo.tL.isSome && decide (esS.g.epoch P + 1 = mo.tH)) = false at hnot_tH
  obtain ⟨hO_ep, hmax0, hroot0⟩ := hS.ping_pong_synced P hsend
  have hroot_max : (esS.g.st (Party.senderOf (max (esS.g.epoch .A) (esS.g.epoch .B)))).root =
      (esS.g.st P).root := by
    rcases party_eq_or_eq_other (Party.senderOf (max (esS.g.epoch .A) (esS.g.epoch .B))) P with
      hEq | hEq
    · rw [hEq]
    · rw [hEq, hroot0]
  by_cases hgt_star : mo.tStar < m
  · have hkr0 : knownRoot mo (esS.g.epoch P) = true := by
      simp [knownRoot, show mo.tStar ≤ esS.g.epoch P by omega]
    have hkr_m : knownRoot mo m = true := by
      simp [knownRoot, show mo.tStar ≤ m by omega]
    have hrootP0 : (esP.g.st P).root = some (esS.g.st P).root := by
      rw [hS.root_P P, hkr0]; rfl
    let σP' := if knownRoot mo m then some p.1 else none
    let resP : Option (Γ × T × Option Sig × SS) × PRNGState T Sig K :=
      (some (c_cka.1, c_cka.2.1, σP', fs.initSender p.2),
        { cache := Function.update esP.h.cache m (some (c_cka.2.1, σP', p.2)) })
    have hP : (simulateQ (pImpl prng)
        ((startSendP_body cka prng fs mo m (esP.g.st P).γ (esP.g.st P).root coins).run
          esP.h)).run sp =
        pure (resP, sp) := by
      simp [startSendP_body, rootPRNG, hgt_star, hrootP0, hkr_m, c_cka, p, σP', resP,
        StateT.run_pure, StateT.run_modify, simulateQ_pure]
    rw [hP, pure_bind]
    exact ih_postSend_new_DFShiftedPaper cka prng fs Δ_off b_auth qep l t P m_msg bad k hS ih
      c_cka.1 c_cka.2.1 c_cka.2.2 sc' sp hsend hb_sc' hS.b_P hcka' (fun h => by omega)
      (fun h => by omega) (fun h => by omega)
  · by_cases heq_star : m = mo.tStar
    · have hkr_m : knownRoot mo m = true := by
        simp [knownRoot, heq_star]
      have hlt0 : max (esS.g.epoch .A) (esS.g.epoch .B) < t := by omega
      have hnot_lt0 :
          ((some (l - 1)).isSome && decide (max (esS.g.epoch .A) (esS.g.epoch .B) < mo.tH)) =
            false := by
        rw [hmax0]
        have htH_le := tH_le_tStar_of_validGuess mo Δ_off hvalid (by simp [htL_eq])
        simp only [htL_eq, Option.isSome_some, Bool.true_and,
          decide_eq_false_iff_not] at hnot_tH ⊢
        omega
      obtain ⟨hσ, hcorr, hprng, _⟩ := hS.baseSync.prng_after_tH hlt0 hnot_lt0
      change sp.σ = (esS.g.st (Party.senderOf (max (esS.g.epoch .A) (esS.g.epoch .B)))).root at hσ
      rw [hroot_max] at hσ
      have hnot_tH_star : ¬(mo.tL.isSome = true ∧ mo.tStar = mo.tH) := by
        rw [← heq_star]
        simpa [m, Bool.and_eq_false_iff, decide_eq_false_iff_not] using hnot_tH
      let σP' := if knownRoot mo m then some p.1 else none
      let resP : Option (Γ × T × Option Sig × SS) × PRNGState T Sig K :=
        (some (c_cka.1, c_cka.2.1, σP', fs.initSender p.2),
          { cache := Function.update esP.h.cache m (some (c_cka.2.1, σP', p.2)) })
      let sp' : PRFPRNG.GameState Sig I K := { sp with prf := true }
      have hP : (simulateQ (pImpl prng)
          ((startSendP_body cka prng fs mo m (esP.g.st P).γ (esP.g.st P).root coins).run
            esP.h)).run sp =
          pure (resP, sp') := by
        simp [startSendP_body, rootPRNG, heq_star, hnot_tH_star,
          liftP, PRFPRNG.challPrfQuery, pImpl, PRFPRNG.oracleImpl, PRFPRNG.challPrfImpl,
          knownRoot, hcorr, hprng, hS.b_P, hσ, c_cka, p, σP', resP, sp',
          simulateQ_bind, simulateQ_query, simulateQ_pure,
          map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify, bind_assoc]
      rw [hP, pure_bind]
      exact ih_postSend_new_DFShiftedPaper cka prng fs Δ_off b_auth qep l t P m_msg bad k hS ih
        c_cka.1 c_cka.2.1 c_cka.2.2 sc' sp' hsend hb_sc' hS.b_P hcka' (fun h => by omega)
        (fun h => by omega) (fun _ _ => ⟨hσ, hcorr, hprng⟩)
    · have hlt_star : m < mo.tStar := by omega
      have hlt0 : max (esS.g.epoch .A) (esS.g.epoch .B) < t := by omega
      by_cases hlt_tH : (mo.tL.isSome && decide (m < mo.tH)) = true
      · have hkr_m : knownRoot mo m = true := by
          simp [knownRoot, hlt_tH]
        have hlt_tH0 :
            ((some (l - 1)).isSome && decide (max (esS.g.epoch .A) (esS.g.epoch .B) < mo.tH)) =
              true := by
          rw [hmax0]
          simp only [htL_eq, Bool.and_eq_true, decide_eq_true_eq] at hlt_tH ⊢
          exact ⟨hlt_tH.1, by omega⟩
        obtain ⟨hσ, hcorr, hprng, hprf⟩ := hS.baseSync.prng_before_tH hlt0 hlt_tH0
        change sp.σ = (esS.g.st (Party.senderOf (max (esS.g.epoch .A) (esS.g.epoch .B)))).root at hσ
        rw [hroot_max] at hσ
        let σP' := if knownRoot mo m then some p.1 else none
        let resP : Option (Γ × T × Option Sig × SS) × PRNGState T Sig K :=
          (some (c_cka.1, c_cka.2.1, σP', fs.initSender p.2),
            { cache := Function.update esP.h.cache m (some (c_cka.2.1, σP', p.2)) })
        let sp' : PRFPRNG.GameState Sig I K := { sp with σ := p.1, corr := true }
        have hP : (simulateQ (pImpl prng)
            ((startSendP_body cka prng fs mo m (esP.g.st P).γ (esP.g.st P).root coins).run
              esP.h)).run sp =
            pure (resP, sp') := by
          simp [startSendP_body, rootPRNG, processCorr, hgt_star, heq_star,
            show (mo.tL.isSome && (m = mo.tH)) = false by simpa [m] using hnot_tH,
            show (mo.tL.isSome && (m < mo.tH)) = true by simpa [m] using hlt_tH,
            liftP, PRFPRNG.processQuery, PRFPRNG.corrQuery, pImpl, PRFPRNG.oracleImpl,
            PRFPRNG.processImpl, PRFPRNG.corrImpl, PRFPRNG.samIfNec,
            hcorr, hprng, hprf, hσ, hkr_m, c_cka, p, σP', resP, sp',
            simulateQ_bind, simulateQ_query, simulateQ_pure,
            map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify]
        rw [hP, pure_bind]
        exact ih_postSend_new_DFShiftedPaper cka prng fs Δ_off b_auth qep l t P m_msg bad k hS ih
          c_cka.1 c_cka.2.1 c_cka.2.2 sc' sp' hsend hb_sc' hS.b_P hcka'
          (fun _ _ => ⟨rfl, rfl, hprng, hprf⟩)
          (fun _ h => by
            change (mo.tL.isSome && decide (m < mo.tH)) = false at h
            rw [hlt_tH] at h; cases h)
          (fun h => by omega)
      · simp only [Bool.not_eq_true] at hlt_tH
        have hkr_m : knownRoot mo m = false := by
          simp [knownRoot, hlt_tH, show ¬ mo.tStar ≤ m by omega]
        have hlt_tH0 :
            ((some (l - 1)).isSome && decide (max (esS.g.epoch .A) (esS.g.epoch .B) < mo.tH)) =
              false := by
          rw [hmax0]
          simp only [htL_eq, Option.isSome_some, Bool.true_and,
            decide_eq_false_iff_not] at hnot_tH hlt_tH ⊢
          change ¬ (esS.g.epoch P + 1 < mo.tH) at hlt_tH
          omega
        obtain ⟨hσ, hcorr, hprng, hprf0⟩ := hS.baseSync.prng_after_tH hlt0 hlt_tH0
        change sp.σ = (esS.g.st (Party.senderOf (max (esS.g.epoch .A) (esS.g.epoch .B)))).root at hσ
        rw [hroot_max] at hσ
        have hprf : sp.prf = false :=
          hprf0 (by change max (esS.g.epoch .A) (esS.g.epoch .B) + 1 < t; rw [hmax0]; omega)
        let σP' := if knownRoot mo m then some p.1 else none
        let resP : Option (Γ × T × Option Sig × SS) × PRNGState T Sig K :=
          (some (c_cka.1, c_cka.2.1, σP', fs.initSender p.2),
            { cache := Function.update esP.h.cache m (some (c_cka.2.1, σP', p.2)) })
        let sp' : PRFPRNG.GameState Sig I K := { sp with σ := p.1, corr := false }
        have hP : (simulateQ (pImpl prng)
            ((startSendP_body cka prng fs mo m (esP.g.st P).γ (esP.g.st P).root coins).run
              esP.h)).run sp =
            pure (resP, sp') := by
          simp [startSendP_body, rootPRNG, hgt_star, heq_star,
            show (mo.tL.isSome && (m = mo.tH)) = false by simpa [m] using hnot_tH,
            show (mo.tL.isSome && (m < mo.tH)) = false by simpa [m] using hlt_tH,
            liftP, PRFPRNG.processQuery, pImpl, PRFPRNG.oracleImpl,
            PRFPRNG.processImpl, PRFPRNG.samIfNec,
            hcorr, hprng, hprf, hσ, hkr_m, c_cka, p, σP', resP, sp',
            simulateQ_bind, simulateQ_query, simulateQ_pure,
            map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify]
        rw [hP, pure_bind]
        exact ih_postSend_new_DFShiftedPaper cka prng fs Δ_off b_auth qep l t P m_msg bad k hS ih
          c_cka.1 c_cka.2.1 c_cka.2.2 sc' sp' hsend hb_sc' hS.b_P hcka'
          (fun _ h => by
            change (mo.tL.isSome && decide (m < mo.tH)) = true at h
            rw [hlt_tH] at h; cases h)
          (fun _ _ => ⟨rfl, rfl, hprng, fun _ => hprf⟩)
          (fun h => by omega)
omit [SampleableType KC] in
theorem startSendP_chall_DFShiftedPaper_le (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δ_off : ℕ) (b_auth : Bool) (qep l t : ℕ)
    (hvalid : SM.lastLeakGuessAdmissible (2 + Δ_off) (some (l - 1)) t = true)
    (P : Party) (m_msg : M)
    (k : Option (Header T × E) → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T} {esP : EStateP Γ T Sig SS RS M E K}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp)
    (ih : ∀ r esS' sc' esP' sp',
      Sync10ShiftedPaper prng Δ_off l t esS' sc' esP' sp' →
      𝒟[runRDFShiftedPaper cka prng fs Δ_off b_auth qep l t (k r) esS' sc'] {true} ≤
        𝒟[runRDFShifted10Paper cka prng fs Δ_off b_auth qep l t (k r) esP' sp'] {true})
    (coins : CCoins) (sc' : CKA.GameState Γ T)
    (hsend : P.sendsIn (esS.g.epoch P + 1) = true)
    (htH : ((some (l - 1)).isSome &&
      decide (esS.g.epoch P + 1 = (⟨true, some (l - 1), t⟩ : Mode).tH)) = true)
    (hb_sc' : sc'.b = true)
    (hcka' : localCKA ⟨true, some (l - 1), t⟩ 1 (esS.g.epoch P) = false →
      sc'.st P = (cka.send (esP.g.st P).γ coins).1 ∧ sc'.epoch P = esS.g.epoch P + 1 ∧
      sc'.st P.other = (esP.g.st P.other).γ ∧ sc'.epoch P.other = esS.g.epoch P ∧
      sc'.lastMsg = some (cka.send (esP.g.st P).γ coins).2.1) :
    let mo : Mode := ⟨true, some (l - 1), t⟩
    let m := esS.g.epoch P + 1
    let c_cka := cka.send (esP.g.st P).γ coins
    𝒟[($ᵗ I : ProbComp I) >>= fun I₁ =>
        let p := prng.up (esS.g.st P).root I₁
        let resC : Option (Option Γ × T × Sig × SS) × CKAStateShifted Γ T I :=
          (some (if localCKA mo 1 m then some c_cka.1 else none, c_cka.2.1, p.1,
            fs.initSender p.2),
            { base := { cache := Function.update esS.h.base.cache m (some (c_cka.2.1, I₁)) }
              γPre := if m + 1 ≤ l then Function.update esS.h.γPre P (some c_cka.1)
                else esS.h.γPre })
        let outC := postSendCShiftedPaper fs Δ_off P m_msg false esS resC
        runRDFShiftedPaper cka prng fs Δ_off b_auth qep l t (k outC.1) outC.2 sc'] {true} ≤
      𝒟[(simulateQ (pImpl prng)
          ((startSendP_body cka prng fs mo m (esP.g.st P).γ (esP.g.st P).root coins).run
            esP.h)).run sp >>=
        fun out =>
          let outP := postSendP fs Δ_off P m_msg false esP out.1
          runRDFShifted10Paper cka prng fs Δ_off b_auth qep l t (k outP.1) outP.2 out.2]
        {true} := by
  intro mo m c_cka
  have htL_eq : mo.tL = some (l - 1) := rfl
  have htStar_eq : mo.tStar = t := rfl
  change (mo.tL.isSome && decide (esS.g.epoch P + 1 = mo.tH)) = true at htH
  obtain ⟨hO_ep, hmax0, hroot0⟩ := hS.ping_pong_synced P hsend
  have hroot_max : (esS.g.st (Party.senderOf (max (esS.g.epoch .A) (esS.g.epoch .B)))).root =
      (esS.g.st P).root := by
    rcases party_eq_or_eq_other (Party.senderOf (max (esS.g.epoch .A) (esS.g.epoch .B))) P with
      hEq | hEq
    · rw [hEq]
    · rw [hEq, hroot0]
  have htH_split : mo.tL.isSome = true ∧ m = mo.tH := by
    simpa [m, Bool.and_eq_true, decide_eq_true_eq] using htH
  obtain ⟨htL_some, hm_tH⟩ := htH_split
  have hm_le_star : m ≤ mo.tStar := by
    have := tH_le_tStar_of_validGuess mo Δ_off hvalid htL_some
    omega
  have hgt_star : ¬ mo.tStar < m := by omega
  have hlt0 : max (esS.g.epoch .A) (esS.g.epoch .B) < t := by omega
  have hlt_tH0 :
      ((some (l - 1)).isSome && decide (max (esS.g.epoch .A) (esS.g.epoch .B) < mo.tH)) = true := by
    rw [hmax0]
    simp [show esS.g.epoch P < mo.tH by omega]
  obtain ⟨hσ, hcorr, hprng, hprf⟩ := hS.baseSync.prng_before_tH hlt0 hlt_tH0
  change sp.σ = (esS.g.st (Party.senderOf (max (esS.g.epoch .A) (esS.g.epoch .B)))).root at hσ
  rw [hroot_max] at hσ
  by_cases heq_star : m = mo.tStar
  · have hkr_m : knownRoot mo m = true := by
      simp [knownRoot, heq_star]
    have hstar_eq_tH : mo.tStar = mo.tH := heq_star.symm.trans hm_tH
    have hP : (simulateQ (pImpl prng)
        ((startSendP_body cka prng fs mo m (esP.g.st P).γ (esP.g.st P).root coins).run
          esP.h)).run sp =
        ($ᵗ I : ProbComp I) >>= fun I₁ =>
          let p := prng.up (esS.g.st P).root I₁
          let σP' := if knownRoot mo m then some p.1 else none
          pure ((some (c_cka.1, c_cka.2.1, σP', fs.initSender p.2),
            { cache := Function.update esP.h.cache m (some (c_cka.2.1, σP', p.2)) }),
            { sp with σ := p.1, corr := true, prng := true }) := by
      simp [startSendP_body, rootPRNG, heq_star, htL_some, hstar_eq_tH,
        liftP, PRFPRNG.challPrngQuery, PRFPRNG.corrQuery, pImpl, PRFPRNG.oracleImpl,
        PRFPRNG.challPrngImpl, PRFPRNG.corrImpl, PRFPRNG.samIfNec,
        knownRoot, hprf, hS.b_P, hσ, c_cka,
        simulateQ_bind, simulateQ_query, simulateQ_pure,
        map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify, bind_assoc]
    rw [hP, bind_assoc]
    refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
      fun I₁ _ => ?_
    rw [pure_bind]
    exact ih_postSend_new_DFShiftedPaper cka prng fs Δ_off b_auth qep l t P m_msg false k hS ih
      c_cka.1 c_cka.2.1 I₁ sc'
      { sp with σ := (prng.up (esS.g.st P).root I₁).1, corr := true, prng := true }
      hsend hb_sc' hS.b_P hcka' (fun h => by omega) (fun h => by omega)
      (fun _ h => by
        change ((some (l - 1)).isSome && decide (mo.tStar = mo.tH)) = false at h
        simp [hstar_eq_tH] at h)
  · have hlt_star : m < mo.tStar := by omega
    have hlt_tH : (mo.tL.isSome && decide (m < mo.tH)) = false := by
      simp [hm_tH]
    have hkr_m : knownRoot mo m = false := by
      simp [knownRoot, hlt_tH, show ¬ mo.tStar ≤ m by omega]
    have hP : (simulateQ (pImpl prng)
        ((startSendP_body cka prng fs mo m (esP.g.st P).γ (esP.g.st P).root coins).run
          esP.h)).run sp =
        ($ᵗ I : ProbComp I) >>= fun I₁ =>
          let p := prng.up (esS.g.st P).root I₁
          let σP' := if knownRoot mo m then some p.1 else none
          pure ((some (c_cka.1, c_cka.2.1, σP', fs.initSender p.2),
            { cache := Function.update esP.h.cache m (some (c_cka.2.1, σP', p.2)) }),
            { sp with σ := p.1, corr := false }) := by
      simp [startSendP_body, rootPRNG, hgt_star, heq_star, htL_some, ← hm_tH,
        liftP, PRFPRNG.processQuery, pImpl, PRFPRNG.oracleImpl,
        PRFPRNG.processImpl, PRFPRNG.samIfNec,
        hprng, hprf, hσ, hkr_m, c_cka,
        simulateQ_bind, simulateQ_query, simulateQ_pure,
        map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify, bind_assoc]
    rw [hP, bind_assoc]
    refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
      fun I₁ _ => ?_
    rw [pure_bind]
    exact ih_postSend_new_DFShiftedPaper cka prng fs Δ_off b_auth qep l t P m_msg false k hS ih
      c_cka.1 c_cka.2.1 I₁ sc' { sp with σ := (prng.up (esS.g.st P).root I₁).1, corr := false }
      hsend hb_sc' hS.b_P hcka'
      (fun _ h => by
        change (mo.tL.isSome && decide (m < mo.tH)) = true at h
        rw [hlt_tH] at h; cases h)
      (fun _ _ => ⟨rfl, rfl, hprng, fun _ => hprf⟩)
      (fun h => by omega)
theorem step_transmitE_new_epoch_DFShiftedPaper_le (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δ_off : ℕ) (b_auth : Bool) (qep l t : ℕ)
    (hl : 1 ≤ l) (hvalid : SM.lastLeakGuessAdmissible (2 + Δ_off) (some (l - 1)) t = true)
    (P : Party) (m_msg : M) (r : Option CCoins)
    (esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I))
    (sc : CKA.GameState Γ T) (esP : EStateP Γ T Sig SS RS M E K)
    (sp : PRFPRNG.GameState Sig I K)
    (k : Option (Header T × E) → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (ih : ∀ r esS' sc' esP' sp',
      Sync10ShiftedPaper prng Δ_off l t esS' sc' esP' sp' →
      𝒟[runRDFShiftedPaper cka prng fs Δ_off b_auth qep l t (k r) esS' sc'] {true} ≤
        𝒟[runRDFShifted10Paper cka prng fs Δ_off b_auth qep l t (k r) esP' sp'] {true})
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp)
    (hwin0 : esS.g.win = false)
    (hsend : P.sendsIn (esS.g.epoch P + 1) = true) :
    𝒟[stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
        (.inr (.inl (.inl (.inl (.inl (.inl (P, m_msg, r))))))) esS sc >>=
      fun res => runRDFShiftedPaper cka prng fs Δ_off b_auth qep l t (k res.1.1) res.1.2 res.2]
        {true} ≤
    𝒟[stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
        (.inr (.inl (.inl (.inl (.inl (.inl (P, m_msg, r))))))) esP sp >>=
      fun res => runRDFShifted10Paper cka prng fs Δ_off b_auth qep l t
        (k res.1.1) res.1.2 res.2] {true} := by
  let mo : Mode := ⟨true, some (l - 1), t⟩
  have hP_eq : stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
      (.inr (.inl (.inl (.inl (.inl (.inl (P, m_msg, r))))))) esP sp =
      stepP cka prng fs Δ_off qep mo (.inr (.inl (.inl (.inl (.inl (P, m_msg, r)))))) esP sp := rfl
  have hwin : esP.g.win = esS.g.win := eraseSt_win hS.g_eq
  have hepP : esP.g.epoch P = esS.g.epoch P := congrFun (eraseSt_epoch hS.g_eq) P
  by_cases hqep : qep < esS.g.epoch P + 1
  · have hqep_le : qep ≤ esS.g.epoch P := by omega
    have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
        (.inr (.inl (.inl (.inl (.inl (.inl (P, m_msg, r))))))) esS sc =
        pure ((none, esS), sc) := by
      simp [stepCDFShiftedPaper, implEDFG, transmitE, SM.GameState.epMgmt, hS.abort_C,
        hwin0, hsend, hqep_le]
    have hP : stepP cka prng fs Δ_off qep mo
        (.inr (.inl (.inl (.inl (.inl (P, m_msg, r)))))) esP sp =
        pure ((none, esP), sp) := by
      simp [stepP, implE, transmitE, SM.GameState.epMgmt, hS.abort_P, hwin, hwin0, hepP,
        hsend, hqep_le]
    rw [hC, hP_eq, hP, pure_bind, pure_bind]
    exact ih none esS sc esP sp hS
  · have hld : mo.policy.leakDoom esP.g (epMgmtNew esP.g (2 + Δ_off) P r.isSome) =
        mo.policy.leakDoom esS.g (epMgmtNew esS.g (2 + Δ_off) P r.isSome) :=
      eraseSt_leakDoom hS.g_eq
        (eraseSt_epMgmtNew hS.g_eq (2 + Δ_off) P r.isSome) mo.policy
    by_cases hdoom : mo.policy.leakDoom esS.g (epMgmtNew esS.g (2 + Δ_off) P r.isSome)
    · have hdoom' :
          (⟨true, some (l - 1), t⟩ : Policy).leakDoom esS.g
            (epMgmtNew esS.g (2 + Δ_off) P r.isSome) = true := hdoom
      have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
          (.inr (.inl (.inl (.inl (.inl (.inl (P, m_msg, r))))))) esS sc =
          pure ((none, { esS with abort := true }), sc) := by
        simp [stepCDFShiftedPaper, implEDFG, transmitE, abortE,
          epMgmt_eq_epMgmtNew esS.g (2 + Δ_off) qep P r.isSome hsend hqep,
          hS.abort_C, hwin0, hdoom', StateT.run_modify]
      rw [hC, pure_bind]
      exact runRDFShiftedPaper_abort_apply_true_le cka prng fs Δ_off b_auth qep l t (k none) rfl _
    · simp only [Bool.not_eq_true] at hdoom
      rw [stepCDFShiftedPaper_transmit_new cka prng fs Δ_off b_auth qep l t P m_msg r esS sc
          hS.abort_C hwin0 (hS.id_C P) (hS.tcur_C P) hsend hqep hdoom,
        hP_eq,
        stepP_transmit_new cka prng fs Δ_off qep mo P m_msg r esP sp hS.abort_P
          (by rw [hwin, hwin0]) (hS.id_P P) (by rw [hS.tcur_P P, hepP])
          (by rw [hepP]; exact hsend) (by rw [hepP]; exact hqep) (by rw [hld, hdoom]),
        bind_assoc, bind_assoc]
      let m := esS.g.epoch P + 1
      have htH_mo : mo.tH = l + 1 := by
        change healEpoch (some (l - 1)) = l + 1
        simp [healEpoch]; omega
      have hloc_eq : ∀ e, localCKA mo 1 e = decide (l + 2 ≤ e) := fun e => by
        change (Option.isNone (some (l - 1)) || decide (mo.tH + 1 ≤ e)) = decide (l + 2 ≤ e)
        rw [htH_mo]; rfl
      by_cases hloc : localCKA mo 1 (esS.g.epoch P)
      · have hloc_m : localCKA mo 1 m = true :=
          localCKA_mono mo 1 hloc (Nat.le_succ _)
        have hloc_le : l + 2 ≤ esS.g.epoch P := by
          rw [hloc_eq, decide_eq_true_eq] at hloc
          exact hloc
        have hnot_pre : ¬ (m + 1 ≤ l) := by omega
        have hnot_tH : ((some (l - 1)).isSome && decide (esS.g.epoch P + 1 = mo.tH)) = false := by
          rw [htH_mo]; simp; omega
        have hγC : (esS.g.st P).γ = some (esP.g.st P).γ := by
          rw [hS.γ_C P, hloc]; rfl
        cases r with
        | some coins =>
          let c_cka := cka.send (esP.g.st P).γ coins
          let p := prng.up (esS.g.st P).root c_cka.2.2
          let resC : Option (Option Γ × T × Sig × SS) × CKAStateShifted Γ T I :=
            (some (if localCKA mo 1 m then some c_cka.1 else none, c_cka.2.1, p.1,
              fs.initSender p.2),
              { base :=
                  { cache := Function.update esS.h.base.cache m (some (c_cka.2.1, c_cka.2.2)) }
                γPre := if m + 1 ≤ l then Function.update esS.h.γPre P (some c_cka.1)
                  else esS.h.γPre })
          have hC : (simulateQ (cImpl cka 1 (l + 1))
              (((hooksCKAShifted cka prng fs l (tStarHook b_auth t)).startSend
                (epMgmtNew esS.g (2 + Δ_off) P true)
                P (esS.g.epoch P + 1) (esS.g.st P).γ (esS.g.st P).root (some coins)).run
                esS.h)).run sc =
              pure (resC, sc) := by
            simp [hooksCKAShifted, cacheCShifted, hγC, hloc_m,
              show ¬(esS.g.epoch P + 1 < l) by omega, m, c_cka, p, resC,
              StateT.run_pure, StateT.run_modify, simulateQ_pure]
          simp only [Option.isSome_some]
          rw [hC, pure_bind, pure_bind, hepP, startSendP_some_eq]
          simpa [m, c_cka, p, resC] using
            startSendP_coins_DFShiftedPaper_le cka prng fs Δ_off b_auth qep l t hvalid P m_msg true
              k hS ih coins sc hsend hnot_tH hS.b_C (fun h => by rw [h] at hloc; cases hloc)
        | none =>
          have hC : (simulateQ (cImpl cka 1 (l + 1))
              (((hooksCKAShifted cka prng fs l (tStarHook b_auth t)).startSend
                (epMgmtNew esS.g (2 + Δ_off) P false)
                P (esS.g.epoch P + 1) (esS.g.st P).γ (esS.g.st P).root none).run esS.h)).run sc =
              ($ᵗ CCoins : ProbComp CCoins) >>= fun coins =>
                let c_cka := cka.send (esP.g.st P).γ coins
                let p := prng.up (esS.g.st P).root c_cka.2.2
                pure ((some (if localCKA mo 1 m then some c_cka.1 else none, c_cka.2.1, p.1,
                  fs.initSender p.2),
                  { base :=
                      { cache := Function.update esS.h.base.cache m (some (c_cka.2.1, c_cka.2.2)) }
                    γPre := if m + 1 ≤ l then Function.update esS.h.γPre P (some c_cka.1)
                      else esS.h.γPre }), sc) := by
            simp [hooksCKAShifted, cacheCShifted, hγC, hloc_m,
              show ¬(esS.g.epoch P + 1 < l) by omega, m,
              StateT.run_bind, StateT.run_pure, StateT.run_modify,
              simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp, bind_assoc]
          simp only [Option.isSome_none]
          rw [hC, hepP, startSendP_none_eq, bind_assoc, bind_assoc]
          refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
            fun coins _ => ?_
          rw [pure_bind, pure_bind]
          exact startSendP_coins_DFShiftedPaper_le cka prng fs Δ_off b_auth qep l t hvalid P m_msg
            false k hS ih coins sc hsend hnot_tH hS.b_C (fun h => by rw [h] at hloc; cases hloc)
      · simp only [Bool.not_eq_true] at hloc
        have hγC : (esS.g.st P).γ = none := by
          rw [hS.γ_C P, hloc]; rfl
        obtain ⟨hsc_stP, hsc_epP⟩ := hS.cka_st P (Or.inl hloc)
        obtain ⟨hsc_stO, hsc_epO⟩ := hS.cka_st P.other (Or.inr (by simpa using hloc))
        obtain ⟨hO_ep, _, _⟩ := hS.ping_pong_synced P hsend
        have hcanS : sc.canSend P = true := by
          simp [CKA.GameState.canSend, hsc_epP, hsc_epO, hO_ep, hsend]
        cases r with
        | some coins =>
          by_cases hbad_ok : l < esS.g.epoch P + 2
          · have hC : (simulateQ (cImpl cka 1 (l + 1))
                (((hooksCKAShifted cka prng fs l (tStarHook b_auth t)).startSend
                  (epMgmtNew esS.g (2 + Δ_off) P true)
                  P (esS.g.epoch P + 1) (esS.g.st P).γ (esS.g.st P).root (some coins)).run
                  esS.h)).run sc =
                pure ((none, esS.h), sc) := by
              simp [hooksCKAShifted, liftCShifted, CKA.sendWithAdversaryCoinsQuery, cImpl, CKA.oracleImpl,
                CKA.sendWithAdversaryCoinsImpl, hγC, hcanS, hsc_epP, hbad_ok,
                simulateQ_bind, simulateQ_query, simulateQ_pure,
                map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure]
            simp only [Option.isSome_some]
            rw [hC, pure_bind, pure_bind]
            exact runRDFShiftedPaper_abort_apply_true_le cka prng fs Δ_off b_auth qep l t (k none)
              rfl _
          · have hpre : m + 1 ≤ l := by omega
            have hnot_tH :
                ((some (l - 1)).isSome && decide (esS.g.epoch P + 1 = mo.tH)) = false := by
              rw [htH_mo]; simp; omega
            have hloc_m : localCKA mo 1 m = false := by
              rw [hloc_eq, decide_eq_false_iff_not]; omega
            let c_cka := cka.send (esP.g.st P).γ coins
            let p := prng.up (esS.g.st P).root c_cka.2.2
            let sc' := sc.afterSend P c_cka.1 c_cka.2.1
            have hall : (sc.afterSend P c_cka.1 c_cka.2.1).allowCorr (l + 1) = true :=
              allowCorr_afterSend_of_le c_cka.1 c_cka.2.1
                (by rw [hsc_epP, hsc_epO, hO_ep]) (by rw [hsc_epP]; exact hpre)
            have hstP' : (sc.afterSend P c_cka.1 c_cka.2.1).st P = c_cka.1 := by
              simp [CKA.GameState.afterSend]
            let resC : Option (Option Γ × T × Sig × SS) × CKAStateShifted Γ T I :=
              (some (if localCKA mo 1 m then some c_cka.1 else none, c_cka.2.1, p.1,
                fs.initSender p.2),
                { base :=
                    { cache := Function.update esS.h.base.cache m (some (c_cka.2.1, c_cka.2.2)) }
                  γPre := if m + 1 ≤ l then Function.update esS.h.γPre P (some c_cka.1)
                    else esS.h.γPre })
            have hC : (simulateQ (cImpl cka 1 (l + 1))
                (((hooksCKAShifted cka prng fs l (tStarHook b_auth t)).startSend
                  (epMgmtNew esS.g (2 + Δ_off) P true)
                  P (esS.g.epoch P + 1) (esS.g.st P).γ (esS.g.st P).root (some coins)).run
                  esS.h)).run sc =
                pure (resC, sc') := by
              simp [hooksCKAShifted, cacheCShifted, setγPreShifted, liftCShifted, CKA.sendWithAdversaryCoinsQuery,
                CKA.corrQuery, cImpl, CKA.oracleImpl, CKA.sendWithAdversaryCoinsImpl, CKA.corrImpl,
                hγC, hcanS, hsc_epP, hsc_stP, hbad_ok,
                show ¬(l < esS.g.epoch P) by omega,
                show esS.g.epoch P + 1 < l by omega, hall, hstP', hloc_m,
                m, c_cka, p, sc', resC, simulateQ_bind, simulateQ_query, simulateQ_pure,
                map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify,
                StateT.run_set]
            simp only [Option.isSome_some]
            rw [hC, pure_bind, pure_bind, hepP, startSendP_some_eq]
            refine startSendP_coins_DFShiftedPaper_le cka prng fs Δ_off b_auth qep l t hvalid P
              m_msg true k hS ih coins sc' hsend hnot_tH hS.b_C fun _ => ?_
            simp [sc', c_cka, CKA.GameState.afterSend, Party.other_ne, hsc_epP, hsc_stO, hsc_epO,
              hO_ep]
        | none =>
          by_cases heq_tH : esS.g.epoch P = l
          · have htH : ((some (l - 1)).isSome && decide (esS.g.epoch P + 1 = mo.tH)) = true := by
              rw [htH_mo]; simp [heq_tH]
            have hloc_l1 : localCKA mo 1 (l + 1) = false := by
              rw [hloc_eq, decide_eq_false_iff_not]; omega
            have hC : (simulateQ (cImpl cka 1 (l + 1))
                (((hooksCKAShifted cka prng fs l (tStarHook b_auth t)).startSend
                  (epMgmtNew esS.g (2 + Δ_off) P false)
                  P (esS.g.epoch P + 1) (esS.g.st P).γ (esS.g.st P).root none).run
                  esS.h)).run sc =
                ($ᵗ CCoins : ProbComp CCoins) >>= fun coins => ($ᵗ I : ProbComp I) >>= fun I₁ =>
                  let c_cka := cka.send (esP.g.st P).γ coins
                  let p := prng.up (esS.g.st P).root I₁
                  pure ((some (if localCKA mo 1 m then some c_cka.1 else none, c_cka.2.1, p.1,
                    fs.initSender p.2),
                    { base := { cache := Function.update esS.h.base.cache m (some (c_cka.2.1, I₁)) }
                      γPre := if m + 1 ≤ l then Function.update esS.h.γPre P (some c_cka.1)
                        else esS.h.γPre }),
                    sc.afterSend P c_cka.1 c_cka.2.1) := by
              simp [hooksCKAShifted, cacheCShifted, liftCShifted, CKA.challQuery, cImpl,
                CKA.oracleImpl, CKA.challImpl, hγC, heq_tH, hcanS, hsc_epP, hsc_stP, hS.b_C,
                hloc_l1, m, simulateQ_bind, simulateQ_query, simulateQ_pure,
                map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify,
                StateT.run_set, StateT.run_lift, bind_assoc]
            simp only [Option.isSome_none]
            rw [hC, hepP, startSendP_none_eq, bind_assoc, bind_assoc]
            refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _
              (MeasurableSet.singleton true) fun coins _ => ?_
            rw [bind_assoc]
            have hstep := startSendP_chall_DFShiftedPaper_le cka prng fs Δ_off b_auth qep l t hvalid
              P m_msg k hS ih coins (sc.afterSend P (cka.send (esP.g.st P).γ coins).1
                (cka.send (esP.g.st P).γ coins).2.1)
              hsend htH hS.b_C (fun _ => by
                simp [CKA.GameState.afterSend, Party.other_ne, hsc_epP, hsc_stO, hsc_epO, hO_ep])
            simpa [pure_bind] using hstep
          · have hnot_tH :
                ((some (l - 1)).isSome && decide (esS.g.epoch P + 1 = mo.tH)) = false := by
              rw [htH_mo]; simp [heq_tH]
            have hC : (simulateQ (cImpl cka 1 (l + 1))
                (((hooksCKAShifted cka prng fs l (tStarHook b_auth t)).startSend
                  (epMgmtNew esS.g (2 + Δ_off) P false)
                  P (esS.g.epoch P + 1) (esS.g.st P).γ (esS.g.st P).root none).run
                  esS.h)).run sc =
                ($ᵗ CCoins : ProbComp CCoins) >>= fun coins =>
                  let c_cka := cka.send (esP.g.st P).γ coins
                  let p := prng.up (esS.g.st P).root c_cka.2.2
                  pure ((some (if localCKA mo 1 m then some c_cka.1 else none, c_cka.2.1, p.1,
                    fs.initSender p.2),
                    { base :=
                        { cache :=
                            Function.update esS.h.base.cache m (some (c_cka.2.1, c_cka.2.2)) }
                      γPre := if m + 1 ≤ l then Function.update esS.h.γPre P (some c_cka.1)
                        else esS.h.γPre }),
                    sc.afterSend P c_cka.1 c_cka.2.1) := by
              have hstP' : ∀ coins,
                  (sc.afterSend P (cka.send (esP.g.st P).γ coins).1
                    (cka.send (esP.g.st P).γ coins).2.1).st P =
                    (cka.send (esP.g.st P).γ coins).1 :=
                fun _ => by simp [CKA.GameState.afterSend]
              by_cases hfin : l + 2 ≤ m
              · have hloc_m : localCKA mo 1 m = true := by
                  rw [hloc_eq, decide_eq_true_eq]; exact hfin
                have hfin_sc : ∀ coins,
                    (sc.afterSend P (cka.send (esP.g.st P).γ coins).1
                      (cka.send (esP.g.st P).γ coins).2.1).finished 1 (l + 1) P = true :=
                  fun _ => finished_afterSend_of_ge _ _ (by rw [hsc_epP]; exact hfin)
                simp [hooksCKAShifted, cacheCShifted, liftCShifted, CKA.sendQuery, CKA.corrQuery,
                  cImpl, CKA.oracleImpl, CKA.sendImpl, CKA.corrImpl,
                  hγC, heq_tH, hcanS, hsc_epP, hsc_stP,
                  show l < esS.g.epoch P by omega,
                  show ¬(esS.g.epoch P + 1 < l) by omega, hfin_sc, hstP',
                  hloc_m, m, simulateQ_bind, simulateQ_query, simulateQ_pure,
                  map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify,
                  StateT.run_set, StateT.run_lift, bind_assoc]
              · have hloc_m : localCKA mo 1 m = false := by
                  rw [hloc_eq, decide_eq_false_iff_not]; exact hfin
                by_cases hpre : m + 1 ≤ l
                · have hall : ∀ coins,
                      (sc.afterSend P (cka.send (esP.g.st P).γ coins).1
                        (cka.send (esP.g.st P).γ coins).2.1).allowCorr (l + 1) = true :=
                    fun _ => allowCorr_afterSend_of_le _ _
                      (by rw [hsc_epP, hsc_epO, hO_ep]) (by rw [hsc_epP]; exact hpre)
                  simp [hooksCKAShifted, cacheCShifted, setγPreShifted, liftCShifted, CKA.sendQuery,
                    CKA.corrQuery, cImpl, CKA.oracleImpl, CKA.sendImpl, CKA.corrImpl,
                    hγC, heq_tH, hcanS, hsc_epP, hsc_stP,
                    show ¬(l < esS.g.epoch P) by omega,
                    show esS.g.epoch P + 1 < l by omega, hall, hstP', hloc_m, m,
                    simulateQ_bind, simulateQ_query, simulateQ_pure,
                    map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify,
                    StateT.run_set, StateT.run_lift, bind_assoc]
                · simp [hooksCKAShifted, cacheCShifted, liftCShifted, CKA.sendQuery,
                    cImpl, CKA.oracleImpl, CKA.sendImpl,
                    hγC, heq_tH, hcanS, hsc_epP, hsc_stP,
                    show ¬(l < esS.g.epoch P) by omega,
                    show ¬(esS.g.epoch P + 1 < l) by omega, hloc_m, m,
                    simulateQ_bind, simulateQ_query, simulateQ_pure,
                    map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify,
                    StateT.run_set, StateT.run_lift, bind_assoc]
            simp only [Option.isSome_none]
            rw [hC, hepP, startSendP_none_eq, bind_assoc, bind_assoc]
            refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _
              (MeasurableSet.singleton true) fun coins _ => ?_
            rw [pure_bind, pure_bind]
            refine startSendP_coins_DFShiftedPaper_le cka prng fs Δ_off b_auth qep l t hvalid P
              m_msg false k hS ih coins (sc.afterSend P (cka.send (esP.g.st P).γ coins).1
                (cka.send (esP.g.st P).γ coins).2.1)
              hsend hnot_tH hS.b_C fun _ => ?_
            simp [CKA.GameState.afterSend, Party.other_ne, hsc_epP, hsc_stO, hsc_epO, hO_ep]
theorem step_transmitE_DFShiftedPaper_le (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δ_off : ℕ) (b_auth : Bool) (qep l t : ℕ)
    (hl : 1 ≤ l) (hvalid : SM.lastLeakGuessAdmissible (2 + Δ_off) (some (l - 1)) t = true)
    (P : Party) (m_msg : M) (r : Option CCoins)
    (esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I))
    (sc : CKA.GameState Γ T) (esP : EStateP Γ T Sig SS RS M E K)
    (sp : PRFPRNG.GameState Sig I K)
    (k : Option (Header T × E) → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (ih : ∀ r esS' sc' esP' sp',
      Sync10ShiftedPaper prng Δ_off l t esS' sc' esP' sp' →
      𝒟[runRDFShiftedPaper cka prng fs Δ_off b_auth qep l t (k r) esS' sc'] {true} ≤
        𝒟[runRDFShifted10Paper cka prng fs Δ_off b_auth qep l t (k r) esP' sp'] {true})
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp) :
    𝒟[stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
        (.inr (.inl (.inl (.inl (.inl (.inl (P, m_msg, r))))))) esS sc >>=
      fun res => runRDFShiftedPaper cka prng fs Δ_off b_auth qep l t (k res.1.1) res.1.2 res.2]
        {true} ≤
    𝒟[stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
        (.inr (.inl (.inl (.inl (.inl (.inl (P, m_msg, r))))))) esP sp >>=
      fun res => runRDFShifted10Paper cka prng fs Δ_off b_auth qep l t
        (k res.1.1) res.1.2 res.2] {true} := by
  let mo : Mode := ⟨true, some (l - 1), t⟩
  have hP_eq : stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
      (.inr (.inl (.inl (.inl (.inl (.inl (P, m_msg, r))))))) esP sp =
      stepP cka prng fs Δ_off qep mo (.inr (.inl (.inl (.inl (.inl (P, m_msg, r)))))) esP sp := rfl
  have hwin : esP.g.win = esS.g.win := eraseSt_win hS.g_eq
  by_cases hwin0 : esS.g.win = true
  · have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
        (.inr (.inl (.inl (.inl (.inl (.inl (P, m_msg, r))))))) esS sc =
        pure ((none, esS), sc) := by
      simp [stepCDFShiftedPaper, implEDFG, transmitE, hS.abort_C, hwin0]
    have hP : stepP cka prng fs Δ_off qep mo
        (.inr (.inl (.inl (.inl (.inl (P, m_msg, r)))))) esP sp =
        pure ((none, esP), sp) := by
      simp [stepP, implE, transmitE, hS.abort_P, hwin, hwin0]
    rw [hC, hP_eq, hP, pure_bind, pure_bind]
    exact ih none esS sc esP sp hS
  · simp only [Bool.not_eq_true] at hwin0
    by_cases hsend : P.sendsIn (esS.g.epoch P + 1) = true
    · exact step_transmitE_new_epoch_DFShiftedPaper_le cka prng fs Δ_off b_auth qep l t hl hvalid P
        m_msg r esS sc esP sp k ih hS hwin0 hsend
    · simp only [Bool.not_eq_true] at hsend
      exact step_transmitE_same_epoch_DFShiftedPaper_le cka prng fs Δ_off b_auth qep l t P m_msg r
        esS sc esP sp k ih hS hwin0 hsend

theorem runRDFShiftedPaper_le_runRDFShifted10Paper (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δ_off : ℕ) (b_auth : Bool) (qep l t : ℕ)
    (hl : 1 ≤ l) (hvalid : SM.lastLeakGuessAdmissible (2 + Δ_off) (some (l - 1)) t = true)
    (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T} {esP : EStateP Γ T Sig SS RS M E K}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp) :
    𝒟[runRDFShiftedPaper cka prng fs Δ_off b_auth qep l t oa esS sc] {true} ≤
      𝒟[runRDFShifted10Paper cka prng fs Δ_off b_auth qep l t oa esP sp] {true} := by
  induction oa using OracleComp.inductionOn generalizing esS sc esP sp with
  | pure b' =>
    rw [runRDFShiftedPaper_pure, runRDFShifted10Paper_pure]
    have hauth : authOut (2 + Δ_off) ⟨true, some (l - 1), t⟩ esS =
        authOut (2 + Δ_off) ⟨true, some (l - 1), t⟩ esP := hS.authOut_eq
    rw [hauth]
  | query_bind q k ih =>
    have hC_qb : runRDFShiftedPaper cka prng fs Δ_off b_auth qep l t
        (liftM (OracleSpec.query q) >>= k) esS sc =
        stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t q esS sc >>= fun r =>
          runRDFShiftedPaper cka prng fs Δ_off b_auth qep l t (k r.1.1) r.1.2 r.2 :=
      runRDFShiftedPaper_query_bind cka prng fs Δ_off b_auth qep l t q k esS sc
    rw [hC_qb, runRDFShifted10Paper_query_bind]
    rcases q with n | (((((⟨P, m_msg, r⟩ | q_ch) | ⟨P, c⟩) | q_inj) | P) | ⟨P, c, c'⟩)
    · exact step_coinsE_DFShiftedPaper_le cka prng fs Δ_off b_auth qep l t n esS sc esP sp k @ih hS
    · exact step_transmitE_DFShiftedPaper_le cka prng fs Δ_off b_auth qep l t hl hvalid P m_msg r
        esS sc esP sp k @ih hS
    · exact step_challE_DFShiftedPaper_le cka prng fs Δ_off b_auth qep l t q_ch esS sc esP sp k @ih
        hS
    · exact step_deliverE_DFShiftedPaper_le cka prng fs Δ_off b_auth qep l t P c esS sc esP sp k @ih
        hS
    · exact step_injectE_DFShiftedPaper_le cka prng fs Δ_off b_auth qep l t q_inj esS sc esP sp k
        @ih hS
    · exact step_corrEShiftedPaper_DF_le cka prng fs Δ_off b_auth qep l t P esS sc esP sp k @ih hS
    · exact step_deliverForgeE_DFShiftedPaper_le cka prng fs Δ_off b_auth qep l t P c c' esS sc esP
        sp k @ih hS

def initES_S (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (kr : KR) (kc : KC) :
    EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I) :=
  let out := prng.up (prng.init kr) lam
  let vp := mkParties (T := T) (none : Option Γ) (none : Option Γ) out.1
    (fs.initSender out.2) (fs.initReceiver out.2)
  { g := { st := fun P => match P with | .A => vp.1 | .B => vp.2, b := false }
    h := { base := {}
           γPre := fun P => match P with | .A => some (cka.initA kc) | .B => some (cka.initB kc) } }

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem sync10ShiftedPaper_init (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δ_off l t : ℕ) (hl : 1 ≤ l)
    (hvg : SM.lastLeakGuessAdmissible (2 + Δ_off) (some (l - 1)) t = true) (kr : KR) (kc : KC) :
    Sync10ShiftedPaper prng Δ_off l t
      (initES_S cka prng fs lam kr kc)
      (CKA.initState cka kc true)
      (initES_P cka prng fs lam (some (prng.up (prng.init kr) lam).1) kr kc)
      (initSP prng lam (some (l - 1)) kr) := by
  have ht : 0 < t := validGuess_some_pos hvg
  have hloc0 : localCKA ⟨true, some (l - 1), t⟩ 1 0 = false := by
    simp [localCKA, Mode.tH, healEpoch]
  refine
    { hl := hl
      baseSync :=
        { abort_C := rfl
          abort_P := rfl
          b_C := rfl
          b_P := rfl
          g_eq := rfl
          id_C := fun P => by cases P <;> rfl
          id_P := fun P => by cases P <;> rfl
          tcur_C := fun P => by cases P <;> rfl
          tcur_P := fun P => by cases P <;> rfl
          vS_eq := fun P => by cases P <;> rfl
          vR_eq := fun P => by cases P <;> rfl
          Tcur_eq := fun P => by cases P <;> rfl
          γ_C := fun P => by cases P <;> simp [initES_S, mkParties, hloc0]
          root_P := fun P => by
            have hkr : knownRoot ⟨true, some (l - 1), t⟩ 0 = true := by
              simp [knownRoot, Mode.tH, healEpoch]
            cases P <;> simp [initES_P, initES_S, mkParties, hkr]
          cka_st := fun P _ => by cases P <;> exact ⟨rfl, rfl⟩
          trans_inv := fun r hr => by simp [initES_S, clearCompTL] at hr
          comp_inv := fun pos hpos => by simp [initES_S, clearCompTL] at hpos
          epoch_S := rfl
          cache_gt := fun _ _ => ⟨rfl, rfl⟩
          ping_pong := Or.inl ⟨rfl, rfl⟩
          prng_before_tH := fun _ _ => ⟨rfl, rfl, rfl, rfl⟩
          prng_after_tH := fun _ h => by
            simp [initES_S, clearCompTL, Mode.tH, healEpoch] at h
          prng_at_tStar := fun h => by
            change 0 = t at h
            omega }
      g_eq := rfl
      comp_inv := fun pos hpos => by cases hpos
      γPre_eq := fun P _ => by cases P <;> rfl }

def engRunDFShiftedPaperGen {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {HS Γv Sv SSv RSv : Type} (b_auth : Bool) (l : ℕ)
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ_off qep maxSkip tStar : ℕ) (cfg : SM.Config M) (π : Policy)
    (init : HM tspec HS (Option (VP Γv T Sv SSv RSv × VP Γv T Sv SSv RSv))) (h₀ : HS) (b : Bool)
    (A : DeliverForge.SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    TComp tspec (Option (Bool × EState (VP Γv T Sv SSv RSv) M (Header T × E) HS)) := do
  let (vpOpt, h₁) ← init.run h₀
  match vpOpt with
  | none => return none
  | some (vpA, vpB) =>
    let g₀ : SM.GameState (VP Γv T Sv SSv RSv) M (Header T × E) :=
      { st := fun | .A => vpA | .B => vpB, b := b }
    let es₀ : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS :=
      { g := g₀, h := h₁, abort := false }
    let res ←
      (simulateQ (AuthL10ShiftedPaper.implEDFG b_auth l hk Δ_off qep maxSkip tStar cfg π) A).run es₀
    return some res

def authSimDFShiftedPaperGen {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {HS Γv Sv SSv RSv : Type} (b_auth : Bool) (l : ℕ)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δ_off qep : ℕ)
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (init : HM tspec HS (Option (VP Γv T Sv SSv RSv × VP Γv T Sv SSv RSv))) (h₀ : HS)
    (tL : Option ℕ) (tStar : ℕ) (A : DeliverForge.SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    TComp tspec Bool := do
  let π : Policy := ⟨true, tL, tStar⟩
  let r ← engRunDFShiftedPaperGen b_auth l hk Δ_off qep fs.maxSkip tStar (SM.Config.auth tStar) π
    init h₀ false A
  match r with
  | none => return false
  | some (_, es) => return authOut (2 + Δ_off) π es

theorem lemma10_df_shifted_paper_gen (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δ_off : ℕ) (b_auth : Bool)
    (qep l t : ℕ) (hl : 1 ≤ l)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    let hkC := hooksCKAShifted cka prng fs l (AuthL10ShiftedPaper.tStarHook b_auth t)
    let hkP := hooksPRNG cka prng fs (AuthL10ShiftedPaper.moHook b_auth l t)
    𝒟[CKA.branch cka 1 (l + 1) true
        (authSimDFShiftedPaperGen b_auth l fs Δ_off qep hkC (initCKAShifted cka prng fs lam l) {}
          (some (l - 1)) t A)] {true} ≤
      𝒟[PRFPRNG.branch prng false
        (authSimDFShiftedPaperGen b_auth l fs Δ_off qep hkP
          (initPRNG cka prng fs lam (AuthL10ShiftedPaper.moHook b_auth l t)) {}
          (some (l - 1)) t A)] {true} := by
  intro hkC hkP
  open AuthL10ShiftedPaper CryptoGames.SM.Construction.AuthL10 in
  by_cases hvg : SM.lastLeakGuessAdmissible (2 + Δ_off) (some (l - 1)) t = true
  · have hL : 𝒟[CKA.branch cka 1 (l + 1) true
        (authSimDFShiftedPaperGen b_auth l fs Δ_off qep hkC (initCKAShifted cka prng fs lam l) {}
          (some (l - 1)) t A)] =
        𝒟[$ᵗ KC >>= fun kc => $ᵗ KR >>= fun kr =>
          runRDFShiftedPaper cka prng fs Δ_off b_auth qep l t A
            (initES_S cka prng fs lam kr kc)
            (CKA.initState cka kc true)] := by
      unfold CKA.branch authSimDFShiftedPaperGen engRunDFShiftedPaperGen initCKAShifted
        runRDFShiftedPaper initES_S
      simp only [hkC, hl, ↓reduceIte, liftCShifted, setγPreShifted, StateT.run'_eq, StateT.run_bind,
        StateT.run_lift, StateT.run_modify, StateT.run_pure, pure_bind, bind_assoc,
        simulateQ_bind, simulateQ_pure, AuthL9.simulateQ_sampleT_run, map_bind]
      refine evalDist_bind_congr _ _ _ fun kc => ?_
      refine evalDist_bind_congr _ _ _ fun kr => ?_
      have hall : (CKA.initState cka kc true).allowCorr (l + 1) = true :=
        allowCorr_initState_of_one_le cka kc true hl
      have hstA : (CKA.initState cka kc true).st .A = cka.initA kc := rfl
      have hstB : (CKA.initState cka kc true).st .B = cka.initB kc := rfl
      have hγPre_init :
          Function.update
            (Function.update (fun _ : Party => (none : Option Γ)) .A (some (cka.initA kc)))
            .B (some (cka.initB kc)) =
          (fun P => match P with | .A => some (cka.initA kc) | .B => some (cka.initB kc)) := by
        funext P; cases P <;> rfl
      simp only [CKA.corrQuery, AuthL9.simulateQ_query_eq, QueryImpl.add_apply, CKA.oracleImpl,
        CKA.corrImpl, hall, Bool.true_or, ↓reduceIte, StateT.run_bind, StateT.run_get,
        StateT.run_pure, pure_bind, hstA, hstB, hγPre_init, bind_pure_comp, map_pure]
      rfl
    have hinit_mo : initPRNG cka prng fs lam (moHook b_auth l t) =
        initPRNG cka prng fs lam ⟨true, some (l - 1), t⟩ := rfl
    have hR : PRFPRNG.branch prng false
        (authSimDFShiftedPaperGen b_auth l fs Δ_off qep hkP
          (initPRNG cka prng fs lam (moHook b_auth l t)) {} (some (l - 1)) t A) =
        ($ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
          runRDFShifted10Paper cka prng fs Δ_off b_auth qep l t A
            (initES_P cka prng fs lam (some (prng.up (prng.init kr) lam).1) kr kc)
            (initSP prng lam (some (l - 1)) kr)) := by
      unfold PRFPRNG.branch authSimDFShiftedPaperGen engRunDFShiftedPaperGen
        runRDFShifted10Paper initES_P
      rw [hinit_mo]
      simp only [hkP, pImpl, StateT.run'_eq, StateT.run_bind, simulateQ_bind,
        initPRNG_run_some cka prng fs lam Δ_off (l - 1) t hvg, map_eq_bind_pure_comp,
        bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, Function.comp_apply]
      rfl
    rw [hL, hR, OracleComp.evalDist_bind_bind_swap ($ᵗ KR) ($ᵗ KC)]
    refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
      fun kc _ => ?_
    refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
      fun kr _ => ?_
    exact runRDFShiftedPaper_le_runRDFShifted10Paper cka prng fs Δ_off b_auth qep l t hl hvg A
      (sync10ShiftedPaper_init cka prng fs lam Δ_off l t hl hvg kr kc)
  · have hvg_f : SM.lastLeakGuessAdmissible (2 + Δ_off) (some (l - 1)) t = false := Bool.eq_false_iff.mpr hvg
    have hred :
        authSimDFShiftedPaperGen b_auth l fs Δ_off qep hkC (initCKAShifted cka prng fs lam l)
          {} (some (l - 1)) t A =
        (engRunDFShiftedPaperGen b_auth l hkC Δ_off qep fs.maxSkip t
          (Config.auth t) ⟨true, some (l - 1), t⟩ (initCKAShifted cka prng fs lam l) {} false A >>=
          fun _ => pure false) := by
      dsimp only [authSimDFShiftedPaperGen]
      congr 1
      funext r
      cases r with
      | none => rfl
      | some p =>
        exact congrArg pure
          (AuthL10.authOut_of_validGuess_false (2 + Δ_off) ⟨true, some (l - 1), t⟩ hvg_f p.2)
    have hbranch : 𝒟[CKA.branch cka 1 (l + 1) true
        (authSimDFShiftedPaperGen b_auth l fs Δ_off qep hkC (initCKAShifted cka prng fs lam l) {}
          (some (l - 1)) t A)] = 𝒟[(pure false : ProbComp Bool)] := by
      unfold CKA.branch
      rw [hred]
      simp only [StateT.run'_eq, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
        map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
      refine AuthL10.evalDist_bind_false_of_support ($ᵗ KC) _ fun k _ => ?_
      exact OracleComp.evalDist_bind_const _ _
    rw [hbranch]
    simp

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
  [SampleableType I] [SampleableType K] in
theorem engRunDFShiftedPaperGen_true_eq {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {HS Γv Sv SSv RSv : Type} (l : ℕ)
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ_off qep maxSkip tStar : ℕ) (cfg : SM.Config M) (π : Policy)
    (init : HM tspec HS (Option (VP Γv T Sv SSv RSv × VP Γv T Sv SSv RSv))) (h₀ : HS) (b : Bool)
    (A : DeliverForge.SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    engRunDFShiftedPaperGen true l hk Δ_off qep maxSkip tStar cfg π init h₀ b A =
      engRunDFShiftedPaper l hk (2 + Δ_off) qep maxSkip cfg π init h₀ b A := by
  unfold engRunDFShiftedPaperGen engRunDFShiftedPaper
  congr 1

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
  [SampleableType I] [SampleableType K] in
theorem engRunDFShiftedPaperGen_false_zero_eq {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {HS Γv Sv SSv RSv : Type} (l : ℕ)
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (qep maxSkip tStar : ℕ) (cfg : SM.Config M) (π : Policy)
    (init : HM tspec HS (Option (VP Γv T Sv SSv RSv × VP Γv T Sv SSv RSv))) (h₀ : HS) (b : Bool)
    (A : DeliverForge.SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    engRunDFShiftedPaperGen false l hk 0 qep maxSkip tStar cfg π init h₀ b A =
      engRunDFShiftedDir2Paper l hk qep maxSkip tStar cfg π init h₀ b A := by
  unfold engRunDFShiftedPaperGen engRunDFShiftedDir2Paper
  congr 1

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
  [SampleableType I] [SampleableType K] in
theorem authSimDFShiftedPaperGen_true_eq {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {HS Γv Sv SSv RSv : Type} (l : ℕ)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δ_off qep : ℕ)
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (init : HM tspec HS (Option (VP Γv T Sv SSv RSv × VP Γv T Sv SSv RSv))) (h₀ : HS)
    (tL : Option ℕ) (tStar : ℕ) (A : DeliverForge.SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    authSimDFShiftedPaperGen true l fs Δ_off qep hk init h₀ tL tStar A =
      authSimDFShiftedPaper l fs Δ_off qep hk init h₀ tL tStar A := by
  dsimp only [authSimDFShiftedPaperGen, authSimDFShiftedPaper]
  rw [engRunDFShiftedPaperGen_true_eq]
  congr 1; funext r; cases r <;> rfl

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
  [SampleableType I] [SampleableType K] in
theorem authSimDFShiftedPaperGen_false_zero_eq {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {HS Γv Sv SSv RSv : Type} (l : ℕ)
    (fs : FSAEADScheme K SS RS (Header T) M E) (qep : ℕ)
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (init : HM tspec HS (Option (VP Γv T Sv SSv RSv × VP Γv T Sv SSv RSv))) (h₀ : HS)
    (tL : Option ℕ) (tStar : ℕ) (A : DeliverForge.SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    authSimDFShiftedPaperGen false l fs 0 qep hk init h₀ tL tStar A =
      authSimDFShiftedDir2Paper l fs qep hk init h₀ tL tStar A := by
  dsimp only [authSimDFShiftedPaperGen, authSimDFShiftedDir2Paper]
  rw [engRunDFShiftedPaperGen_false_zero_eq]
  congr 1; funext r; cases r <;> rfl

end AuthL10ShiftedPaper

/-- Shifted-paper Lemma 10 for `redCKAAuthDFShiftedPaper` and `redPRNGAuthDFShiftedPaper`. -/
theorem lemma10_df_shifted_paper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δ_off qep l t : ℕ)
    (hl : 1 ≤ l)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[CKA.branch cka 1 (l + 1) true
        (redCKAAuthDFShiftedPaper cka prng fs lam Δ_off qep l t A)] {true} ≤
      𝒟[PRFPRNG.branch prng false
        (redPRNGAuthDFShiftedPaper cka prng fs lam Δ_off qep l t A)] {true} := by
  have h := AuthL10ShiftedPaper.lemma10_df_shifted_paper_gen cka prng fs lam Δ_off true qep l t hl A
  dsimp only [AuthL10ShiftedPaper.tStarHook, AuthL10ShiftedPaper.moHook, ↓reduceIte] at h
  rwa [AuthL10ShiftedPaper.authSimDFShiftedPaperGen_true_eq,
    AuthL10ShiftedPaper.authSimDFShiftedPaperGen_true_eq] at h

/-- Shifted-paper Lemma 10 at `Δ = 2` for `redCKAAuthDFShiftedDir2Paper` and
`redPRNGAuthDFShiftedDir2Paper`. -/
theorem lemma10_df_shifted_dir2_paper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (qep l t : ℕ)
    (hl : 1 ≤ l)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[CKA.branch cka 1 (l + 1) true
        (redCKAAuthDFShiftedDir2Paper cka prng fs lam qep l t A)] {true} ≤
      𝒟[PRFPRNG.branch prng false
        (redPRNGAuthDFShiftedDir2Paper cka prng fs lam qep l t A)] {true} := by
  have h := AuthL10ShiftedPaper.lemma10_df_shifted_paper_gen cka prng fs lam 0 false qep l t hl A
  dsimp only [AuthL10ShiftedPaper.tStarHook, AuthL10ShiftedPaper.moHook,
    Bool.false_eq_true, ↓reduceIte] at h
  rwa [AuthL10ShiftedPaper.authSimDFShiftedPaperGen_false_zero_eq,
    AuthL10ShiftedPaper.authSimDFShiftedPaperGen_false_zero_eq] at h

end CryptoGames.SM.Construction.DeliverForge

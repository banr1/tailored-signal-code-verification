/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperShiftedPRNG
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma9
import ProofLib.SepLogic.WP.StateNorm

/-!
# Shifted-Paper Hop 2, Part 2

Step lemmas of the shifted-paper Hop 2 for `deliverE`, `deliverForgeE`, and same-epoch `transmitE`.
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
open AuthL10Shifted

namespace AuthL10ShiftedPaper

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

omit [SampleableType KC] in
theorem step_deliverE_new_epoch_DFShiftedPaper_le (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δ_off : ℕ) (b_auth : Bool) (qep l t : ℕ)
    (P : Party) (c : Header T × E) (r : SM.Record M (Header T × E))
    (esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I))
    (sc : CKA.GameState Γ T) (esP : EStateP Γ T Sig SS RS M E K)
    (sp : PRFPRNG.GameState Sig I K)
    (k : Option (SM.RecvResult M) → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (ih : ∀ r esS' sc' esP' sp',
      Sync10ShiftedPaper prng Δ_off l t esS' sc' esP' sp' →
      𝒟[runRDFShiftedPaper cka prng fs Δ_off b_auth qep l t (k r) esS' sc'] {true} ≤
        𝒟[runRDFShifted10Paper cka prng fs Δ_off b_auth qep l t (k r) esP' sp'] {true})
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp)
    (hwin0 : esS.g.win = false)
    (hr : esS.g.inTransit P.other c = some r)
    (hsend0 : P.sendsIn c.1.1 = false)
    (hnew : c.1.1 = esS.g.epoch P + 1) :
    𝒟[stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
        (.inr (.inl (.inl (.inl (.inr (P, c)))))) esS sc >>=
      fun res => runRDFShiftedPaper cka prng fs Δ_off b_auth qep l t (k res.1.1) res.1.2 res.2]
        {true} ≤
    𝒟[stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
        (.inr (.inl (.inl (.inl (.inr (P, c)))))) esP sp >>=
      fun res => runRDFShifted10Paper cka prng fs Δ_off b_auth qep l t (k res.1.1) res.1.2 res.2]
        {true} := by
  let mo : Mode := ⟨true, some (l - 1), t⟩
  have htH : mo.tH = l + 1 := by
    have := hS.hl; simp [mo, Mode.tH, healEpoch]; omega
  have hwin : esP.g.win = esS.g.win := eraseSt_win hS.g_eq
  have htrans : esP.g.inTransit P.other c = esS.g.inTransit P.other c :=
    eraseSt_inTransit hS.g_eq P.other c
  have hchall : esP.g.chall = esS.g.chall := eraseSt_chall hS.g_eq
  have hesS_eq := estate_mk_abort_false hS.abort_C
  have hesP_eq := estate_mk_abort_false hS.abort_P
  have hsend0' : P.sendsIn (esS.g.epoch P + 1) = false := hnew ▸ hsend0
  obtain ⟨hr_ep, hP_eq_R, hO_eq_S, hO_ep, hmax_eq, Tm, Im, hct2, hcC, hST, hSroot,
    hcP, hlast⟩ := hS.deliver_new_info hr hnew
  let p := prng.up (esS.g.st P).root Im
  have hp1 : (prng.up (esS.g.st P).root Im).1 = (esS.g.st P.other).root := hSroot.symm
  let γP' := (cka.receive (esP.g.st P).γ Tm).1
  have hstartC := fun ctx γv =>
    hooksCKAShifted_startRecv_honest cka prng fs l (tStarHook b_auth t) ctx P (esS.g.epoch P + 1)
      γv (esS.g.st P).root Tm Im esS.h hcC
  have hstartP : (simulateQ (pImpl prng)
      (((hooksPRNG cka prng fs (moHook b_auth l t)).startRecv esP.g P (esS.g.epoch P + 1)
        (esP.g.st P).γ (esP.g.st P).root Tm).run esP.h)).run sp =
      pure ((some (some (γP', (esP.g.st P.other).root, fs.initReceiver p.2)), esP.h), sp) := by
    simp [hooksPRNG, hcP, p, γP', StateT.run_bind, StateT.run_get, StateT.run_pure, simulateQ_pure]
  cases hfs : fs.receive (fs.initReceiver p.2) c.1 c.2 with
  | none =>
    have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
        (.inr (.inl (.inl (.inl (.inr (P, c)))))) esS sc =
        pure ((some .rejected, esS), sc) := by
      simp [stepCDFShiftedPaper, implEDFG, deliverE, vRecv, SM.Config.auth,
        hS.abort_C, hwin0, hr, hS.id_C P, hS.tcur_C P, hsend0', hnew,
        hct2, hstartC, hp1, p, hfs, StateT.run_bind, StateT.run_pure, simulateQ_pure, hesS_eq]
    have hP : stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
        (.inr (.inl (.inl (.inl (.inr (P, c)))))) esP sp =
        pure ((some .rejected, esP), sp) := by
      simp [stepPDFShiftedPaperGen, implEDFG, deliverE, vRecv, SM.Config.auth,
        hS.abort_P, hwin, hwin0, htrans, hr,
        hS.id_P P, hS.tcur_P P, hsend0', hnew, hct2, hstartP, hfs,
        StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure, hesP_eq]
    rw [hC, hP, pure_bind, pure_bind]
    exact ih (some .rejected) esS sc esP sp hS
  | some vim =>
    rcases vim with ⟨v', i', m'⟩
    let m := esS.g.epoch P + 1
    let vR' := Function.update (Function.update (esS.g.st P).vR m
      (some (fs.initReceiver p.2))) m (some v')
    let γC_final := if localCKA mo 1 m then some γP' else none
    let stC_final : VP (Option Γ) T Sig SS RS :=
      { esS.g.st P with tcur := m, γ := γC_final, root := (esS.g.st P.other).root, vR := vR' }
    let stP_final : VP Γ T (Option Sig) SS RS :=
      { esP.g.st P with tcur := m, γ := γP', root := (esP.g.st P.other).root, vR := vR' }
    let h_final : CKAStateShifted Γ T I :=
      if m + 1 ≤ l then { esS.h with γPre := Function.update esS.h.γPre P (some γP') } else esS.h
    have hvRP : (esP.g.st P).vR = (esS.g.st P).vR := hS.vR_eq P
    have hP : stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
        (.inr (.inl (.inl (.inl (.inr (P, c)))))) esP sp =
        pure ((some (.accepted m i' (if esS.g.chall.contains r.pos then none else some m')),
          { esP with g := esP.g.accept P stP_final r.pos }), sp) := by
      simp [stepPDFShiftedPaperGen, implEDFG, deliverE, commitE, vRecv, SM.Config.auth,
        hS.abort_P, hwin, hwin0, htrans, hr, hchall, hS.id_P P, hS.tcur_P P, hsend0', hnew, hct2,
        hvRP, hstartP, hfs, m, vR', stP_final, γP', StateT.run_bind, StateT.run_pure,
        StateT.run_modify, simulateQ_bind, simulateQ_pure]
    by_cases hloc : localCKA mo 1 (esS.g.epoch P) = true
    · have hge : l + 2 ≤ esS.g.epoch P := by
        simp only [localCKA, mo, Option.isNone_some, Bool.false_or, htH, decide_eq_true_eq] at hloc
        omega
      have hloc_m : localCKA mo 1 m = true := by
        simp [localCKA, mo, htH, show l + 1 + 1 ≤ m by omega]
      have hnot_pre : ¬ (m + 1 ≤ l) := by omega
      have hh_eq : h_final = esS.h := by simp [h_final, hnot_pre]
      have hγC : (esS.g.st P).γ = some (esP.g.st P).γ := by
        rw [hS.γ_C P, hloc]; rfl
      have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
          (.inr (.inl (.inl (.inl (.inr (P, c)))))) esS sc =
          pure ((some (.accepted m i' (if esS.g.chall.contains r.pos then none else some m')),
            { esS with g := esS.g.accept P stC_final r.pos, h := h_final }), sc) := by
        rw [hh_eq]
        simp [stepCDFShiftedPaper, implEDFG, deliverE, commitE, vRecv,
          SM.Config.auth, hS.abort_C, hwin0, hr, hS.id_C P, hS.tcur_C P,
          hsend0', hnew, hct2, hstartC, hp1, p, hfs, hγC, hloc_m, m, vR', γC_final, stC_final, γP',
          StateT.run_bind, StateT.run_pure, StateT.run_modify, simulateQ_pure]
      rw [hC, hP, pure_bind, pure_bind]
      exact ih _ _ _ _ _ (hS.accept_new P γP' vR' r.pos hr_ep hO_ep hS.b_C
        (fun h => by simp [m, mo, hloc_m] at h))
    · simp only [Bool.not_eq_true] at hloc
      have hγC : (esS.g.st P).γ = none := by rw [hS.γ_C P, hloc]; rfl
      obtain ⟨hsc_stP, hsc_epP⟩ := hS.cka_st P (Or.inl hloc)
      obtain ⟨hsc_stO, hsc_epO⟩ := hS.cka_st P.other (Or.inr (by simpa using hloc))
      have hcanR : sc.canReceive P = true := by
        simp [CKA.GameState.canReceive, hsc_epO, hsc_epP, hO_ep]
      have hlast_eq : sc.lastMsg = some Tm := hlast hloc
      let sc' := sc.afterReceive P γP'
      have hstP' : (sc.afterReceive P γP').st P = γP' := by simp [CKA.GameState.afterReceive]
      by_cases hfin : l + 2 ≤ m
      · have hloc_m : localCKA mo 1 m = true := by
          simp [localCKA, mo, htH, show l + 1 + 1 ≤ m by omega]
        have hnot_pre : ¬ (m + 1 ≤ l) := by omega
        have hh_eq : h_final = esS.h := by simp [h_final, hnot_pre]
        have hfin_sc : (sc.afterReceive P γP').finished 1 (l + 1) P = true :=
          finished_afterReceive_of_ge γP' (by rw [hsc_epP]; exact hfin)
        have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
            (.inr (.inl (.inl (.inl (.inr (P, c)))))) esS sc =
            pure ((some (.accepted m i' (if esS.g.chall.contains r.pos then none else some m')),
              { esS with g := esS.g.accept P stC_final r.pos, h := h_final }), sc') := by
          rw [hh_eq]
          simp [stepCDFShiftedPaper, implEDFG, deliverE, commitE, liftCShifted,
            CKA.receiveQuery, CKA.corrQuery, cImpl, CKA.oracleImpl, CKA.receiveImpl,
            CKA.corrImpl, vRecv, SM.Config.auth, hS.abort_C, hwin0, hr,
            hS.id_C P, hS.tcur_C P, hsend0', hnew, hct2, hstartC, hp1, p, hfs,
            hγC, hcanR, hlast_eq, hsc_stP, hfin, hfin_sc, hstP', hloc_m, sc',
            m, vR', γC_final, stC_final, γP',
            simulateQ_bind, simulateQ_query, simulateQ_pure, map_eq_bind_pure_comp,
            StateT.run_bind, StateT.run_pure, StateT.run_modify]
        rw [hC, hP, pure_bind, pure_bind]
        exact ih _ _ _ _ _ (hS.accept_new P γP' vR' r.pos hr_ep hO_ep hS.b_C
          (fun h => by simp [m, mo, hloc_m] at h))
      · have hloc_m : localCKA mo 1 m = false := by
          simp [localCKA, mo, htH, show ¬ (l + 1 + 1 ≤ m) by omega]
        have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
            (.inr (.inl (.inl (.inl (.inr (P, c)))))) esS sc =
            pure ((some (.accepted m i' (if esS.g.chall.contains r.pos then none else some m')),
              { esS with g := esS.g.accept P stC_final r.pos, h := h_final }), sc') := by
          by_cases hpre : m + 1 ≤ l
          · have hall : (sc.afterReceive P γP').allowCorr (l + 1) = true :=
              allowCorr_afterReceive_of_le γP' (by rw [hsc_epP, hsc_epO, hO_ep])
                (by rw [hsc_epP]; exact hpre)
            have hh_eq : h_final =
                { esS.h with γPre := Function.update esS.h.γPre P (some γP') } := by
              simp [h_final, hpre]
            rw [hh_eq]
            simp [stepCDFShiftedPaper, implEDFG, deliverE, commitE,
              setγPreShifted, liftCShifted, CKA.receiveQuery, CKA.corrQuery, cImpl,
              CKA.oracleImpl, CKA.receiveImpl, CKA.corrImpl, vRecv, SM.Config.auth,
              hS.abort_C, hwin0, hr, hS.id_C P, hS.tcur_C P, hsend0',
              hnew, hct2, hstartC, hp1, p, hfs, hγC, hcanR, hlast_eq, hsc_stP, hfin,
              show esS.g.epoch P + 1 < l by omega, hall,
              hstP', hloc_m, sc', m, vR', γC_final, stC_final, γP',
              simulateQ_bind, simulateQ_query, simulateQ_pure, map_eq_bind_pure_comp,
              StateT.run_bind, StateT.run_pure, StateT.run_modify]
          · have hh_eq : h_final = esS.h := by simp [h_final, hpre]
            rw [hh_eq]
            simp [stepCDFShiftedPaper, implEDFG, deliverE, commitE, liftCShifted,
              CKA.receiveQuery, cImpl, CKA.oracleImpl, CKA.receiveImpl, vRecv,
              SM.Config.auth, hS.abort_C, hwin0, hr, hS.id_C P,
              hS.tcur_C P, hsend0', hnew, hct2, hstartC, hp1, p, hfs, hγC, hcanR,
              hlast_eq, hsc_stP, hfin, show ¬(esS.g.epoch P + 1 < l) by omega,
              hloc_m, sc', m, vR', γC_final, stC_final, γP',
              simulateQ_bind, simulateQ_query, simulateQ_pure, map_eq_bind_pure_comp,
              StateT.run_bind, StateT.run_pure, StateT.run_modify]
        rw [hC, hP, pure_bind, pure_bind]
        refine ih _ _ _ _ _ (hS.accept_new P γP' vR' r.pos hr_ep hO_ep hS.b_C fun _ => ?_)
        simp [sc', CKA.GameState.afterReceive, Party.other_ne, hsc_epP, hsc_stO, hsc_epO, hO_ep]
omit [SampleableType KC] in
theorem step_deliverE_DFShiftedPaper_le (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δ_off : ℕ) (b_auth : Bool) (qep l t : ℕ)
    (P : Party) (c : Header T × E)
    (esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I))
    (sc : CKA.GameState Γ T) (esP : EStateP Γ T Sig SS RS M E K)
    (sp : PRFPRNG.GameState Sig I K)
    (k : Option (SM.RecvResult M) → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (ih : ∀ r esS' sc' esP' sp',
      Sync10ShiftedPaper prng Δ_off l t esS' sc' esP' sp' →
      𝒟[runRDFShiftedPaper cka prng fs Δ_off b_auth qep l t (k r) esS' sc'] {true} ≤
        𝒟[runRDFShifted10Paper cka prng fs Δ_off b_auth qep l t (k r) esP' sp'] {true})
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp) :
    𝒟[stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
        (.inr (.inl (.inl (.inl (.inr (P, c)))))) esS sc >>=
      fun r => runRDFShiftedPaper cka prng fs Δ_off b_auth qep l t (k r.1.1) r.1.2 r.2] {true} ≤
    𝒟[stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
      (.inr (.inl (.inl (.inl (.inr (P, c)))))) esP sp >>=
      fun r => runRDFShifted10Paper cka prng fs Δ_off b_auth qep l t (k r.1.1) r.1.2 r.2]
      {true} := by
  let mo : Mode := ⟨true, some (l - 1), t⟩
  have hwin : esP.g.win = esS.g.win := eraseSt_win hS.g_eq
  have htrans : esP.g.inTransit P.other c = esS.g.inTransit P.other c :=
    eraseSt_inTransit hS.g_eq P.other c
  have hchall : esP.g.chall = esS.g.chall := eraseSt_chall hS.g_eq
  have hesS_eq := estate_mk_abort_false hS.abort_C
  have hesP_eq := estate_mk_abort_false hS.abort_P
  by_cases hwin0 : esS.g.win = true
  · have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
        (.inr (.inl (.inl (.inl (.inr (P, c)))))) esS sc =
        pure ((none, esS), sc) := by
      simp [stepCDFShiftedPaper, implEDFG, deliverE, hS.abort_C, hwin0]
    have hP : stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
        (.inr (.inl (.inl (.inl (.inr (P, c)))))) esP sp =
        pure ((none, esP), sp) := by
      simp [stepPDFShiftedPaperGen, implEDFG, deliverE, hS.abort_P, hwin, hwin0]
    rw [hC, hP, pure_bind, pure_bind]
    exact ih none esS sc esP sp hS
  · simp only [Bool.not_eq_true] at hwin0
    cases hr : esS.g.inTransit P.other c with
    | none =>
      have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
          (.inr (.inl (.inl (.inl (.inr (P, c)))))) esS sc =
          pure ((none, esS), sc) := by
        simp [stepCDFShiftedPaper, implEDFG, deliverE, hS.abort_C, hwin0, hr]
      have hP : stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
          (.inr (.inl (.inl (.inl (.inr (P, c)))))) esP sp =
          pure ((none, esP), sp) := by
        simp [stepPDFShiftedPaperGen, implEDFG, deliverE, hS.abort_P, hwin,
          hwin0, htrans, hr]
      rw [hC, hP, pure_bind, pure_bind]
      exact ih none esS sc esP sp hS
    | some r =>
      obtain ⟨hmem, hsender, hct⟩ := inTransit_some_props hr
      obtain ⟨ht1, hsend_other, hle_other, _⟩ := hS.trans_inv r hmem
      rw [hct] at ht1
      rw [hsender] at hsend_other hle_other
      have hsend0 : P.sendsIn c.1.1 = false := by
        rw [ht1]
        have h1 := AuthL10.sendsIn_other P r.pos.epoch
        rw [hsend_other] at h1
        simpa using h1.symm
      have hmax_bound : esS.g.epoch P.other ≤ esS.g.epoch P + 1 := by
        rcases hS.ping_pong with ⟨hR, _⟩ | ⟨_, hR, _⟩
        · have hepP := epoch_eq_of_synced hS.epoch_S hR P
          have hepO := epoch_eq_of_synced hS.epoch_S hR P.other
          omega
        · rcases party_cases_of_epoch (max (esS.g.epoch .A) (esS.g.epoch .B)) P with hP | hP
          · have hO : P.other = Party.receiverOf (max (esS.g.epoch .A) (esS.g.epoch .B)) := by
              rw [hP, senderOf_other]
            have hS_ep := hS.epoch_S
            rw [← hP] at hS_ep
            rw [← hO] at hR
            omega
          · have hO : P.other = Party.senderOf (max (esS.g.epoch .A) (esS.g.epoch .B)) := by
              rw [hP, receiverOf_other]
            have hS_ep := hS.epoch_S
            rw [← hO] at hS_ep
            rw [← hP] at hR
            omega
      have hle : ¬ (esS.g.epoch P + 1 < c.1.1) := by omega
      by_cases hnew : c.1.1 = esS.g.epoch P + 1
      · exact step_deliverE_new_epoch_DFShiftedPaper_le cka prng fs Δ_off b_auth qep l t P c r esS
          sc esP sp k ih hS hwin0 hr hsend0 hnew
      · have hle_ep : r.pos.epoch ≤ esS.g.epoch P := by omega
        have hvRP : (esP.g.st P).vR c.1.1 = (esS.g.st P).vR c.1.1 := by rw [hS.vR_eq P]
        cases hvR : (esS.g.st P).vR c.1.1 with
        | none =>
          have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
              (.inr (.inl (.inl (.inl (.inr (P, c)))))) esS sc =
              pure ((some .rejected, esS), sc) := by
            simp [stepCDFShiftedPaper, implEDFG, deliverE, vRecv, SM.Config.auth,
              hS.abort_C, hwin0, hr, hS.id_C P, hS.tcur_C P, hsend0, hle,
              hnew, hvR, StateT.run_pure, hesS_eq]
          have hP : stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
              (.inr (.inl (.inl (.inl (.inr (P, c)))))) esP sp =
              pure ((some .rejected, esP), sp) := by
            simp [stepPDFShiftedPaperGen, implEDFG, deliverE, vRecv, SM.Config.auth,
              hS.abort_P, hwin, hwin0, htrans, hr, hS.id_P P,
              hS.tcur_P P, hsend0, hle, hnew, hvRP, hvR, StateT.run_pure, hesP_eq]
          rw [hC, hP, pure_bind, pure_bind]
          exact ih (some .rejected) esS sc esP sp hS
        | some v =>
          cases hfs : fs.receive v c.1 c.2 with
          | none =>
            have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
                (.inr (.inl (.inl (.inl (.inr (P, c)))))) esS sc =
                pure ((some .rejected, esS), sc) := by
              simp [stepCDFShiftedPaper, implEDFG, deliverE, vRecv, SM.Config.auth,
                hS.abort_C, hwin0, hr, hS.id_C P, hS.tcur_C P, hsend0,
                hle, hnew, hvR, hfs, StateT.run_pure, hesS_eq]
            have hP : stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
                (.inr (.inl (.inl (.inl (.inr (P, c)))))) esP sp =
                pure ((some .rejected, esP), sp) := by
              simp [stepPDFShiftedPaperGen, implEDFG, deliverE, vRecv, SM.Config.auth,
                hS.abort_P, hwin, hwin0, htrans, hr, hS.id_P P,
                hS.tcur_P P, hsend0, hle, hnew, hvRP, hvR, hfs, StateT.run_pure, hesP_eq]
            rw [hC, hP, pure_bind, pure_bind]
            exact ih (some .rejected) esS sc esP sp hS
          | some vim =>
            rcases vim with ⟨v', i', m'⟩
            let vR' := Function.update (esS.g.st P).vR c.1.1 (some v')
            have hvRP_all : (esP.g.st P).vR = (esS.g.st P).vR := hS.vR_eq P
            have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
                (.inr (.inl (.inl (.inl (.inr (P, c)))))) esS sc =
                pure ((some (.accepted c.1.1 i'
                  (if esS.g.chall.contains r.pos then none else some m')),
                  { esS with g := esS.g.accept P { esS.g.st P with vR := vR' } r.pos }), sc) := by
              simp [stepCDFShiftedPaper, implEDFG, deliverE, commitE, vRecv,
                SM.Config.auth, hS.abort_C, hwin0, hr, hS.id_C P,
                hS.tcur_C P, hsend0, hle, hnew, hvR, hfs, vR', StateT.run_pure,
                StateT.run_modify]
            have hP : stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
                (.inr (.inl (.inl (.inl (.inr (P, c)))))) esP sp =
                pure ((some (.accepted c.1.1 i'
                  (if esS.g.chall.contains r.pos then none else some m')),
                  { esP with g := esP.g.accept P { esP.g.st P with vR := vR' } r.pos }), sp) := by
              simp [stepPDFShiftedPaperGen, implEDFG, deliverE, commitE, vRecv,
                SM.Config.auth, hS.abort_P, hwin, hwin0,
                htrans, hr, hchall, hS.id_P P, hS.tcur_P P, hsend0,
                hle, hnew, hvRP, hvR, hfs, hvRP_all, vR', StateT.run_pure, StateT.run_modify]
            rw [hC, hP, pure_bind, pure_bind]
            exact ih _ _ _ _ _ (hS.accept_old P vR' r.pos hle_ep)
omit [SampleableType KC] in
theorem step_deliverForgeE_new_epoch_triv_DFShiftedPaper_le (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δ_off : ℕ) (b_auth : Bool) (qep l t : ℕ)
    (P : Party) (c c' : Header T × E) (r : SM.Record M (Header T × E))
    (Tm : T) (Im : I) (v' : RS) (i' : ℕ) (m' : M)
    (esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I))
    (sc : CKA.GameState Γ T) (esP : EStateP Γ T Sig SS RS M E K)
    (sp : PRFPRNG.GameState Sig I K)
    (k : Option (SM.RecvResult M) → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (ih : ∀ r esS' sc' esP' sp',
      Sync10ShiftedPaper prng Δ_off l t esS' sc' esP' sp' →
      𝒟[runRDFShiftedPaper cka prng fs Δ_off b_auth qep l t (k r) esS' sc'] {true} ≤
        𝒟[runRDFShifted10Paper cka prng fs Δ_off b_auth qep l t (k r) esP' sp'] {true})
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp)
    (hwin0 : esS.g.win = false)
    (hr : esS.g.inTransit P.other c = some r)
    (htrans0 : esS.g.inTransit P.other c' = none)
    (hcomp0' : r.pos ∉ esS.g.comp)
    (hhdr : c.1 = c'.1)
    (hsend0' : P.sendsIn (esS.g.epoch P + 1) = false)
    (hnew : c'.1.1 = esS.g.epoch P + 1)
    (hr_ep : r.pos.epoch = esS.g.epoch P + 1)
    (hO_ep : esS.g.epoch P.other = esS.g.epoch P + 1)
    (hc'2 : c'.1.2 = some Tm)
    (hcC : esS.h.base.cache (esS.g.epoch P + 1) = some (Tm, Im))
    (hSroot : (esS.g.st P.other).root = (prng.up (esS.g.st P).root Im).1)
    (hcP : esP.h.cache (esS.g.epoch P + 1) =
      some (Tm, (esP.g.st P.other).root, (prng.up (esS.g.st P).root Im).2))
    (hlast : localCKA ⟨true, some (l - 1), t⟩ 1 (esS.g.epoch P) = false → sc.lastMsg = some Tm)
    (hfs : fs.receive (fs.initReceiver (prng.up (esS.g.st P).root Im).2) c'.1 c'.2 =
      some (v', i', m'))
    (hqep : ¬ (qep + 1 < esS.g.epoch P + 1))
    (htriv : trivHook b_auth Δ_off t esS.g ⟨P.other, esS.g.epoch P + 1, i'⟩ = true) :
    𝒟[stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t (.inr (.inr (P, c, c'))) esS sc >>=
      fun r => runRDFShiftedPaper cka prng fs Δ_off b_auth qep l t (k r.1.1) r.1.2 r.2] {true} ≤
    𝒟[stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
      (.inr (.inr (P, c, c'))) esP sp >>=
      fun r => runRDFShifted10Paper cka prng fs Δ_off b_auth qep l t (k r.1.1) r.1.2 r.2]
      {true} := by
  let mo : Mode := ⟨true, some (l - 1), t⟩
  have htH : mo.tH = l + 1 := by
    have := hS.hl; simp [mo, Mode.tH, healEpoch]; omega
  have hwin : esP.g.win = esS.g.win := eraseSt_win hS.g_eq
  have htrans_c : esP.g.inTransit P.other c = esS.g.inTransit P.other c :=
    eraseSt_inTransit hS.g_eq P.other c
  have htrans_c' : esP.g.inTransit P.other c' = esS.g.inTransit P.other c' :=
    eraseSt_inTransit hS.g_eq P.other c'
  have hcomp : esP.g.comp = esS.g.comp := eraseSt_comp hS.g_eq
  let m := esS.g.epoch P + 1
  let pos : SM.Pos := ⟨P.other, m, i'⟩
  have htriv_eq : trivHook b_auth Δ_off t esP.g pos = trivHook b_auth Δ_off t esS.g pos :=
    eraseSt_trivHook hS.g_eq b_auth Δ_off t pos
  let p := prng.up (esS.g.st P).root Im
  have hp1 : (prng.up (esS.g.st P).root Im).1 = (esS.g.st P.other).root := hSroot.symm
  let γP' := (cka.receive (esP.g.st P).γ Tm).1
  have hstartC := fun ctx γv =>
    hooksCKAShifted_startRecv_honest cka prng fs l (tStarHook b_auth t) ctx P (esS.g.epoch P + 1)
      γv (esS.g.st P).root Tm Im esS.h hcC
  have hstartP : (simulateQ (pImpl prng)
      (((hooksPRNG cka prng fs (moHook b_auth l t)).startRecv esP.g P (esS.g.epoch P + 1)
        (esP.g.st P).γ (esP.g.st P).root Tm).run esP.h)).run sp =
      pure ((some (some (γP', (esP.g.st P.other).root, fs.initReceiver p.2)), esP.h),
        sp) := by
    simp [hooksPRNG, hcP, p, γP', StateT.run_bind, StateT.run_get, StateT.run_pure,
      simulateQ_pure]
  let vR' := Function.update (Function.update (esS.g.st P).vR m
    (some (fs.initReceiver p.2))) m (some v')
  let γC_final := if localCKA mo 1 m then some γP' else none
  let stC_final : VP (Option Γ) T Sig SS RS :=
    { esS.g.st P with tcur := m, γ := γC_final, root := (esS.g.st P.other).root, vR := vR' }
  let stP_final : VP Γ T (Option Sig) SS RS :=
    { esP.g.st P with tcur := m, γ := γP', root := (esP.g.st P.other).root, vR := vR' }
  let h_final : CKAStateShifted Γ T I :=
    if m + 1 ≤ l then { esS.h with γPre := Function.update esS.h.γPre P (some γP') } else esS.h
  have hvRP : (esP.g.st P).vR = (esS.g.st P).vR := hS.vR_eq P
  have hP :
      stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t (.inr (.inr (P, c, c'))) esP sp =
      pure ((some (.accepted m i' (some m')),
        { esP with g := esP.g.accept P stP_final pos }), sp) := by
    simp [stepPDFShiftedPaperGen, implEDFG, deliverForgeEG, commitE, vRecv,
      hS.abort_P, hwin, hwin0, htrans_c, hr, htrans_c', htrans0, hcomp, hcomp0', hhdr,
      hS.id_P P, hS.tcur_P P, hsend0', hnew, hc'2, hvRP, hstartP, hfs, m,
      hqep, hr_ep, pos, p, htriv_eq, htriv, vR', stP_final, γP', StateT.run_bind,
      StateT.run_pure, StateT.run_modify, simulateQ_bind, simulateQ_pure]
  by_cases hloc : localCKA mo 1 (esS.g.epoch P) = true
  · have hge : l + 2 ≤ esS.g.epoch P := by
      simp only [localCKA, mo, Option.isNone_some, Bool.false_or, htH,
        decide_eq_true_eq] at hloc
      omega
    have hloc_m : localCKA mo 1 m = true := by
      simp [localCKA, mo, htH, show l + 1 + 1 ≤ m by omega]
    have hnot_pre : ¬ (m + 1 ≤ l) := by omega
    have hh_eq : h_final = esS.h := by simp [h_final, hnot_pre]
    have hγC : (esS.g.st P).γ = some (esP.g.st P).γ := by
      rw [hS.γ_C P, hloc]; rfl
    have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t (.inr (.inr (P, c, c'))) esS sc =
        pure ((some (.accepted m i' (some m')),
          { esS with g := esS.g.accept P stC_final pos, h := h_final }), sc) := by
      rw [hh_eq]
      simp [stepCDFShiftedPaper, implEDFG, deliverForgeEG, commitE, vRecv, hS.abort_C,
        hwin0, hr, htrans0, hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0', hnew, hc'2,
        hstartC, hp1, hfs, hγC, hloc_m, m, hqep, hr_ep, pos, htriv, vR', γC_final,
        stC_final, γP', StateT.run_bind, StateT.run_pure, StateT.run_modify, simulateQ_pure]
    rw [hC, hP, pure_bind, pure_bind]
    exact ih _ _ _ _ _ (hS.accept_new P γP' vR' pos rfl hO_ep hS.b_C
      (fun h => by simp [m, mo, hloc_m] at h))
  · simp only [Bool.not_eq_true] at hloc
    have hγC : (esS.g.st P).γ = none := by rw [hS.γ_C P, hloc]; rfl
    obtain ⟨hsc_stP, hsc_epP⟩ := hS.cka_st P (Or.inl hloc)
    obtain ⟨hsc_stO, hsc_epO⟩ := hS.cka_st P.other (Or.inr (by simpa using hloc))
    have hcanR : sc.canReceive P = true := by
      simp [CKA.GameState.canReceive, hsc_epO, hsc_epP, hO_ep]
    have hlast_eq : sc.lastMsg = some Tm := hlast hloc
    let sc' := sc.afterReceive P γP'
    have hstP' : (sc.afterReceive P γP').st P = γP' := by simp [CKA.GameState.afterReceive]
    by_cases hfin : l + 2 ≤ m
    · have hloc_m : localCKA mo 1 m = true := by
        simp [localCKA, mo, htH, show l + 1 + 1 ≤ m by omega]
      have hnot_pre : ¬ (m + 1 ≤ l) := by omega
      have hh_eq : h_final = esS.h := by simp [h_final, hnot_pre]
      have hfin_sc : (sc.afterReceive P γP').finished 1 (l + 1) P = true :=
        finished_afterReceive_of_ge γP' (by rw [hsc_epP]; exact hfin)
      have hC :
          stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t (.inr (.inr (P, c, c'))) esS sc =
          pure ((some (.accepted m i' (some m')),
            { esS with g := esS.g.accept P stC_final pos, h := h_final }), sc') := by
        rw [hh_eq]
        simp [stepCDFShiftedPaper, implEDFG, deliverForgeEG, commitE, liftCShifted,
          CKA.receiveQuery, CKA.corrQuery, cImpl, CKA.oracleImpl, CKA.receiveImpl,
          CKA.corrImpl, vRecv, hS.abort_C, hwin0, hr, htrans0, hcomp0', hhdr, hS.id_C P,
          hS.tcur_C P, hsend0', hnew, hc'2, hstartC, hp1, hfs, hγC, hcanR, hlast_eq,
          hsc_stP, hfin, hfin_sc, hstP', hloc_m, sc',
          m, hqep, hr_ep, pos, htriv, vR', γC_final, stC_final, γP',
          simulateQ_bind, simulateQ_query, simulateQ_pure, map_eq_bind_pure_comp,
          StateT.run_bind, StateT.run_pure, StateT.run_modify]
      rw [hC, hP, pure_bind, pure_bind]
      exact ih _ _ _ _ _ (hS.accept_new P γP' vR' pos rfl hO_ep hS.b_C
        (fun h => by simp [m, mo, hloc_m] at h))
    · have hloc_m : localCKA mo 1 m = false := by
        simp [localCKA, mo, htH, show ¬ (l + 1 + 1 ≤ m) by omega]
      have hC :
          stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t (.inr (.inr (P, c, c'))) esS sc =
          pure ((some (.accepted m i' (some m')),
            { esS with g := esS.g.accept P stC_final pos, h := h_final }), sc') := by
        by_cases hpre : m + 1 ≤ l
        · have hall : (sc.afterReceive P γP').allowCorr (l + 1) = true :=
            allowCorr_afterReceive_of_le γP' (by rw [hsc_epP, hsc_epO, hO_ep])
              (by rw [hsc_epP]; exact hpre)
          have hh_eq : h_final =
              { esS.h with γPre := Function.update esS.h.γPre P (some γP') } := by
            simp [h_final, hpre]
          rw [hh_eq]
          simp [stepCDFShiftedPaper, implEDFG, deliverForgeEG, commitE, setγPreShifted,
            liftCShifted, CKA.receiveQuery, CKA.corrQuery, cImpl, CKA.oracleImpl,
            CKA.receiveImpl, CKA.corrImpl, vRecv, hS.abort_C, hwin0, hr, htrans0, hcomp0',
            hhdr, hS.id_C P, hS.tcur_C P, hsend0', hnew, hc'2, hstartC, hp1, hfs, hγC,
            hcanR, hlast_eq, hsc_stP, hfin, show esS.g.epoch P + 1 < l by omega,
            hall, hstP', hloc_m, sc', m, hqep, hr_ep, pos, htriv, vR', γC_final,
            stC_final, γP', simulateQ_bind, simulateQ_query, simulateQ_pure,
            map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify]
        · have hh_eq : h_final = esS.h := by simp [h_final, hpre]
          rw [hh_eq]
          simp [stepCDFShiftedPaper, implEDFG, deliverForgeEG, commitE, liftCShifted,
            CKA.receiveQuery, cImpl, CKA.oracleImpl, CKA.receiveImpl, vRecv, hS.abort_C,
            hwin0, hr, htrans0, hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0', hnew, hc'2,
            hstartC, hp1, hfs, hγC, hcanR, hlast_eq, hsc_stP, hfin,
            show ¬(esS.g.epoch P + 1 < l) by omega, hloc_m, sc', m,
            hqep, hr_ep, pos, htriv, vR', γC_final, stC_final, γP', simulateQ_bind,
            simulateQ_query, simulateQ_pure, map_eq_bind_pure_comp, StateT.run_bind,
            StateT.run_pure, StateT.run_modify]
      rw [hC, hP, pure_bind, pure_bind]
      refine ih _ _ _ _ _ (hS.accept_new P γP' vR' pos rfl hO_ep hS.b_C fun _ => ?_)
      simp [sc', CKA.GameState.afterReceive, Party.other_ne, hsc_epP, hsc_stO, hsc_epO,
        hO_ep]
omit [SampleableType KC] in
theorem step_deliverForgeE_new_epoch_DFShiftedPaper_le (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δ_off : ℕ) (b_auth : Bool) (qep l t : ℕ)
    (P : Party) (c c' : Header T × E) (r : SM.Record M (Header T × E))
    (esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I))
    (sc : CKA.GameState Γ T) (esP : EStateP Γ T Sig SS RS M E K)
    (sp : PRFPRNG.GameState Sig I K)
    (k : Option (SM.RecvResult M) → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (ih : ∀ r esS' sc' esP' sp',
      Sync10ShiftedPaper prng Δ_off l t esS' sc' esP' sp' →
      𝒟[runRDFShiftedPaper cka prng fs Δ_off b_auth qep l t (k r) esS' sc'] {true} ≤
        𝒟[runRDFShifted10Paper cka prng fs Δ_off b_auth qep l t (k r) esP' sp'] {true})
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp)
    (hwin0 : esS.g.win = false)
    (hr : esS.g.inTransit P.other c = some r)
    (htrans0 : esS.g.inTransit P.other c' = none)
    (hcomp0' : r.pos ∉ esS.g.comp)
    (hhdr : c.1 = c'.1)
    (hsend0 : P.sendsIn c'.1.1 = false)
    (hnew : c'.1.1 = esS.g.epoch P + 1) :
    𝒟[stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t (.inr (.inr (P, c, c'))) esS sc >>=
      fun r => runRDFShiftedPaper cka prng fs Δ_off b_auth qep l t (k r.1.1) r.1.2 r.2] {true} ≤
    𝒟[stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
      (.inr (.inr (P, c, c'))) esP sp >>=
      fun r => runRDFShifted10Paper cka prng fs Δ_off b_auth qep l t (k r.1.1) r.1.2 r.2]
      {true} := by
  have hwin : esP.g.win = esS.g.win := eraseSt_win hS.g_eq
  have htrans_c : esP.g.inTransit P.other c = esS.g.inTransit P.other c :=
    eraseSt_inTransit hS.g_eq P.other c
  have htrans_c' : esP.g.inTransit P.other c' = esS.g.inTransit P.other c' :=
    eraseSt_inTransit hS.g_eq P.other c'
  have hcomp : esP.g.comp = esS.g.comp := eraseSt_comp hS.g_eq
  have hesS_eq := estate_mk_abort_false hS.abort_C
  have hesP_eq := estate_mk_abort_false hS.abort_P
  have hnew_c : c.1.1 = esS.g.epoch P + 1 := by rw [hhdr, hnew]
  have hsend0' : P.sendsIn (esS.g.epoch P + 1) = false := hnew ▸ hsend0
  obtain ⟨hr_ep, hP_eq_R, hO_eq_S, hO_ep, hmax_eq, Tm, Im, hct2, hcC, hST, hSroot,
    hcP, hlast⟩ := hS.deliver_new_info hr hnew_c
  have hc'2 : c'.1.2 = some Tm := by rw [← hhdr, hct2]
  let p := prng.up (esS.g.st P).root Im
  have hp1 : (prng.up (esS.g.st P).root Im).1 = (esS.g.st P.other).root := hSroot.symm
  let γP' := (cka.receive (esP.g.st P).γ Tm).1
  have hstartC := fun ctx γv =>
    hooksCKAShifted_startRecv_honest cka prng fs l (tStarHook b_auth t) ctx P (esS.g.epoch P + 1)
      γv (esS.g.st P).root Tm Im esS.h hcC
  have hstartP : (simulateQ (pImpl prng)
      (((hooksPRNG cka prng fs (moHook b_auth l t)).startRecv esP.g P (esS.g.epoch P + 1)
        (esP.g.st P).γ (esP.g.st P).root Tm).run esP.h)).run sp =
      pure ((some (some (γP', (esP.g.st P.other).root, fs.initReceiver p.2)), esP.h),
        sp) := by
    simp [hooksPRNG, hcP, p, γP', StateT.run_bind, StateT.run_get, StateT.run_pure,
      simulateQ_pure]
  cases hfs : fs.receive (fs.initReceiver p.2) c'.1 c'.2 with
  | none =>
    have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t (.inr (.inr (P, c, c'))) esS sc =
        pure ((some .rejected, esS), sc) := by
      simp [stepCDFShiftedPaper, implEDFG, deliverForgeEG, vRecv, hS.abort_C, hwin0, hr,
        htrans0, hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0', hnew, hc'2, hstartC,
        hp1, p, hfs, StateT.run_bind, StateT.run_pure, simulateQ_pure, hesS_eq]
    have hP : stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
        (.inr (.inr (P, c, c'))) esP sp =
        pure ((some .rejected, esP), sp) := by
      simp [stepPDFShiftedPaperGen, implEDFG, deliverForgeEG, vRecv, hS.abort_P,
        hwin, hwin0, htrans_c, hr, htrans_c', htrans0, hcomp, hcomp0', hhdr, hS.id_P P,
        hS.tcur_P P, hsend0', hnew, hc'2, hstartP, hfs, StateT.run_bind, StateT.run_pure,
        simulateQ_bind, simulateQ_pure, hesP_eq]
    rw [hC, hP, pure_bind, pure_bind]
    exact ih (some .rejected) esS sc esP sp hS
  | some vim =>
    rcases vim with ⟨v', i', m'⟩
    let m := esS.g.epoch P + 1
    by_cases hqep : qep + 1 < m
    · have hC :
          stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t (.inr (.inr (P, c, c'))) esS sc =
          pure ((some .rejected, esS), sc) := by
        simp [stepCDFShiftedPaper, implEDFG, deliverForgeEG, vRecv, hS.abort_C, hwin0, hr,
          htrans0, hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0', hnew, hc'2, hstartC,
          hp1, p, hfs, m, hqep, StateT.run_bind, StateT.run_pure, simulateQ_pure, hesS_eq]
      have hP : stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
          (.inr (.inr (P, c, c'))) esP sp =
          pure ((some .rejected, esP), sp) := by
        simp [stepPDFShiftedPaperGen, implEDFG, deliverForgeEG, vRecv,
          hS.abort_P, hwin, hwin0, htrans_c, hr, htrans_c', htrans0, hcomp, hcomp0', hhdr,
          hS.id_P P, hS.tcur_P P, hsend0', hnew, hc'2, hstartP, hfs, m, hqep,
          StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure, hesP_eq]
      rw [hC, hP, pure_bind, pure_bind]
      exact ih (some .rejected) esS sc esP sp hS
    · let pos : SM.Pos := ⟨P.other, m, i'⟩
      have htriv_eq : trivHook b_auth Δ_off t esP.g pos = trivHook b_auth Δ_off t esS.g pos :=
        eraseSt_trivHook hS.g_eq b_auth Δ_off t pos
      by_cases htriv : trivHook b_auth Δ_off t esS.g pos
      · exact step_deliverForgeE_new_epoch_triv_DFShiftedPaper_le cka prng fs Δ_off b_auth qep l t P
          c c' r Tm Im v' i' m' esS sc esP sp k ih hS hwin0 hr htrans0 hcomp0' hhdr hsend0' hnew
          hr_ep hO_ep hc'2 hcC hSroot hcP hlast hfs hqep htriv
      · simp only [Bool.not_eq_true] at htriv
        by_cases hinj : (SM.Config.auth (Msg := M) t).injectFull m
        · have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
              (.inr (.inr (P, c, c'))) esS sc =
              pure ((some .rejected, { esS with g := { esS.g with win := true } }), sc) := by
            simp [stepCDFShiftedPaper, implEDFG, deliverForgeEG, vRecv, hS.abort_C, hwin0,
              hr, htrans0, hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0', hnew, hc'2, hstartC,
              hp1, p, hfs, m, hqep, hr_ep, pos, htriv, hinj, StateT.run_bind,
              StateT.run_pure, StateT.run_modify, simulateQ_pure]
          have hP : stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
              (.inr (.inr (P, c, c'))) esP sp =
              pure ((some .rejected, { esP with g := { esP.g with win := true } }), sp) := by
            simp [stepPDFShiftedPaperGen, implEDFG, deliverForgeEG, vRecv,
              hS.abort_P, hwin, hwin0, htrans_c, hr, htrans_c', htrans0, hcomp, hcomp0',
              hhdr, hS.id_P P, hS.tcur_P P, hsend0', hnew, hc'2, hstartP, hfs, m,
              hqep, hr_ep, pos, htriv_eq, htriv, hinj, StateT.run_bind, StateT.run_pure,
              StateT.run_modify, simulateQ_bind, simulateQ_pure]
          rw [hC, hP, pure_bind, pure_bind]
          exact ih (some .rejected) _ _ _ _ (hS.set_win_prf true sp.prf (Or.inl rfl))
        · simp only [Bool.not_eq_true] at hinj
          have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
              (.inr (.inr (P, c, c'))) esS sc =
              pure ((some .rejected, esS), sc) := by
            simp [stepCDFShiftedPaper, implEDFG, deliverForgeEG, vRecv, hS.abort_C, hwin0,
              hr, htrans0, hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0', hnew, hc'2, hstartC,
              hp1, p, hfs, m, hqep, hr_ep, pos, htriv, hinj, StateT.run_bind,
              StateT.run_pure, simulateQ_pure, hesS_eq]
          have hP : stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
              (.inr (.inr (P, c, c'))) esP sp =
              pure ((some .rejected, esP), sp) := by
            simp [stepPDFShiftedPaperGen, implEDFG, deliverForgeEG, vRecv,
              hS.abort_P, hwin, hwin0, htrans_c, hr, htrans_c', htrans0, hcomp, hcomp0',
              hhdr, hS.id_P P, hS.tcur_P P, hsend0', hnew, hc'2, hstartP, hfs, m,
              hqep, hr_ep, pos, htriv_eq, htriv, hinj, StateT.run_bind, StateT.run_pure,
              simulateQ_bind, simulateQ_pure, hesP_eq]
          rw [hC, hP, pure_bind, pure_bind]
          exact ih (some .rejected) esS sc esP sp hS
omit [SampleableType KC] in
theorem step_deliverForgeE_DFShiftedPaper_le (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δ_off : ℕ) (b_auth : Bool) (qep l t : ℕ)
    (P : Party) (c c' : Header T × E)
    (esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I))
    (sc : CKA.GameState Γ T) (esP : EStateP Γ T Sig SS RS M E K)
    (sp : PRFPRNG.GameState Sig I K)
    (k : Option (SM.RecvResult M) → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (ih : ∀ r esS' sc' esP' sp',
      Sync10ShiftedPaper prng Δ_off l t esS' sc' esP' sp' →
      𝒟[runRDFShiftedPaper cka prng fs Δ_off b_auth qep l t (k r) esS' sc'] {true} ≤
        𝒟[runRDFShifted10Paper cka prng fs Δ_off b_auth qep l t (k r) esP' sp'] {true})
    (hS : Sync10ShiftedPaper prng Δ_off l t esS sc esP sp) :
    𝒟[stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t (.inr (.inr (P, c, c'))) esS sc >>=
      fun r => runRDFShiftedPaper cka prng fs Δ_off b_auth qep l t (k r.1.1) r.1.2 r.2] {true} ≤
    𝒟[stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
      (.inr (.inr (P, c, c'))) esP sp >>=
      fun r => runRDFShifted10Paper cka prng fs Δ_off b_auth qep l t (k r.1.1) r.1.2 r.2]
      {true} := by
  have hwin : esP.g.win = esS.g.win := eraseSt_win hS.g_eq
  have htrans_c : esP.g.inTransit P.other c = esS.g.inTransit P.other c :=
    eraseSt_inTransit hS.g_eq P.other c
  have htrans_c' : esP.g.inTransit P.other c' = esS.g.inTransit P.other c' :=
    eraseSt_inTransit hS.g_eq P.other c'
  have hcomp : esP.g.comp = esS.g.comp := eraseSt_comp hS.g_eq
  have hesS_eq := estate_mk_abort_false hS.abort_C
  have hesP_eq := estate_mk_abort_false hS.abort_P
  by_cases hwin0 : esS.g.win = true
  · have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t (.inr (.inr (P, c, c'))) esS sc =
        pure ((none, esS), sc) := by
      simp [stepCDFShiftedPaper, implEDFG, deliverForgeEG, hS.abort_C, hwin0]
    have hP : stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
        (.inr (.inr (P, c, c'))) esP sp =
        pure ((none, esP), sp) := by
      simp [stepPDFShiftedPaperGen, implEDFG, deliverForgeEG, hS.abort_P, hwin,
        hwin0]
    rw [hC, hP, pure_bind, pure_bind]
    exact ih none esS sc esP sp hS
  · simp only [Bool.not_eq_true] at hwin0
    cases hr : esS.g.inTransit P.other c with
    | none =>
      have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
          (.inr (.inr (P, c, c'))) esS sc =
          pure ((none, esS), sc) := by
        simp [stepCDFShiftedPaper, implEDFG, deliverForgeEG, hS.abort_C, hwin0, hr]
      have hP : stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
          (.inr (.inr (P, c, c'))) esP sp =
          pure ((none, esP), sp) := by
        simp [stepPDFShiftedPaperGen, implEDFG, deliverForgeEG, hS.abort_P, hwin,
          hwin0, htrans_c, hr]
      rw [hC, hP, pure_bind, pure_bind]
      exact ih none esS sc esP sp hS
    | some r =>
      by_cases hguard :
          ((esS.g.inTransit P.other c').isSome || esS.g.comp.contains r.pos || c.1 != c'.1) = true
      · simp only [Bool.or_eq_true, List.contains_iff_mem, bne_iff_ne] at hguard
        have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
            (.inr (.inr (P, c, c'))) esS sc =
            pure ((none, esS), sc) := by
          simp [stepCDFShiftedPaper, implEDFG, deliverForgeEG, hS.abort_C, hwin0, hr,
            hguard, StateT.run_pure]
        have hP : stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
            (.inr (.inr (P, c, c'))) esP sp =
            pure ((none, esP), sp) := by
          simp [stepPDFShiftedPaperGen, implEDFG, deliverForgeEG, hS.abort_P,
            hwin, hwin0, htrans_c, hr, htrans_c', hcomp, hguard, StateT.run_pure]
        rw [hC, hP, pure_bind, pure_bind]
        exact ih none esS sc esP sp hS
      · simp only [Bool.not_eq_true, Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hguard
        rcases hguard with ⟨⟨htrans0, hcomp0⟩, hhdr⟩
        have hcomp0' : r.pos ∉ esS.g.comp := by simpa using hcomp0
        have hhdr' : c'.1 = c.1 := hhdr.symm
        obtain ⟨hmem, hsender, hct⟩ := inTransit_some_props hr
        obtain ⟨ht1, hsend_other, hle_other, _⟩ := hS.trans_inv r hmem
        rw [hct] at ht1
        rw [hsender] at hsend_other hle_other
        have hsend0 : P.sendsIn c'.1.1 = false := by
          rw [hhdr', ht1]
          have h1 := AuthL10.sendsIn_other P r.pos.epoch
          rw [hsend_other] at h1
          simpa using h1.symm
        have hmax_bound : esS.g.epoch P.other ≤ esS.g.epoch P + 1 := by
          rcases hS.ping_pong with ⟨hR, _⟩ | ⟨_, hR, _⟩
          · have hepP := epoch_eq_of_synced hS.epoch_S hR P
            have hepO := epoch_eq_of_synced hS.epoch_S hR P.other
            omega
          · rcases party_cases_of_epoch (max (esS.g.epoch .A) (esS.g.epoch .B)) P with hP | hP
            · have hO : P.other = Party.receiverOf (max (esS.g.epoch .A) (esS.g.epoch .B)) := by
                rw [hP, senderOf_other]
              have hS_ep := hS.epoch_S
              rw [← hP] at hS_ep
              rw [← hO] at hR
              omega
            · have hO : P.other = Party.senderOf (max (esS.g.epoch .A) (esS.g.epoch .B)) := by
                rw [hP, receiverOf_other]
              have hS_ep := hS.epoch_S
              rw [← hO] at hS_ep
              rw [← hP] at hR
              omega
        have hle : ¬ (esS.g.epoch P + 1 < c'.1.1) := by rw [hhdr', ht1]; omega
        by_cases hnew : c'.1.1 = esS.g.epoch P + 1
        · exact step_deliverForgeE_new_epoch_DFShiftedPaper_le cka prng fs Δ_off b_auth qep l t P c
            c' r esS sc esP sp k ih hS hwin0 hr (by simpa using htrans0) hcomp0' hhdr hsend0 hnew
        · have hle_ep : c'.1.1 ≤ esS.g.epoch P := by omega
          have hvRP : (esP.g.st P).vR c'.1.1 = (esS.g.st P).vR c'.1.1 := by rw [hS.vR_eq P]
          cases hvR : (esS.g.st P).vR c'.1.1 with
          | none =>
            have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
                (.inr (.inr (P, c, c'))) esS sc =
                pure ((some .rejected, esS), sc) := by
              simp [stepCDFShiftedPaper, implEDFG, deliverForgeEG, vRecv, hS.abort_C,
                hwin0, hr, htrans0, hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR,
                StateT.run_bind, StateT.run_pure, simulateQ_pure, hesS_eq]
            have hP : stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
                (.inr (.inr (P, c, c'))) esP sp =
                pure ((some .rejected, esP), sp) := by
              simp [stepPDFShiftedPaperGen, implEDFG, deliverForgeEG, vRecv,
                hS.abort_P, hwin, hwin0, htrans_c, hr, htrans_c', htrans0, hcomp, hcomp0',
                hhdr, hS.id_P P, hS.tcur_P P, hsend0, hle, hnew, hvRP, hvR,
                StateT.run_bind, StateT.run_pure, simulateQ_pure, hesP_eq]
            rw [hC, hP, pure_bind, pure_bind]
            exact ih (some .rejected) esS sc esP sp hS
          | some v =>
            cases hfs : fs.receive v c'.1 c'.2 with
            | none =>
              have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
                  (.inr (.inr (P, c, c'))) esS sc =
                  pure ((some .rejected, esS), sc) := by
                simp [stepCDFShiftedPaper, implEDFG, deliverForgeEG, vRecv, hS.abort_C,
                  hwin0, hr, htrans0, hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0, hle, hnew,
                  hvR, hfs, StateT.run_bind, StateT.run_pure, simulateQ_pure, hesS_eq]
              have hP : stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
                  (.inr (.inr (P, c, c'))) esP sp =
                  pure ((some .rejected, esP), sp) := by
                simp [stepPDFShiftedPaperGen, implEDFG, deliverForgeEG, vRecv,
                  hS.abort_P, hwin, hwin0, htrans_c, hr, htrans_c', htrans0, hcomp,
                  hcomp0', hhdr, hS.id_P P, hS.tcur_P P, hsend0, hle, hnew, hvRP,
                  hvR, hfs, StateT.run_bind, StateT.run_pure, simulateQ_pure, hesP_eq]
              rw [hC, hP, pure_bind, pure_bind]
              exact ih (some .rejected) esS sc esP sp hS
            | some vim =>
              rcases vim with ⟨v', i', m'⟩
              have heq_ep : r.pos.epoch = c'.1.1 := by rw [hhdr', ht1]
              by_cases hqep : qep + 1 < c'.1.1
              · have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
                    (.inr (.inr (P, c, c'))) esS sc =
                    pure ((some .rejected, esS), sc) := by
                  simp [stepCDFShiftedPaper, implEDFG, deliverForgeEG, vRecv, hS.abort_C,
                    hwin0, hr, htrans0, hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0, hle, hnew,
                    hvR, hfs, hqep, StateT.run_bind, StateT.run_pure, simulateQ_pure, hesS_eq]
                have hP : stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
                    (.inr (.inr (P, c, c'))) esP sp =
                    pure ((some .rejected, esP), sp) := by
                  simp [stepPDFShiftedPaperGen, implEDFG, deliverForgeEG, vRecv,
                    hS.abort_P, hwin, hwin0, htrans_c, hr, htrans_c', htrans0, hcomp,
                    hcomp0', hhdr, hS.id_P P, hS.tcur_P P, hsend0, hle, hnew,
                    hvRP, hvR, hfs, hqep, StateT.run_bind, StateT.run_pure, simulateQ_pure, hesP_eq]
                rw [hC, hP, pure_bind, pure_bind]
                exact ih (some .rejected) esS sc esP sp hS
              · let pos : SM.Pos := ⟨P.other, c'.1.1, i'⟩
                have htriv_eq :
                    trivHook b_auth Δ_off t esP.g pos = trivHook b_auth Δ_off t esS.g pos :=
                  eraseSt_trivHook hS.g_eq b_auth Δ_off t pos
                by_cases htriv : trivHook b_auth Δ_off t esS.g pos
                · let vR' := Function.update (esS.g.st P).vR c'.1.1 (some v')
                  have hvR'_eq : Function.update (esP.g.st P).vR c'.1.1 (some v') = vR' := by
                    simp [vR', hS.vR_eq P]
                  have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
                      (.inr (.inr (P, c, c'))) esS sc =
                      pure ((some (.accepted c'.1.1 i' (some m')),
                        { esS with g := esS.g.accept P { esS.g.st P with vR := vR' } pos }),
                        sc) := by
                    simp [stepCDFShiftedPaper, implEDFG, deliverForgeEG, vRecv, commitE,
                      hS.abort_C, hwin0, hr, htrans0, hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0,
                      hle, hnew, hvR, hfs, hqep, heq_ep, htriv, pos, vR', StateT.run_bind,
                      StateT.run_pure, StateT.run_modify, simulateQ_pure]
                  have hP : stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
                      (.inr (.inr (P, c, c'))) esP sp =
                      pure ((some (.accepted c'.1.1 i' (some m')),
                        { esP with g := esP.g.accept P { esP.g.st P with vR := vR' } pos }),
                        sp) := by
                    simp [stepPDFShiftedPaperGen, implEDFG, deliverForgeEG, vRecv,
                      commitE, hS.abort_P, hwin, hwin0, htrans_c, hr, htrans_c', htrans0,
                      hcomp, hcomp0', hhdr, hS.id_P P, hS.tcur_P P, hsend0, hle,
                      hnew, hvRP, hvR, hfs, hqep, heq_ep, htriv_eq, htriv, pos, hvR'_eq,
                      StateT.run_bind, StateT.run_pure, StateT.run_modify, simulateQ_pure]
                  rw [hC, hP, pure_bind, pure_bind]
                  exact ih _ _ _ _ _ (hS.accept_old P vR' pos hle_ep)
                · simp only [Bool.not_eq_true] at htriv
                  by_cases hinj : (SM.Config.auth (Msg := M) t).injectFull c'.1.1
                  · have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
                        (.inr (.inr (P, c, c'))) esS sc =
                        pure ((some .rejected, { esS with g := { esS.g with win := true } }),
                          sc) := by
                      simp [stepCDFShiftedPaper, implEDFG, deliverForgeEG, vRecv,
                        hS.abort_C, hwin0, hr, htrans0, hcomp0', hhdr, hS.id_C P, hS.tcur_C P,
                        hsend0, hle, hnew, hvR, hfs, hqep, heq_ep, htriv, hinj, pos,
                        StateT.run_bind, StateT.run_pure, StateT.run_modify, simulateQ_pure]
                    have hP : stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
                        (.inr (.inr (P, c, c'))) esP sp =
                        pure ((some .rejected, { esP with g := { esP.g with win := true } }),
                          sp) := by
                      simp [stepPDFShiftedPaperGen, implEDFG, deliverForgeEG, vRecv,
                        hS.abort_P, hwin, hwin0, htrans_c, hr, htrans_c', htrans0, hcomp,
                        hcomp0', hhdr, hS.id_P P, hS.tcur_P P, hsend0, hle, hnew,
                        hvRP, hvR, hfs, hqep, heq_ep, htriv_eq, htriv, hinj, pos,
                        StateT.run_bind, StateT.run_pure, StateT.run_modify, simulateQ_pure]
                    rw [hC, hP, pure_bind, pure_bind]
                    exact ih (some .rejected) _ _ _ _ (hS.set_win_prf true sp.prf (Or.inl rfl))
                  · simp only [Bool.not_eq_true] at hinj
                    have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
                        (.inr (.inr (P, c, c'))) esS sc =
                        pure ((some .rejected, esS), sc) := by
                      simp [stepCDFShiftedPaper, implEDFG, deliverForgeEG, vRecv,
                        hS.abort_C, hwin0, hr, htrans0, hcomp0', hhdr, hS.id_C P, hS.tcur_C P,
                        hsend0, hle, hnew, hvR, hfs, hqep, heq_ep, htriv, hinj, pos,
                        StateT.run_bind, StateT.run_pure, simulateQ_pure, hesS_eq]
                    have hP : stepPDFShiftedPaperGen cka prng fs Δ_off b_auth qep l t
                        (.inr (.inr (P, c, c'))) esP sp =
                        pure ((some .rejected, esP), sp) := by
                      simp [stepPDFShiftedPaperGen, implEDFG, deliverForgeEG, vRecv,
                        hS.abort_P, hwin, hwin0, htrans_c, hr, htrans_c', htrans0, hcomp,
                        hcomp0', hhdr, hS.id_P P, hS.tcur_P P, hsend0, hle, hnew,
                        hvRP, hvR, hfs, hqep, heq_ep, htriv_eq, htriv, hinj, pos,
                        StateT.run_bind, StateT.run_pure, simulateQ_pure, hesP_eq]
                    rw [hC, hP, pure_bind, pure_bind]
                    exact ih (some .rejected) esS sc esP sp hS
def postSendCShiftedPaper (fs : FSAEADScheme K SS RS (Header T) M E) (Δ_off : ℕ) (P : Party)
    (m_msg : M) (bad : Bool)
    (esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I))
    (res : Option (Option Γ × T × Sig × SS) × CKAStateShifted Γ T I) :
    Option (Header T × E) ×
      EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I) :=
  match res.1 with
  | none => (none, { esS with h := res.2, abort := true })
  | some (γ', Tm, σ', ss) =>
    let m := esS.g.epoch P + 1
    let h : Header T := (m, some Tm)
    let fe := fs.send ss h m_msg
    let stC' : VP (Option Γ) T Sig SS RS :=
      { esS.g.st P with tcur := m, γ := γ', curCkaMsg := some Tm, root := σ', vS := some fe.1 }
    let gC₁ := epMgmtNew esS.g (2 + Δ_off) P bad
    let rcd : SM.Record M (Header T × E) := ⟨⟨P, m, 1⟩, m_msg, (h, fe.2)⟩
    (some (h, fe.2), { esS with g := gC₁.record (2 + Δ_off) P stC' rcd false, h := res.2 })

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem stepCDFShiftedPaper_transmit_new (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δ_off : ℕ) (b_auth : Bool) (qep l t : ℕ) (P : Party) (m_msg : M)
    (r : Option CCoins)
    (esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I))
    (sc : CKA.GameState Γ T)
    (hab : esS.abort = false) (hwin : esS.g.win = false)
    (hid : (esS.g.st P).id = P) (htcur : (esS.g.st P).tcur = esS.g.epoch P)
    (hsend : P.sendsIn (esS.g.epoch P + 1) = true)
    (hqep : ¬ qep < esS.g.epoch P + 1)
    (hdoom : (⟨true, some (l - 1), t⟩ : Policy).leakDoom esS.g
      (epMgmtNew esS.g (2 + Δ_off) P r.isSome) = false) :
    stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
        (.inr (.inl (.inl (.inl (.inl (.inl (P, m_msg, r))))))) esS sc =
      (simulateQ (cImpl cka 1 (l + 1))
        (((hooksCKAShifted cka prng fs l (tStarHook b_auth t)).startSend
          (epMgmtNew esS.g (2 + Δ_off) P r.isSome)
          P (esS.g.epoch P + 1) (esS.g.st P).γ (esS.g.st P).root r).run esS.h)).run sc >>=
        fun out => pure (postSendCShiftedPaper fs Δ_off P m_msg r.isSome esS out.1, out.2) := by
  have hep := epMgmt_eq_epMgmtNew esS.g (2 + Δ_off) qep P r.isSome hsend hqep
  simp only [stepCDFShiftedPaper, implEDFG, QueryImpl.add_apply, transmitE, hab, hwin,
    Bool.or_self, Bool.false_eq_true, ↓reduceIte, hep, hdoom, vSend, epMgmtNew_st, hid, htcur,
    hsend, run_liftH, StateT.run_bind, StateT.run_get, pure_bind, bind_assoc, simulateQ_bind]
  congr 1
  funext out
  rcases out with ⟨⟨ans, h'⟩, sc'⟩
  cases ans with
  | none =>
    simp [postSendCShiftedPaper, abortE, StateT.run_modify, simulateQ_pure, StateT.run_pure]
  | some val =>
    rcases val with ⟨γ', Tm, σ', ss⟩
    simp [postSendCShiftedPaper, hooksCKAShifted, hid, hab, StateT.run_modify,
      StateT.run_pure, simulateQ_pure]

omit [SampleableType KC] in
theorem ih_postSend_new_DFShiftedPaper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δ_off : ℕ) (b_auth : Bool) (qep l t : ℕ)
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
    (γP' : Γ) (Tm : T) (Im : I) (sc' : CKA.GameState Γ T) (sp' : PRFPRNG.GameState Sig I K)
    (hsend : P.sendsIn (esS.g.epoch P + 1) = true)
    (hb_sc' : sc'.b = true) (hb_sp' : sp'.b = false)
    (hcka' : localCKA ⟨true, some (l - 1), t⟩ 1 (esS.g.epoch P) = false →
      sc'.st P = γP' ∧ sc'.epoch P = esS.g.epoch P + 1 ∧
      sc'.st P.other = (esP.g.st P.other).γ ∧ sc'.epoch P.other = esS.g.epoch P ∧
      sc'.lastMsg = some Tm)
    (hprng_before : esS.g.epoch P + 1 < t →
      ((some (l - 1)).isSome && decide (esS.g.epoch P + 1 < (⟨true, some (l - 1), t⟩ : Mode).tH)) =
        true →
      sp'.σ = (prng.up (esS.g.st P).root Im).1 ∧
      sp'.corr = true ∧ sp'.prng = false ∧ sp'.prf = false)
    (hprng_after : esS.g.epoch P + 1 < t →
      ((some (l - 1)).isSome && decide (esS.g.epoch P + 1 < (⟨true, some (l - 1), t⟩ : Mode).tH)) =
        false →
      sp'.σ = (prng.up (esS.g.st P).root Im).1 ∧
      sp'.corr = false ∧ sp'.prng = false ∧
      (esS.g.epoch P + 1 + 1 < t → sp'.prf = false))
    (hprng_at : esS.g.epoch P + 1 = t →
      ((some (l - 1)).isSome && decide (t = (⟨true, some (l - 1), t⟩ : Mode).tH)) = false →
      sp'.σ = (esS.g.st P).root ∧ sp'.corr = false ∧ sp'.prng = false) :
    let mo : Mode := ⟨true, some (l - 1), t⟩
    let m := esS.g.epoch P + 1
    let p := prng.up (esS.g.st P).root Im
    let σP' := if knownRoot mo m then some p.1 else none
    let resC : Option (Option Γ × T × Sig × SS) × CKAStateShifted Γ T I :=
      (some (if localCKA mo 1 m then some γP' else none, Tm, p.1, fs.initSender p.2),
        { base := { cache := Function.update esS.h.base.cache m (some (Tm, Im)) }
          γPre := if m + 1 ≤ l then Function.update esS.h.γPre P (some γP') else esS.h.γPre })
    let resP : Option (Γ × T × Option Sig × SS) × PRNGState T Sig K :=
      (some (γP', Tm, σP', fs.initSender p.2),
        { cache := Function.update esP.h.cache m (some (Tm, σP', p.2)) })
    let outC := postSendCShiftedPaper fs Δ_off P m_msg bad esS resC
    let outP := postSendP fs Δ_off P m_msg bad esP resP
    𝒟[runRDFShiftedPaper cka prng fs Δ_off b_auth qep l t (k outC.1) outC.2 sc'] {true} ≤
      𝒟[runRDFShifted10Paper cka prng fs Δ_off b_auth qep l t (k outP.1) outP.2 sp'] {true} := by
  intro mo m p σP' resC resP outC outP
  have hepP : esP.g.epoch P = esS.g.epoch P := congrFun (eraseSt_epoch hS.g_eq) P
  let fe := fs.send (fs.initSender p.2) (m, some Tm) m_msg
  have hS' := hS.record_new_epoch P bad γP' Tm Im fe.1 m_msg fe.2 sc' sp' hsend hb_sc' hb_sp'
    hcka' hprng_before hprng_after hprng_at
  dsimp only [outC, outP, resC, resP, postSendCShiftedPaper, postSendP]
  simp only [hepP, m]
  exact ih (some ((m, some Tm), fe.2)) _ _ _ _ hS'
omit [SampleableType KC] in
theorem step_transmitE_same_epoch_DFShiftedPaper_le (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δ_off : ℕ) (b_auth : Bool) (qep l t : ℕ)
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
    (hsend : P.sendsIn (esS.g.epoch P + 1) = false) :
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
  have hidxP : esP.g.idx P = esS.g.idx P := congrFun (eraseSt_idx hS.g_eq) P
  have hsend0 : P.sendsIn (esS.g.epoch P) = true := sendsIn_of_succ_false hsend
  by_cases hqep : qep < esS.g.epoch P
  · have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
        (.inr (.inl (.inl (.inl (.inl (.inl (P, m_msg, r))))))) esS sc =
        pure ((none, esS), sc) := by
      simp [stepCDFShiftedPaper, implEDFG, transmitE, SM.GameState.epMgmt, hS.abort_C,
        hwin0, hsend, hqep]
    have hP : stepP cka prng fs Δ_off qep mo
        (.inr (.inl (.inl (.inl (.inl (P, m_msg, r)))))) esP sp =
        pure ((none, esP), sp) := by
      simp [stepP, implE, transmitE, SM.GameState.epMgmt, hS.abort_P, hwin, hwin0, hepP,
        hsend, hqep]
    rw [hC, hP_eq, hP, pure_bind, pure_bind]
    exact ih none esS sc esP sp hS
  · have hld : mo.policy.leakDoom esP.g esP.g = mo.policy.leakDoom esS.g esS.g :=
      eraseSt_leakDoom hS.g_eq hS.g_eq mo.policy
    by_cases hdoom : mo.policy.leakDoom esS.g esS.g
    · have hdoom' : (⟨true, some (l - 1), t⟩ : Policy).leakDoom esS.g esS.g = true := hdoom
      have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
          (.inr (.inl (.inl (.inl (.inl (.inl (P, m_msg, r))))))) esS sc =
          pure ((none, { esS with abort := true }), sc) := by
        simp [stepCDFShiftedPaper, implEDFG, transmitE, abortE, SM.GameState.epMgmt,
          hS.abort_C, hwin0, hsend, hqep, hdoom', StateT.run_modify]
      rw [hC, pure_bind]
      exact runRDFShiftedPaper_abort_apply_true_le cka prng fs Δ_off b_auth qep l t (k none) rfl _
    · simp only [Bool.not_eq_true] at hdoom
      have hdoom' : (⟨true, some (l - 1), t⟩ : Policy).leakDoom esS.g esS.g = false := hdoom
      have hvSP : (esP.g.st P).vS = (esS.g.st P).vS := hS.vS_eq P
      have hTcurP : (esP.g.st P).curCkaMsg = (esS.g.st P).curCkaMsg := hS.Tcur_eq P
      cases hvS : (esS.g.st P).vS with
      | none =>
        have hstC : ({ esS.g.st P with vS := none } : VP (Option Γ) T Sig SS RS) = esS.g.st P := by
          rcases h : esS.g.st P with ⟨id, root, vS, vR, γ, curCkaMsg, tcur⟩
          rw [h] at hvS; subst hvS; rfl
        have hstP : ({ esP.g.st P with vS := none } : VP Γ T (Option Sig) SS RS) = esP.g.st P := by
          have hvSP0 : (esP.g.st P).vS = none := hvSP.trans hvS
          rcases h : esP.g.st P with ⟨id, root, vS, vR, γ, curCkaMsg, tcur⟩
          rw [h] at hvSP0; subst hvSP0; rfl
        let c : Header T × E := ((esS.g.epoch P, (esS.g.st P).curCkaMsg), default)
        let rcd : SM.Record M (Header T × E) := ⟨⟨P, esS.g.epoch P, esS.g.idx P + 1⟩, m_msg, c⟩
        have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
            (.inr (.inl (.inl (.inl (.inl (.inl (P, m_msg, r))))))) esS sc =
            pure ((some c, { esS with g := esS.g.record (2 + Δ_off) P (esS.g.st P) rcd false }),
              sc) := by
          simp [stepCDFShiftedPaper, implEDFG, transmitE, vSend, SM.GameState.epMgmt,
            hS.abort_C, hwin0, hsend, hqep, hdoom', hS.id_C P, hS.tcur_C P, hvS, c, rcd,
            StateT.run_pure, StateT.run_modify]
        have hP : stepP cka prng fs Δ_off qep mo
            (.inr (.inl (.inl (.inl (.inl (P, m_msg, r)))))) esP sp =
            pure ((some c, { esP with g := esP.g.record (2 + Δ_off) P (esP.g.st P) rcd false }),
              sp) := by
          simp [stepP, implE, transmitE, vSend, SM.GameState.epMgmt, hS.abort_P, hwin,
            hwin0, hepP, hidxP, hld, hsend, hqep, hdoom, hS.id_P P, hS.tcur_P P,
            hvSP, hvS, hTcurP, c, rcd, StateT.run_pure, StateT.run_modify]
        rw [hC, hP_eq, hP, pure_bind, pure_bind, ← hstC, ← hstP]
        exact ih (some c) _ _ _ _ (hS.record_same_epoch P none m_msg default hsend0)
      | some v =>
        let h : Header T := (esS.g.epoch P, (esS.g.st P).curCkaMsg)
        let fe := fs.send v h m_msg
        let c : Header T × E := (h, fe.2)
        let rcd : SM.Record M (Header T × E) := ⟨⟨P, esS.g.epoch P, esS.g.idx P + 1⟩, m_msg, c⟩
        have hC : stepCDFShiftedPaper cka prng fs Δ_off b_auth qep l t
            (.inr (.inl (.inl (.inl (.inl (.inl (P, m_msg, r))))))) esS sc =
            pure ((some c, { esS with
              g := esS.g.record (2 + Δ_off) P { esS.g.st P with vS := some fe.1 } rcd false }),
              sc) := by
          simp [stepCDFShiftedPaper, implEDFG, transmitE, vSend, hooksCKAShifted,
            SM.GameState.epMgmt, hS.abort_C, hwin0, hsend, hqep, hdoom',
            hS.id_C P, hS.tcur_C P, hvS, h, fe, c, rcd, StateT.run_pure, StateT.run_modify]
        have hP : stepP cka prng fs Δ_off qep mo
            (.inr (.inl (.inl (.inl (.inl (P, m_msg, r)))))) esP sp =
            pure ((some c, { esP with
              g := esP.g.record (2 + Δ_off) P { esP.g.st P with vS := some fe.1 } rcd false }),
              sp) := by
          simp [stepP, implE, transmitE, vSend, SM.GameState.epMgmt,
            hS.abort_P, hwin, hwin0, hepP, hidxP, hld, hsend, hqep, hdoom,
            hS.id_P P, hS.tcur_P P, hvSP, hvS, hTcurP, h, fe, c, rcd,
            StateT.run_pure, StateT.run_modify]
        rw [hC, hP_eq, hP, pure_bind, pure_bind]
        exact ih (some c) _ _ _ _ (hS.record_same_epoch P (some fe.1) m_msg fe.2 hsend0)

end AuthL10ShiftedPaper

end CryptoGames.SM.Construction.DeliverForge

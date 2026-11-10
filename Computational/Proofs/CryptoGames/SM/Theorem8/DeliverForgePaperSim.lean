/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperCKA
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFS
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma10
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma9
import VCVio.OracleComp.EvalDist.Measure

/-!
# `DeliverForge` Paper-Game Lemma 10 and Theorem 8

**Checked by Lean.** Proves `lemma10_df_paper` and assembles `theorem8_df_paper` under
`corrAllowedPaper`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.SM.Construction.DeliverForge.AuthL10DF

open CryptoGames.SM CryptoGames.SM.Engine CryptoGames.SM.Construction.AuthL10

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

variable (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)

theorem step_deliverForgeE_DFPaper_le (mo : Mode) (_hauth : mo.auth = true)
    (P : Party) (c c' : Header T × E)
    (k : Option (SM.RecvResult M) → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp)
    (ih : ∀ u {esC' sc' esP' sp'},
      Sync prng Δcka mo esC' sc' esP' sp' →
      𝒟[runLDFPaper cka prng fs Δcka qep mo (k u) esC' sc'] {true} ≤
        𝒟[runRDFPaper cka prng fs Δcka qep mo (k u) esP' sp'] {true}) :
    𝒟[stepCDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esC sc >>= fun r =>
        runLDFPaper cka prng fs Δcka qep mo (k r.1.1) r.1.2 r.2] {true} ≤
      𝒟[stepPDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esP sp >>= fun r =>
        runRDFPaper cka prng fs Δcka qep mo (k r.1.1) r.1.2 r.2] {true} := by
  have hwin : esP.g.win = esC.g.win := eraseSt_win hS.g_eq
  have htrans_c : esP.g.inTransit P.other c = esC.g.inTransit P.other c :=
    eraseSt_inTransit hS.g_eq P.other c
  have htrans_c' : esP.g.inTransit P.other c' = esC.g.inTransit P.other c' :=
    eraseSt_inTransit hS.g_eq P.other c'
  have hcomp : esP.g.comp = esC.g.comp := eraseSt_comp hS.g_eq
  have hesC_eq :
      ({ g := esC.g, h := esC.h, abort := false } : EStateC Γ T Sig SS RS M E I) = esC :=
    estate_mk_abort_false hS.abort_C
  have hesP_eq :
      ({ g := esP.g, h := esP.h, abort := false } : EStateP Γ T Sig SS RS M E K) = esP :=
    estate_mk_abort_false hS.abort_P
  by_cases hwin0 : esC.g.win = true
  · have hC : stepCDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esC sc =
        pure ((none, esC), sc) := by
      simp [stepCDF, implEDF, deliverForgeE, hS.abort_C, hwin0]
    have hP : stepPDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esP sp =
        pure ((none, esP), sp) := by
      simp [stepPDF, implEDF, deliverForgeE, hS.abort_P, hwin, hwin0]
    rw [hC, hP, pure_bind, pure_bind]
    exact ih none hS
  · simp only [Bool.not_eq_true] at hwin0
    cases hr : esC.g.inTransit P.other c with
    | none =>
      have hC : stepCDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esC sc =
          pure ((none, esC), sc) := by
        simp [stepCDF, implEDF, deliverForgeE, hS.abort_C, hwin0, hr]
      have hP : stepPDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esP sp =
          pure ((none, esP), sp) := by
        simp [stepPDF, implEDF, deliverForgeE, hS.abort_P, hwin, hwin0, htrans_c, hr]
      rw [hC, hP, pure_bind, pure_bind]
      exact ih none hS
    | some r =>
      by_cases hguard :
          ((esC.g.inTransit P.other c').isSome || esC.g.comp.contains r.pos || c.1 != c'.1) = true
      · simp only [Bool.or_eq_true, List.contains_iff_mem, bne_iff_ne] at hguard
        have hC : stepCDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esC sc =
            pure ((none, esC), sc) := by
          simp [stepCDF, implEDF, deliverForgeE, hS.abort_C, hwin0, hr, hguard, StateT.run_pure]
        have hP : stepPDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esP sp =
            pure ((none, esP), sp) := by
          simp [stepPDF, implEDF, deliverForgeE, hS.abort_P, hwin, hwin0, htrans_c, hr,
            htrans_c', hcomp, hguard, StateT.run_pure]
        rw [hC, hP, pure_bind, pure_bind]
        exact ih none hS
      · simp only [Bool.not_eq_true, Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hguard
        rcases hguard with ⟨⟨htrans0, hcomp0⟩, hhdr⟩
        have hcomp0' : r.pos ∉ esC.g.comp := by simpa using hcomp0
        have hhdr' : c'.1 = c.1 := hhdr.symm
        obtain ⟨hmem, hsender, hct⟩ := inTransit_some_props hr
        obtain ⟨ht1, hsend_other, hle_other, _⟩ := hS.trans_inv r hmem
        rw [hct] at ht1
        rw [hsender] at hsend_other hle_other
        have hsend0 : P.sendsIn c'.1.1 = false := by
          rw [hhdr', ht1]
          have h1 := sendsIn_other P r.pos.epoch
          rw [hsend_other] at h1
          simpa using h1.symm
        have hmax_bound : esC.g.epoch P.other ≤ esC.g.epoch P + 1 := by
          rcases hS.ping_pong with ⟨hR, _⟩ | ⟨_, hR, _⟩
          · have hepP := epoch_eq_of_synced hS.epoch_S hR P
            have hepO := epoch_eq_of_synced hS.epoch_S hR P.other
            omega
          · rcases party_cases_of_epoch (max (esC.g.epoch .A) (esC.g.epoch .B)) P with hP | hP
            · have hO : P.other = Party.receiverOf (max (esC.g.epoch .A) (esC.g.epoch .B)) := by
                rw [hP, senderOf_other]
              have hS_ep := hS.epoch_S
              rw [← hP] at hS_ep
              rw [← hO] at hR
              omega
            · have hO : P.other = Party.senderOf (max (esC.g.epoch .A) (esC.g.epoch .B)) := by
                rw [hP, receiverOf_other]
              have hS_ep := hS.epoch_S
              rw [← hO] at hS_ep
              rw [← hP] at hR
              omega
        have hle : ¬ (esC.g.epoch P + 1 < c'.1.1) := by rw [hhdr', ht1]; omega
        by_cases hnew : c'.1.1 = esC.g.epoch P + 1
        ·
          have hnew_c : c.1.1 = esC.g.epoch P + 1 := by rw [hhdr, hnew]
          have hsend0' : P.sendsIn (esC.g.epoch P + 1) = false := hnew ▸ hsend0
          obtain ⟨hr_ep, hP_eq_R, hO_eq_S, hO_ep, hmax_eq, Tm, Im, hct2, hcC, hST, hSroot,
            hcP, hlast⟩ := hS.deliver_new_info hr hnew_c
          have hc'2 : c'.1.2 = some Tm := by rw [hhdr', hct2]
          let p := prng.up (esC.g.st P).root Im
          have hp1 : (prng.up (esC.g.st P).root Im).1 = (esC.g.st P.other).root := hSroot.symm
          let γP' := (cka.receive (esP.g.st P).γ Tm).1
          have hstartC := fun ctx γv =>
            hooksCKA_startRecv_honest cka prng fs Δcka mo ctx P (esC.g.epoch P + 1) γv
              (esC.g.st P).root Tm Im esC.h hcC
          have hstartP : (simulateQ (pImpl prng)
              (((hooksPRNG cka prng fs mo).startRecv esP.g P (esC.g.epoch P + 1)
                (esP.g.st P).γ (esP.g.st P).root Tm).run esP.h)).run sp =
              pure ((some (some (γP', (esP.g.st P.other).root, fs.initReceiver p.2)), esP.h),
                sp) := by
            simp [hooksPRNG, hcP, p, γP', StateT.run_bind, StateT.run_get, StateT.run_pure,
              simulateQ_pure]
          cases hfs : fs.receive (fs.initReceiver p.2) c'.1 c'.2 with
          | none =>
            have hC : stepCDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esC sc =
                pure ((some .rejected, esC), sc) := by
              simp [stepCDF, implEDF, deliverForgeE, vRecv, hS.abort_C, hwin0, hr, htrans0,
                hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0', hnew, hc'2, hstartC,
                hp1, p, hfs, StateT.run_bind, StateT.run_pure, simulateQ_pure,
                hesC_eq]
            have hP : stepPDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esP sp =
                pure ((some .rejected, esP), sp) := by
              simp [stepPDF, implEDF, deliverForgeE, vRecv, hS.abort_P, hwin, hwin0, htrans_c, hr,
                htrans_c', htrans0, hcomp, hcomp0', hhdr, hS.id_P P, hS.tcur_P P, hsend0',
                hnew, hc'2, hstartP, hfs, StateT.run_bind, StateT.run_pure, simulateQ_bind,
                simulateQ_pure, hesP_eq]
            rw [hC, hP, pure_bind, pure_bind]
            exact ih (some .rejected) hS
          | some vim =>
            rcases vim with ⟨v', i', m'⟩
            let m := esC.g.epoch P + 1
            have hne_ep : (m != r.pos.epoch) = false := by
              simp [m, hr_ep]
            by_cases hqep : qep + 1 < m
            · have hC : stepCDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esC sc =
                  pure ((some .rejected, esC), sc) := by
                simp [stepCDF, implEDF, deliverForgeE, vRecv, hS.abort_C, hwin0, hr, htrans0,
                  hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0', hnew, hc'2, hstartC,
                  hp1, p, hfs, m, hqep, StateT.run_bind, StateT.run_pure, simulateQ_pure, hesC_eq]
              have hP : stepPDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esP sp =
                  pure ((some .rejected, esP), sp) := by
                simp [stepPDF, implEDF, deliverForgeE, vRecv, hS.abort_P, hwin, hwin0, htrans_c, hr,
                  htrans_c', htrans0, hcomp, hcomp0', hhdr, hS.id_P P, hS.tcur_P P,
                  hsend0', hnew, hc'2, hstartP, hfs, m, hqep, StateT.run_bind, StateT.run_pure,
                  simulateQ_bind, simulateQ_pure, hesP_eq]
              rw [hC, hP, pure_bind, pure_bind]
              exact ih (some .rejected) hS
            · let pos : SM.Pos := ⟨P.other, m, i'⟩
              have htriv_eq : esP.g.trivial (2 + Δcka) pos = esC.g.trivial (2 + Δcka) pos :=
                eraseSt_trivial hS.g_eq (2 + Δcka) pos
              by_cases htriv : esC.g.trivial (2 + Δcka) pos
              · let vR' := Function.update (Function.update (esC.g.st P).vR m
                  (some (fs.initReceiver p.2))) m (some v')
                let γC_final := if localCKA mo Δcka m then some γP' else none
                let stC_final : VP (Option Γ) T Sig SS RS :=
                  { esC.g.st P with
                    tcur := m, γ := γC_final, root := (esC.g.st P.other).root, vR := vR' }
                let stP_final : VP Γ T (Option Sig) SS RS :=
                  { esP.g.st P with
                    tcur := m, γ := γP', root := (esP.g.st P.other).root, vR := vR' }
                have hvRP : (esP.g.st P).vR = (esC.g.st P).vR := hS.vR_eq P
                have hP : stepPDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esP sp =
                    pure ((some (.accepted m i' (some m')),
                      { esP with g := esP.g.accept P stP_final pos }), sp) := by
                  simp [stepPDF, implEDF, deliverForgeE, commitE, vRecv, hS.abort_P, hwin, hwin0,
                    htrans_c, hr, htrans_c', htrans0, hcomp, hcomp0', hhdr, hS.id_P P,
                    hS.tcur_P P, hsend0', hnew, hc'2, hvRP, hstartP, hfs, m, hqep, hr_ep, pos,
                    htriv_eq, htriv, vR', stP_final, γP', StateT.run_bind, StateT.run_pure,
                    StateT.run_modify, simulateQ_bind, simulateQ_pure]
                by_cases hloc : localCKA mo Δcka (esC.g.epoch P) = true
                · have hloc_m : localCKA mo Δcka m = true := by
                    simp only [localCKA, Bool.or_eq_true, decide_eq_true_eq] at hloc ⊢
                    rcases hloc with h1 | h2
                    · exact Or.inl h1
                    · exact Or.inr (by omega)
                  have hγC : (esC.g.st P).γ = some (esP.g.st P).γ := by
                    rw [hS.γ_C P, hloc]; rfl
                  have hC : stepCDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esC sc =
                      pure ((some (.accepted m i' (some m')),
                        { esC with g := esC.g.accept P stC_final pos }), sc) := by
                    simp [stepCDF, implEDF, deliverForgeE, commitE, vRecv, hS.abort_C, hwin0, hr,
                      htrans0, hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0', hnew, hc'2,
                      hstartC, hp1, p, hfs, hγC, hloc_m, m, hqep, hr_ep, pos, htriv, vR',
                      γC_final, stC_final, γP', StateT.run_bind, StateT.run_pure,
                      StateT.run_modify, simulateQ_pure]
                  rw [hC, hP, pure_bind, pure_bind]
                  exact ih _ (hS.accept_new P γP' vR' pos rfl hO_ep hS.b_C
                    (fun h => by simp [m, hloc_m] at h))
                · simp only [Bool.not_eq_true] at hloc
                  have hγC : (esC.g.st P).γ = none := by
                    rw [hS.γ_C P, hloc]; rfl
                  obtain ⟨hsc_stP, hsc_epP⟩ := hS.cka_st P (Or.inl hloc)
                  obtain ⟨hsc_stO, hsc_epO⟩ := hS.cka_st P.other (Or.inr (by simpa using hloc))
                  have hcanR : sc.canReceive P = true := by
                    simp [CKA.GameState.canReceive, hsc_epO, hsc_epP, hO_ep]
                  have hlast_eq : sc.lastMsg = some Tm := hlast hloc
                  let sc' := sc.afterReceive P γP'
                  have htL_none : mo.tL.isNone = false := by
                    simp only [localCKA, Bool.or_eq_false_iff] at hloc
                    exact hloc.1
                  by_cases hfin : mo.tH + Δcka ≤ m
                  · have hloc_m : localCKA mo Δcka m = true := by
                      simp [localCKA, hfin]
                    have hC : stepCDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esC sc =
                        pure ((some (.accepted m i' (some m')),
                          { esC with g := esC.g.accept P stC_final pos }), sc') := by
                      simp [stepCDF, implEDF, deliverForgeE, commitE, liftC, CKA.receiveQuery,
                        CKA.corrQuery, cImpl, CKA.oracleImpl, CKA.receiveImpl, CKA.corrImpl, vRecv,
                        hS.abort_C, hwin0, hr, htrans0, hcomp0', hhdr, hS.id_C P,
                        hS.tcur_C P, hsend0', hnew, hc'2, hstartC, hp1, p, hfs, hγC, hcanR,
                        hlast_eq, hsc_stP, hfin, hloc_m, sc', CKA.GameState.afterReceive,
                        CKA.GameState.finished, hsc_epP, m, hqep, hr_ep, pos, htriv, vR',
                        γC_final, stC_final, γP', simulateQ_bind, simulateQ_query,
                        simulateQ_pure, map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure,
                        StateT.run_modify]
                    rw [hC, hP, pure_bind, pure_bind]
                    exact ih _ (hS.accept_new P γP' vR' pos rfl hO_ep hS.b_C
                      (fun h => by simp [m, hloc_m] at h))
                  · have hloc_m : localCKA mo Δcka m = false := by
                      simp [localCKA, htL_none, hfin]
                    have hC : stepCDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esC sc =
                        pure ((some (.accepted m i' (some m')),
                          { esC with g := esC.g.accept P stC_final pos }), sc') := by
                      simp [stepCDF, implEDF, deliverForgeE, commitE, liftC, CKA.receiveQuery,
                        cImpl, CKA.oracleImpl, CKA.receiveImpl, vRecv, hS.abort_C, hwin0, hr,
                        htrans0, hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0', hnew,
                        hc'2, hstartC, hp1, p, hfs, hγC, hcanR, hlast_eq, hsc_stP, hfin, hloc_m,
                        sc', m, hqep, hr_ep, pos, htriv, vR', γC_final, stC_final, γP',
                        simulateQ_bind, simulateQ_query, simulateQ_pure,
                        map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify]
                    rw [hC, hP, pure_bind, pure_bind]
                    refine ih _ (hS.accept_new P γP' vR' pos rfl hO_ep hS.b_C fun _ => ?_)
                    simp [sc', CKA.GameState.afterReceive, Party.other_ne, hsc_epP, hsc_stO,
                      hsc_epO, hO_ep]
              · simp only [Bool.not_eq_true] at htriv
                by_cases hinj : (mo.cfg (M := M)).injectFull m
                · have hC : stepCDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esC sc =
                      pure ((some .rejected,
                        { esC with g := { esC.g with win := true } }), sc) := by
                    simp [stepCDF, implEDF, deliverForgeE, vRecv, hS.abort_C, hwin0, hr, htrans0,
                      hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0', hnew, hc'2, hstartC,
                      hp1, p, hfs, m, hqep, hr_ep, pos, htriv, hinj, StateT.run_bind,
                      StateT.run_pure, StateT.run_modify, simulateQ_pure]
                  have hP : stepPDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esP sp =
                      pure ((some .rejected,
                        { esP with g := { esP.g with win := true } }), sp) := by
                    simp [stepPDF, implEDF, deliverForgeE, vRecv, hS.abort_P, hwin, hwin0, htrans_c,
                      hr, htrans_c', htrans0, hcomp, hcomp0', hhdr, hS.id_P P, hS.tcur_P P,
                      hsend0', hnew, hc'2, hstartP, hfs, m, hqep, hr_ep, pos, htriv_eq,
                      htriv, hinj, StateT.run_bind, StateT.run_pure, StateT.run_modify,
                      simulateQ_bind, simulateQ_pure]
                  rw [hC, hP, pure_bind, pure_bind]
                  exact ih (some .rejected) (hS.set_win_prf true sp.prf (Or.inl rfl))
                · simp only [Bool.not_eq_true] at hinj
                  have hC : stepCDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esC sc =
                      pure ((some .rejected, esC), sc) := by
                    simp [stepCDF, implEDF, deliverForgeE, vRecv, hS.abort_C, hwin0, hr, htrans0,
                      hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0', hnew, hc'2, hstartC,
                      hp1, p, hfs, m, hqep, hr_ep, pos, htriv, hinj, StateT.run_bind,
                      StateT.run_pure, simulateQ_pure, hesC_eq]
                  have hP : stepPDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esP sp =
                      pure ((some .rejected, esP), sp) := by
                    simp [stepPDF, implEDF, deliverForgeE, vRecv, hS.abort_P, hwin, hwin0, htrans_c,
                      hr, htrans_c', htrans0, hcomp, hcomp0', hhdr, hS.id_P P, hS.tcur_P P,
                      hsend0', hnew, hc'2, hstartP, hfs, m, hqep, hr_ep, pos, htriv_eq,
                      htriv, hinj, StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure,
                      hesP_eq]
                  rw [hC, hP, pure_bind, pure_bind]
                  exact ih (some .rejected) hS
        ·
          have hle_ep : c'.1.1 ≤ esC.g.epoch P := by omega
          have hvRP : (esP.g.st P).vR c'.1.1 = (esC.g.st P).vR c'.1.1 := by rw [hS.vR_eq P]
          cases hvR : (esC.g.st P).vR c'.1.1 with
          | none =>
            have hC : stepCDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esC sc =
                pure ((some .rejected, esC), sc) := by
              simp [stepCDF, implEDF, deliverForgeE, vRecv, hS.abort_C, hwin0, hr, htrans0,
                hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR, StateT.run_bind,
                StateT.run_pure, simulateQ_pure, hesC_eq]
            have hP : stepPDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esP sp =
                pure ((some .rejected, esP), sp) := by
              simp [stepPDF, implEDF, deliverForgeE, vRecv, hS.abort_P, hwin, hwin0, htrans_c, hr,
                htrans_c', htrans0, hcomp, hcomp0', hhdr, hS.id_P P, hS.tcur_P P, hsend0,
                hle, hnew, hvRP, hvR, StateT.run_bind, StateT.run_pure, simulateQ_pure, hesP_eq]
            rw [hC, hP, pure_bind, pure_bind]
            exact ih (some .rejected) hS
          | some v =>
            cases hfs : fs.receive v c'.1 c'.2 with
            | none =>
              have hC : stepCDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esC sc =
                  pure ((some .rejected, esC), sc) := by
                simp [stepCDF, implEDF, deliverForgeE, vRecv, hS.abort_C, hwin0, hr, htrans0,
                  hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR, hfs,
                  StateT.run_bind, StateT.run_pure, simulateQ_pure, hesC_eq]
              have hP : stepPDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esP sp =
                  pure ((some .rejected, esP), sp) := by
                simp [stepPDF, implEDF, deliverForgeE, vRecv, hS.abort_P, hwin, hwin0, htrans_c,
                  hr, htrans_c', htrans0, hcomp, hcomp0', hhdr, hS.id_P P, hS.tcur_P P,
                  hsend0, hle, hnew, hvRP, hvR, hfs, StateT.run_bind, StateT.run_pure,
                  simulateQ_pure, hesP_eq]
              rw [hC, hP, pure_bind, pure_bind]
              exact ih (some .rejected) hS
            | some vim =>
              rcases vim with ⟨v', i', m'⟩
              have heq_ep : r.pos.epoch = c'.1.1 := by rw [hhdr', ht1]
              have hne_ep : (c'.1.1 != r.pos.epoch) = false := by simp [heq_ep]
              by_cases hqep : qep + 1 < c'.1.1
              · have hC : stepCDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esC sc =
                    pure ((some .rejected, esC), sc) := by
                  simp [stepCDF, implEDF, deliverForgeE, vRecv, hS.abort_C, hwin0, hr, htrans0,
                    hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR, hfs,
                    hqep, StateT.run_bind, StateT.run_pure, simulateQ_pure,
                    hesC_eq]
                have hP : stepPDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esP sp =
                    pure ((some .rejected, esP), sp) := by
                  simp [stepPDF, implEDF, deliverForgeE, vRecv, hS.abort_P, hwin, hwin0, htrans_c,
                    hr, htrans_c', htrans0, hcomp, hcomp0', hhdr, hS.id_P P, hS.tcur_P P,
                    hsend0, hle, hnew, hvRP, hvR, hfs, hqep, StateT.run_bind, StateT.run_pure,
                    simulateQ_pure, hesP_eq]
                rw [hC, hP, pure_bind, pure_bind]
                exact ih (some .rejected) hS
              · let pos : SM.Pos := ⟨P.other, c'.1.1, i'⟩
                have htriv_eq : esP.g.trivial (2 + Δcka) pos = esC.g.trivial (2 + Δcka) pos :=
                  eraseSt_trivial hS.g_eq (2 + Δcka) pos
                by_cases htriv : esC.g.trivial (2 + Δcka) pos
                · let vR' := Function.update (esC.g.st P).vR c'.1.1 (some v')
                  have hvR'_eq : Function.update (esP.g.st P).vR c'.1.1 (some v') = vR' := by
                    simp [vR', hS.vR_eq P]
                  have hC : stepCDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esC sc =
                      pure ((some (.accepted c'.1.1 i' (some m')),
                        { esC with g := esC.g.accept P { esC.g.st P with vR := vR' } pos }),
                        sc) := by
                    simp [stepCDF, implEDF, deliverForgeE, vRecv, commitE, hooksCKA, hS.abort_C,
                      hwin0, hr, htrans0, hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0,
                      hle, hnew, hvR, hfs, hqep, heq_ep, htriv, pos, vR', StateT.run_bind,
                      StateT.run_pure, StateT.run_modify, simulateQ_pure]
                  have hP : stepPDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esP sp =
                      pure ((some (.accepted c'.1.1 i' (some m')),
                        { esP with g := esP.g.accept P { esP.g.st P with vR := vR' } pos }),
                        sp) := by
                    simp [stepPDF, implEDF, deliverForgeE, vRecv, commitE, hS.abort_P, hwin, hwin0,
                      htrans_c, hr, htrans_c', htrans0, hcomp, hcomp0', hhdr, hS.id_P P,
                      hS.tcur_P P, hsend0, hle, hnew, hvRP, hvR, hfs, hqep, heq_ep, htriv_eq,
                      htriv, pos, hvR'_eq, StateT.run_bind, StateT.run_pure,
                      StateT.run_modify, simulateQ_pure]
                  rw [hC, hP, pure_bind, pure_bind]
                  exact ih _ (hS.accept_old P vR' pos hle_ep)
                · simp only [Bool.not_eq_true] at htriv
                  by_cases hinj : (mo.cfg (M := M)).injectFull c'.1.1
                  · have hC : stepCDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esC sc =
                        pure ((some .rejected, { esC with g := { esC.g with win := true } }),
                          sc) := by
                      simp [stepCDF, implEDF, deliverForgeE, vRecv, hS.abort_C, hwin0, hr, htrans0,
                        hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR, hfs,
                        hqep, heq_ep, htriv, hinj, pos, StateT.run_bind, StateT.run_pure,
                        StateT.run_modify, simulateQ_pure]
                    have hP : stepPDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esP sp =
                        pure ((some .rejected, { esP with g := { esP.g with win := true } }),
                          sp) := by
                      simp [stepPDF, implEDF, deliverForgeE, vRecv, hS.abort_P, hwin, hwin0,
                        htrans_c, hr, htrans_c', htrans0, hcomp, hcomp0', hhdr, hS.id_P P,
                        hS.tcur_P P, hsend0, hle, hnew, hvRP, hvR, hfs, hqep, heq_ep, htriv_eq,
                        htriv, hinj, pos, StateT.run_bind, StateT.run_pure,
                        StateT.run_modify, simulateQ_pure]
                    rw [hC, hP, pure_bind, pure_bind]
                    exact ih (some .rejected) (hS.set_win_prf true sp.prf (Or.inl rfl))
                  · simp only [Bool.not_eq_true] at hinj
                    have hC : stepCDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esC sc =
                        pure ((some .rejected, esC), sc) := by
                      simp [stepCDF, implEDF, deliverForgeE, vRecv, hS.abort_C, hwin0, hr, htrans0,
                        hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR, hfs,
                        hqep, heq_ep, htriv, hinj, pos, StateT.run_bind, StateT.run_pure,
                        simulateQ_pure, hesC_eq]
                    have hP : stepPDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esP sp =
                        pure ((some .rejected, esP), sp) := by
                      simp [stepPDF, implEDF, deliverForgeE, vRecv, hS.abort_P, hwin, hwin0,
                        htrans_c, hr, htrans_c', htrans0, hcomp, hcomp0', hhdr, hS.id_P P,
                        hS.tcur_P P, hsend0, hle, hnew, hvRP, hvR, hfs, hqep, heq_ep, htriv_eq,
                        htriv, hinj, pos, StateT.run_bind, StateT.run_pure,
                        simulateQ_pure, hesP_eq]
                    rw [hC, hP, pure_bind, pure_bind]
                    exact ih (some .rejected) hS

theorem runLDFPaper_le_runRDFPaper (mo : Mode) (hauth : mo.auth = true)
    (hvalid : SM.lastLeakGuessAdmissible (2 + Δcka) mo.tL mo.tStar = true)
    (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp) :
    𝒟[runLDFPaper cka prng fs Δcka qep mo oa esC sc] {true} ≤
      𝒟[runRDFPaper cka prng fs Δcka qep mo oa esP sp] {true} := by
  induction oa using OracleComp.inductionOn generalizing esC sc esP sp with
  | pure b' =>
    rw [runLDFPaper_pure, runRDFPaper_pure, hS.authOut_eq]
  | query_bind q k ih =>
    rw [runLDFPaper_query_bind, runRDFPaper_query_bind]
    rcases q with n | (((((⟨P, m_msg, r⟩ | q_ch) | ⟨P, c⟩) | q_inj) | P) | ⟨P, c, c'⟩)
    · exact step_coinsE_le cka prng fs Δcka qep mo n
        (fun u => runLDFPaper cka prng fs Δcka qep mo (k u))
        (fun u => runRDFPaper cka prng fs Δcka qep mo (k u)) hS @ih
    · exact step_transmitE_le cka prng fs Δcka qep mo hvalid P m_msg r
        (fun u => runLDFPaper cka prng fs Δcka qep mo (k u))
        (fun u => runRDFPaper cka prng fs Δcka qep mo (k u))
        (fun rhs hab => runLDFPaper_abort_apply_true_le cka prng fs Δcka qep mo (k none) hab rhs)
        hS @ih
    · exact step_challE_le cka prng fs Δcka qep mo hauth q_ch
        (fun u => runLDFPaper cka prng fs Δcka qep mo (k u))
        (fun u => runRDFPaper cka prng fs Δcka qep mo (k u)) hS @ih
    · exact step_deliverE_le cka prng fs Δcka qep mo hauth P c
        (fun u => runLDFPaper cka prng fs Δcka qep mo (k u))
        (fun u => runRDFPaper cka prng fs Δcka qep mo (k u)) hS @ih
    · exact step_injectE_le cka prng fs Δcka qep mo hauth q_inj
        (fun u => runLDFPaper cka prng fs Δcka qep mo (k u))
        (fun u => runRDFPaper cka prng fs Δcka qep mo (k u))
        (fun rhs hab => runLDFPaper_abort_apply_true_le cka prng fs Δcka qep mo (k none) hab rhs)
        hS @ih
    · exact step_corrE_DFPaper_le cka prng fs Δcka qep mo hauth P k hS @ih
    · exact step_deliverForgeE_DFPaper_le cka prng fs Δcka qep mo hauth P c c' k hS @ih

theorem lemma10_df_paper (_hc : cka.Correct) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[CKA.branch cka Δcka (healEpoch tL) true
        (redCKAAuthDFPaper cka prng fs lam Δcka qep tL t A)] {true} ≤
      𝒟[PRFPRNG.branch prng false (redPRNGAuthDFPaper cka prng fs lam Δcka qep tL t A)] {true} := by
  by_cases hvg : SM.lastLeakGuessAdmissible (2 + Δcka) tL t = true
  · cases htL : tL with
    | none =>
      subst htL
      have hL : CKA.branch cka Δcka (healEpoch none) true
          (redCKAAuthDFPaper cka prng fs lam Δcka qep none t A) =
          ($ᵗ KC >>= fun kc_ext => $ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
            runLDFPaper cka prng fs Δcka qep ⟨true, none, t⟩ A
              (initES_C cka prng fs lam none kr kc)
              (CKA.initState cka kc_ext true)) := by
        unfold CKA.branch redCKAAuthDFPaper authSimDFPaper engRunDFPaper initCKA runLDFPaper
          initES_C
        simp only [cImpl, Mode.tH, Mode.policy, StateT.run'_eq, StateT.run_lift,
          StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure,
          simulateQ_sampleT_run, map_eq_bind_pure_comp, bind_assoc, pure_bind,
          Function.comp_apply]
        rfl
      rcases Nat.eq_zero_or_pos t with rfl | ht
      · have hR : PRFPRNG.branch prng false
            (redPRNGAuthDFPaper cka prng fs lam Δcka qep none 0 A) =
            ($ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
              runRDFPaper cka prng fs Δcka qep ⟨true, none, 0⟩ A
                (initES_P cka prng fs lam (some (prng.up (prng.init kr) lam).1) kr kc)
                (initSP_zero prng kr)) := by
          unfold PRFPRNG.branch redPRNGAuthDFPaper authSimDFPaper engRunDFPaper runRDFPaper initES_P
          simp only [pImpl, Mode.policy, StateT.run'_eq, StateT.run_bind, simulateQ_bind,
            initPRNG_run_none_zero cka prng fs lam, map_eq_bind_pure_comp,
            bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, Function.comp_apply]
          rfl
        rw [hL, hR]
        have hconst :
            𝒟[$ᵗ KC >>= fun _ : KC => $ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
              runRDFPaper cka prng fs Δcka qep ⟨true, none, 0⟩ A
                (initES_P cka prng fs lam (some (prng.up (prng.init kr) lam).1) kr kc)
                (initSP_zero prng kr)] {true} =
            𝒟[$ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
              runRDFPaper cka prng fs Δcka qep ⟨true, none, 0⟩ A
                (initES_P cka prng fs lam (some (prng.up (prng.init kr) lam).1) kr kc)
                (initSP_zero prng kr)] {true} := by
          rw [OracleComp.evalDist_bind_const]
        rw [← hconst]
        refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
          fun kc_ext _ => ?_
        refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
          fun kr _ => ?_
        refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
          fun kc _ => ?_
        exact runLDFPaper_le_runRDFPaper cka prng fs Δcka qep ⟨true, none, 0⟩ rfl hvg A
          (sync_init_none_zero cka prng fs lam Δcka kr kc kc_ext)
      · have hR : PRFPRNG.branch prng false
            (redPRNGAuthDFPaper cka prng fs lam Δcka qep none t A) =
            ($ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
              runRDFPaper cka prng fs Δcka qep ⟨true, none, t⟩ A
                (initES_P cka prng fs lam none kr kc)
                (initSP prng lam none kr)) := by
          unfold PRFPRNG.branch redPRNGAuthDFPaper authSimDFPaper engRunDFPaper runRDFPaper initES_P
          simp only [pImpl, Mode.policy, StateT.run'_eq, StateT.run_bind, simulateQ_bind,
            initPRNG_run_none_pos cka prng fs lam t ht, map_eq_bind_pure_comp,
            bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, Function.comp_apply]
          rfl
        rw [hL, hR]
        have hconst :
            𝒟[$ᵗ KC >>= fun _ : KC => $ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
              runRDFPaper cka prng fs Δcka qep ⟨true, none, t⟩ A
                (initES_P cka prng fs lam none kr kc)
                (initSP prng lam none kr)] {true} =
            𝒟[$ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
              runRDFPaper cka prng fs Δcka qep ⟨true, none, t⟩ A
                (initES_P cka prng fs lam none kr kc)
                (initSP prng lam none kr)] {true} := by
          rw [OracleComp.evalDist_bind_const]
        rw [← hconst]
        refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
          fun kc_ext _ => ?_
        refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
          fun kr _ => ?_
        refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
          fun kc _ => ?_
        exact runLDFPaper_le_runRDFPaper cka prng fs Δcka qep ⟨true, none, t⟩ rfl hvg A
          (sync_init_none_pos cka prng fs lam Δcka t ht kr kc kc_ext)
    | some l =>
      subst htL
      have hL : CKA.branch cka Δcka (healEpoch (some l)) true
          (redCKAAuthDFPaper cka prng fs lam Δcka qep (some l) t A) =
          ($ᵗ KC >>= fun kc => $ᵗ KR >>= fun kr =>
            runLDFPaper cka prng fs Δcka qep ⟨true, some l, t⟩ A
              (initES_C cka prng fs lam (some l) kr kc)
              (CKA.initState cka kc true)) := by
        unfold CKA.branch redCKAAuthDFPaper authSimDFPaper engRunDFPaper initCKA runLDFPaper
          initES_C
        simp only [cImpl, Mode.tH, Mode.policy, StateT.run'_eq, StateT.run_lift,
          StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure,
          simulateQ_sampleT_run, map_eq_bind_pure_comp, bind_assoc, pure_bind,
          Function.comp_apply]
        rfl
      have hR : PRFPRNG.branch prng false
          (redPRNGAuthDFPaper cka prng fs lam Δcka qep (some l) t A) =
          ($ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
            runRDFPaper cka prng fs Δcka qep ⟨true, some l, t⟩ A
              (initES_P cka prng fs lam (some (prng.up (prng.init kr) lam).1) kr kc)
              (initSP prng lam (some l) kr)) := by
        unfold PRFPRNG.branch redPRNGAuthDFPaper authSimDFPaper engRunDFPaper runRDFPaper initES_P
        simp only [pImpl, Mode.policy, StateT.run'_eq, StateT.run_bind, simulateQ_bind,
          initPRNG_run_some cka prng fs lam Δcka l t hvg, map_eq_bind_pure_comp,
          bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, Function.comp_apply]
        rfl
      rw [hL, hR, OracleComp.evalDist_bind_bind_swap ($ᵗ KR) ($ᵗ KC)]
      refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
        fun kc _ => ?_
      refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
        fun kr _ => ?_
      exact runLDFPaper_le_runRDFPaper cka prng fs Δcka qep ⟨true, some l, t⟩ rfl hvg A
        (sync_init_some cka prng fs lam Δcka l t hvg kr kc)
  · have hvg_f : SM.lastLeakGuessAdmissible (2 + Δcka) tL t = false := Bool.eq_false_iff.mpr hvg
    have hred : redCKAAuthDFPaper cka prng fs lam Δcka qep tL t A =
        (engRunDFPaper (hooksCKA cka prng fs Δcka ⟨true, tL, t⟩) (2 + Δcka) qep fs.maxSkip
          (Config.auth t) ⟨true, tL, t⟩ (initCKA cka prng fs lam ⟨true, tL, t⟩) {} false A >>=
          fun _ => pure false) := by
      dsimp only [redCKAAuthDFPaper, authSimDFPaper]
      congr 1
      funext r
      cases r with
      | none => rfl
      | some p =>
        exact congrArg pure (authOut_of_validGuess_false (2 + Δcka) ⟨true, tL, t⟩ hvg_f p.2)
    have hbranch : 𝒟[CKA.branch cka Δcka (healEpoch tL) true
        (redCKAAuthDFPaper cka prng fs lam Δcka qep tL t A)] = 𝒟[(pure false : ProbComp Bool)] := by
      unfold CKA.branch
      rw [hred]
      simp only [StateT.run'_eq, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
        map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
      refine evalDist_bind_false_of_support ($ᵗ KC) _ fun k _ => ?_
      exact OracleComp.evalDist_bind_const _ _
    rw [hbranch]
    simp

end CryptoGames.SM.Construction.DeliverForge.AuthL10DF

namespace CryptoGames.SM.Construction.DeliverForge

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

variable (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)

theorem lemma9_df_paper (hc : cka.Correct) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    forgeGuessedAdvantagePaper (scheme cka prng fs lam) (2 + Δcka) qep sameHdrScheme
        tL t A ≤
      𝒟[CKA.branch cka Δcka (healEpoch tL) false
        (redCKAAuthDFPaper cka prng fs lam Δcka qep tL t A)] {true} :=
  AuthL9DF.lemma9_df_paper cka prng fs lam Δcka qep hc tL t A

theorem lemma10_df_paper (hc : cka.Correct) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[CKA.branch cka Δcka (healEpoch tL) true
        (redCKAAuthDFPaper cka prng fs lam Δcka qep tL t A)] {true} ≤
      𝒟[PRFPRNG.branch prng false (redPRNGAuthDFPaper cka prng fs lam Δcka qep tL t A)] {true} :=
  AuthL10DF.lemma10_df_paper cka prng fs lam Δcka qep hc tL t A

theorem lemma11_df_paper (tL : Option ℕ) (t q : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E)
    (hq : MakesAtMostQueriesDF A q) :
    𝒟[PRFPRNG.branch prng true (redPRNGAuthDFPaper cka prng fs lam Δcka qep tL t A)] {true} ≤
      ∑ j ∈ Finset.range q,
        FSAEAD.advantage fs (redFSAuthDFPaper cka prng fs lam Δcka qep j tL t A) :=
  AuthL11.lemma11_df_paper_proof cka prng fs lam Δcka qep tL t q A hq

/-- Theorem 8 for `DeliverForge` under `corrAllowedPaper` at a single guessed pair `(tL, t)`. -/
theorem theorem8_df_paper (hc : cka.Correct) (tL : Option ℕ) (t q : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E)
    (hq : MakesAtMostQueriesDF A q) :
    forgeGuessedAdvantagePaper (scheme cka prng fs lam) (2 + Δcka) qep sameHdrScheme
        tL t A ≤
      CKA.advantage cka Δcka (healEpoch tL) (redCKAAuthDFPaper cka prng fs lam Δcka qep tL t A) +
      PRFPRNG.advantage prng (redPRNGAuthDFPaper cka prng fs lam Δcka qep tL t A) +
      ∑ j ∈ Finset.range q,
        FSAEAD.advantage fs (redFSAuthDFPaper cka prng fs lam Δcka qep j tL t A) := by
  rw [CKA.advantage_eq_boolDist, PRFPRNG.advantage_eq_boolDist]
  set cT := 𝒟[CKA.branch cka Δcka (healEpoch tL) true
    (redCKAAuthDFPaper cka prng fs lam Δcka qep tL t A)]
  set cF := 𝒟[CKA.branch cka Δcka (healEpoch tL) false
    (redCKAAuthDFPaper cka prng fs lam Δcka qep tL t A)]
  set pT := 𝒟[PRFPRNG.branch prng true (redPRNGAuthDFPaper cka prng fs lam Δcka qep tL t A)]
  set pF := 𝒟[PRFPRNG.branch prng false (redPRNGAuthDFPaper cka prng fs lam Δcka qep tL t A)]
  have h9 := lemma9_df_paper cka prng fs lam Δcka qep hc tL t A
  have h10 := lemma10_df_paper cka prng fs lam Δcka qep hc tL t A
  have h11 := lemma11_df_paper cka prng fs lam Δcka qep tL t q A hq
  have hc' : cF {true} ≤ cT {true} + cT.boolDist cF := by
    rw [Measure.boolDist_comm]; exact Measure.apply_true_le_add_boolDist _ _
  have hp' : pF {true} ≤ pT {true} + pT.boolDist pF := by
    rw [Measure.boolDist_comm]; exact Measure.apply_true_le_add_boolDist _ _
  calc forgeGuessedAdvantagePaper (scheme cka prng fs lam) (2 + Δcka) qep sameHdrScheme
          tL t A
      ≤ cF {true} := h9
    _ ≤ cT {true} + cT.boolDist cF := hc'
    _ ≤ (pT {true} + pT.boolDist pF) + cT.boolDist cF := add_le_add (h10.trans hp') le_rfl
    _ ≤ ((∑ j ∈ Finset.range q, FSAEAD.advantage fs
          (redFSAuthDFPaper cka prng fs lam Δcka qep j tL t A)) + pT.boolDist pF) +
        cT.boolDist cF :=
        add_le_add (add_le_add h11 le_rfl) le_rfl
    _ = _ := by ring

section CoinStrippingPaper

open CryptoGames.SM CryptoGames.SM.Engine CryptoGames.SM.Thm1 CryptoGames.SM.Thm1L17

variable {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]

end CoinStrippingPaper

end CryptoGames.SM.Construction.DeliverForge

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.LibsignalCli.CliKemFailCouplingHopBCore
import Computational.Proofs.LibsignalCli.Oom.Faithful
import VCVio.EvalDist.MeasureTVDist.Event
import VCVio.OracleComp.EvalDist.Measure

/-!
# Coin-logged send/challenge couplings and multi-query `simulateQ` induction

Proves coin-logged `tr` and `ch` per-instance SM oracle couplings, the multi-query `simulateQ`
coupling bound, and the whole-game good-log probability inequality modulo the step bridges.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.LibsignalCli.CliKemFailCouplingHopBAux

open OracleComp OracleSpec
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.LibsignalSession (Crypto GhostState PublicKey)
open CryptoGames.Ratchet.LibsignalInst (configR1OnCurve)
open CryptoVerification.LibsignalSpqrV1 (MlKem coinBytes spqrV1SessionUniformCoins)
open CryptoVerification.SignalSession (CliRun CliSpecPqxdh)
open CryptoVerification.E2E (BHAdapterInstMeta BHDrvM BHE2EDrvState BHModelInst BinState Bytes
  CliAdapterDrvRel CliAdapterDrvRemoteIdInv CliAdapterState CliE2ERemoteIdInv CliGameAdversary
  CliGameAdversaryPerInstanceBounded CliKeyIndStepBridgeProp CliSmStepBridgeProp
  CliStartStepBridgeProp L_bh ModelDriverInstanceMeta ModelDriverState PEParams
  UnreachedPqxdhPrimitives allTestedSessionsFresh bhConfigSpkS bhDrvInstClean
  bhDrvInstClean_eq_bhE2EDrvInstClean_of_cliRel bhDrvInstClean_imp_ikACorrAtAccept_false
  bhE2EDrvInstClean bhE2EDrvWon bhE2EStepLocalSm bhIsBobAcceptSMResp bhIsBobRecvSMQuery
  bhIsInstQueryWithSpqr bhNoExtWithSpqr bhPackSmResp bhSmDefaultWithSpqr challRM
  cliAdapterDrvRel_decrement_i cliAdapterDrvRel_init
  cliAdapterDrvRemoteIdInv_of_cliE2ERemoteIdInv cliAdapterInitState cliClause2BadKemBool
  cliComposedAdapterImplWith cliComposedAdapterImplWith_ch_run cliComposedAdapterImplWith_tr_run
  cliDrvImpl cliDrvSM_adapter_coupling_ch cliDrvSM_adapter_coupling_tr cliE2ERemoteIdInv_init
  cliGameAdversaryReassoc cliGameSmSpec cliGameSpec cliRunBadKemExp cliUnifStepBridgeProp_holds
  cliWrapAdapterSend configRefuseEarlyBobCorr driverSomeInstanceWon evalDist_cliPostObs_eq_of_rel
  liftQueryImplStateT2 modelPrims oracleImplRM paramsIdsWithSpqr
  probExpect_simulateQ_cliBadKem_eq_one_of_bad sessionSchemeFixedSpk smSchemeCoinLogged transmitRM)
open Computational.Proofs.LibsignalCli.CliKemFailCouplingDefs (CoinLogM
  bhE2EStepLocalSmCoinLogged cliDrvImplCoinLogged cliDrvSMCoinLogged cliE2EExpWithKiCoinLogged
  cliPqExpProjCoinLogged)
open Computational.Proofs.LibsignalCli.Oom.Faithful (instLawfulMonadWriterTList)
open Computational.Proofs.LibsignalCli.CliKemFailCouplingHopBCoreAux (
  cliComposedAdapterImplWithCoinLogged cliComposedAdapterImplWithCoinLogged_nonSend_eq_liftCoinS2
  cliComposedAdapterImplWithCoinLogged_preserves_remoteIdInv
  cliDrvImplCoinLogged_nonSend_eq_liftCoinS2 forgetCoinS2_cliDrvImplCoinLogged
  simulateQ_cliE2EDrvImplWithCoinLogged_L_bh_run writerT_run_liftCoinS2 writerT_run_liftM_prob)
open Computational.Proofs.LibsignalCli.CliKemFailCouplingHopBCore (
  bhDrvState_set_same_gs_local bhE2EDrvState_set_same_gs_local cliAdapterCoinStepCoupled
  cliAdapterCoinStepCoupled_bind_pure cliAdapterCoinStepCoupled_of_empty_log
  cliAdapterCoinStepCoupled_of_some_cns cliAdapterCoinStepCoupled_ret
  cliComposedAdapterImplWithCoinLogged_ch_run cliComposedAdapterImplWithCoinLogged_tr_run
  cliDrvSMCoinLogged_clean_tc_run cliDrvSM_clean_tc_run epMgmt_false_rel
  evalDist_bind_coinCoupled_le evalDist_bind_true_eq_probExpect_hopB oracleImplRM_ch
  oracleImplRM_tr oracleImplR_ch oracleImplR_tr probExpect_add_hopB send_record_rel_of_tr_some
  writerT_run_challRM_none writerT_run_challRM_some writerT_run_transmitRM_none
  writerT_run_transmitRM_some)

theorem cliComposedAdapterCoinLogged_clean_tr_run {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (i : ℕ) (p : Party) (m : Plain ℓ) (r : Option (BitVec 512))
    (σ_ad : CliAdapterState S) (σ_e2e : BHE2EDrvState S ℓ)
    (inst : BHAdapterInstMeta S) (d : BHModelInst S ℓ) (im_e2e : ModelDriverInstanceMeta S)
    (gs_m : CryptoGames.SM.GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (hinst_ad : σ_ad.1 i = some inst)
    (hClean : bhE2EDrvInstClean σ_e2e i = true)
    (hd : σ_e2e.insts[i]? = some d) (hime : σ_e2e.instMeta[i]? = some im_e2e)
    (hgs : d.gs = some gs_m) :
    WriterT.run (((cliComposedAdapterImplWithCoinLogged P ki C K qep decT encT
        (.inr ⟨i, .inl (.inl (.inl (.inl (p, m, r))))⟩)).run σ_ad).run σ_e2e) =
      let sch_m := sessionSchemeFixedSpk
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) d.idA d.idB) ℓ d.spkCoins
      let cfg_m := configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT
      (fun xw =>
        (((xw.1.1.map (cliWrapAdapterSend inst (σ_ad.2.1 i) p), σ_ad),
          { σ_e2e with insts := σ_e2e.insts.set i { d with gs := some xw.1.2 },
                       instMeta := σ_e2e.instMeta.set i im_e2e }), xw.2)) <$>
        WriterT.run ((transmitRM (smSchemeCoinLogged sch_m) (2 + 1) qep cfg_m (p, m, r)).run gs_m) := by
  rw [cliComposedAdapterImplWithCoinLogged_tr_run, hinst_ad]
  unfold bhE2EStepLocalSmCoinLogged
  simp only [hClean, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hd, hime, hgs,
    bhIsBobRecvSMQuery, bhIsBobAcceptSMResp, Bool.and_false, Bool.false_and, bhPackSmResp]
  dsimp only [oracleImplRM]
  simp only [bind_assoc, pure_bind, WriterT.run_bind, map_eq_bind_pure_comp, Function.comp_def]
  congr 1; funext ⟨⟨res, gsOut⟩, w⟩
  cases res <;> simp [WriterT.run_pure]

theorem cliComposedAdapter_clean_tr_run {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (i : ℕ) (p : Party) (m : Plain ℓ) (r : Option (BitVec 512))
    (σ_ad : CliAdapterState S) (σ_e2e : BHE2EDrvState S ℓ)
    (inst : BHAdapterInstMeta S) (d : BHModelInst S ℓ) (im_e2e : ModelDriverInstanceMeta S)
    (gs_m : CryptoGames.SM.GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (hinst_ad : σ_ad.1 i = some inst)
    (hClean : bhE2EDrvInstClean σ_e2e i = true)
    (hd : σ_e2e.insts[i]? = some d) (hime : σ_e2e.instMeta[i]? = some im_e2e)
    (hgs : d.gs = some gs_m) :
    (((cliComposedAdapterImplWith P ki C K qep decT encT
        (.inr ⟨i, .inl (.inl (.inl (.inl (p, m, r))))⟩)).run σ_ad).run σ_e2e) =
      let sch_m := sessionSchemeFixedSpk
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) d.idA d.idB) ℓ d.spkCoins
      let cfg_m := configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT
      (fun x =>
        ((x.1.map (cliWrapAdapterSend inst (σ_ad.2.1 i) p), σ_ad),
          { σ_e2e with insts := σ_e2e.insts.set i { d with gs := some x.2 },
                       instMeta := σ_e2e.instMeta.set i im_e2e })) <$>
        ((CryptoGames.SM.transmitR sch_m (2 + 1) qep cfg_m (p, m, r)).run gs_m) := by
  rw [cliComposedAdapterImplWith_tr_run, hinst_ad]
  unfold bhE2EStepLocalSm
  simp only [hClean, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hd, hime, hgs,
    bhIsBobRecvSMQuery, bhIsBobAcceptSMResp, Bool.and_false, Bool.false_and, bhPackSmResp]
  dsimp only [CryptoGames.SM.oracleImplR]
  simp only [bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp_def]
  congr 1; funext ⟨res, gsOut⟩
  cases res <;> rfl

theorem cliComposedAdapterCoinLogged_clean_ch_run {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (i : ℕ) (p : Party) (m0 m1 : Plain ℓ) (r : Option (BitVec 512))
    (σ_ad : CliAdapterState S) (σ_e2e : BHE2EDrvState S ℓ)
    (inst : BHAdapterInstMeta S) (d : BHModelInst S ℓ) (im_e2e : ModelDriverInstanceMeta S)
    (gs_m : CryptoGames.SM.GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (hinst_ad : σ_ad.1 i = some inst)
    (hClean : bhE2EDrvInstClean σ_e2e i = true)
    (hd : σ_e2e.insts[i]? = some d) (hime : σ_e2e.instMeta[i]? = some im_e2e)
    (hgs : d.gs = some gs_m) :
    WriterT.run (((cliComposedAdapterImplWithCoinLogged P ki C K qep decT encT
        (.inr ⟨i, .inl (.inl (.inl (.inr (p, m0, m1, r))))⟩)).run σ_ad).run σ_e2e) =
      let sch_m := sessionSchemeFixedSpk
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) d.idA d.idB) ℓ d.spkCoins
      let cfg_m := configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT
      (fun xw =>
        (((xw.1.1.map (cliWrapAdapterSend inst (σ_ad.2.1 i) p), σ_ad),
          { σ_e2e with insts := σ_e2e.insts.set i { d with gs := some xw.1.2 },
                       instMeta := σ_e2e.instMeta.set i im_e2e }), xw.2)) <$>
        WriterT.run ((challRM (smSchemeCoinLogged sch_m) (2 + 1) qep cfg_m (p, m0, m1, r)).run gs_m) := by
  rw [cliComposedAdapterImplWithCoinLogged_ch_run, hinst_ad]
  unfold bhE2EStepLocalSmCoinLogged
  simp only [hClean, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hd, hime, hgs,
    bhIsBobRecvSMQuery, bhIsBobAcceptSMResp, Bool.and_false, Bool.false_and, bhPackSmResp]
  dsimp only [oracleImplRM]
  simp only [bind_assoc, pure_bind, WriterT.run_bind, map_eq_bind_pure_comp, Function.comp_def]
  congr 1; funext ⟨⟨res, gsOut⟩, w⟩
  cases res <;> simp [WriterT.run_pure]

theorem cliComposedAdapter_clean_ch_run {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (i : ℕ) (p : Party) (m0 m1 : Plain ℓ) (r : Option (BitVec 512))
    (σ_ad : CliAdapterState S) (σ_e2e : BHE2EDrvState S ℓ)
    (inst : BHAdapterInstMeta S) (d : BHModelInst S ℓ) (im_e2e : ModelDriverInstanceMeta S)
    (gs_m : CryptoGames.SM.GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (hinst_ad : σ_ad.1 i = some inst)
    (hClean : bhE2EDrvInstClean σ_e2e i = true)
    (hd : σ_e2e.insts[i]? = some d) (hime : σ_e2e.instMeta[i]? = some im_e2e)
    (hgs : d.gs = some gs_m) :
    (((cliComposedAdapterImplWith P ki C K qep decT encT
        (.inr ⟨i, .inl (.inl (.inl (.inr (p, m0, m1, r))))⟩)).run σ_ad).run σ_e2e) =
      let sch_m := sessionSchemeFixedSpk
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) d.idA d.idB) ℓ d.spkCoins
      let cfg_m := configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT
      (fun x =>
        ((x.1.map (cliWrapAdapterSend inst (σ_ad.2.1 i) p), σ_ad),
          { σ_e2e with insts := σ_e2e.insts.set i { d with gs := some x.2 },
                       instMeta := σ_e2e.instMeta.set i im_e2e })) <$>
        ((CryptoGames.SM.challR sch_m (2 + 1) qep cfg_m (p, m0, m1, r)).run gs_m) := by
  rw [cliComposedAdapterImplWith_ch_run, hinst_ad]
  unfold bhE2EStepLocalSm
  simp only [hClean, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hd, hime, hgs,
    bhIsBobRecvSMQuery, bhIsBobAcceptSMResp, Bool.and_false, Bool.false_and, bhPackSmResp]
  dsimp only [CryptoGames.SM.oracleImplR]
  simp only [bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp_def]
  congr 1; funext ⟨res, gsOut⟩
  cases res <;> rfl

theorem cliDrvSMCoinLogged_adapter_coupling_tr {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ext : QueryImpl (cliGameSmSpec ℓ (BitVec 512)) (BHDrvM S ℓ))
    (hCli : CliSpecPqxdh run X W) (hℓ : ℓ < 10 ^ 6)
    {b : Bool} {qStart : ℕ} {qs_rem : ℕ → ℕ}
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {σ_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ}
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e)
    (hRem : CliAdapterDrvRemoteIdInv S ℓ ds_cli σ_e2e)
    (i : ℕ) (p : Party) (m : Plain ℓ) (r : Option (BitVec 512))
    (hq_pos : i < ds_cli.bhInsts.length → 0 < qs_rem i) :
    let P := modelPrims X W
    let ki := SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P
    cliAdapterCoinStepCoupled X W b qStart (Function.update qs_rem i (qs_rem i - 1))
      (WriterT.run (((cliDrvSMCoinLogged S ℓ run W qep decT encT
          (liftQueryImplStateT2 (n := CoinLogM) ext)
          ⟨i, .inl (.inl (.inl (.inl (p, m, r))))⟩).run ds_cli).run st_cli))
      (WriterT.run (((cliComposedAdapterImplWithCoinLogged P ki W.C W.Q.K qep decT encT
          (.inr ⟨i, .inl (.inl (.inl (.inl (p, m, r))))⟩)).run σ_ad).run σ_e2e)) := by
  intro P ki
  cases hClean : bhDrvInstClean ds_cli i
  · have hClean_e2e : bhE2EDrvInstClean σ_e2e i = false :=
      (bhDrvInstClean_eq_bhE2EDrvInstClean_of_cliRel hRel i).symm.trans hClean
    have h_cli : WriterT.run (((cliDrvSMCoinLogged S ℓ run W qep decT encT
        (liftQueryImplStateT2 (n := CoinLogM) ext)
        ⟨i, .inl (.inl (.inl (.inl (p, m, r))))⟩).run ds_cli).run st_cli) =
        pure (((none, ds_cli), st_cli), []) := by
      unfold cliDrvSMCoinLogged
      simp [StateT.run_bind, StateT.run_get, hClean, StateT.run_pure, WriterT.run_pure,
        bhSmDefaultWithSpqr]
    have h_ad : WriterT.run (((cliComposedAdapterImplWithCoinLogged P ki W.C W.Q.K qep decT encT
        (.inr ⟨i, .inl (.inl (.inl (.inl (p, m, r))))⟩)).run σ_ad).run σ_e2e) =
        pure (((none, σ_ad), σ_e2e), []) := by
      rw [cliComposedAdapterImplWithCoinLogged_tr_run]
      rcases σ_ad.1 i with _ | inst
      · simp [WriterT.run_pure]
      · unfold bhE2EStepLocalSmCoinLogged
        simp [hClean_e2e, WriterT.run_pure]
    rw [h_cli, h_ad]
    exact cliAdapterCoinStepCoupled_ret _ _ _ _ _ _ (cliAdapterDrvRel_decrement_i hRel i)
  · by_cases hi_cli : i < ds_cli.bhInsts.length
    swap
    · have hOob : ds_cli.bhInsts.length ≤ i := Nat.le_of_not_lt hi_cli
      have hbi_none : ds_cli.bhInsts[i]? = none := List.getElem?_eq_none hOob
      have hd_none : σ_e2e.insts[i]? = none := List.getElem?_eq_none (hRel.insts_len_eq ▸ hOob)
      have h_cli : WriterT.run (((cliDrvSMCoinLogged S ℓ run W qep decT encT
          (liftQueryImplStateT2 (n := CoinLogM) ext)
          ⟨i, .inl (.inl (.inl (.inl (p, m, r))))⟩).run ds_cli).run st_cli) =
          pure (((none, ds_cli), st_cli), []) := by
        unfold cliDrvSMCoinLogged
        simp [StateT.run_bind, StateT.run_get, hClean, hbi_none,
          StateT.run_pure, WriterT.run_pure, bhSmDefaultWithSpqr]
      have h_ad : WriterT.run (((cliComposedAdapterImplWithCoinLogged P ki W.C W.Q.K qep decT encT
          (.inr ⟨i, .inl (.inl (.inl (.inl (p, m, r))))⟩)).run σ_ad).run σ_e2e) =
          pure (((none, σ_ad), σ_e2e), []) := by
        rw [cliComposedAdapterImplWithCoinLogged_tr_run]
        rcases σ_ad.1 i with _ | inst
        · simp [WriterT.run_pure]
        · unfold bhE2EStepLocalSmCoinLogged
          simp only [hd_none]; split_ifs <;> simp [WriterT.run_pure]
      rw [h_cli, h_ad]
      exact cliAdapterCoinStepCoupled_ret _ _ _ _ _ _ (cliAdapterDrvRel_decrement_i hRel i)
    · have hi_e2e : i < σ_e2e.insts.length := hRel.insts_len_eq ▸ hi_cli
      have hi_mb : i < ds_cli.instMeta.length := hRel.meta_cli_len_eq.symm ▸ hi_cli
      have hi_me : i < σ_e2e.instMeta.length := hRel.meta_e2e_len_eq.symm ▸ hi_e2e
      have hCorr : ds_cli.instMeta[i].ikACorrAtAccept = false :=
        bhDrvInstClean_imp_ikACorrAtAccept_false hClean hi_cli hi_mb
      obtain ⟨inst, hinst_ad, hInstRel⟩ := hRel.insts_rel i hi_cli hi_e2e hi_mb hi_me
      set bi := ds_cli.bhInsts[i]; set d := σ_e2e.insts[i]
      set im := ds_cli.instMeta[i]; set im_e2e := σ_e2e.instMeta[i]
      have hbi_opt : ds_cli.bhInsts[i]? = some bi := List.getElem?_eq_getElem hi_cli
      have hd_opt : σ_e2e.insts[i]? = some d := List.getElem?_eq_getElem hi_e2e
      have him_opt : ds_cli.instMeta[i]? = some im := List.getElem?_eq_getElem hi_mb
      have hime_opt : σ_e2e.instMeta[i]? = some im_e2e := List.getElem?_eq_getElem hi_me
      have hClean_e2e : bhE2EDrvInstClean σ_e2e i = true :=
        (bhDrvInstClean_eq_bhE2EDrvInstClean_of_cliRel hRel i).symm.trans hClean
      have hgs := hInstRel.gs_rel
      cases hgs_cli : bi.gs with
      | none => rw [hgs_cli] at hgs; exact False.elim hgs
      | some gs_cli =>
        cases hgs_m : d.gs with
        | none => rw [hgs_cli, hgs_m] at hgs; exact False.elim hgs
        | some gs_m =>
          rcases r with _ | cns
          ·
            rw [hgs_cli, hgs_m] at hgs; rcases hgs with ⟨hb_eq, hrest⟩
            simp only [hCorr, Bool.false_eq_true, ↓reduceIte] at hrest
            rcases hrest with
              ⟨_, h_win, h_ep, h_idx, h_max, h_ch, h_comp, h_tL, h_lk, h_cr,
               _, _, _, _, _, h_epA0, h_epB0, _, h_cpA0, h_tL0,
               _, _, _, _, _, _, _, _⟩
            have h_sendOK :
                (bhConfigSpkS (Msg := Plain ℓ) decT encT).sendOK gs_cli p =
                  (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).sendOK gs_m p := by
              dsimp [bhConfigSpkS, configRefuseEarlyBobCorr, configR1OnCurve,
                CryptoGames.SM.configR1, CryptoGames.SM.noBobSendInEpoch0]; rw [h_ep]
            rw [cliDrvSMCoinLogged_clean_tc_run run W qep decT encT _ ds_cli st_cli i bi im gs_cli
                (.inl (p, m, none)) hClean hbi_opt him_opt hgs_cli,
              cliComposedAdapterCoinLogged_clean_tr_run P ki W.C W.Q.K qep decT encT i p m none
                σ_ad σ_e2e inst d im_e2e gs_m hinst_ad hClean_e2e hd_opt hime_opt hgs_m]
            dsimp only
            rw [oracleImplRM_tr, writerT_run_transmitRM_none, writerT_run_transmitRM_none]
            cases h_sendOK_m : (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).sendOK gs_m p
            · rw [h_sendOK, h_sendOK_m]
              simp only [Bool.not_false, ↓reduceIte, map_pure, Option.map_none,
                bi, im, bhDrvState_set_same_gs_local ds_cli i hi_cli hi_mb gs_cli hgs_cli,
                d, im_e2e, bhE2EDrvState_set_same_gs_local σ_e2e i hi_e2e hi_me gs_m hgs_m]
              exact cliAdapterCoinStepCoupled_ret _ _ _ _ _ _ (cliAdapterDrvRel_decrement_i hRel i)
            · rw [h_sendOK, h_sendOK_m]
              cases h_win_m : gs_m.win
              · rw [h_win, h_win_m]
                simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                have hbob_of_B : p = .B → im.bobAccepted = true := by
                  intro hpB; subst hpB
                  by_cases hbob : im.bobAccepted = true
                  · exact hbob
                  · simp only [Bool.not_eq_true] at hbob
                    have hepB0 : gs_m.epoch .B = 0 := h_epB0 (by simp [hbob])
                    dsimp [configRefuseEarlyBobCorr, configR1OnCurve,
                      CryptoGames.SM.configR1, CryptoGames.SM.noBobSendInEpoch0] at h_sendOK_m
                    simp [hepB0] at h_sendOK_m
                rcases epMgmt_false_rel qep p hb_eq h_win h_ep h_idx h_max h_ch h_comp h_tL h_lk h_cr
                    h_epA0 h_epB0 h_cpA0 h_tL0 hbob_of_B with
                  ⟨hep_cli, hep_m⟩ |
                  ⟨s_cli, s_m, hep_cli, hep_m, _⟩
                · rw [hep_cli, hep_m]
                  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
                    Option.map_none,
                    bi, im, bhDrvState_set_same_gs_local ds_cli i hi_cli hi_mb gs_cli hgs_cli,
                    d, im_e2e, bhE2EDrvState_set_same_gs_local σ_e2e i hi_e2e hi_me gs_m hgs_m]
                  exact cliAdapterCoinStepCoupled_bind_pure ($ᵗ (BitVec 512)) _ _ fun _ _ =>
                    ⟨rfl, rfl, cliAdapterDrvRel_decrement_i hRel i⟩
                · rw [hep_cli, hep_m]
                  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
                    Option.map_some]
                  refine cliAdapterCoinStepCoupled_bind_pure ($ᵗ (BitVec 512)) _ _ fun cns _ => ?_
                  obtain ⟨hout2, hRel'⟩ := send_record_rel_of_tr_some qep decT encT hCli hℓ
                    hRel hRem hi_cli (hq_pos hi_cli) hClean hinst_ad hgs_cli hgs_m
                    h_sendOK_m h_win_m hep_cli hep_m m cns false
                  exact ⟨congrArg some hout2, rfl, hRel'⟩
              · rw [h_win, h_win_m]
                simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, map_pure, Option.map_none,
                  bi, im, bhDrvState_set_same_gs_local ds_cli i hi_cli hi_mb gs_cli hgs_cli,
                  d, im_e2e, bhE2EDrvState_set_same_gs_local σ_e2e i hi_e2e hi_me gs_m hgs_m]
                exact cliAdapterCoinStepCoupled_ret _ _ _ _ _ _ (cliAdapterDrvRel_decrement_i hRel i)
          ·
            refine cliAdapterCoinStepCoupled_of_some_cns cns
              (cliDrvSM_adapter_coupling_tr run X W qep decT encT ext ki
                hCli hℓ hRel hRem i p m (some cns) (hq_pos hi_cli)) ?_ ?_
            · rw [cliDrvSMCoinLogged_clean_tc_run run W qep decT encT _ ds_cli st_cli i bi im gs_cli
                  (.inl (p, m, some cns)) hClean hbi_opt him_opt hgs_cli,
                cliDrvSM_clean_tc_run run W qep decT encT ext ds_cli st_cli i bi im gs_cli
                  (.inl (p, m, some cns)) hClean hbi_opt him_opt hgs_cli]
              rw [oracleImplRM_tr, oracleImplR_tr, writerT_run_transmitRM_some,
                Functor.map_map, Functor.map_map]; rfl
            · rw [cliComposedAdapterCoinLogged_clean_tr_run P ki W.C W.Q.K qep decT encT i p m
                  (some cns) σ_ad σ_e2e inst d im_e2e gs_m hinst_ad hClean_e2e hd_opt hime_opt hgs_m,
                cliComposedAdapter_clean_tr_run P ki W.C W.Q.K qep decT encT i p m
                  (some cns) σ_ad σ_e2e inst d im_e2e gs_m hinst_ad hClean_e2e hd_opt hime_opt hgs_m]
              dsimp only
              rw [writerT_run_transmitRM_some]
              simp only [Functor.map_map, Option.isSome_map]

theorem cliDrvSMCoinLogged_adapter_coupling_ch {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ext : QueryImpl (cliGameSmSpec ℓ (BitVec 512)) (BHDrvM S ℓ))
    (hCli : CliSpecPqxdh run X W) (hℓ : ℓ < 10 ^ 6)
    {b : Bool} {qStart : ℕ} {qs_rem : ℕ → ℕ}
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {σ_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ}
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e)
    (hRem : CliAdapterDrvRemoteIdInv S ℓ ds_cli σ_e2e)
    (i : ℕ) (p : Party) (m0 m1 : Plain ℓ) (r : Option (BitVec 512))
    (hq_pos : i < ds_cli.bhInsts.length → 0 < qs_rem i) :
    let P := modelPrims X W
    let ki := SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P
    cliAdapterCoinStepCoupled X W b qStart (Function.update qs_rem i (qs_rem i - 1))
      (WriterT.run (((cliDrvSMCoinLogged S ℓ run W qep decT encT
          (liftQueryImplStateT2 (n := CoinLogM) ext)
          ⟨i, .inl (.inl (.inl (.inr (p, m0, m1, r))))⟩).run ds_cli).run st_cli))
      (WriterT.run (((cliComposedAdapterImplWithCoinLogged P ki W.C W.Q.K qep decT encT
          (.inr ⟨i, .inl (.inl (.inl (.inr (p, m0, m1, r))))⟩)).run σ_ad).run σ_e2e)) := by
  intro P ki
  cases hClean : bhDrvInstClean ds_cli i
  · have hClean_e2e : bhE2EDrvInstClean σ_e2e i = false :=
      (bhDrvInstClean_eq_bhE2EDrvInstClean_of_cliRel hRel i).symm.trans hClean
    have h_cli : WriterT.run (((cliDrvSMCoinLogged S ℓ run W qep decT encT
        (liftQueryImplStateT2 (n := CoinLogM) ext)
        ⟨i, .inl (.inl (.inl (.inr (p, m0, m1, r))))⟩).run ds_cli).run st_cli) =
        pure (((none, ds_cli), st_cli), []) := by
      unfold cliDrvSMCoinLogged
      simp [StateT.run_bind, StateT.run_get, hClean, StateT.run_pure, WriterT.run_pure,
        bhSmDefaultWithSpqr]
    have h_ad : WriterT.run (((cliComposedAdapterImplWithCoinLogged P ki W.C W.Q.K qep decT encT
        (.inr ⟨i, .inl (.inl (.inl (.inr (p, m0, m1, r))))⟩)).run σ_ad).run σ_e2e) =
        pure (((none, σ_ad), σ_e2e), []) := by
      rw [cliComposedAdapterImplWithCoinLogged_ch_run]
      rcases σ_ad.1 i with _ | inst
      · simp [WriterT.run_pure]
      · unfold bhE2EStepLocalSmCoinLogged
        simp [hClean_e2e, WriterT.run_pure]
    rw [h_cli, h_ad]
    exact cliAdapterCoinStepCoupled_ret _ _ _ _ _ _ (cliAdapterDrvRel_decrement_i hRel i)
  · by_cases hi_cli : i < ds_cli.bhInsts.length
    swap
    · have hOob : ds_cli.bhInsts.length ≤ i := Nat.le_of_not_lt hi_cli
      have hbi_none : ds_cli.bhInsts[i]? = none := List.getElem?_eq_none hOob
      have hd_none : σ_e2e.insts[i]? = none := List.getElem?_eq_none (hRel.insts_len_eq ▸ hOob)
      have h_cli : WriterT.run (((cliDrvSMCoinLogged S ℓ run W qep decT encT
          (liftQueryImplStateT2 (n := CoinLogM) ext)
          ⟨i, .inl (.inl (.inl (.inr (p, m0, m1, r))))⟩).run ds_cli).run st_cli) =
          pure (((none, ds_cli), st_cli), []) := by
        unfold cliDrvSMCoinLogged
        simp [StateT.run_bind, StateT.run_get, hClean, hbi_none,
          StateT.run_pure, WriterT.run_pure, bhSmDefaultWithSpqr]
      have h_ad : WriterT.run (((cliComposedAdapterImplWithCoinLogged P ki W.C W.Q.K qep decT encT
          (.inr ⟨i, .inl (.inl (.inl (.inr (p, m0, m1, r))))⟩)).run σ_ad).run σ_e2e) =
          pure (((none, σ_ad), σ_e2e), []) := by
        rw [cliComposedAdapterImplWithCoinLogged_ch_run]
        rcases σ_ad.1 i with _ | inst
        · simp [WriterT.run_pure]
        · unfold bhE2EStepLocalSmCoinLogged
          simp only [hd_none]; split_ifs <;> simp [WriterT.run_pure]
      rw [h_cli, h_ad]
      exact cliAdapterCoinStepCoupled_ret _ _ _ _ _ _ (cliAdapterDrvRel_decrement_i hRel i)
    · have hi_e2e : i < σ_e2e.insts.length := hRel.insts_len_eq ▸ hi_cli
      have hi_mb : i < ds_cli.instMeta.length := hRel.meta_cli_len_eq.symm ▸ hi_cli
      have hi_me : i < σ_e2e.instMeta.length := hRel.meta_e2e_len_eq.symm ▸ hi_e2e
      have hCorr : ds_cli.instMeta[i].ikACorrAtAccept = false :=
        bhDrvInstClean_imp_ikACorrAtAccept_false hClean hi_cli hi_mb
      obtain ⟨inst, hinst_ad, hInstRel⟩ := hRel.insts_rel i hi_cli hi_e2e hi_mb hi_me
      set bi := ds_cli.bhInsts[i]; set d := σ_e2e.insts[i]
      set im := ds_cli.instMeta[i]; set im_e2e := σ_e2e.instMeta[i]
      have hbi_opt : ds_cli.bhInsts[i]? = some bi := List.getElem?_eq_getElem hi_cli
      have hd_opt : σ_e2e.insts[i]? = some d := List.getElem?_eq_getElem hi_e2e
      have him_opt : ds_cli.instMeta[i]? = some im := List.getElem?_eq_getElem hi_mb
      have hime_opt : σ_e2e.instMeta[i]? = some im_e2e := List.getElem?_eq_getElem hi_me
      have hClean_e2e : bhE2EDrvInstClean σ_e2e i = true :=
        (bhDrvInstClean_eq_bhE2EDrvInstClean_of_cliRel hRel i).symm.trans hClean
      have hgs := hInstRel.gs_rel
      cases hgs_cli : bi.gs with
      | none => rw [hgs_cli] at hgs; exact False.elim hgs
      | some gs_cli =>
        cases hgs_m : d.gs with
        | none => rw [hgs_cli, hgs_m] at hgs; exact False.elim hgs
        | some gs_m =>
          rcases r with _ | cns
          ·
            rw [hgs_cli, hgs_m] at hgs; rcases hgs with ⟨hb_eq, hrest⟩
            simp only [hCorr, Bool.false_eq_true, ↓reduceIte] at hrest
            rcases hrest with
              ⟨_, h_win, h_ep, h_idx, h_max, h_ch, h_comp, h_tL, h_lk, h_cr,
               _, _, _, _, _, h_epA0, h_epB0, _, h_cpA0, h_tL0,
               _, _, _, _, _, _, _, _⟩
            have h_sendOK :
                (bhConfigSpkS (Msg := Plain ℓ) decT encT).sendOK gs_cli p =
                  (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).sendOK gs_m p := by
              dsimp [bhConfigSpkS, configRefuseEarlyBobCorr, configR1OnCurve,
                CryptoGames.SM.configR1, CryptoGames.SM.noBobSendInEpoch0]; rw [h_ep]
            rw [cliDrvSMCoinLogged_clean_tc_run run W qep decT encT _ ds_cli st_cli i bi im gs_cli
                (.inr (p, m0, m1, none)) hClean hbi_opt him_opt hgs_cli,
              cliComposedAdapterCoinLogged_clean_ch_run P ki W.C W.Q.K qep decT encT i p m0 m1 none
                σ_ad σ_e2e inst d im_e2e gs_m hinst_ad hClean_e2e hd_opt hime_opt hgs_m]
            dsimp only
            rw [oracleImplRM_ch, writerT_run_challRM_none, writerT_run_challRM_none]
            cases h_sendOK_m : (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).sendOK gs_m p
            · rw [h_sendOK, h_sendOK_m]
              simp only [Bool.not_false, ↓reduceIte, map_pure, Option.map_none,
                bi, im, bhDrvState_set_same_gs_local ds_cli i hi_cli hi_mb gs_cli hgs_cli,
                d, im_e2e, bhE2EDrvState_set_same_gs_local σ_e2e i hi_e2e hi_me gs_m hgs_m]
              exact cliAdapterCoinStepCoupled_ret _ _ _ _ _ _ (cliAdapterDrvRel_decrement_i hRel i)
            · rw [h_sendOK, h_sendOK_m]
              cases h_win_m : gs_m.win
              · rw [h_win, h_win_m]
                simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                have hbob_of_B : p = .B → im.bobAccepted = true := by
                  intro hpB; subst hpB
                  by_cases hbob : im.bobAccepted = true
                  · exact hbob
                  · simp only [Bool.not_eq_true] at hbob
                    have hepB0 : gs_m.epoch .B = 0 := h_epB0 (by simp [hbob])
                    dsimp [configRefuseEarlyBobCorr, configR1OnCurve,
                      CryptoGames.SM.configR1, CryptoGames.SM.noBobSendInEpoch0] at h_sendOK_m
                    simp [hepB0] at h_sendOK_m
                rcases epMgmt_false_rel qep p hb_eq h_win h_ep h_idx h_max h_ch h_comp h_tL h_lk h_cr
                    h_epA0 h_epB0 h_cpA0 h_tL0 hbob_of_B with
                  ⟨hep_cli, hep_m⟩ |
                  ⟨s_cli, s_m, hep_cli, hep_m, _, _, _, _,
                   _, _, hs_ep, _, _, _, _, hs_tL, _, _,
                   _, _, _, _⟩
                · rw [hep_cli, hep_m]
                  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
                    Option.map_none,
                    bi, im, bhDrvState_set_same_gs_local ds_cli i hi_cli hi_mb gs_cli hgs_cli,
                    d, im_e2e, bhE2EDrvState_set_same_gs_local σ_e2e i hi_e2e hi_me gs_m hgs_m]
                  exact cliAdapterCoinStepCoupled_bind_pure ($ᵗ (BitVec 512)) _ _ fun _ _ =>
                    ⟨rfl, rfl, cliAdapterDrvRel_decrement_i hRel i⟩
                · rw [hep_cli, hep_m]
                  have h_safeCh_s : s_cli.safeCh (2 + 1) p = s_m.safeCh (2 + 1) p := by
                    unfold CryptoGames.SM.GameState.safeCh CryptoGames.SM.healedBy
                    rw [hs_tL, hs_ep]
                  have h_challOK_s :
                      (bhConfigSpkS (Msg := Plain ℓ) decT encT).base.challAllowedIn (s_cli.epoch p) =
                        (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).base.challAllowedIn (s_m.epoch p) := by
                    dsimp [bhConfigSpkS, configRefuseEarlyBobCorr, configR1OnCurve]
                    rw [hs_ep]; rfl
                  have h_challMsg_s :
                      (bhConfigSpkS (Msg := Plain ℓ) decT encT).base.challMsg (s_cli.epoch p) =
                        (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).base.challMsg (s_m.epoch p) := by
                    dsimp [bhConfigSpkS, configRefuseEarlyBobCorr, configR1OnCurve]
                    rw [hs_ep]; rfl
                  dsimp only
                  rw [h_safeCh_s, h_challOK_s, h_challMsg_s, hb_eq]
                  cases (!s_m.safeCh (2 + 1) p ||
                    !(configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).base.challAllowedIn (s_m.epoch p))
                  · simp only [Bool.false_eq_true, ↓reduceIte, map_eq_bind_pure_comp,
                      Function.comp_def, bind_assoc, pure_bind, Option.map_some]
                    refine cliAdapterCoinStepCoupled_bind_pure ($ᵗ (BitVec 512)) _ _ fun cns _ => ?_
                    let m_send :=
                      ((configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).base.challMsg (s_m.epoch p)).getD
                        (if gs_m.b then m1 else m0)
                    obtain ⟨hout2, hRel'⟩ := send_record_rel_of_tr_some qep decT encT hCli hℓ
                      hRel hRem hi_cli (hq_pos hi_cli) hClean hinst_ad hgs_cli hgs_m
                      h_sendOK_m h_win_m hep_cli hep_m m_send cns true
                    exact ⟨congrArg some hout2, rfl, hRel'⟩
                  · simp only [↓reduceIte, map_eq_bind_pure_comp, Function.comp_def, bind_assoc,
                      pure_bind, Option.map_none,
                      bi, im, bhDrvState_set_same_gs_local ds_cli i hi_cli hi_mb gs_cli hgs_cli,
                      d, im_e2e, bhE2EDrvState_set_same_gs_local σ_e2e i hi_e2e hi_me gs_m hgs_m]
                    exact cliAdapterCoinStepCoupled_bind_pure ($ᵗ (BitVec 512)) _ _ fun _ _ =>
                      ⟨rfl, rfl, cliAdapterDrvRel_decrement_i hRel i⟩
              · rw [h_win, h_win_m]
                simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, map_pure, Option.map_none,
                  bi, im, bhDrvState_set_same_gs_local ds_cli i hi_cli hi_mb gs_cli hgs_cli,
                  d, im_e2e, bhE2EDrvState_set_same_gs_local σ_e2e i hi_e2e hi_me gs_m hgs_m]
                exact cliAdapterCoinStepCoupled_ret _ _ _ _ _ _ (cliAdapterDrvRel_decrement_i hRel i)
          ·
            refine cliAdapterCoinStepCoupled_of_some_cns cns
              (cliDrvSM_adapter_coupling_ch run X W qep decT encT ext ki
                hCli hℓ hRel hRem i p m0 m1 (some cns) (hq_pos hi_cli)) ?_ ?_
            · rw [cliDrvSMCoinLogged_clean_tc_run run W qep decT encT _ ds_cli st_cli i bi im gs_cli
                  (.inr (p, m0, m1, some cns)) hClean hbi_opt him_opt hgs_cli,
                cliDrvSM_clean_tc_run run W qep decT encT ext ds_cli st_cli i bi im gs_cli
                  (.inr (p, m0, m1, some cns)) hClean hbi_opt him_opt hgs_cli]
              rw [oracleImplRM_ch, oracleImplR_ch, writerT_run_challRM_some,
                Functor.map_map, Functor.map_map]; rfl
            · rw [cliComposedAdapterCoinLogged_clean_ch_run P ki W.C W.Q.K qep decT encT i p m0 m1
                  (some cns) σ_ad σ_e2e inst d im_e2e gs_m hinst_ad hClean_e2e hd_opt hime_opt hgs_m,
                cliComposedAdapter_clean_ch_run P ki W.C W.Q.K qep decT encT i p m0 m1
                  (some cns) σ_ad σ_e2e inst d im_e2e gs_m hinst_ad hClean_e2e hd_opt hime_opt hgs_m]
              dsimp only
              rw [writerT_run_challRM_some]
              simp only [Functor.map_map, Option.isSome_map]

private theorem simulateQ_query_bind_run₂_local {ι : Type} {spec : OracleSpec ι} {M : Type → Type}
    [Monad M] [LawfulMonad M] {σ₁ σ₂ α : Type}
    (impl : QueryImpl spec (StateT σ₁ (StateT σ₂ M)))
    (q : ι) (oa : spec.Range q → OracleComp spec α)
    (s₁ : σ₁) (s₂ : σ₂) :
    (((simulateQ impl (liftM (OracleSpec.query q) >>= oa)).run s₁).run s₂) =
      (((impl q).run s₁).run s₂ >>= fun z => ((simulateQ impl (oa z.1.1)).run z.1.2).run z.2) := by
  simp [simulateQ_bind, StateT.run_bind]

private theorem writerT_run_simulateQ_query_bind_cont
    {ι : Type} {spec : OracleSpec ι} {σ₁ σ₂ α γ : Type}
    (impl : QueryImpl spec (StateT σ₁ (StateT σ₂ CoinLogM)))
    (q : ι) (oa : spec.Range q → OracleComp spec α)
    (s₁ : σ₁) (s₂ : σ₂)
    (G : List (BitVec 512) → (((α × σ₁) × σ₂) × List (BitVec 512)) → ProbComp γ)
    (hAssoc : ∀ acc z w₁ w₂, G acc (z, w₁ ++ w₂) = G (acc ++ w₁) (z, w₂))
    (acc : List (BitVec 512)) :
    (WriterT.run (((simulateQ impl (liftM (OracleSpec.query q) >>= oa)).run s₁).run s₂) >>=
        G acc) =
      (WriterT.run (((impl q).run s₁).run s₂) >>= fun zw =>
        WriterT.run (((simulateQ impl (oa zw.1.1.1)).run zw.1.1.2).run zw.1.2) >>=
          G (acc ++ zw.2)) := by
  rw [simulateQ_query_bind_run₂_local]
  simp only [WriterT.run_bind, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  congr 1; funext ⟨z, w₁⟩
  congr 1; funext ⟨z', w₂⟩
  change G acc (z', w₁ ++ w₂) = G (acc ++ w₁) (z', w₂)
  exact hAssoc acc z' w₁ w₂

private theorem isQueryBoundP_congr_pred_local {ι α : Type} {spec : OracleSpec ι}
    {p₁ p₂ : ι → Prop} [d₁ : DecidablePred p₁] [d₂ : DecidablePred p₂]
    (h : ∀ q, p₁ q ↔ p₂ q) {n : ℕ}
    (oa : OracleComp spec α) :
    oa.IsQueryBoundP p₁ n ↔ oa.IsQueryBoundP p₂ n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure _ => simp [OracleComp.IsQueryBoundP]
  | query_bind q oa ih =>
    simp only [OracleComp.isQueryBoundP_query_bind_iff]
    by_cases hp : p₁ q
    · have hp₂ : p₂ q := (h q).mp hp
      simp only [hp, hp₂, ↓reduceIte, not_true_eq_false, false_or]
      exact and_congr_right' (forall_congr' fun u => ih u)
    · have hp₂ : ¬ p₂ q := fun h2 => hp ((h q).mpr h2)
      simp only [hp, hp₂, ↓reduceIte, not_false_eq_true, true_or, true_and]
      exact forall_congr' fun u => ih u

theorem simulateQ_cliDrvImplCoinLogged_adapter_coupling_le
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt α : Type}
    (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (hCli : CliSpecPqxdh run X W) (hℓ : ℓ < 10 ^ 6)
    (hKeyInd : CliKeyIndStepBridgeProp S ℓ X W qep decT encT)
    (hStart : CliStartStepBridgeProp S ℓ run X W qep decT encT)
    (hSm : CliSmStepBridgeProp S ℓ run X W qep decT encT)
    (b val : Bool) (qStart : ℕ)
    (obs_cli : ((α × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S) → ProbComp Bool)
    (obs_ad : ((α × CliAdapterState S) × BHE2EDrvState S ℓ) → ProbComp Bool)
    (hObs : ∀ {n : ℕ} {qs_rem : ℕ → ℕ} x y, x.1.1 = y.1.1 →
      CliAdapterDrvRel S ℓ X W b n qs_rem x.2 x.1.2 y.1.2 y.2 →
      𝒟[obs_cli x] = 𝒟[obs_ad y])
    (oa : OracleComp (cliGameSpec S ℓ (BitVec 512)) α)
    (acc : List (BitVec 512))
    {n qStart_rem : ℕ} {qs_rem : ℕ → ℕ}
    (hn : n + qStart_rem ≤ qStart)
    (hb_start : OracleComp.IsQueryBoundP oa (fun q => q matches .inl (.inr _)) qStart_rem)
    (hb_inst : ∀ k < qStart,
      OracleComp.IsQueryBoundP oa
        (fun q => bhIsInstQueryWithSpqr k q) (qs_rem k))
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {σ_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ}
    (hRel : CliAdapterDrvRel S ℓ X W b n qs_rem st_cli ds_cli σ_ad σ_e2e)
    (hRem : CliE2ERemoteIdInv σ_e2e) :
    let P := modelPrims X W
    let impl_cli_log := cliDrvImplCoinLogged S ℓ P run W qep decT encT
      bhNoExtWithSpqr (fun _ _ _ _ _ => some b)
    let impl_cli := cliDrvImpl S ℓ P run W qep decT encT
      bhNoExtWithSpqr (fun _ _ _ _ _ => some b)
    let impl_ad_log := cliComposedAdapterImplWithCoinLogged P
      (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) W.C W.Q.K qep decT encT
    let G_cli : List (BitVec 512) →
        (((α × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S) × List (BitVec 512)) →
        ProbComp Bool :=
      fun acc0 xw => obs_cli xw.1 >>= fun out =>
        pure (if W.Q.K.KemFailBad
          ((acc0 ++ xw.2).map coinBytes)
          then false else (out == val))
    let G_ad : List (BitVec 512) →
        (((α × CliAdapterState S) × BHE2EDrvState S ℓ) × List (BitVec 512)) →
        ProbComp Bool :=
      fun acc0 yw => obs_ad yw.1 >>= fun out =>
        pure (if W.Q.K.KemFailBad
          ((acc0 ++ yw.2).map coinBytes)
          then false else (out == val))
    let F_bad : ((α × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S) → ProbComp Bool :=
      fun x => pure (cliClause2BadKemBool S P x.2 x.1.2)
    𝒟[WriterT.run (((simulateQ impl_cli_log oa).run ds_cli).run st_cli) >>= G_cli acc] {true} ≤
      𝒟[WriterT.run (((simulateQ impl_ad_log oa).run σ_ad).run σ_e2e) >>= G_ad acc] {true} +
        𝒟[(((simulateQ impl_cli oa).run ds_cli).run st_cli) >>= F_bad] {true} := by
  intro P impl_cli_log impl_cli impl_ad_log G_cli G_ad F_bad
  induction oa using OracleComp.inductionOn
      generalizing acc n qStart_rem qs_rem st_cli ds_cli σ_ad σ_e2e with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure, pure_bind]
    have hEq : 𝒟[G_cli acc (((a, ds_cli), st_cli), ∅)] {true} =
        𝒟[G_ad acc (((a, σ_ad), σ_e2e), ∅)] {true} := by
      dsimp only [G_cli, G_ad]
      rw [evalDist_bind_true_eq_probExpect_hopB, evalDist_bind_true_eq_probExpect_hopB]
      unfold SignalPqxdh.Security.probExpect
      rw [hObs ((a, ds_cli), st_cli) ((a, σ_ad), σ_e2e) rfl hRel]
    rw [hEq]
    exact le_self_add
  | query_bind q oa ih =>
    by_cases hBad : cliClause2BadKemBool S P st_cli ds_cli = true
    · have hBadOne :
          𝒟[(((simulateQ impl_cli (liftM (OracleSpec.query q) >>= oa)).run ds_cli).run st_cli) >>=
              F_bad] {true} = 1 := by
        rw [evalDist_bind_true_eq_probExpect_hopB]
        exact probExpect_simulateQ_cliBadKem_eq_one_of_bad S ℓ P run W qep
          decT encT (fun _ _ _ _ _ => some b) (liftM (OracleSpec.query q) >>= oa) st_cli ds_cli hBad
      rw [hBadOne]
      exact (MeasureTheory.measure_le_one _ _).trans le_add_self
    · have hGood : cliClause2BadKemBool S P st_cli ds_cli = false := Bool.eq_false_iff.mpr hBad
      have hForget : Prod.fst <$> WriterT.run (((impl_cli_log q).run ds_cli).run st_cli) =
          ((impl_cli q).run ds_cli).run st_cli :=
        congrArg (fun m => (m.run ds_cli).run st_cli)
          (forgetCoinS2_cliDrvImplCoinLogged S ℓ P run W qep decT encT
            bhNoExtWithSpqr (fun _ _ _ _ _ => some b) q)
      have hRemPost : ∀ yw ∈ support (WriterT.run (((impl_ad_log q).run σ_ad).run σ_e2e)),
          CliE2ERemoteIdInv yw.1.2 :=
        cliComposedAdapterImplWithCoinLogged_preserves_remoteIdInv P
          (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) W.C W.Q.K qep decT encT q σ_ad σ_e2e hRem
      rw [writerT_run_simulateQ_query_bind_cont impl_cli_log q oa ds_cli st_cli G_cli
            (fun acc0 z w₁ w₂ => by dsimp only [G_cli]; simp only [List.append_assoc]) acc,
          writerT_run_simulateQ_query_bind_cont impl_ad_log q oa σ_ad σ_e2e G_ad
            (fun acc0 z w₁ w₂ => by dsimp only [G_ad]; simp only [List.append_assoc]) acc,
          simulateQ_query_bind_run₂_local impl_cli q oa ds_cli st_cli, bind_assoc]
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hb_start
      have hb_inst' : ∀ k < qStart,
          (¬ (bhIsInstQueryWithSpqr k q = true) ∨ 0 < qs_rem k) ∧
          ∀ u, OracleComp.IsQueryBoundP (oa u)
            (fun q' => bhIsInstQueryWithSpqr k q')
            (if bhIsInstQueryWithSpqr k q = true then
               qs_rem k - 1 else qs_rem k) := by
        intro k hk
        simpa only [OracleComp.isQueryBoundP_query_bind_iff] using hb_inst k hk
      rcases q with ((uq | kq) | ctlq) | ⟨i, sq⟩
      ·
        have hStep : cliAdapterCoinStepCoupled X W b n qs_rem
            (WriterT.run (((impl_cli_log (.inl (.inl (.inl uq)))).run ds_cli).run st_cli))
            (WriterT.run (((impl_ad_log (.inl (.inl (.inl uq)))).run σ_ad).run σ_e2e)) :=
          cliAdapterCoinStepCoupled_of_empty_log
            (cliUnifStepBridgeProp_holds S ℓ X W qep decT encT hRel uq)
            (by dsimp only [impl_cli_log]
                rw [cliDrvImplCoinLogged_nonSend_eq_liftCoinS2 S ℓ P run W qep decT encT
                  bhNoExtWithSpqr (fun _ _ _ _ _ => some b) _ rfl,
                  writerT_run_liftCoinS2]; rfl)
            (by dsimp only [impl_ad_log]
                rw [cliComposedAdapterImplWithCoinLogged_nonSend_eq_liftCoinS2 P
                  (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) W.C W.Q.K qep decT encT _ rfl,
                  writerT_run_liftCoinS2])
        refine evalDist_bind_coinCoupled_le hForget hStep hRemPost _ _ _
          (fun xw yw hr hw hRel' hRem' => ?_)
        rw [← hr, ← hw]
        refine ih xw.1.1.1 (acc ++ xw.2) hn ?_ ?_ hRel' hRem'
        · simpa using hb_start.2 xw.1.1.1
        · intro k hk
          have hcond : @bhIsInstQueryWithSpqr S ℓ (BitVec 512) k
              (.inl (.inl (.inl uq))) = false := rfl
          simpa only [hcond, Bool.false_eq_true, ↓reduceIte] using (hb_inst' k hk).2 xw.1.1.1
      ·
        have hStep : cliAdapterCoinStepCoupled X W b n qs_rem
            (WriterT.run (((impl_cli_log (.inl (.inl (.inr kq)))).run ds_cli).run st_cli))
            (WriterT.run (((impl_ad_log (.inl (.inl (.inr kq)))).run σ_ad).run σ_e2e)) :=
          cliAdapterCoinStepCoupled_of_empty_log
            (hKeyInd hRel hRem hGood kq)
            (by dsimp only [impl_cli_log]
                rw [cliDrvImplCoinLogged_nonSend_eq_liftCoinS2 S ℓ P run W qep decT encT
                  bhNoExtWithSpqr (fun _ _ _ _ _ => some b) _ rfl,
                  writerT_run_liftCoinS2]; rfl)
            (by dsimp only [impl_ad_log]
                rw [cliComposedAdapterImplWithCoinLogged_nonSend_eq_liftCoinS2 P
                  (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) W.C W.Q.K qep decT encT _ rfl,
                  writerT_run_liftCoinS2])
        refine evalDist_bind_coinCoupled_le hForget hStep hRemPost _ _ _
          (fun xw yw hr hw hRel' hRem' => ?_)
        rw [← hr, ← hw]
        refine ih xw.1.1.1 (acc ++ xw.2) hn ?_ ?_ hRel' hRem'
        · simpa using hb_start.2 xw.1.1.1
        · intro k hk
          have hcond : @bhIsInstQueryWithSpqr S ℓ (BitVec 512) k
              (.inl (.inl (.inr kq))) = false := rfl
          simpa only [hcond, Bool.false_eq_true, ↓reduceIte] using (hb_inst' k hk).2 xw.1.1.1
      ·
        cases ctlq with
        | startDR sid =>
          have hpos : 0 < qStart_rem := by
            rcases hb_start.1 with hnot | hpos
            · exfalso; exact hnot rfl
            · exact hpos
          have hRelSucc : CliAdapterDrvRel S ℓ X W b (n + 1) qs_rem st_cli ds_cli σ_ad σ_e2e :=
            hRel.mono_qStart (Nat.le_succ n)
          have hLenLt : ds_cli.bhInsts.length < n + 1 :=
            Nat.lt_succ_of_le hRel.insts_len_le
          have hStep : cliAdapterCoinStepCoupled X W b (n + 1) qs_rem
              (WriterT.run (((impl_cli_log (.inl (.inr (.startDR sid)))).run ds_cli).run st_cli))
              (WriterT.run (((impl_ad_log (.inl (.inr (.startDR sid)))).run σ_ad).run σ_e2e)) :=
            cliAdapterCoinStepCoupled_of_empty_log
              (hStart hRelSucc hRem hGood hLenLt sid)
              (by dsimp only [impl_cli_log]
                  rw [cliDrvImplCoinLogged_nonSend_eq_liftCoinS2 S ℓ P run W qep decT encT
                    bhNoExtWithSpqr (fun _ _ _ _ _ => some b) _ rfl,
                    writerT_run_liftCoinS2]; rfl)
              (by dsimp only [impl_ad_log]
                  rw [cliComposedAdapterImplWithCoinLogged_nonSend_eq_liftCoinS2 P
                    (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) W.C W.Q.K qep decT encT _ rfl,
                    writerT_run_liftCoinS2])
          refine evalDist_bind_coinCoupled_le hForget hStep hRemPost _ _ _
            (fun xw yw hr hw hRel' hRem' => ?_)
          rw [← hr, ← hw]
          refine ih xw.1.1.1 (acc ++ xw.2) (n := n + 1) (qStart_rem := qStart_rem - 1)
            (by omega) ?_ ?_ hRel' hRem'
          · simpa using hb_start.2 xw.1.1.1
          · intro k hk
            have hcond : @bhIsInstQueryWithSpqr S ℓ (BitVec 512) k
                (.inl (.inr (.startDR sid))) = false := rfl
            simpa only [hcond, Bool.false_eq_true, ↓reduceIte] using (hb_inst' k hk).2 xw.1.1.1
      ·
        have hq_pos : i < ds_cli.bhInsts.length → 0 < qs_rem i := by
          intro hi
          have hi_lt : i < qStart := by have := hRel.insts_len_le; omega
          rcases (hb_inst' i hi_lt).1 with hnot | hpos
          · exfalso; apply hnot; simp [bhIsInstQueryWithSpqr]
          · exact hpos
        have hStep : cliAdapterCoinStepCoupled X W b n (Function.update qs_rem i (qs_rem i - 1))
            (WriterT.run (((impl_cli_log (.inr ⟨i, sq⟩)).run ds_cli).run st_cli))
            (WriterT.run (((impl_ad_log (.inr ⟨i, sq⟩)).run σ_ad).run σ_e2e)) := by
          rcases sq with (((⟨p, m, r⟩ | ⟨p, m0, m1, r⟩) | ⟨p, c⟩) | ⟨p, c⟩) | p
          · exact cliDrvSMCoinLogged_adapter_coupling_tr qep decT encT
              bhNoExtWithSpqr hCli hℓ hRel
              (cliAdapterDrvRemoteIdInv_of_cliE2ERemoteIdInv hRem)
              i p m r hq_pos
          · exact cliDrvSMCoinLogged_adapter_coupling_ch qep decT encT
              bhNoExtWithSpqr hCli hℓ hRel
              (cliAdapterDrvRemoteIdInv_of_cliE2ERemoteIdInv hRem)
              i p m0 m1 r hq_pos
          · exact cliAdapterCoinStepCoupled_of_empty_log
              (hSm hRel hRem hGood i (.inl (.inl (.inr (p, c)))) hq_pos)
              (by dsimp only [impl_cli_log]
                  rw [cliDrvImplCoinLogged_nonSend_eq_liftCoinS2 S ℓ P run W qep decT encT
                    bhNoExtWithSpqr (fun _ _ _ _ _ => some b) _ rfl,
                    writerT_run_liftCoinS2]; rfl)
              (by dsimp only [impl_ad_log]
                  rw [cliComposedAdapterImplWithCoinLogged_nonSend_eq_liftCoinS2 P
                    (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) W.C W.Q.K qep decT encT _ rfl,
                    writerT_run_liftCoinS2])
          · exact cliAdapterCoinStepCoupled_of_empty_log
              (hSm hRel hRem hGood i (.inl (.inr (p, c))) hq_pos)
              (by dsimp only [impl_cli_log]
                  rw [cliDrvImplCoinLogged_nonSend_eq_liftCoinS2 S ℓ P run W qep decT encT
                    bhNoExtWithSpqr (fun _ _ _ _ _ => some b) _ rfl,
                    writerT_run_liftCoinS2]; rfl)
              (by dsimp only [impl_ad_log]
                  rw [cliComposedAdapterImplWithCoinLogged_nonSend_eq_liftCoinS2 P
                    (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) W.C W.Q.K qep decT encT _ rfl,
                    writerT_run_liftCoinS2])
          · exact cliAdapterCoinStepCoupled_of_empty_log
              (hSm hRel hRem hGood i (.inr p) hq_pos)
              (by dsimp only [impl_cli_log]
                  rw [cliDrvImplCoinLogged_nonSend_eq_liftCoinS2 S ℓ P run W qep decT encT
                    bhNoExtWithSpqr (fun _ _ _ _ _ => some b) _ rfl,
                    writerT_run_liftCoinS2]; rfl)
              (by dsimp only [impl_ad_log]
                  rw [cliComposedAdapterImplWithCoinLogged_nonSend_eq_liftCoinS2 P
                    (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) W.C W.Q.K qep decT encT _ rfl,
                    writerT_run_liftCoinS2])
        refine evalDist_bind_coinCoupled_le hForget hStep hRemPost _ _ _
          (fun xw yw hr hw hRel' hRem' => ?_)
        rw [← hr, ← hw]
        refine ih xw.1.1.1 (acc ++ xw.2) hn ?_ ?_ hRel' hRem'
        · simpa using hb_start.2 xw.1.1.1
        · intro k hk
          have h := (hb_inst' k hk).2 xw.1.1.1
          have hcond :
              (if @bhIsInstQueryWithSpqr S ℓ (BitVec 512) k
                    (.inr ⟨i, sq⟩) = true then
                 qs_rem k - 1
               else qs_rem k) =
              Function.update qs_rem i (qs_rem i - 1) k := by
            by_cases hki : k = i
            · subst hki; simp [bhIsInstQueryWithSpqr, Function.update]
            · have hik : (i == k) = false := beq_false_of_ne (Ne.symm hki)
              simp [bhIsInstQueryWithSpqr, Function.update, hki, hik]
          rwa [hcond] at h

private theorem cliPqExpProjCoinLogged_bind {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt γ : Type}
    (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S ℓ (BitVec 512))
    (p : Bool × List (BitVec 512) → ProbComp γ) :
    (cliPqExpProjCoinLogged S run X W ℓ qep decT encT A >>= p) =
    (($ᵗ Bool : ProbComp Bool) >>= fun b =>
      WriterT.run (((simulateQ (cliDrvImplCoinLogged S ℓ (modelPrims X W) run W qep decT encT
          bhNoExtWithSpqr (fun _ _ _ _ _ => some b)) A.run).run {}).run
        (SignalPqxdh.KeyIndState.empty S true)) >>= fun xw =>
        (if !allTestedSessionsFresh (modelPrims X W) xw.1.2 then
           ($ᵗ Bool : ProbComp Bool)
         else pure (xw.1.1.1 == b || driverSomeInstanceWon xw.1.1.2 b)) >>=
          fun out => p (out, xw.2)) := by
  have h_emp : (∅ : List (BitVec 512)) = [] := rfl
  unfold cliPqExpProjCoinLogged
  simp only [WriterT.run_bind, writerT_run_liftM_prob, map_eq_bind_pure_comp,
    Function.comp_def, bind_assoc, pure_bind, List.nil_append]
  congr 1; funext b; congr 1; funext ⟨⟨⟨b', ds⟩, st⟩, w⟩
  split_ifs <;>
    simp only [writerT_run_liftM_prob, WriterT.run_pure, h_emp, map_eq_bind_pure_comp,
      Function.comp_def, bind_assoc, pure_bind, List.append_nil]

private theorem cliE2EExpWithKiCoinLogged_L_bh_bind
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt γ : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S ℓ (BitVec 512))
    (p : Bool × List (BitVec 512) → ProbComp γ) :
    (cliE2EExpWithKiCoinLogged true S P ki C K ℓ qep decT encT
        ((L_bh (S := S) (ℓ := ℓ) (PQC := BitVec 512) decT encT).eval
          (fun _ => cliGameAdversaryReassoc A) ()) >>= p) =
    (($ᵗ Bool : ProbComp Bool) >>= fun b =>
      WriterT.run (((simulateQ (cliComposedAdapterImplWithCoinLogged P ki C K qep decT encT)
          A.run).run (cliAdapterInitState S)).run
        { b := b, st := SignalPqxdh.KeyIndState.empty S true }) >>= fun yw =>
        (if !allTestedSessionsFresh P yw.1.2.st then
           ($ᵗ Bool : ProbComp Bool)
         else pure (yw.1.1.1 == b || bhE2EDrvWon yw.1.2 b)) >>=
          fun out => p (out, yw.2)) := by
  have h_emp : (∅ : List (BitVec 512)) = [] := rfl
  unfold cliE2EExpWithKiCoinLogged
  simp only [WriterT.run_bind, writerT_run_liftM_prob, map_eq_bind_pure_comp,
    Function.comp_def, bind_assoc, pure_bind, List.nil_append]
  congr 1; funext b
  rw [simulateQ_cliE2EDrvImplWithCoinLogged_L_bh_run P ki C K qep decT encT A
    { b := b, st := SignalPqxdh.KeyIndState.empty S true }]
  simp only [map_eq_bind_pure_comp, Function.comp_def, WriterT.run_bind, WriterT.run_pure,
    h_emp, bind_assoc, pure_bind, List.append_nil]
  congr 1; funext ⟨⟨⟨b', σ_ad⟩, σ_e2e⟩, w⟩
  split_ifs <;>
    simp only [writerT_run_liftM_prob, WriterT.run_pure, h_emp, map_eq_bind_pure_comp,
      Function.comp_def, bind_assoc, pure_bind, List.append_nil]

theorem cliPqExpProjCoinLogged_good_val_le_e2eCoinLogged_of_step_bridges
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (hCli : CliSpecPqxdh run X W) (hℓ : ℓ < 10 ^ 6)
    (hKeyInd : CliKeyIndStepBridgeProp S ℓ X W qep decT encT)
    (hStart : CliStartStepBridgeProp S ℓ run X W qep decT encT)
    (hSm : CliSmStepBridgeProp S ℓ run X W qep decT encT)
    (b_bud : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (A : CliGameAdversary S ℓ (BitVec 512))
    (hA : CliGameAdversaryPerInstanceBounded A b_bud qStart qs)
    (val : Bool) :
    let P := modelPrims X W
    let B_Lbh := (L_bh (S := S) (ℓ := ℓ) (PQC := BitVec 512) decT encT).eval
      (fun _ => cliGameAdversaryReassoc A) ()
    let pGood : Bool × List (BitVec 512) → ProbComp Bool :=
      fun w => pure (if W.Q.K.KemFailBad (w.2.map coinBytes) then false else (w.1 == val))
    𝒟[cliPqExpProjCoinLogged S run X W ℓ qep decT encT A >>= pGood] {true} ≤
      𝒟[cliE2EExpWithKiCoinLogged true S P
          (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) W.C W.Q.K ℓ qep decT encT B_Lbh >>=
            pGood] {true} +
        𝒟[cliRunBadKemExp S P run W ℓ qep decT encT A] {true} := by
  intro P B_Lbh pGood
  have hb_start0 : OracleComp.IsQueryBoundP A.run (fun q => q matches .inl (.inr _)) qStart :=
    (isQueryBoundP_congr_pred_local (fun q => by rcases q with ((_ | _) | _) | _ <;> exact Iff.rfl)
      A.run).mp hA.2.1
  rw [cliPqExpProjCoinLogged_bind run X W qep decT encT A pGood,
      cliE2EExpWithKiCoinLogged_L_bh_bind P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P)
        W.C W.Q.K qep decT encT A pGood]
  unfold cliRunBadKemExp
  dsimp only [P]
  rw [evalDist_bind_true_eq_probExpect_hopB ($ᵗ Bool),
      evalDist_bind_true_eq_probExpect_hopB ($ᵗ Bool),
      evalDist_bind_true_eq_probExpect_hopB ($ᵗ Bool),
      ← probExpect_add_hopB]
  refine SignalPqxdh.Security.probExpect_mono_of_support ($ᵗ Bool) _ _ (fun b_chal _ => ?_)
  exact simulateQ_cliDrvImplCoinLogged_adapter_coupling_le run X W qep decT encT
    hCli hℓ hKeyInd hStart hSm b_chal val qStart
    (fun x => if !allTestedSessionsFresh (modelPrims X W) x.2 then
                ($ᵗ Bool : ProbComp Bool)
              else pure (x.1.1 == b_chal || driverSomeInstanceWon x.1.2 b_chal))
    (fun y => if !allTestedSessionsFresh (modelPrims X W) y.2.st then
                ($ᵗ Bool : ProbComp Bool)
              else pure (y.1.1 == b_chal || bhE2EDrvWon y.2 b_chal))
    (fun x y hr hRel => evalDist_cliPostObs_eq_of_rel hr hRel)
    A.run [] (n := 0) (qStart_rem := qStart) (qs_rem := qs)
    (Nat.zero_add qStart).le hb_start0 hA.2.2
    (cliAdapterDrvRel_init S ℓ X W b_chal 0 qs)
    (cliE2ERemoteIdInv_init S ℓ b_chal true)

private theorem prEvent_good_val_eq_evalDist_bind (K : MlKem) (val : Bool)
    (oa : ProbComp (Bool × List (BitVec 512))) :
    Pr{let w ← oa}[w.1 = val ∧ ¬ (K.KemFailBad (w.2.map coinBytes) = true)] =
      𝒟[oa >>= fun w => pure (if K.KemFailBad (w.2.map coinBytes) then false else (w.1 == val))]
        {true} := by
  let f : Bool × List (BitVec 512) → Bool :=
    fun w => if K.KemFailBad (w.2.map coinBytes) then false else (w.1 == val)
  have hcongr :
      Pr{let w ← oa}[w.1 = val ∧ ¬ (K.KemFailBad (w.2.map coinBytes) = true)] =
        Pr{let w ← oa}[f w = true] :=
    prEvent_congr oa _ _ fun w => by
      dsimp only [f]
      cases K.KemFailBad (w.2.map coinBytes) <;> simp [beq_iff_eq]
  rw [hcongr, ← prEvent_map oa f (fun b => b = true),
      prEvent_eq_evalDist_singleton (f <$> oa) true, map_eq_bind_pure_comp]
  rfl

theorem cliPqExpProjCoinLogged_good_val_le_e2eCoinLogged_of_step_bridges_pr
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (hCli : CliSpecPqxdh run X W) (hℓ : ℓ < 10 ^ 6)
    (hKeyInd : CliKeyIndStepBridgeProp S ℓ X W qep decT encT)
    (hStart : CliStartStepBridgeProp S ℓ run X W qep decT encT)
    (hSm : CliSmStepBridgeProp S ℓ run X W qep decT encT)
    (b_bud : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (A : CliGameAdversary S ℓ (BitVec 512))
    (hA : CliGameAdversaryPerInstanceBounded A b_bud qStart qs)
    (val : Bool) :
    let P := modelPrims X W
    let B_Lbh := (L_bh (S := S) (ℓ := ℓ) (PQC := BitVec 512) decT encT).eval
      (fun _ => cliGameAdversaryReassoc A) ()
    Pr{let w ← cliPqExpProjCoinLogged S run X W ℓ qep decT encT A}[
        w.1 = val ∧ ¬ (W.Q.K.KemFailBad (w.2.map coinBytes) = true)] ≤
      Pr{let w ← cliE2EExpWithKiCoinLogged true S P
          (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) W.C W.Q.K ℓ qep decT encT B_Lbh}[
        w.1 = val ∧ ¬ (W.Q.K.KemFailBad (w.2.map coinBytes) = true)] +
      𝒟[cliRunBadKemExp S P run W ℓ qep decT encT A] {true} := by
  intro P B_Lbh
  rw [prEvent_good_val_eq_evalDist_bind W.Q.K val
        (cliPqExpProjCoinLogged S run X W ℓ qep decT encT A),
      prEvent_good_val_eq_evalDist_bind W.Q.K val
        (cliE2EExpWithKiCoinLogged true S P
          (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) W.C W.Q.K ℓ qep decT encT B_Lbh)]
  exact cliPqExpProjCoinLogged_good_val_le_e2eCoinLogged_of_step_bridges
    run X W qep decT encT hCli hℓ hKeyInd hStart hSm b_bud qStart qs A hA val

end Computational.Proofs.LibsignalCli.CliKemFailCouplingHopBAux

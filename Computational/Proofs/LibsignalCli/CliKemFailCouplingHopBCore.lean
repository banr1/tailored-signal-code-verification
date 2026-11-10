/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Game.StatementPqOomGame
public import Computational.Specifications.Session.StatementSession
public import Computational.Specifications.Composition.StatementModel
public import Computational.Specifications.Assumptions.KeyInd1KeyReal
public import Computational.Proofs.LibsignalCli.StatementPqSecure
public import Computational.Proofs.LibsignalCli.CliKemFailCouplingDefs
public import Computational.Proofs.LibsignalCli.CliPqAdapterDefs
import Computational.Proofs.LibsignalCli.Oom.Faithful
public import Computational.Proofs.LibsignalCli.CliPqAdapterRemoteIdInv
public import Computational.Proofs.LibsignalCli.CliPqAdapterSmSendCorrA
public import Computational.Proofs.LibsignalCli.CliPqAdapterCoupling
public import Computational.Proofs.LibsignalCli.CliPqBadKemBound
public import Computational.Proofs.LibsignalCli.CliKemFailCouplingHopBCoreAux

/-!
# Coin-logged composed adapter and step-coupling combinators

Defines `cliAdapterCoinStepCoupled` and proves `tr`/`ch` unfoldings for
`cliComposedAdapterImplWithCoinLogged` alongside empty-log step-coupling combinators.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.LibsignalCli.CliKemFailCouplingHopBCore

open OracleComp OracleSpec
open CryptoGames (Party SMSchemeR)
open CryptoGames.CBC (Plain)
open CryptoGames.LibsignalSession (Crypto GhostState PublicKey)
open CryptoGames.Ratchet.LibsignalInst (configR1OnCurve)
open CryptoVerification.LibsignalSpqrV1 (MlKem coinBytes spqrV1SessionUniformCoins)
open CryptoVerification.SignalSession (CliRun CliSpecPqxdh)
open CryptoVerification.E2E (BHAdapterInstMeta BHDrvM BHDrvMode BHE2EDrvState BHE2ESmResp
  BHModelInst BhShallowRed BinState Bytes CliAdapterDrvRel CliAdapterDrvRemoteIdInv
  CliAdapterInstRel CliAdapterInstRemoteIdInv CliAdapterState CliE2ERemoteIdInv
  CliGameAdversary CliGameAdversaryPerInstanceBounded CliKeyIndStepBridgeProp
  CliSmStepBridgeProp CliStartStepBridgeProp L_bh ModelDriverInstance ModelDriverInstanceMeta
  ModelDriverState PEParams UnreachedPqxdhPrimitives allTestedSessionsFresh bhAlignTransForBob
  bhConfigSpkS bhDecodePreKeyMsgE bhDrvInstClean bhDrvInstClean_eq_bhE2EDrvInstClean_of_cliRel
  bhDrvInstClean_imp_ikACorrAtAccept_false bhDrvKeyInd bhDrvKiQueryOk
  bhE2EDrvInstClean bhE2EDrvWon
  bhE2EInstIkACorr bhE2EMirror bhE2EStepLocalSm bhExpectedPreKeyMsg bhFwdU bhGameSpec
  bhHdrOfPreKeyMsg bhInitRegId bhInstIkACorrupted bhIsBobAcceptSMResp bhIsBobRecvSMQuery
  bhIsInstQueryWithSpqr bhMetaAfterSM bhNoExtWithSpqr bhNoOpkRespPromoted bhPackSmResp
  bhPartneredInTransitA bhPartneredInnerBytes bhShallowAdapterGameStep bhShallowAdapterImpl
  bhShallowAliceUpdate bhShallowBobUpdate bhShallowParsePreKey bhShallowQueryTarget
  bhShallowSplitWhisper bhShallowStepMirrorGuard bhShallowUpdateInstMeta bhShallowWrapWhisper
  bhSmDefaultWithSpqr bhTargetGameSpec bhUnpackSmResp challRM
  cliAdapterDrvRel_decrement_i cliAdapterDrvRel_init cliAdapterDrvRel_mono_qs_rem
  cliAdapterDrvRel_update_inst_ad cliAdapterDrvRemoteIdInv_of_cliE2ERemoteIdInv
  cliAdapterDrvRemoteIdInv_update_inst cliAdapterInitState cliAdapterInstRel_with_insts
  cliAdapterKeyIndInv_with_insts cliAdapterStepCoupled cliAdapterStepImplWith
  cliClause2BadKemBool cliComposedAdapterImplWith cliComposedAdapterImplWith_ch_run
  cliComposedAdapterImplWith_preserves_remoteIdInv cliComposedAdapterImplWith_tr_run
  cliDrvCtl cliDrvImpl cliDrvSM cliDrvSM_adapter_coupling_ch cliDrvSM_adapter_coupling_tr
  cliDrvStart cliE2EDrvImplWith cliE2ERemoteIdInv_init cliGameAdversaryReassoc cliGameDrSpec
  cliGameSmSpec cliGameSpec cliPqScheme cliPqSigsOf cliRunBadKemExp cliRunStdSM cliStepLocalSM
  cliUnifStepBridgeProp_holds cliWrapAdapterSend compositionLocalStart
  configRefuseEarlyBobCorr deliverRM deq_support_snd_imp driverSomeInstanceWon
  evalDist_cliPostObs_eq_of_rel injectRM liftQueryImplStateT2 liftStateT modelPrims
  oracleImplRM paramsIdsWithSpqr probExpect_simulateQ_cliBadKem_eq_one_of_bad runCliDriver
  sessionSchemeFixedSpk shortCiphertext smSchemeCoinLogged
  transmitRM wirePrekey)
open Computational.Proofs.LibsignalCli.CliKemFailCouplingDefs (BHDrvMCoinLogged CoinLogM
  bhE2EStepLocalSmCoinLogged cliDrvImplCoinLogged cliDrvSMCoinLogged cliE2EDrvImplWithCoinLogged
  cliE2EExpWithKiCoinLogged cliPqExpProjCoinLogged cliRunStdSMCoinLogged cliStepLocalSMCoinLogged
  forgetCoinS1 forgetCoinS1_bind forgetCoinS1_cliE2EDrvImplWithCoinLogged forgetCoinS1_get
  forgetCoinS1_ite forgetCoinS1_lift forgetCoinS1_liftM_prob forgetCoinS1_liftStateT
  forgetCoinS1_map forgetCoinS1_oracleImplRM_smSchemeCoinLogged forgetCoinS1_pure
  forgetCoinS1_run forgetCoinS1_set forgetCoinS1_simulateQ forgetCoinW
  forgetCoinW_bhE2EStepLocalSmCoinLogged forgetCoinW_bind forgetCoinW_ite forgetCoinW_liftM
  forgetCoinW_map forgetCoinW_pure forgetCoinW_tell kemFailBad_map_coinBytes_mono)
open Computational.Proofs.LibsignalCli.Oom.Faithful (instLawfulMonadWriterTList)
open Computational.Proofs.LibsignalCli.CliKemFailCouplingHopBCoreAux (
  cliComposedAdapterImplWithCoinLogged liftM_prob_bind liftM_prob_pure writerT_run_liftM_prob)

@[simp] private theorem stateT_run_ite {σ : Type} {m : Type → Type} {α : Type}
    (c : Prop) [Decidable c] (t e : StateT σ m α) (s : σ) :
    (if c then t else e).run s = if c then t.run s else e.run s := by
  split_ifs <;> rfl

theorem cliComposedAdapterImplWithCoinLogged_tr_run
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (i : ℕ) (p : Party) (m : Plain ℓ) (r : Option (BitVec 512))
    (σ_ad : CliAdapterState S) (σ_e2e : BHE2EDrvState S ℓ) :
    (((cliComposedAdapterImplWithCoinLogged P ki C K qep decT encT
        (.inr ⟨i, .inl (.inl (.inl (.inl (p, m, r))))⟩)).run σ_ad).run σ_e2e) =
      match σ_ad.1 i with
      | none => pure ((none, σ_ad), σ_e2e)
      | some inst =>
        bhE2EStepLocalSmCoinLogged C K qep decT encT σ_e2e i (.inl (.inl (.inl (.inl (p, m, r))))) >>=
          fun (sr, σ_e2e') =>
            match sr.1 with
            | none => pure ((none, σ_ad), σ_e2e')
            | some ct => pure ((some (cliWrapAdapterSend inst (σ_ad.2.1 i) p ct), σ_ad), σ_e2e') := by
  have hSmBind : ∀ (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
      {α : Type} (k : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range sq →
        OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α),
      (simulateQ (cliE2EDrvImplWithCoinLogged P ki C K qep decT encT)
        ((liftM ((unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).query (.inr (.inr ⟨i, sq⟩))) :
          OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) _) >>= k)).run σ_e2e =
      (bhE2EStepLocalSmCoinLogged C K qep decT encT σ_e2e i sq >>= fun (sr, σ_e2e') =>
        (simulateQ (cliE2EDrvImplWithCoinLogged P ki C K qep decT encT)
          (k (bhUnpackSmResp sq sr))).run σ_e2e') := by
    intro sq α k
    simp only [simulateQ_bind, StateT.run_bind, simulateQ_query, OracleSpec.query_def]
    dsimp [OracleQuery.cont, OracleQuery.input, cliE2EDrvImplWithCoinLogged]
    simp only [id_map, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift,
      StateT.run_set, StateT.run_pure, bind_assoc]
  change (simulateQ (cliE2EDrvImplWithCoinLogged P ki C K qep decT encT)
    ((bhShallowAdapterImpl S ℓ (BitVec 512)
      (.inr (.inr ⟨i, .inl (.inl (.inl (.inl (p, m, r))))⟩))).run σ_ad)).run σ_e2e = _
  dsimp [bhShallowAdapterImpl, bhShallowAdapterGameStep, bhShallowQueryTarget,
    bhShallowWrapWhisper, cliWrapAdapterSend]
  rcases σ_ad.1 i with _ | inst
  · simp only [simulateQ_pure, StateT.run_pure]
  · dsimp only; rw [hSmBind]; congr 1
    funext x; rcases x with ⟨⟨_ | ct, _, _⟩, σ_e2e'⟩ <;>
      simp only [bhUnpackSmResp, simulateQ_pure, StateT.run_pure]

theorem cliComposedAdapterImplWithCoinLogged_ch_run
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (i : ℕ) (p : Party) (m0 m1 : Plain ℓ) (r : Option (BitVec 512))
    (σ_ad : CliAdapterState S) (σ_e2e : BHE2EDrvState S ℓ) :
    (((cliComposedAdapterImplWithCoinLogged P ki C K qep decT encT
        (.inr ⟨i, .inl (.inl (.inl (.inr (p, m0, m1, r))))⟩)).run σ_ad).run σ_e2e) =
      match σ_ad.1 i with
      | none => pure ((none, σ_ad), σ_e2e)
      | some inst =>
        bhE2EStepLocalSmCoinLogged C K qep decT encT σ_e2e i
          (.inl (.inl (.inl (.inr (p, m0, m1, r))))) >>=
          fun (sr, σ_e2e') =>
            match sr.1 with
            | none => pure ((none, σ_ad), σ_e2e')
            | some ct => pure ((some (cliWrapAdapterSend inst (σ_ad.2.1 i) p ct), σ_ad), σ_e2e') := by
  have hSmBind : ∀ (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
      {α : Type} (k : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range sq →
        OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α),
      (simulateQ (cliE2EDrvImplWithCoinLogged P ki C K qep decT encT)
        ((liftM ((unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).query (.inr (.inr ⟨i, sq⟩))) :
          OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) _) >>= k)).run σ_e2e =
      (bhE2EStepLocalSmCoinLogged C K qep decT encT σ_e2e i sq >>= fun (sr, σ_e2e') =>
        (simulateQ (cliE2EDrvImplWithCoinLogged P ki C K qep decT encT)
          (k (bhUnpackSmResp sq sr))).run σ_e2e') := by
    intro sq α k
    simp only [simulateQ_bind, StateT.run_bind, simulateQ_query, OracleSpec.query_def]
    dsimp [OracleQuery.cont, OracleQuery.input, cliE2EDrvImplWithCoinLogged]
    simp only [id_map, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift,
      StateT.run_set, StateT.run_pure, bind_assoc]
  change (simulateQ (cliE2EDrvImplWithCoinLogged P ki C K qep decT encT)
    ((bhShallowAdapterImpl S ℓ (BitVec 512)
      (.inr (.inr ⟨i, .inl (.inl (.inl (.inr (p, m0, m1, r))))⟩))).run σ_ad)).run σ_e2e = _
  dsimp [bhShallowAdapterImpl, bhShallowAdapterGameStep, bhShallowQueryTarget,
    bhShallowWrapWhisper, cliWrapAdapterSend]
  rcases σ_ad.1 i with _ | inst
  · simp only [simulateQ_pure, StateT.run_pure]
  · dsimp only; rw [hSmBind]; congr 1
    funext x; rcases x with ⟨⟨_ | ct, _, _⟩, σ_e2e'⟩ <;>
      simp only [bhUnpackSmResp, simulateQ_pure, StateT.run_pure]

/-- Single-step coin-logged coupling between a projected CLI driver step and a composed `L_bh`
adapter step. -/
def cliAdapterCoinStepCoupled {S : SignalPqxdh.Setup} {ℓ : ℕ} {α : Type}
    (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (b : Bool) (qStart' : ℕ) (qs_rem' : ℕ → ℕ)
    (c_cli : ProbComp (((α × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S) × List (BitVec 512)))
    (c_ad : ProbComp (((α × CliAdapterState S) × BHE2EDrvState S ℓ) × List (BitVec 512))) : Prop :=
  ∃ μ : ProbComp
      ((((α × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S) × List (BitVec 512)) ×
       (((α × CliAdapterState S) × BHE2EDrvState S ℓ) × List (BitVec 512))),
    CryptoGames.Lazy.DEq (Prod.fst <$> μ) c_cli ∧
    CryptoGames.Lazy.DEq (Prod.snd <$> μ) c_ad ∧
    ∀ xw yw, (xw, yw) ∈ support μ →
      xw.1.1.1 = yw.1.1.1 ∧
      xw.2 = yw.2 ∧
      CliAdapterDrvRel S ℓ X W b qStart' qs_rem' xw.1.2 xw.1.1.2 yw.1.1.2 yw.1.2

theorem cliAdapterCoinStepCoupled_ret {S : SignalPqxdh.Setup} {ℓ : ℕ} {α : Type}
    {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {b : Bool} {qStart' : ℕ} {qs_rem' : ℕ → ℕ}
    (r : α) (st_cli' : SignalPqxdh.KeyIndState S) (ds_cli' : ModelDriverState S ℓ)
    (σ_ad' : CliAdapterState S) (σ_e2e' : BHE2EDrvState S ℓ) (w : List (BitVec 512))
    (hRel' : CliAdapterDrvRel S ℓ X W b qStart' qs_rem' st_cli' ds_cli' σ_ad' σ_e2e') :
    cliAdapterCoinStepCoupled X W b qStart' qs_rem'
      (pure (((r, ds_cli'), st_cli'), w))
      (pure (((r, σ_ad'), σ_e2e'), w)) := by
  refine ⟨pure ((((r, ds_cli'), st_cli'), w), (((r, σ_ad'), σ_e2e'), w)), ?_, ?_, ?_⟩
  · intro f; simp
  · intro f; simp
  · intro xw yw hmem
    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl, hRel'⟩

theorem cliAdapterCoinStepCoupled_bind_pure {S : SignalPqxdh.Setup} {ℓ : ℕ} {α β : Type}
    {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {b : Bool} {qStart' : ℕ} {qs_rem' : ℕ → ℕ}
    (m : ProbComp β)
    (f_cli : β → ((α × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S) × List (BitVec 512))
    (f_ad : β → ((α × CliAdapterState S) × BHE2EDrvState S ℓ) × List (BitVec 512))
    (h : ∀ x ∈ support m,
      (f_cli x).1.1.1 = (f_ad x).1.1.1 ∧
      (f_cli x).2 = (f_ad x).2 ∧
      CliAdapterDrvRel S ℓ X W b qStart' qs_rem'
        (f_cli x).1.2 (f_cli x).1.1.2 (f_ad x).1.1.2 (f_ad x).1.2) :
    cliAdapterCoinStepCoupled X W b qStart' qs_rem'
      (m >>= fun x => pure (f_cli x))
      (m >>= fun x => pure (f_ad x)) := by
  refine ⟨m >>= fun x => pure (f_cli x, f_ad x), ?_, ?_, ?_⟩
  · intro g; simp [map_eq_bind_pure_comp, bind_assoc]
  · intro g; simp [map_eq_bind_pure_comp, bind_assoc]
  · intro xw yw hmem
    rw [mem_support_bind_iff] at hmem
    rcases hmem with ⟨x, hx, hpair⟩
    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hpair
    rcases hpair with ⟨rfl, rfl⟩
    exact h x hx

theorem cliAdapterCoinStepCoupled_of_empty_log {S : SignalPqxdh.Setup} {ℓ : ℕ} {α : Type}
    {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {b : Bool} {qStart' : ℕ} {qs_rem' : ℕ → ℕ}
    {c_cli : ProbComp ((α × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S)}
    {c_ad : ProbComp ((α × CliAdapterState S) × BHE2EDrvState S ℓ)}
    {c_cli_log : ProbComp (((α × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S) × List (BitVec 512))}
    {c_ad_log : ProbComp (((α × CliAdapterState S) × BHE2EDrvState S ℓ) × List (BitVec 512))}
    (hCoupled : cliAdapterStepCoupled X W b qStart' qs_rem' c_cli c_ad)
    (h_cli : c_cli_log = (fun x => (x, ([] : List (BitVec 512)))) <$> c_cli)
    (h_ad : c_ad_log = (fun y => (y, ([] : List (BitVec 512)))) <$> c_ad) :
    cliAdapterCoinStepCoupled X W b qStart' qs_rem' c_cli_log c_ad_log := by
  rcases hCoupled with ⟨μ, h1, h2, hsupp⟩
  refine ⟨(fun p => ((p.1, ([] : List (BitVec 512))), (p.2, ([] : List (BitVec 512))))) <$> μ, ?_, ?_, ?_⟩
  · subst h_cli
    intro f
    have hd := h1 (fun x => f (x, []))
    simpa only [Functor.map_map, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] using hd
  · subst h_ad
    intro f
    have hd := h2 (fun y => f (y, []))
    simpa only [Functor.map_map, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] using hd
  · intro xw yw hmem
    rw [support_map] at hmem
    rcases hmem with ⟨⟨x, y⟩, hxy, heq⟩
    simp only [Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl⟩
    exact ⟨(hsupp x y hxy).1, rfl, (hsupp x y hxy).2⟩

theorem cliAdapterCoinStepCoupled.mono_qs_rem {S : SignalPqxdh.Setup} {ℓ : ℕ} {α : Type}
    {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {b : Bool} {qStart' : ℕ} {qs_rem' qs_rem'' : ℕ → ℕ}
    {c_cli : ProbComp (((α × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S) × List (BitVec 512))}
    {c_ad : ProbComp (((α × CliAdapterState S) × BHE2EDrvState S ℓ) × List (BitVec 512))}
    (hC : cliAdapterCoinStepCoupled X W b qStart' qs_rem' c_cli c_ad)
    (hle : ∀ k, qs_rem'' k ≤ qs_rem' k) :
    cliAdapterCoinStepCoupled X W b qStart' qs_rem'' c_cli c_ad := by
  rcases hC with ⟨μ, h1, h2, hsupp⟩
  exact ⟨μ, h1, h2, fun xw yw hmem =>
    ⟨(hsupp xw yw hmem).1, (hsupp xw yw hmem).2.1,
      cliAdapterDrvRel_mono_qs_rem (hsupp xw yw hmem).2.2 hle⟩⟩

theorem cliAdapterCoinStepCoupled.mono_qStart {S : SignalPqxdh.Setup} {ℓ : ℕ} {α : Type}
    {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {b : Bool} {qStart₁ qStart₂ : ℕ} {qs_rem' : ℕ → ℕ}
    {c_cli : ProbComp (((α × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S) × List (BitVec 512))}
    {c_ad : ProbComp (((α × CliAdapterState S) × BHE2EDrvState S ℓ) × List (BitVec 512))}
    (hC : cliAdapterCoinStepCoupled X W b qStart₁ qs_rem' c_cli c_ad)
    (hle : qStart₁ ≤ qStart₂) :
    cliAdapterCoinStepCoupled X W b qStart₂ qs_rem' c_cli c_ad := by
  rcases hC with ⟨μ, h1, h2, hsupp⟩
  exact ⟨μ, h1, h2, fun xw yw hmem =>
    ⟨(hsupp xw yw hmem).1, (hsupp xw yw hmem).2.1,
      { (hsupp xw yw hmem).2.2 with
        insts_len_le := (hsupp xw yw hmem).2.2.insts_len_le.trans hle }⟩⟩

theorem deq_pure_pure_of_stepCoupled {S : SignalPqxdh.Setup} {ℓ : ℕ} {α : Type}
    {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {b : Bool} {qStart' : ℕ} {qs_rem' : ℕ → ℕ}
    {x₀ : (α × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S}
    {y₀ : (α × CliAdapterState S) × BHE2EDrvState S ℓ}
    (hC : cliAdapterStepCoupled X W b qStart' qs_rem' (pure x₀) (pure y₀)) :
    x₀.1.1 = y₀.1.1 ∧
    CliAdapterDrvRel S ℓ X W b qStart' qs_rem' x₀.2 x₀.1.2 y₀.1.2 y₀.2 := by
  rcases hC with ⟨μ, h1, h2, hsupp⟩
  obtain ⟨⟨x, y⟩, hxy⟩ := μ.support_nonempty
  have hy : y = y₀ := deq_support_snd_imp h2 (fun z hz => by simpa using hz) x y hxy
  have h1_swap : CryptoGames.Lazy.DEq (Prod.snd <$> (Prod.swap <$> μ)) (pure x₀) := by
    simpa only [Functor.map_map, Prod.snd_swap] using h1
  have hxy_swap : (y, x) ∈ support (Prod.swap <$> μ) := by
    rw [support_map]; exact ⟨(x, y), hxy, rfl⟩
  have hx : x = x₀ := deq_support_snd_imp h1_swap (fun z hz => by simpa using hz) y x hxy_swap
  subst hx hy
  exact hsupp x y hxy

theorem evalDist_bind_true_eq_probExpect_hopB {α : Type}
    (mx : ProbComp α) (k : α → ProbComp Bool) :
    𝒟[mx >>= k] {true} = SignalPqxdh.Security.probExpect mx (fun a => 𝒟[k a] {true}) := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  rw [evalDist_bind_of_discrete,
      MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
        Measurable.of_discrete.aemeasurable]
  rfl

theorem probExpect_add_hopB {α : Type} (mx : ProbComp α) (f g : α → ENNReal) :
    SignalPqxdh.Security.probExpect mx (fun x => f x + g x) =
      SignalPqxdh.Security.probExpect mx f + SignalPqxdh.Security.probExpect mx g := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  unfold SignalPqxdh.Security.probExpect
  exact MeasureTheory.lintegral_add_left Measurable.of_discrete g

theorem evalDist_bind_coinCoupled_le {S : SignalPqxdh.Setup} {ℓ : ℕ} {α : Type}
    {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {b : Bool} {qStart' : ℕ} {qs_rem' : ℕ → ℕ}
    {c_cli_log : ProbComp (((α × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S) × List (BitVec 512))}
    {c_ad_log : ProbComp (((α × CliAdapterState S) × BHE2EDrvState S ℓ) × List (BitVec 512))}
    {c_cli : ProbComp ((α × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S)}
    (hForget : Prod.fst <$> c_cli_log = c_cli)
    (hC : cliAdapterCoinStepCoupled X W b qStart' qs_rem' c_cli_log c_ad_log)
    (hRemPost : ∀ yw ∈ support c_ad_log, CliE2ERemoteIdInv yw.1.2)
    (F_cli : (((α × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S) × List (BitVec 512)) → ProbComp Bool)
    (F_ad : (((α × CliAdapterState S) × BHE2EDrvState S ℓ) × List (BitVec 512)) → ProbComp Bool)
    (F_bad : ((α × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S) → ProbComp Bool)
    (hIH : ∀ xw yw, xw.1.1.1 = yw.1.1.1 → xw.2 = yw.2 →
      CliAdapterDrvRel S ℓ X W b qStart' qs_rem' xw.1.2 xw.1.1.2 yw.1.1.2 yw.1.2 →
      CliE2ERemoteIdInv yw.1.2 →
      𝒟[F_cli xw] {true} ≤ 𝒟[F_ad yw] {true} + 𝒟[F_bad xw.1] {true}) :
    𝒟[c_cli_log >>= F_cli] {true} ≤
      𝒟[c_ad_log >>= F_ad] {true} + 𝒟[c_cli >>= F_bad] {true} := by
  rcases hC with ⟨μ, h1, h2, hsupp⟩
  have hL : ∀ G : (((α × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S) × List (BitVec 512)) → ProbComp Bool,
      𝒟[c_cli_log >>= G] {true} =
        SignalPqxdh.Security.probExpect μ (fun p => 𝒟[G p.1] {true}) := by
    intro G
    have hd := congrArg (fun ν => ν {true}) (h1 G).symm
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] at hd
    exact hd.trans (evalDist_bind_true_eq_probExpect_hopB μ (fun p => G p.1))
  have hR : 𝒟[c_ad_log >>= F_ad] {true} =
      SignalPqxdh.Security.probExpect μ (fun p => 𝒟[F_ad p.2] {true}) := by
    have hd := congrArg (fun ν => ν {true}) (h2 F_ad).symm
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] at hd
    exact hd.trans (evalDist_bind_true_eq_probExpect_hopB μ (fun p => F_ad p.2))
  have hBad : 𝒟[c_cli >>= F_bad] {true} =
      SignalPqxdh.Security.probExpect μ (fun p => 𝒟[F_bad p.1.1] {true}) := by
    subst hForget
    simpa only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] using
      hL (fun xw => F_bad xw.1)
  have hRemμ : ∀ xw yw, (xw, yw) ∈ support μ → CliE2ERemoteIdInv yw.1.2 :=
    deq_support_snd_imp h2 hRemPost
  rw [hL F_cli, hR, hBad, ← probExpect_add_hopB]
  exact SignalPqxdh.Security.probExpect_mono_of_support μ _ _ (fun ⟨xw, yw⟩ hmem =>
    hIH xw yw (hsupp xw yw hmem).1 (hsupp xw yw hmem).2.1 (hsupp xw yw hmem).2.2
      (hRemμ xw yw hmem))

theorem cliAdapterCoinStepCoupled_of_some_cns {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {b : Bool} {qStart' : ℕ} {qs_rem' : ℕ → ℕ} (cns : BitVec 512)
    {c_cli : ProbComp ((Option Bytes × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S)}
    {c_ad : ProbComp ((Option Bytes × CliAdapterState S) × BHE2EDrvState S ℓ)}
    {c_cli_log : ProbComp (((Option Bytes × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S) × List (BitVec 512))}
    {c_ad_log : ProbComp (((Option Bytes × CliAdapterState S) × BHE2EDrvState S ℓ) × List (BitVec 512))}
    (hCoupled : cliAdapterStepCoupled X W b qStart' qs_rem' c_cli c_ad)
    (h_cli : c_cli_log = (fun x => (x, if x.1.1.isSome then [cns] else [])) <$> c_cli)
    (h_ad : c_ad_log = (fun y => (y, if y.1.1.isSome then [cns] else [])) <$> c_ad) :
    cliAdapterCoinStepCoupled X W b qStart' qs_rem' c_cli_log c_ad_log := by
  rcases hCoupled with ⟨μ, h1, h2, hsupp⟩
  refine ⟨(fun p =>
      ((p.1, if p.1.1.1.isSome then [cns] else []),
       (p.2, if p.2.1.1.isSome then [cns] else []))) <$> μ, ?_, ?_, ?_⟩
  · subst h_cli; intro f
    have hd := h1 (fun x => f (x, if x.1.1.isSome then [cns] else []))
    simpa only [Functor.map_map, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] using hd
  · subst h_ad; intro f
    have hd := h2 (fun y => f (y, if y.1.1.isSome then [cns] else []))
    simpa only [Functor.map_map, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] using hd
  · intro xw yw hmem
    rw [support_map] at hmem
    rcases hmem with ⟨⟨x, y⟩, hxy, heq⟩
    simp only [Prod.mk.injEq] at heq; rcases heq with ⟨rfl, rfl⟩
    exact ⟨(hsupp x y hxy).1, by rw [(hsupp x y hxy).1], (hsupp x y hxy).2⟩

theorem epMgmt_true_of_epMgmt_false {St Msg C : Type}
    {gs s : CryptoGames.SM.GameState St Msg C} {Δ qep : ℕ} {p : Party}
    (hep : gs.epMgmt Δ qep p false = some s) :
    s.epMgmt Δ qep p true = some s := by
  unfold CryptoGames.SM.GameState.epMgmt at hep ⊢
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hep
  split_ifs at hep with h1 h2 h3
  · cases Option.some.inj hep.symm
    have hsends2 : p.sendsIn (gs.epoch p + 1 + 1) = false := by
      cases p <;> simp [Party.sendsIn] at h1 ⊢ <;> omega
    simp [Function.update_self, hsends2, h2]
  · cases Option.some.inj hep.symm
    simp [h1, h3]

theorem epMgmt_false_rel {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {im : ModelDriverInstanceMeta S}
    {gs_cli : CryptoGames.SM.GameState BinState (Plain ℓ) Bytes}
    {gs_m : CryptoGames.SM.GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (qep : ℕ) (p : Party)
    (hb_eq : gs_cli.b = gs_m.b) (h_win : gs_cli.win = gs_m.win)
    (h_ep : gs_cli.epoch = gs_m.epoch) (h_idx : gs_cli.idx = gs_m.idx)
    (h_max : gs_cli.maxAcc = gs_m.maxAcc) (h_ch : gs_cli.chall = gs_m.chall)
    (h_comp : gs_cli.comp = gs_m.comp) (h_tL : gs_cli.tL = gs_m.tL)
    (h_lk : gs_cli.leaks = gs_m.leaks) (h_cr : gs_cli.corrs = gs_m.corrs)
    (h_epA0 : !im.bobAccepted → gs_m.epoch .A ≤ 1)
    (h_epB0 : !im.bobAccepted → gs_m.epoch .B = 0)
    (h_cpA0 : !im.bobAccepted → ∀ pos ∈ gs_m.comp, pos.sender = .A)
    (h_tL0 : !im.bobAccepted → gs_m.tL = none)
    (hbob_of_B : p = .B → im.bobAccepted = true) :
    (gs_cli.epMgmt (2 + 1) qep p false = none ∧ gs_m.epMgmt (2 + 1) qep p false = none) ∨
    (∃ s_cli s_m,
      gs_cli.epMgmt (2 + 1) qep p false = some s_cli ∧
      gs_m.epMgmt (2 + 1) qep p false = some s_m ∧
      s_cli.st = gs_cli.st ∧ s_m.st = gs_m.st ∧
      s_cli.trans = gs_cli.trans ∧ s_m.trans = gs_m.trans ∧
      s_cli.b = s_m.b ∧ s_cli.win = s_m.win ∧ s_cli.epoch = s_m.epoch ∧
      s_cli.idx = s_m.idx ∧ s_cli.maxAcc = s_m.maxAcc ∧ s_cli.chall = s_m.chall ∧
      s_cli.comp = s_m.comp ∧ s_cli.tL = s_m.tL ∧ s_cli.leaks = s_m.leaks ∧
      s_cli.corrs = s_m.corrs ∧
      (!im.bobAccepted → s_m.epoch .A ≤ 1) ∧ (!im.bobAccepted → s_m.epoch .B = 0) ∧
      (!im.bobAccepted → ∀ pos ∈ s_m.comp, pos.sender = .A) ∧ (!im.bobAccepted → s_m.tL = none)) := by
  unfold CryptoGames.SM.GameState.epMgmt
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rw [h_ep]
  split_ifs with h1 h2 h3
  · exact Or.inl ⟨rfl, rfl⟩
  · refine Or.inr ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, hb_eq, h_win,
      rfl, by dsimp only; rw [h_idx],
      h_max, h_ch, h_comp, h_tL, h_lk, h_cr, ?_, ?_, h_cpA0, h_tL0⟩
    · intro hnot; cases p
      · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (h_epA0 hnot) with h0 | h1_eq
        · simp [Function.update, h0]
        · rw [h1_eq] at h1; cases h1
      · rw [hbob_of_B rfl] at hnot; cases hnot
    · intro hnot; cases p
      · simp [Function.update, h_epB0 hnot]
      · rw [hbob_of_B rfl] at hnot; cases hnot
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨gs_cli, gs_m, rfl, rfl, rfl, rfl, rfl, rfl, hb_eq, h_win, h_ep, h_idx,
      h_max, h_ch, h_comp, h_tL, h_lk, h_cr, h_epA0, h_epB0, h_cpA0, h_tL0⟩

theorem send_record_rel_of_tr_some {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (hCli : CliSpecPqxdh run X W) (hℓ : ℓ < 10 ^ 6)
    {b : Bool} {qStart : ℕ} {qs_rem : ℕ → ℕ}
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {σ_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ}
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e)
    (hRem : CliAdapterDrvRemoteIdInv S ℓ ds_cli σ_e2e)
    {i : ℕ} (hi_cli : i < ds_cli.bhInsts.length) (hq_pos : 0 < qs_rem i)
    (hClean : bhDrvInstClean ds_cli i = true)
    {inst : BHAdapterInstMeta S} (hinst_ad : σ_ad.1 i = some inst)
    {p : Party}
    {gs_cli s_cli : CryptoGames.SM.GameState BinState (Plain ℓ) Bytes}
    {gs_m s_m : CryptoGames.SM.GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (hgs_cli : ds_cli.bhInsts[i].gs = some gs_cli)
    (hgs_m : (σ_e2e.insts[i]'(hRel.insts_len_eq ▸ hi_cli)).gs = some gs_m)
    (h_sendOK_m : (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).sendOK gs_m p = true)
    (h_win_m : gs_m.win = false)
    (hep_cli : gs_cli.epMgmt (2 + 1) qep p false = some s_cli)
    (hep_m : gs_m.epMgmt (2 + 1) qep p false = some s_m)
    (m_send : Plain ℓ) (cns : BitVec 512) (isChall : Bool) :
    let hi_e2e : i < σ_e2e.insts.length := hRel.insts_len_eq ▸ hi_cli
    let hi_mb : i < ds_cli.instMeta.length := hRel.meta_cli_len_eq.symm ▸ hi_cli
    let hi_me : i < σ_e2e.instMeta.length := hRel.meta_e2e_len_eq.symm ▸ hi_e2e
    let bi := ds_cli.bhInsts[i]
    let d := σ_e2e.insts[i]
    let im := ds_cli.instMeta[i]
    let im_e2e := σ_e2e.instMeta[i]
    let sch_cli := cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0
    let P_v1 := paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) d.idA d.idB
    let sch_m := sessionSchemeFixedSpk P_v1 ℓ d.spkCoins
    let out_cli := sch_cli.sendPart.send (s_cli.st p) m_send cns
    let out_m := sch_m.sendPart.send (s_m.st p) m_send cns
    let gs_cli' := s_cli.record (2 + 1) p out_cli.1 ⟨⟨p, s_cli.epoch p, s_cli.idx p + 1⟩, m_send, out_cli.2⟩ isChall
    let gs_m' := s_m.record (2 + 1) p out_m.1 ⟨⟨p, s_m.epoch p, s_m.idx p + 1⟩, m_send, out_m.2⟩ isChall
    out_cli.2 = cliWrapAdapterSend inst (σ_ad.2.1 i) p out_m.2 ∧
    CliAdapterDrvRel S ℓ X W b qStart (Function.update qs_rem i (qs_rem i - 1)) st_cli
      { ds_cli with bhInsts := ds_cli.bhInsts.set i { bi with gs := some gs_cli' },
                    instMeta := ds_cli.instMeta.set i im }
      σ_ad
      { σ_e2e with insts := σ_e2e.insts.set i { d with gs := some gs_m' },
                   instMeta := σ_e2e.instMeta.set i im_e2e } := by
  intro hi_e2e hi_mb hi_me bi d im im_e2e sch_cli P_v1 sch_m out_cli out_m gs_cli' gs_m'
  have hCorr : im.ikACorrAtAccept = false :=
    bhDrvInstClean_imp_ikACorrAtAccept_false hClean hi_cli hi_mb
  obtain ⟨inst₀, hinst₀, hInstRel₀⟩ := hRel.insts_rel i hi_cli hi_e2e hi_mb hi_me
  have hinst_eq : inst₀ = inst := Option.some.inj (hinst₀.symm.trans hinst_ad)
  subst inst₀
  have hgs := hInstRel₀.gs_rel
  change match bi.gs, d.gs with | _, _ => _ at hgs
  rw [hgs_cli, hgs_m] at hgs; rcases hgs with ⟨hb_eq, hrest⟩
  simp only [im, hCorr, Bool.false_eq_true, ↓reduceIte] at hrest
  rcases hrest with
    ⟨h_acc, h_win, h_ep, h_idx, h_max, h_ch, h_comp, h_tL, h_lk, h_cr,
     h_tr, h_ppkA, h_ppkB, h_idA, h_ack0, h_epA0, h_epB0, h_trA0, h_cpA0, h_tL0,
     h_epB1, h_stA, h_stB0, h_stB1, h_pA, h_pB, h_actA, h_actB⟩
  have hbob_of_B : p = .B → im.bobAccepted = true := by
    intro hpB; subst hpB
    by_cases hbob : im.bobAccepted = true
    · exact hbob
    · simp only [Bool.not_eq_true] at hbob
      have hepB0 : gs_m.epoch .B = 0 := h_epB0 (by dsimp only [im] at hbob; simp [hbob])
      dsimp [configRefuseEarlyBobCorr, configR1OnCurve, CryptoGames.SM.configR1,
        CryptoGames.SM.noBobSendInEpoch0] at h_sendOK_m
      simp [hepB0] at h_sendOK_m
  rcases epMgmt_false_rel qep p hb_eq h_win h_ep h_idx h_max h_ch h_comp h_tL h_lk h_cr
      h_epA0 h_epB0 h_cpA0 h_tL0 hbob_of_B with
    ⟨hnone, _⟩ |
    ⟨s_cli₁, s_m₁, hep_cli₁, hep_m₁, hs_st_cli, hs_st_m, hs_tr_cli, hs_tr_m,
     hs_b, hs_win, hs_ep, hs_idx, hs_max, hs_ch, hs_comp, hs_tL, hs_lk, hs_cr,
     hs_epA0, hs_epB0, hs_cpA0, hs_tL0⟩
  · rw [hep_cli] at hnone; cases hnone
  · cases Option.some.inj (hep_cli.symm.trans hep_cli₁)
    cases Option.some.inj (hep_m.symm.trans hep_m₁)
    let bi_s : ModelDriverInstance S ℓ := { bi with gs := some s_cli }
    let d_s : BHModelInst S ℓ := { d with gs := some s_m }
    let ds_s : ModelDriverState S ℓ :=
      { ds_cli with bhInsts := ds_cli.bhInsts.set i bi_s, instMeta := ds_cli.instMeta.set i im }
    let σ_s : BHE2EDrvState S ℓ :=
      { σ_e2e with insts := σ_e2e.insts.set i d_s, instMeta := σ_e2e.instMeta.set i im_e2e }
    have hInstRel_s : CliAdapterInstRel X W (qs_rem i) st_cli ds_cli bi_s d_s im im_e2e inst (σ_ad.2.1 i) := by
      refine
        { im_eq := hInstRel₀.im_eq
          sid_eq := hInstRel₀.sid_eq
          hdr_eq := hInstRel₀.hdr_eq
          idB_eq := hInstRel₀.idB_eq
          respSlot_eq := hInstRel₀.respSlot_eq
          respMeta_eq := hInstRel₀.respMeta_eq
          regIdA_eq := hInstRel₀.regIdA_eq
          regIdB_eq := hInstRel₀.regIdB_eq
          aliceAcked_false := hInstRel₀.aliceAcked_false
          idA_pub_eq := hInstRel₀.idA_pub_eq
          idB_pub_eq := hInstRel₀.idB_pub_eq
          extrasB_eq := hInstRel₀.extrasB_eq
          stB0_empty := hInstRel₀.stB0_empty
          resp_bundle_rel := hInstRel₀.resp_bundle_rel
          handshake_rel := ?_
          gs_rel := ?_ }
      · obtain ⟨bundleE, dk, ac, u_init, bnd, t_init, ss, h1, h2, h3, h4⟩ := hInstRel₀.handshake_rel
        refine ⟨bundleE, dk, ac, u_init, bnd, t_init, ss, h1, h2, h3,
          fun gs_c₁ gs_m₁ hc₁ hm₁ hcorr₁ hacc₁ => ?_⟩
        simp only [bi_s, d_s, Option.some.injEq] at hc₁ hm₁; subst hc₁ hm₁
        rw [hs_st_m]; exact h4 gs_cli gs_m hgs_cli hgs_m hcorr₁ hacc₁
      · dsimp only [bi_s, d_s]; refine ⟨hs_b, ?_⟩
        simp only [im, hCorr, Bool.false_eq_true, ↓reduceIte]
        rw [hs_st_cli, hs_st_m, hs_tr_cli, hs_tr_m]
        exact ⟨h_acc, hs_win, hs_ep, hs_idx, hs_max, hs_ch, hs_comp, hs_tL, hs_lk, hs_cr, h_tr,
          h_ppkA, h_ppkB, h_idA, h_ack0, hs_epA0, hs_epB0, h_trA0, hs_cpA0, hs_tL0,
          h_epB1, h_stA, h_stB0, h_stB1, h_pA, h_pB, h_actA, h_actB⟩
    have hRel_s : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_s σ_ad σ_s := by
      refine ⟨hRel.b_eq, hRel.st_rel, cliAdapterKeyIndInv_with_insts hRel.ki_inv _ _,
        hRel.base_e2e_eq, hRel.base_ad_eq, hRel.corrPrins_eq, hRel.revealedSpks_eq,
        by simp only [ds_s, List.length_set]; exact hRel.insts_len_le,
        by simp only [ds_s, σ_s, List.length_set]; exact hRel.insts_len_eq,
        by simp only [ds_s, List.length_set]; exact hRel.meta_cli_len_eq,
        by simp only [σ_s, List.length_set]; exact hRel.meta_e2e_len_eq,
        fun k hk => by simp only [σ_s, List.length_set] at hk; exact hRel.ad_none_of_ge k hk,
        fun k h_c h_e h_m1 h_m2 => ?_⟩
      simp only [ds_s, σ_s, List.length_set] at h_c h_e h_m1 h_m2
      by_cases hki : k = i
      · subst hki; refine ⟨inst, hinst_ad, ?_⟩
        simp only [ds_s, σ_s, List.getElem_set_self]
        exact cliAdapterInstRel_with_insts hInstRel_s _ _
      · obtain ⟨inst_k, had_k, hInst_k⟩ := hRel.insts_rel k h_c h_e h_m1 h_m2
        refine ⟨inst_k, had_k, ?_⟩
        simp only [ds_s, σ_s, List.getElem_set_ne (Ne.symm hki)]
        exact cliAdapterInstRel_with_insts hInst_k _ _
    have hRem_s : CliAdapterDrvRemoteIdInv S ℓ ds_s σ_s := by
      refine cliAdapterDrvRemoteIdInv_update_inst hRem i bi_s d_s im im_e2e ?_
      intro gs₁ hgs₁ hnc
      simp only [d_s, Option.some.injEq] at hgs₁; subst hgs₁
      rw [hs_st_m]; exact hRem i hi_e2e hi_mb gs_m hgs_m hnc
    have hClean_s : bhDrvInstClean ds_s i = true := by
      unfold bhDrvInstClean at hClean ⊢
      have hbi_opt : ds_cli.bhInsts[i]? = some bi := List.getElem?_eq_getElem hi_cli
      have him_opt : ds_cli.instMeta[i]? = some im := List.getElem?_eq_getElem hi_mb
      have hbis_opt : ds_s.bhInsts[i]? = some bi_s := by simp [ds_s, hi_cli]
      have hims_opt : ds_s.instMeta[i]? = some im := by simp [ds_s, hi_mb]
      rw [hbi_opt, him_opt] at hClean
      rw [hbis_opt, hims_opt]
      exact hClean
    have hClean_e2e_s : bhE2EDrvInstClean σ_s i = true :=
      (bhDrvInstClean_eq_bhE2EDrvInstClean_of_cliRel hRel_s i).symm.trans hClean_s
    have h_sendOK_sm :
        (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).sendOK s_m p = true := by
      dsimp [configRefuseEarlyBobCorr, configR1OnCurve, CryptoGames.SM.configR1,
        CryptoGames.SM.noBobSendInEpoch0] at h_sendOK_m ⊢
      cases p
      · rfl
      · unfold CryptoGames.SM.GameState.epMgmt at hep_m
        simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hep_m
        split_ifs at hep_m with h1 h2 h3
        · cases Option.some.inj hep_m.symm; simp [Function.update_self]
        · cases Option.some.inj hep_m.symm; exact h_sendOK_m
    have h_sendOK_scli : (bhConfigSpkS (Msg := Plain ℓ) decT encT).sendOK s_cli p = true := by
      dsimp [bhConfigSpkS, configRefuseEarlyBobCorr, configR1OnCurve,
        CryptoGames.SM.configR1, CryptoGames.SM.noBobSendInEpoch0] at h_sendOK_sm ⊢
      rwa [hs_ep]
    have hs_win_m : s_m.win = false := by
      unfold CryptoGames.SM.GameState.epMgmt at hep_m
      simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hep_m
      split_ifs at hep_m with h1 h2 h3
      · cases Option.some.inj hep_m.symm; exact h_win_m
      · cases Option.some.inj hep_m.symm; exact h_win_m
    have hs_win_cli : s_cli.win = false := hs_win.trans hs_win_m
    have hep_s_cli : s_cli.epMgmt 3 qep p true = some s_cli := epMgmt_true_of_epMgmt_false hep_cli
    have hep_s_m : s_m.epMgmt 3 qep p true = some s_m := epMgmt_true_of_epMgmt_false hep_m
    let gs_cli_f := s_cli.record (2 + 1) p out_cli.1 ⟨⟨p, s_cli.epoch p, s_cli.idx p + 1⟩, m_send, out_cli.2⟩ false
    let gs_m_f := s_m.record (2 + 1) p out_m.1 ⟨⟨p, s_m.epoch p, s_m.idx p + 1⟩, m_send, out_m.2⟩ false
    let ds_f : ModelDriverState S ℓ :=
      { ds_cli with bhInsts := ds_cli.bhInsts.set i { bi with gs := some gs_cli_f },
                    instMeta := ds_cli.instMeta.set i im }
    let σ_f : BHE2EDrvState S ℓ :=
      { σ_e2e with insts := σ_e2e.insts.set i { d with gs := some gs_m_f },
                   instMeta := σ_e2e.instMeta.set i im_e2e }
    have hC_tr := cliDrvSM_adapter_coupling_tr run X W qep decT encT bhNoExtWithSpqr
      (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S (modelPrims X W)) hCli hℓ hRel_s hRem_s
      i p m_send (some cns) hq_pos
    have h_cli_eq :
        (((cliDrvSM S ℓ run W qep decT encT bhNoExtWithSpqr
            ⟨i, .inl (.inl (.inl (.inl (p, m_send, some cns))))⟩).run ds_s).run st_cli) =
          pure ((some out_cli.2, ds_f), st_cli) := by
      have hbis_opt : ds_s.bhInsts[i]? = some bi_s := by simp [ds_s, hi_cli]
      have hims_opt : ds_s.instMeta[i]? = some im := by simp [ds_s, hi_mb]
      have hsch_s : cliPqScheme run W ℓ bi_s (cliPqSigsOf st_cli bi_s) bi_s.stA0 bi_s.stB0 = sch_cli := rfl
      have h_lift_get : ∀ {σ₁ σ₂ α : Type} (f : σ₂ → StateT σ₁ (StateT σ₂ ProbComp) α)
          (s₁ : σ₁) (s₂ : σ₂),
          (((StateT.lift (get : StateT σ₂ ProbComp σ₂) >>= f).run s₁).run s₂) =
            (((f s₂).run s₁).run s₂) := fun {σ₁ σ₂ α} f s₁ s₂ => by
        change (((get : StateT σ₂ ProbComp σ₂) >>= fun a => pure (a, s₁)) >>=
          fun x => (f x.1).run x.2).run s₂ = _
        simp only [bind_assoc, pure_bind, StateT.run_bind, StateT.run_get]
      have h_lift_m : ∀ {σ₁ σ₂ α β : Type} (c : ProbComp α)
          (f : α → StateT σ₁ (StateT σ₂ ProbComp) β) (s₁ : σ₁) (s₂ : σ₂),
          (((StateT.lift (liftM c : StateT σ₂ ProbComp α) >>= f).run s₁).run s₂) =
            (c >>= fun a => ((f a).run s₁).run s₂) := fun {σ₁ σ₂ α β} c f s₁ s₂ => by
        change (((liftM c : StateT σ₂ ProbComp α) >>= fun a => pure (a, s₁)) >>=
          fun x => (f x.1).run x.2).run s₂ = _
        simp only [bind_assoc, pure_bind, StateT.run_bind, StateT.run_monadLift, monadLift_self]
      have h1 : (((cliDrvSM S ℓ run W qep decT encT bhNoExtWithSpqr
          ⟨i, .inl (.inl (.inl (.inl (p, m_send, some cns))))⟩).run ds_s).run st_cli) =
          (((cliRunStdSM S ℓ run W qep decT encT ds_s i bi_s im s_cli
            (.inl (.inl (.inl (.inl (p, m_send, some cns)))))).run ds_s).run st_cli) := by
        unfold cliDrvSM
        simp only [StateT.run_bind, StateT.run_get, pure_bind, hClean_s, Bool.not_true,
          Bool.false_eq_true, ↓reduceIte, hbis_opt, hims_opt, bhIsBobRecvSMQuery,
          Bool.and_false, Bool.false_and]
        rfl
      rw [h1]
      unfold cliRunStdSM bhMetaAfterSM bhIsBobAcceptSMResp
      rw [h_lift_get]; dsimp only [hsch_s]
      rw [h_lift_m]
      dsimp [CryptoGames.SM.oracleImplR, CryptoGames.SM.transmitR,
        CryptoGames.SM.transmitImpl, CryptoGames.SM.samIfNec]
      simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
        StateT.run_monadLift, monadLift_self, pure_bind, Bool.and_false,
        h_sendOK_scli, hs_win_cli, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hep_s_cli]
      rw [hsch_s]
      dsimp only [bi_s, ds_s, ds_f, gs_cli_f, out_cli, sch_cli]
      simp only [List.set_set]
    have h_ad_eq :
        (((cliComposedAdapterImplWith (modelPrims X W)
            (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S (modelPrims X W)) W.C W.Q.K qep decT encT
            (.inr ⟨i, .inl (.inl (.inl (.inl (p, m_send, some cns))))⟩)).run σ_ad).run σ_s) =
          pure ((some (cliWrapAdapterSend inst (σ_ad.2.1 i) p out_m.2), σ_ad), σ_f) := by
      have hds_opt : σ_s.insts[i]? = some d_s := by simp [σ_s, hi_e2e]
      have himse_opt : σ_s.instMeta[i]? = some im_e2e := by simp [σ_s, hi_me]
      rw [cliComposedAdapterImplWith_tr_run, hinst_ad]
      dsimp [bhE2EStepLocalSm, CryptoGames.SM.oracleImplR, CryptoGames.SM.transmitR,
        CryptoGames.SM.transmitImpl, CryptoGames.SM.samIfNec,
        configRefuseEarlyBobCorr, configR1OnCurve]
      dsimp only [configRefuseEarlyBobCorr, configR1OnCurve] at h_sendOK_sm
      simp only [hClean_e2e_s, hds_opt, himse_opt, bhIsBobRecvSMQuery, bhIsBobAcceptSMResp,
        StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
        StateT.run_monadLift, monadLift_self, pure_bind, bhPackSmResp,
        h_sendOK_sm, hs_win_m, Bool.not_true, Bool.false_eq_true, Bool.and_false,
        Bool.false_and, ↓reduceIte, d_s, hep_s_m]
      dsimp only [σ_s, σ_f, gs_m_f, out_m, sch_m, P_v1]
      simp only [List.set_set]
    rw [h_cli_eq, h_ad_eq] at hC_tr
    obtain ⟨hsome_eq, hRel_f⟩ := deq_pure_pure_of_stepCoupled hC_tr
    have hout2 : out_cli.2 = cliWrapAdapterSend inst (σ_ad.2.1 i) p out_m.2 :=
      Option.some.inj hsome_eq
    refine ⟨hout2, ?_⟩
    cases isChall
    · exact hRel_f
    · have hi_f_cli : i < ds_f.bhInsts.length := by simp [ds_f, hi_cli]
      have hi_f_e2e : i < σ_f.insts.length := by simp [σ_f, hi_e2e]
      have hi_f_mb : i < ds_f.instMeta.length := by simp [ds_f, hi_mb]
      have hi_f_me : i < σ_f.instMeta.length := by simp [σ_f, hi_me]
      obtain ⟨inst_f, hinst_f, hInst_f⟩ := hRel_f.insts_rel i hi_f_cli hi_f_e2e hi_f_mb hi_f_me
      have hinst_f_eq : inst_f = inst := Option.some.inj (hinst_f.symm.trans hinst_ad)
      subst inst_f
      simp only [ds_f, σ_f, List.getElem_set_self, Function.update_self] at hInst_f
      have hInst_t : CliAdapterInstRel X W (qs_rem i - 1) st_cli ds_cli
          { bi with gs := some gs_cli' } { d with gs := some gs_m' } im im_e2e inst (σ_ad.2.1 i) := by
        refine
          { im_eq := hInst_f.im_eq
            sid_eq := hInst_f.sid_eq
            hdr_eq := hInst_f.hdr_eq
            idB_eq := hInst_f.idB_eq
            respSlot_eq := hInst_f.respSlot_eq
            respMeta_eq := hInst_f.respMeta_eq
            regIdA_eq := hInst_f.regIdA_eq
            regIdB_eq := hInst_f.regIdB_eq
            aliceAcked_false := hInst_f.aliceAcked_false
            idA_pub_eq := hInst_f.idA_pub_eq
            idB_pub_eq := hInst_f.idB_pub_eq
            extrasB_eq := hInst_f.extrasB_eq
            stB0_empty := hInst_f.stB0_empty
            resp_bundle_rel := hInst_f.resp_bundle_rel
            handshake_rel := ?_
            gs_rel := ?_ }
        · obtain ⟨bundleE, dk, ac, u_init, bnd, t_init, ss, h1, h2, h3, h4⟩ := hInst_f.handshake_rel
          refine ⟨bundleE, dk, ac, u_init, bnd, t_init, ss, h1,
            by simpa [ds_f] using h2, h3, fun gs_c₁ gs_m₁ hc₁ hm₁ hcorr₁ hacc₁ => ?_⟩
          simp only [Option.some.injEq] at hc₁ hm₁; subst hc₁ hm₁
          exact h4 gs_cli_f gs_m_f rfl rfl hcorr₁ hacc₁
        · have hgs_f := hInst_f.gs_rel
          dsimp only at hgs_f ⊢
          rcases hgs_f with ⟨hb_f, hrest_f⟩
          simp only [im, hCorr, Bool.false_eq_true, ↓reduceIte] at hrest_f ⊢
          rcases hrest_f with
            ⟨h1, h2, h3, h4, h5, _, h7, h8, h9, h10, h11, h12, h13, h14,
             h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
          have hch_t : gs_cli'.chall = gs_m'.chall := by
            dsimp [gs_cli', gs_m', CryptoGames.SM.GameState.record]; rw [hs_ep, hs_idx, hs_ch]
          exact ⟨hb_f, h1, h2, h3, h4, h5, hch_t, h7, h8, h9, h10, h11, h12, h13, h14,
            h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
      exact cliAdapterDrvRel_update_inst_ad hRel hi_cli
        { bi with gs := some gs_cli' } { d with gs := some gs_m' } im im_e2e inst (σ_ad.2.1 i)
        rfl hinst_ad rfl (fun _ _ => rfl) (fun _ _ => rfl) hInst_t

private theorem list_set_getElem_self_local {α : Type} (l : List α) (i : ℕ) (hi : i < l.length) :
    l.set i l[i] = l := by
  apply List.ext_getElem (by simp)
  intro j hj1 hj2
  by_cases hji : j = i
  · subst hji; simp
  · rw [List.getElem_set_ne (Ne.symm hji)]

private theorem bhInst_set_same_gs_local {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {bi : ModelDriverInstance S ℓ} {gs : CryptoGames.SM.GameState BinState (Plain ℓ) Bytes}
    (hgs : bi.gs = some gs) :
    { bi with gs := some gs } = bi := by
  cases bi; dsimp only at hgs; subst hgs; rfl

private theorem bhModelInst_set_same_gs_local {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {d : BHModelInst S ℓ} {gs : CryptoGames.SM.GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (hgs : d.gs = some gs) :
    { d with gs := some gs } = d := by
  cases d; dsimp only at hgs; subst hgs; rfl

theorem bhDrvState_set_same_gs_local {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (ds : ModelDriverState S ℓ) (i : ℕ) (hi : i < ds.bhInsts.length)
    (him : i < ds.instMeta.length)
    (gs : CryptoGames.SM.GameState BinState (Plain ℓ) Bytes)
    (hgs : ds.bhInsts[i].gs = some gs) :
    { ds with bhInsts := ds.bhInsts.set i { ds.bhInsts[i] with gs := some gs },
              instMeta := ds.instMeta.set i ds.instMeta[i] } = ds := by
  rw [bhInst_set_same_gs_local hgs, list_set_getElem_self_local _ i hi,
      list_set_getElem_self_local _ i him]

theorem bhE2EDrvState_set_same_gs_local {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (σ : BHE2EDrvState S ℓ) (i : ℕ) (hi : i < σ.insts.length)
    (him : i < σ.instMeta.length)
    (gs : CryptoGames.SM.GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (hgs : σ.insts[i].gs = some gs) :
    { σ with insts := σ.insts.set i { σ.insts[i] with gs := some gs },
             instMeta := σ.instMeta.set i σ.instMeta[i] } = σ := by
  rw [bhModelInst_set_same_gs_local hgs, list_set_getElem_self_local _ i hi,
      list_set_getElem_self_local _ i him]

private theorem stateT_lift_get_bind_run_m {M : Type → Type} [Monad M] [LawfulMonad M]
    {σ₁ σ₂ α : Type} (f : σ₂ → StateT σ₁ (StateT σ₂ M) α) (s₁ : σ₁) (s₂ : σ₂) :
    (((StateT.lift (get : StateT σ₂ M σ₂) >>= f).run s₁).run s₂) =
      (((f s₂).run s₁).run s₂) := by
  change (((get : StateT σ₂ M σ₂) >>= fun a => pure (a, s₁)) >>=
    fun x => (f x.1).run x.2).run s₂ = _
  simp only [bind_assoc, pure_bind, StateT.run_bind, StateT.run_get]

private theorem stateT_lift_lift_bind_run_m {M : Type → Type} [Monad M] [LawfulMonad M]
    {σ₁ σ₂ α β : Type} (c : M α) (f : α → StateT σ₁ (StateT σ₂ M) β) (s₁ : σ₁) (s₂ : σ₂) :
    (((StateT.lift (StateT.lift c : StateT σ₂ M α) >>= f).run s₁).run s₂) =
      (c >>= fun a => ((f a).run s₁).run s₂) := by
  change (((StateT.lift c : StateT σ₂ M α) >>= fun a => pure (a, s₁)) >>=
    fun x => (f x.1).run x.2).run s₂ = _
  simp only [bind_assoc, pure_bind, StateT.run_bind, StateT.run_lift]

theorem writerT_run_transmitRM_some {Key St Msg C : Type}
    (sch : CryptoGames.SMSchemeR Key St Msg (BitVec 512) (BitVec 256) C)
    (Δ qep : ℕ) (cfg : CryptoGames.SM.ConfigR St Msg C)
    (p : Party) (m : Msg) (cns : BitVec 512)
    (gs : CryptoGames.SM.GameState St Msg C) :
    WriterT.run ((transmitRM (smSchemeCoinLogged sch) Δ qep cfg (p, m, some cns)).run gs) =
      (fun x => (x, if x.1.isSome then [cns] else [])) <$>
        ((CryptoGames.SM.transmitR sch Δ qep cfg (p, m, some cns)).run gs) := by
  have hsend : ∀ s m' r, WriterT.run ((smSchemeCoinLogged sch).send s m' r) =
      pure (sch.send s m' r, [r]) := fun s m' r => by
    simp [smSchemeCoinLogged, MonadWriter.tell]
  unfold transmitRM CryptoGames.SM.transmitR
    CryptoGames.SM.transmitImpl CryptoGames.SMSchemeR.sendPart
  dsimp only [CryptoGames.SM.samIfNec]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases cfg.sendOK gs p
  · simp [StateT.run_pure, WriterT.run_pure]
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
    cases gs.win
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
        StateT.run_monadLift, monadLift_self, liftM_prob_pure, pure_bind]
      rcases hep : gs.epMgmt Δ qep p true with _ | s₁
      · simp [StateT.run_pure, WriterT.run_pure]
      · simp [StateT.run_bind, StateT.run_lift, StateT.run_set, hsend]
    · simp [StateT.run_pure, WriterT.run_pure]

theorem writerT_run_challRM_some {Key St Msg C : Type}
    (sch : CryptoGames.SMSchemeR Key St Msg (BitVec 512) (BitVec 256) C)
    (Δ qep : ℕ) (cfg : CryptoGames.SM.ConfigR St Msg C)
    (p : Party) (m0 m1 : Msg) (cns : BitVec 512)
    (gs : CryptoGames.SM.GameState St Msg C) :
    WriterT.run ((challRM (smSchemeCoinLogged sch) Δ qep cfg (p, m0, m1, some cns)).run gs) =
      (fun x => (x, if x.1.isSome then [cns] else [])) <$>
        ((CryptoGames.SM.challR sch Δ qep cfg (p, m0, m1, some cns)).run gs) := by
  have hsend : ∀ s m' r, WriterT.run ((smSchemeCoinLogged sch).send s m' r) =
      pure (sch.send s m' r, [r]) := fun s m' r => by
    simp [smSchemeCoinLogged, MonadWriter.tell]
  unfold challRM CryptoGames.SM.challR
    CryptoGames.SM.challImpl CryptoGames.SMSchemeR.sendPart
  dsimp only [CryptoGames.SM.samIfNec]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases cfg.sendOK gs p
  · simp [StateT.run_pure, WriterT.run_pure]
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
    cases gs.win
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
        StateT.run_monadLift, monadLift_self, liftM_prob_pure, pure_bind]
      rcases hep : gs.epMgmt Δ qep p true with _ | s₁
      · simp [StateT.run_pure, WriterT.run_pure]
      · dsimp only
        cases (!s₁.safeCh Δ p || !cfg.base.challAllowedIn (s₁.epoch p))
        · simp [StateT.run_bind, StateT.run_lift, StateT.run_set, hsend]
        · simp [StateT.run_pure, WriterT.run_pure]
    · simp [StateT.run_pure, WriterT.run_pure]

theorem writerT_run_transmitRM_none {Key St Msg C : Type}
    (sch : CryptoGames.SMSchemeR Key St Msg (BitVec 512) (BitVec 256) C)
    (Δ qep : ℕ) (cfg : CryptoGames.SM.ConfigR St Msg C)
    (p : Party) (m : Msg)
    (gs : CryptoGames.SM.GameState St Msg C) :
    WriterT.run ((transmitRM (smSchemeCoinLogged sch) Δ qep cfg (p, m, none)).run gs) =
      if !cfg.sendOK gs p then pure ((none, gs), [])
      else if gs.win then pure ((none, gs), [])
      else match gs.epMgmt Δ qep p false with
        | none => ($ᵗ (BitVec 512)) >>= fun _ => pure ((none, gs), [])
        | some s₁ => ($ᵗ (BitVec 512)) >>= fun cns =>
            let out := sch.send (s₁.st p) m cns
            pure ((some out.2, s₁.record Δ p out.1 ⟨⟨p, s₁.epoch p, s₁.idx p + 1⟩, m, out.2⟩ false), [cns]) := by
  have hsend : ∀ s m' r, WriterT.run ((smSchemeCoinLogged sch).send s m' r) =
      pure (sch.send s m' r, [r]) := fun s m' r => by
    simp [smSchemeCoinLogged, MonadWriter.tell]
  unfold transmitRM
  dsimp only [CryptoGames.SM.samIfNec]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases cfg.sendOK gs p
  · simp [StateT.run_pure, WriterT.run_pure]
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases gs.win
    · simp only [Bool.false_eq_true, ↓reduceIte, map_eq_bind_pure_comp, Function.comp_def,
        liftM_prob_bind, liftM_prob_pure, StateT.run_bind, StateT.run_lift,
        pure_bind, bind_assoc, writerT_run_liftM_prob, WriterT.run_bind]
      rcases hep : gs.epMgmt Δ qep p false with _ | s₁ <;> dsimp only
      · simp [StateT.run_pure, WriterT.run_pure]
      · simp [StateT.run_bind, StateT.run_lift, StateT.run_set, hsend]
    · simp [StateT.run_pure, WriterT.run_pure]

theorem writerT_run_challRM_none {Key St Msg C : Type}
    (sch : CryptoGames.SMSchemeR Key St Msg (BitVec 512) (BitVec 256) C)
    (Δ qep : ℕ) (cfg : CryptoGames.SM.ConfigR St Msg C)
    (p : Party) (m0 m1 : Msg)
    (gs : CryptoGames.SM.GameState St Msg C) :
    WriterT.run ((challRM (smSchemeCoinLogged sch) Δ qep cfg (p, m0, m1, none)).run gs) =
      if !cfg.sendOK gs p then pure ((none, gs), [])
      else if gs.win then pure ((none, gs), [])
      else match gs.epMgmt Δ qep p false with
        | none => ($ᵗ (BitVec 512)) >>= fun _ => pure ((none, gs), [])
        | some s₁ =>
          if !s₁.safeCh Δ p || !cfg.base.challAllowedIn (s₁.epoch p) then
            ($ᵗ (BitVec 512)) >>= fun _ => pure ((none, gs), [])
          else ($ᵗ (BitVec 512)) >>= fun cns =>
            let m := (cfg.base.challMsg (s₁.epoch p)).getD (if gs.b then m1 else m0)
            let out := sch.send (s₁.st p) m cns
            pure ((some out.2, s₁.record Δ p out.1 ⟨⟨p, s₁.epoch p, s₁.idx p + 1⟩, m, out.2⟩ true), [cns]) := by
  have hsend : ∀ s m' r, WriterT.run ((smSchemeCoinLogged sch).send s m' r) =
      pure (sch.send s m' r, [r]) := fun s m' r => by
    simp [smSchemeCoinLogged, MonadWriter.tell]
  unfold challRM
  dsimp only [CryptoGames.SM.samIfNec]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases cfg.sendOK gs p
  · simp [StateT.run_pure, WriterT.run_pure]
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases gs.win
    · simp only [Bool.false_eq_true, ↓reduceIte, map_eq_bind_pure_comp, Function.comp_def,
        liftM_prob_bind, liftM_prob_pure, StateT.run_bind, StateT.run_lift,
        pure_bind, bind_assoc, writerT_run_liftM_prob, WriterT.run_bind]
      rcases hep : gs.epMgmt Δ qep p false with _ | s₁ <;> dsimp only
      · simp [StateT.run_pure, WriterT.run_pure]
      · cases (!s₁.safeCh Δ p || !cfg.base.challAllowedIn (s₁.epoch p))
        · simp [StateT.run_bind, StateT.run_lift, StateT.run_set, hsend]
        · simp [StateT.run_pure, WriterT.run_pure]
    · simp [StateT.run_pure, WriterT.run_pure]

theorem oracleImplRM_tr {Key St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    (sch : CryptoGames.SMSchemeR Key St Msg (BitVec 512) (BitVec 256) C)
    (Δ qep : ℕ) (cfg : CryptoGames.SM.ConfigR St Msg C)
    (x : Party × Msg × Option (BitVec 512)) :
    oracleImplRM (smSchemeCoinLogged sch) Δ qep cfg (.inl (.inl (.inl (.inl x)))) =
      transmitRM (smSchemeCoinLogged sch) Δ qep cfg x := rfl

theorem oracleImplRM_ch {Key St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    (sch : CryptoGames.SMSchemeR Key St Msg (BitVec 512) (BitVec 256) C)
    (Δ qep : ℕ) (cfg : CryptoGames.SM.ConfigR St Msg C)
    (x : Party × Msg × Msg × Option (BitVec 512)) :
    oracleImplRM (smSchemeCoinLogged sch) Δ qep cfg (.inl (.inl (.inl (.inr x)))) =
      challRM (smSchemeCoinLogged sch) Δ qep cfg x := rfl

theorem oracleImplR_tr {Key St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    (sch : CryptoGames.SMSchemeR Key St Msg (BitVec 512) (BitVec 256) C)
    (Δ qep : ℕ) (cfg : CryptoGames.SM.ConfigR St Msg C)
    (x : Party × Msg × Option (BitVec 512)) :
    CryptoGames.SM.oracleImplR sch Δ qep cfg (.inl (.inl (.inl (.inl x)))) =
      CryptoGames.SM.transmitR sch Δ qep cfg x := rfl

theorem oracleImplR_ch {Key St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    (sch : CryptoGames.SMSchemeR Key St Msg (BitVec 512) (BitVec 256) C)
    (Δ qep : ℕ) (cfg : CryptoGames.SM.ConfigR St Msg C)
    (x : Party × Msg × Msg × Option (BitVec 512)) :
    CryptoGames.SM.oracleImplR sch Δ qep cfg (.inl (.inl (.inl (.inr x)))) =
      CryptoGames.SM.challR sch Δ qep cfg x := rfl

theorem cliDrvSMCoinLogged_clean_tc_run {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (run : CliRun) (W : PEParams) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ext : QueryImpl (cliGameSmSpec ℓ (BitVec 512)) (BHDrvMCoinLogged S ℓ))
    (ds : ModelDriverState S ℓ) (st : SignalPqxdh.KeyIndState S)
    (i : ℕ) (bi : ModelDriverInstance S ℓ) (im : ModelDriverInstanceMeta S)
    (gs : CryptoGames.SM.GameState BinState (Plain ℓ) Bytes)
    (tc : (Party × Plain ℓ × Option (BitVec 512)) ⊕
          (Party × Plain ℓ × Plain ℓ × Option (BitVec 512)))
    (hClean : bhDrvInstClean ds i = true)
    (hbi : ds.bhInsts[i]? = some bi) (him : ds.instMeta[i]? = some im)
    (hgs : bi.gs = some gs) :
    WriterT.run (((cliDrvSMCoinLogged S ℓ run W qep decT encT ext
        ⟨i, .inl (.inl (.inl tc))⟩).run ds).run st) =
      (fun xw =>
        (((xw.1.1, { ds with bhInsts := ds.bhInsts.set i { bi with gs := some xw.1.2 },
                             instMeta := ds.instMeta.set i im }), st), xw.2)) <$>
        WriterT.run ((oracleImplRM
            (smSchemeCoinLogged (cliPqScheme run W ℓ bi (cliPqSigsOf st bi) bi.stA0 bi.stB0))
            (2 + 1) qep (bhConfigSpkS (Msg := Plain ℓ) decT encT) (.inl (.inl (.inl tc)))).run gs) := by
  have hrecv : @bhIsBobRecvSMQuery ℓ (BitVec 512) (.inl (.inl (.inl tc))) = false := by
    rcases tc with _ | _ <;> rfl
  have hstep : cliStepLocalSMCoinLogged S ℓ run W qep decT encT ds i bi im gs
      (.inl (.inl (.inl tc))) =
      cliRunStdSMCoinLogged S ℓ run W qep decT encT ds i bi im gs (.inl (.inl (.inl tc))) := by
    rcases tc with _ | _ <;> rfl
  have hmeta : ∀ r, bhMetaAfterSM ds bi im (.inl (.inl (.inl tc))) r = im := fun _ => by
    rcases tc with _ | _ <;> simp [bhMetaAfterSM, bhIsBobAcceptSMResp]
  have h1 : (((cliDrvSMCoinLogged S ℓ run W qep decT encT ext
      ⟨i, .inl (.inl (.inl tc))⟩).run ds).run st) =
      (((cliRunStdSMCoinLogged S ℓ run W qep decT encT ds i bi im gs
        (.inl (.inl (.inl tc)))).run ds).run st) := by
    unfold cliDrvSMCoinLogged
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hClean, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, hbi, him, hrecv, Bool.and_false, Bool.false_and, hgs, hstep]
  rw [h1]
  unfold cliRunStdSMCoinLogged
  rw [stateT_lift_get_bind_run_m]
  dsimp only
  rw [stateT_lift_lift_bind_run_m]
  simp [StateT.run_bind, StateT.run_set, StateT.run_pure, hmeta,
    WriterT.run_bind, WriterT.run_pure, map_eq_bind_pure_comp]

theorem cliDrvSM_clean_tc_run {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (run : CliRun) (W : PEParams) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ext : QueryImpl (cliGameSmSpec ℓ (BitVec 512)) (BHDrvM S ℓ))
    (ds : ModelDriverState S ℓ) (st : SignalPqxdh.KeyIndState S)
    (i : ℕ) (bi : ModelDriverInstance S ℓ) (im : ModelDriverInstanceMeta S)
    (gs : CryptoGames.SM.GameState BinState (Plain ℓ) Bytes)
    (tc : (Party × Plain ℓ × Option (BitVec 512)) ⊕
          (Party × Plain ℓ × Plain ℓ × Option (BitVec 512)))
    (hClean : bhDrvInstClean ds i = true)
    (hbi : ds.bhInsts[i]? = some bi) (him : ds.instMeta[i]? = some im)
    (hgs : bi.gs = some gs) :
    (((cliDrvSM S ℓ run W qep decT encT ext
        ⟨i, .inl (.inl (.inl tc))⟩).run ds).run st) =
      (fun x =>
        ((x.1, { ds with bhInsts := ds.bhInsts.set i { bi with gs := some x.2 },
                         instMeta := ds.instMeta.set i im }), st)) <$>
        ((CryptoGames.SM.oracleImplR
            (cliPqScheme run W ℓ bi (cliPqSigsOf st bi) bi.stA0 bi.stB0)
            (2 + 1) qep (bhConfigSpkS (Msg := Plain ℓ) decT encT) (.inl (.inl (.inl tc)))).run gs) := by
  have hrecv : @bhIsBobRecvSMQuery ℓ (BitVec 512) (.inl (.inl (.inl tc))) = false := by
    rcases tc with _ | _ <;> rfl
  have hstep : cliStepLocalSM S ℓ run W qep decT encT ds i bi im gs (.inl (.inl (.inl tc))) =
      cliRunStdSM S ℓ run W qep decT encT ds i bi im gs (.inl (.inl (.inl tc))) := by
    rcases tc with _ | _ <;> rfl
  have hmeta : ∀ r, bhMetaAfterSM ds bi im (.inl (.inl (.inl tc))) r = im := fun _ => by
    rcases tc with _ | _ <;> simp [bhMetaAfterSM, bhIsBobAcceptSMResp]
  have h_lift_m : ∀ {σ₁ σ₂ α β : Type} (c : ProbComp α)
      (f : α → StateT σ₁ (StateT σ₂ ProbComp) β) (s₁ : σ₁) (s₂ : σ₂),
      (((StateT.lift (liftM c : StateT σ₂ ProbComp α) >>= f).run s₁).run s₂) =
        (c >>= fun a => ((f a).run s₁).run s₂) := fun {σ₁ σ₂ α β} c f s₁ s₂ => by
    change (((liftM c : StateT σ₂ ProbComp α) >>= fun a => pure (a, s₁)) >>=
      fun x => (f x.1).run x.2).run s₂ = _
    simp only [bind_assoc, pure_bind, StateT.run_bind, StateT.run_monadLift, monadLift_self]
  have h1 : (((cliDrvSM S ℓ run W qep decT encT ext
      ⟨i, .inl (.inl (.inl tc))⟩).run ds).run st) =
      (((cliRunStdSM S ℓ run W qep decT encT ds i bi im gs
        (.inl (.inl (.inl tc)))).run ds).run st) := by
    unfold cliDrvSM
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hClean, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, hbi, him, hrecv, Bool.and_false, Bool.false_and, hgs, hstep]
  rw [h1]
  unfold cliRunStdSM
  rw [stateT_lift_get_bind_run_m]
  dsimp only
  rw [h_lift_m]
  simp [StateT.run_bind, StateT.run_set, StateT.run_pure, hmeta, map_eq_bind_pure_comp]


end Computational.Proofs.LibsignalCli.CliKemFailCouplingHopBCore

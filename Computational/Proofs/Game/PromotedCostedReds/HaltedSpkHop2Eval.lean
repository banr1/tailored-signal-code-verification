/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2Step -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.HaltedSpkDefs
import Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDsl

/-!
# Evaluation and Invariant Preservation for Tracker-Halted Hop-2 Step Handler

Bridges `KemFailTrackBridge.KemFailTrackState` to `Refinement.KemFailTrackState` and proves monadic
`.eval` agreement and invariant preservation for `hop2SendAfterPreTrackC` and `hop2StepTrackC`
across all five session-manager arms.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2Eval

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Ops Iface Expr Comp
  atomicSig atomicSessionOps coinOnlyIface extractPtPrfIface e2eSessionCodec
  BV256 BV512 GhostStT PlainT B smQT smRT recvResultEnc)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.SM (ConfigR GameState RecvResult partyEnc posEnc samIfNec corrR)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey GhostState ShaCompress)
open CryptoGames.Ratchet.LibsignalSim (kemTrackEnc)
open CryptoGames.LibsignalSM.Proofs.Refinement (KemFailTrackState initKemFailTrack)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.E2E (Bytes Hop2Aux Hop2Comp Hop2Hyb configRefuseEarlyBobCorr
  hop2Lift paramsIdsWithSpqr sessionSchemeFixedSpk sessionSchemeU)
open Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping (e2eGsTy e2eGsEnc e2eGsSt e2eGsB
  e2eGsWin e2eGsEpoch e2eGsIdx e2eSendOKE e2eEpMgmtE e2eSafeChE
  eval_e2eSendOKE eval_e2eEpMgmtE eval_e2eSafeChE eval_e2eRecordE smRenc)
open Computational.Proofs.E2E.Dsl.SpqrSim (spqrDslHooks)
open Computational.Proofs.E2E.Dsl.DrSessionSimSend (drSendC_eval)
open Computational.Proofs.E2E.Dsl.DrSessionSim (e2eSamIfNec512C_eval drCrArmC drCrArmC_eval)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge (zeroPqxdhPrims
  liftTy liftVal wk1Comp_eval coinE2EIface coinE2ESamplers liftCompCoins liftCompCoins_eval)
open Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon (comp_eval_ret
  comp_eval_bind comp_eval_bind_ret comp_eval_ite comp_eval_caseOpt comp_eval_caseSum)
open Computational.Proofs.E2E.Dsl.SmReachInvParty (PartyReachInv)
open Computational.Proofs.E2E.Dsl.SmReachInv (dedupComp SmReachBounded
  smReachBounded_transmitR smReachBounded_challR smReachBounded_corrR)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedInit (kemTrackT kemTrackAtomicEnc)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedSendCorrSub (trE_cand
  stepKemFailSendAtomicC_eval)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitness (KemTrackDeliverInv
  KemTrackDeliverInv.mono kemTrackDeliverInv_step kemTrackDeliverInv_stepSend
  kemOnDeliverPostAtomicE_eval)
open Computational.Proofs.Game.PromotedCostedReds.SpkHop2RInProg (hop2FullEnc
  Hop2Mode Hop2EvalSpec Hop2AuxBounded compCoinToPrf_eval_eq_liftM
  coinOnlyIface_liftP
  stS stGs stAux stChall stMk hop2DlArmC_eval_and_inv hop2IjArmC_eval_and_inv)
open Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2Step (hop2HaltedStTy
  hstBase hstSessionTr hstTr hstWires hstMk hop2HaltedEnc eval_findHonestWireIdxE
  trPreE2EC chPreE2EC sendPostE2EC hop2SendAfterPreTrackC hop2StepTrackC)
open Computational.Proofs.E2E.HaltedSpkDefs (updateKemFailOnDeliver hop2LiftTrackHalted
  liftHop2NoTrackM hop2DeliverTrackHalted_run hop2ImplTrackHalted
  transmitRTrackHalted_support challRTrackHalted_support)

/-! ## Tracker state conversion -/

section BridgeToRefinement

/-- Structural conversion from `KemFailTrackBridge.KemFailTrackState` to `Refinement.KemFailTrackState`. -/
@[expose] def kemBridgeToRef {F : ShaCompress}
    (tr : Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.KemFailTrackState F) :
    KemFailTrackState F :=
  ⟨tr.e, tr.auth, tr.c, tr.st, tr.sentB, tr.sendCtr, tr.cand⟩

@[expose] def kemSessionBridgeToRef {F : ShaCompress} {W : Type}
    (tr : Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.KemFailSessionTrack F W) :
    KemFailTrackState F × List (W × Party) :=
  (kemBridgeToRef tr.1, tr.2)

@[expose] def hop2BridgeHaltedEnc {ℓ : ℕ} {Pt : Type} (C : Crypto)
    (s : BitVec 256) (chall : BitVec 256 × BitVec 256)
    (gat : (GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt) ×
      Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.KemFailSessionTrack C.F Bytes) :
    (hop2HaltedStTy ℓ Pt).denote :=
  hop2HaltedEnc C (ℓ := ℓ) (Pt := Pt) s chall (gat.1, kemSessionBridgeToRef gat.2)

@[simp] theorem kemBridgeToRef_init (F : ShaCompress) (k : BitVec 256) :
    kemBridgeToRef
      (Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.initKemFailTrack F k) =
    initKemFailTrack F k := rfl

@[simp] theorem kemBridgeToRef_cand {F : ShaCompress}
    (tr : Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.KemFailTrackState F) :
    (kemBridgeToRef tr).cand = tr.cand := rfl

@[simp] theorem kemBridgeToRef_withCand {F : ShaCompress}
    (tr : Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.KemFailTrackState F)
    (c : Option (List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 32)) :
    kemBridgeToRef { tr with cand := c } = { kemBridgeToRef tr with cand := c } := rfl

theorem kemBridgeToRef_stepSend (F : ShaCompress) (K : MlKem)
    (tr : Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.KemFailTrackState F)
    (Q : Party) (r : BitVec 512) :
    kemBridgeToRef
      (Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.stepKemFailSend F K tr Q r) =
    CryptoGames.LibsignalSM.Proofs.Refinement.stepKemFailSend F K (kemBridgeToRef tr) Q r := by
  have hbp :
      Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.kemBraidParty Q =
      CryptoGames.LibsignalSM.Proofs.Refinement.kemBraidParty Q := by
    cases Q <;> rfl
  unfold Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.stepKemFailSend
    CryptoGames.LibsignalSM.Proofs.Refinement.stepKemFailSend
  rw [hbp]
  dsimp only [kemBridgeToRef]
  cases h : (tr.st Q).send K (CryptoVerification.LibsignalSpqrV1.coinBytes r) with
  | error _ => rfl
  | ok p => rcases p with ⟨_, _⟩; rfl

theorem kemBridgeToRef_stepDeliver (F : ShaCompress) (K : MlKem)
    (tr : Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.KemFailTrackState F)
    (Q : Party) (j : ℕ) :
    kemBridgeToRef
      (Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.stepKemFailDeliver F K tr Q j) =
    CryptoGames.LibsignalSM.Proofs.Refinement.stepKemFailDeliver F K (kemBridgeToRef tr) Q j := by
  unfold Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.stepKemFailDeliver
    CryptoGames.LibsignalSM.Proofs.Refinement.stepKemFailDeliver
  dsimp only [kemBridgeToRef]
  cases tr.sentB[j]? with
  | none => rfl
  | some mc =>
    rcases mc with ⟨m, _⟩
    dsimp only
    cases (tr.st Q).recv K m with
    | error _ => rfl
    | ok out =>
      dsimp only
      by_cases hm : m = CryptoVerification.SpqrV1Sync.Braid.noneMsg (tr.e + 1#64)
      · simp only [hm, ↓reduceIte]
        cases tr.c <;> rfl
      · simp only [hm, ↓reduceIte]

theorem kemTrackDeliverInv_withCand (F : ShaCompress) (K : MlKem) (L : ℕ)
    (tr : KemFailTrackState F)
    (c : Option (List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 32))
    (hInv : KemTrackDeliverInv F K L (kemTrackEnc tr)) :
    KemTrackDeliverInv F K L (kemTrackEnc { tr with cand := c }) :=
  ⟨hInv.sentB_len, hInv.bOk, hInv.sentB_deser⟩

end BridgeToRefinement

/-! ## Step evaluation and invariant preservation -/

section StepEval

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (K : MlKem)
  (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (idA idB : IdentityKey) (lam : Pt)

local notation "ESig" => CryptoVerification.E2E.Costed.e2eSig ℓ
local notation "EOps" =>
  CryptoVerification.E2E.Costed.e2eOps ℓ
    Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.zeroPqxdhPrims C K decT encT
local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

private theorem epMgmt_preserve_fields {Δ qep : ℕ}
    {st s1 : GameState (GhostState Bytes) (Plain ℓ) Bytes} {party : Party} {bad : Bool}
    (hep : st.epMgmt Δ qep party bad = some s1) :
    s1.st = st.st ∧ s1.trans = st.trans ∧ s1.comp = st.comp := by
  unfold GameState.epMgmt at hep
  split_ifs at hep <;> simp only [Option.some.injEq] at hep <;> subst hep <;> exact ⟨rfl, rfl, rfl⟩

private theorem liftM_hop2_map {α β : Type} (f : α → β) (p : ProbComp α) :
    (liftM (f <$> p) : Hop2Comp Pt β) = f <$> (liftM p : Hop2Comp Pt α) := by
  simp only [map_eq_bind_pure_comp, Function.comp_def, liftM_bind, liftM_pure]

private theorem coinE2E_coinOnly_liftP {α : Type} (p : ProbComp α) :
    (coinE2EIface (coinOnlyIface ℓ Pt)).liftP p = p :=
  coinOnlyIface_liftP (ℓ := ℓ) (Pt := Pt) p

private theorem stateT_lift_get_run2 {S₁ S₂ : Type} {M : Type → Type} [Monad M] [LawfulMonad M]
    (s₁ : S₁) (s₂ : S₂) :
    (((StateT.lift get : StateT S₁ (StateT S₂ M) S₂).run s₁).run s₂) = pure ((s₂, s₁), s₂) := by
  simp only [StateT.run_lift, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind]

private theorem stateT_lift_set_run2 {S₁ S₂ : Type} {M : Type → Type} [Monad M] [LawfulMonad M]
    (s₁ : S₁) (s₂ s₂' : S₂) :
    (((StateT.lift (set s₂') : StateT S₁ (StateT S₂ M) PUnit).run s₁).run s₂) =
      pure (((), s₁), s₂') := by
  simp only [StateT.run_lift, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]

private theorem stateT_lift_prob_run2 {S₁ S₂ α : Type}
    (p : ProbComp α) (s₁ : S₁) (s₂ : S₂) :
    (((StateT.lift (liftM p : StateT S₂ ProbComp α) :
        StateT S₁ (StateT S₂ ProbComp) α).run s₁).run s₂) =
      p >>= fun a => pure ((a, s₁), s₂) := by
  simp only [StateT.run_lift, StateT.run_bind, StateT.run_monadLift, monadLift_self,
    StateT.run_pure, bind_assoc, pure_bind]

private theorem liftHop2NoTrackM_run {F : ShaCompress} {α : Type}
    (m : StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt) (Hop2Comp Pt) α)
    (sa : GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt)
    (thw : Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.KemFailSessionTrack F Bytes) :
    (((liftHop2NoTrackM (Pt := Pt) (ℓ := ℓ) (F := F) m).run sa).run thw) =
      (m.run sa >>= fun r => pure (r, thw)) := by
  simp only [liftHop2NoTrackM, StateT.run_mk, StateT.run_lift]

theorem eval_trPreE2EC (qep : ℕ)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (party : Party) (m : Plain ℓ) (optR : Option (BitVec 512)) :
    let cfg := configRefuseEarlyBobCorr decT encT
    (trPreE2EC (ℓ := ℓ) (Pt := Pt) C K encT decT qep).eval
      (.cons (e2eGsEnc st, (partyEnc party, (m, optR))) .nil) =
    (if !(cfg.sendOK st party) || st.win then pure none
     else do
       let (rCoins, bad) ← (samIfNec optR : ProbComp (BitVec 512 × Bool))
       match st.epMgmt 3 qep party bad with
       | none => pure none
       | some s1 => pure (some (e2eGsEnc s1, (m, rCoins)))) := by
  intro cfg
  let CoinI := coinOnlyIface ℓ Pt
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) CoinI
  let t0 : Ty ESig := .prod (e2eGsTy ℓ)
    (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
      (.opt CryptoVerification.E2E.Costed.BV512)))
  set ρ₁ : Env [t0] := .cons (e2eGsEnc st, (partyEnc party, (m, optR))) .nil
  have hSendOK :
      (e2eSendOKE (.fst (Expr.v0 (O := EOps))) (.fst (.snd .v0))).eval ρ₁ =
        cfg.sendOK st party :=
    eval_e2eSendOKE decT encT (.fst .v0) (.fst (.snd .v0)) ρ₁ st party rfl rfl
  have hWin : (e2eGsWin (.fst (Expr.v0 (O := EOps)))).eval ρ₁ = st.win := rfl
  dsimp only [trPreE2EC]
  rw [comp_eval_ite]
  simp only [CryptoGames.SM.orE_eval, Expr.eval, hSendOK, hWin]
  cases hgate : (!(cfg.sendOK st party) || st.win)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [comp_eval_bind, e2eSamIfNec512C_eval coins]
    have hOptR :
        (Expr.snd (.snd (.snd (Expr.v0 (O := EOps))))).eval ρ₁ = optR := rfl
    dsimp only [CoinI]
    rw [hOptR, coinE2E_coinOnly_liftP (ℓ := ℓ) (Pt := Pt)]
    refine bind_congr fun ⟨rCoins, bad⟩ => ?_
    let t1 : Ty ESig := .prod CryptoVerification.E2E.Costed.BV512 .bool
    set ρ₂ : Env [t1, t0] := .cons (rCoins, bad) ρ₁
    rw [comp_eval_caseOpt]
    have hep :
        (e2eEpMgmtE 3 qep (.fst (Expr.v1 (O := EOps))) (.fst (.snd .v1)) (.snd .v0)).eval ρ₂ =
          (st.epMgmt 3 qep party bad).map e2eGsEnc :=
      eval_e2eEpMgmtE 3 qep (.fst .v1) (.fst (.snd .v1)) (.snd .v0) ρ₂ st party rfl rfl
    rw [hep]
    cases st.epMgmt 3 qep party bad <;> rfl
  · rfl

theorem eval_chPreE2EC (qep : ℕ)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (party : Party) (m0 m1 : Plain ℓ) (optR : Option (BitVec 512)) :
    let cfg := configRefuseEarlyBobCorr decT encT
    (chPreE2EC (ℓ := ℓ) (Pt := Pt) C K encT decT qep).eval
      (.cons (e2eGsEnc st, (partyEnc party, (m0, (m1, optR)))) .nil) =
    (if !(cfg.sendOK st party) || st.win then pure none
     else do
       let (rCoins, bad) ← (samIfNec optR : ProbComp (BitVec 512 × Bool))
       match st.epMgmt 3 qep party bad with
       | none => pure none
       | some s1 =>
         if !(s1.safeCh 3 party) || !(cfg.base.challAllowedIn (s1.epoch party)) then pure none
         else
           let mCh := (cfg.base.challMsg (s1.epoch party)).getD (if st.b then m1 else m0)
           pure (some (e2eGsEnc s1, (mCh, rCoins)))) := by
  intro cfg
  have hchallAllowed : ∀ t, cfg.base.challAllowedIn t = true := fun _ => rfl
  have hchallMsg : ∀ t, cfg.base.challMsg t = none := fun _ => rfl
  let CoinI := coinOnlyIface ℓ Pt
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) CoinI
  let t0 : Ty ESig := .prod (e2eGsTy ℓ)
    (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
      (.prod CryptoVerification.E2E.Costed.PlainT
        (.opt CryptoVerification.E2E.Costed.BV512))))
  set ρ₁ : Env [t0] := .cons (e2eGsEnc st, (partyEnc party, (m0, (m1, optR)))) .nil
  have hSendOK :
      (e2eSendOKE (.fst (Expr.v0 (O := EOps))) (.fst (.snd .v0))).eval ρ₁ =
        cfg.sendOK st party :=
    eval_e2eSendOKE decT encT (.fst .v0) (.fst (.snd .v0)) ρ₁ st party rfl rfl
  have hWin : (e2eGsWin (.fst (Expr.v0 (O := EOps)))).eval ρ₁ = st.win := rfl
  dsimp only [chPreE2EC]
  rw [comp_eval_ite]
  simp only [CryptoGames.SM.orE_eval, Expr.eval, hSendOK, hWin]
  cases hgate : (!(cfg.sendOK st party) || st.win)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [comp_eval_bind, e2eSamIfNec512C_eval coins]
    have hOptR :
        (Expr.snd (.snd (.snd (.snd (Expr.v0 (O := EOps)))))).eval ρ₁ = optR := rfl
    dsimp only [CoinI]
    rw [hOptR, coinE2E_coinOnly_liftP (ℓ := ℓ) (Pt := Pt)]
    refine bind_congr fun ⟨rCoins, bad⟩ => ?_
    let t1 : Ty ESig := .prod CryptoVerification.E2E.Costed.BV512 .bool
    set ρ₂ : Env [t1, t0] := .cons (rCoins, bad) ρ₁
    rw [comp_eval_caseOpt]
    have hep :
        (e2eEpMgmtE 3 qep (.fst (Expr.v1 (O := EOps))) (.fst (.snd .v1)) (.snd .v0)).eval ρ₂ =
          (st.epMgmt 3 qep party bad).map e2eGsEnc :=
      eval_e2eEpMgmtE 3 qep (.fst .v1) (.fst (.snd .v1)) (.snd .v0) ρ₂ st party rfl rfl
    rw [hep]
    cases st.epMgmt 3 qep party bad with
    | none => rfl
    | some s1 =>
      simp only [Option.map_some, hchallAllowed, Bool.not_true, Bool.or_false,
        hchallMsg, Option.getD_none]
      set ρ₃ : Env [e2eGsTy ℓ, t1, t0] := .cons (e2eGsEnc s1) ρ₂
      rw [comp_eval_ite]
      have hSafe :
          (e2eSafeChE 3 (Expr.v0 (O := EOps)) (.fst (.snd .v2))).eval ρ₃ =
            s1.safeCh 3 party :=
        eval_e2eSafeChE 3 .v0 (.fst (.snd .v2)) ρ₃ s1 party rfl rfl
      simp only [Expr.eval, hSafe]
      cases hsafe : s1.safeCh 3 party
      · rfl
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, comp_eval_ret,
          Expr.eval, Expr.v0, Expr.v1, Expr.v2, e2eGsB, e2eGsEnc, ρ₃, ρ₂, ρ₁, Env.get]
  · rfl

theorem eval_sendPostE2EC (q : ℕ) (isChall : Bool) (s : BitVec 256)
    (s1 : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (party : Party) (m : Plain ℓ) (rCoins : BitVec 512)
    (hgParty : PartyReachInv C K (s1.st party))
    (htr1_le : s1.trans.length ≤ q)
    (hcp1_le : (dedupComp s1.comp).length ≤ q) :
    let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
    let sm := sessionSchemeU P ℓ
    let out := sm.send (s1.st party) m rCoins
    (sendPostE2EC (ℓ := ℓ) (Pt := Pt) C K encT decT q isChall).eval
      (.cons (e2eGsEnc s1, (partyEnc party, (m, rCoins))) .nil) =
    pure (out.2,
      e2eGsEnc
        (s1.record 3 party out.1
          ⟨⟨party, s1.epoch party, s1.idx party + 1⟩, m, out.2⟩ isChall)) := by
  intro P sm out
  let CoinI := coinOnlyIface ℓ Pt
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  let t0 : Ty ESig := .prod (e2eGsTy ℓ)
    (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT CryptoVerification.E2E.Costed.BV512))
  set ρ₀ : Env [t0] := .cons (e2eGsEnc s1, (partyEnc party, (m, rCoins))) .nil
  have hSendIn :
      (Expr.pair
        (CryptoGames.SM.pGet (e2eGsSt (.fst (Expr.v0 (O := EOps)))) (.fst (.snd .v0)))
        (.snd (.snd .v0))).eval ρ₀ =
      (s1.st party, (m, rCoins)) := by
    rw [CryptoGames.SM.pair_eval,
      CryptoGames.SM.pGet_eval _ _ ρ₀ s1.st party rfl rfl]
    rfl
  have hgParty' :
      PartyReachInv C K
        ((Expr.pair
          (CryptoGames.SM.pGet (e2eGsSt (.fst (Expr.v0 (O := EOps)))) (.fst (.snd .v0)))
          (.snd (.snd .v0))).eval ρ₀).1 := by
    rw [hSendIn]
    exact hgParty
  dsimp only [sendPostE2EC]
  rw [comp_eval_bind, drSendC_eval hooks (coinE2EIface CoinI) _ ρ₀ idA idB s hgParty', hSendIn]
  have hsendEq :
      (sessionSchemeFixedSpk P ℓ s).send (s1.st party) m rCoins = out := rfl
  rw [hsendEq, pure_bind, comp_eval_ret]
  let tOut : Ty ESig := .prod CryptoVerification.E2E.Costed.GhostStT
    (CryptoVerification.E2E.Costed.B 32)
  set ρ₁ : Env [tOut, t0] := .cons out ρ₀
  have hpos1 :
      (Expr.pair (.fst (.snd (Expr.v1 (O := EOps))))
        (.pair (CryptoGames.SM.pGet (e2eGsEpoch (.fst .v1)) (.fst (.snd .v1)))
          (.add (CryptoGames.SM.pGet (e2eGsIdx (.fst .v1)) (.fst (.snd .v1))) (.nat 1)))).eval ρ₁ =
      posEnc ⟨party, s1.epoch party, s1.idx party + 1⟩ := by
    have hep1 :
        (CryptoGames.SM.pGet (e2eGsEpoch (.fst (Expr.v1 (O := EOps)))) (.fst (.snd .v1))).eval ρ₁ =
          s1.epoch party :=
      CryptoGames.SM.pGet_eval (t := .nat) _ _ ρ₁ s1.epoch party rfl rfl
    have hidx1 :
        (CryptoGames.SM.pGet (e2eGsIdx (.fst (Expr.v1 (O := EOps)))) (.fst (.snd .v1))).eval ρ₁ =
          s1.idx party :=
      CryptoGames.SM.pGet_eval (t := .nat) _ _ ρ₁ s1.idx party rfl rfl
    simp only [Expr.eval, hep1, hidx1]
    rfl
  have hrec1 := eval_e2eRecordE q 3
    (.fst .v1 : Expr EOps [tOut, t0] (e2eGsTy ℓ)) (.fst (.snd .v1))
    (.fst .v0)
    (.pair (.fst (.snd .v1))
      (.pair (CryptoGames.SM.pGet (e2eGsEpoch (.fst .v1)) (.fst (.snd .v1)))
        (.add (CryptoGames.SM.pGet (e2eGsIdx (.fst .v1)) (.fst (.snd .v1))) (.nat 1))))
    (.fst (.snd (.snd .v1))) (.snd .v0) (.bool isChall)
    ρ₁ s1 party ⟨party, s1.epoch party, s1.idx party + 1⟩
    htr1_le hcp1_le rfl rfl hpos1
  simp only [CryptoGames.SM.pair_eval, hrec1]
  rfl

theorem hop2SendAfterPreTrackC_eval
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      (extractPtPrfIface ℓ Pt))
    {stepOf : BitVec 256 → Pt → Hop2Comp Pt (BitVec 256)}
    (hM : Hop2EvalSpec M stepOf)
    (q : ℕ) (isChall : Bool) (s : BitVec 256) (chall : BitVec 256 × BitVec 256)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (aux : Hop2Aux Pt)
    (tr : Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.KemFailTrackState C.F)
    (honestWires : List (Bytes × Party))
    (party : Party)
    (preOpt : Option (GameState (GhostState Bytes) (Plain ℓ) Bytes × (Plain ℓ × BitVec 512)))
    (hTrQ : KemTrackDeliverInv C.F K q (kemTrackEnc (kemBridgeToRef tr)))
    (hPre : ∀ s1 m rCoins, preOpt = some (s1, (m, rCoins)) →
      PartyReachInv C K (s1.st party) ∧ s1.trans.length ≤ q ∧ (dedupComp s1.comp).length ≤ q) :
    let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
    let sm := sessionSchemeU P ℓ
    (hop2SendAfterPreTrackC C K Dh encPt encT decT lam M q isChall).eval
      (.cons (hop2BridgeHaltedEnc C s chall ((st, aux), (tr, honestWires)),
        (ReductionDsl.partyToBool party,
          preOpt.map fun x => (liftVal (Pt := Pt) (e2eGsEnc x.1), x.2))) .nil) =
    match preOpt with
    | none =>
      pure ((none, (none, none)), hop2BridgeHaltedEnc C s chall ((st, aux), (tr, honestWires)))
    | some (s1, (m, rCoins)) =>
      let tr' :=
        Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.stepKemFailSend C.F K tr party
          rCoins
      if tr'.cand.isSome then
        pure ((none, (none, none)),
          hop2BridgeHaltedEnc C s chall ((st, aux), ({ tr with cand := tr'.cand }, honestWires)))
      else
        let out := sm.send (s1.st party) m rCoins
        let s' := s1.record 3 party out.1
          ⟨⟨party, s1.epoch party, s1.idx party + 1⟩, m, out.2⟩ isChall
        pure ((some out.2, (none, none)),
          hop2BridgeHaltedEnc C s chall ((s', aux), (tr', (out.2, party) :: honestWires))) := by
  intro P sm
  let CoinI := coinOnlyIface ℓ Pt
  let tPre : Ty ASig := .prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (.prod PlainT BV512)
  let tIn : Ty ASig := .prod (hop2HaltedStTy ℓ Pt) (.prod .bool (.opt tPre))
  set ρ₀ : Env [tIn] :=
    .cons (hop2BridgeHaltedEnc C s chall ((st, aux), (tr, honestWires)),
      (ReductionDsl.partyToBool party,
        preOpt.map fun x => (liftVal (Pt := Pt) (e2eGsEnc x.1), x.2))) .nil
  dsimp only [hop2SendAfterPreTrackC]
  rw [comp_eval_caseOpt]
  have hopt0 : (Expr.snd (.snd (Expr.v0 (O := AOps)))).eval ρ₀ =
      preOpt.map (fun x => (liftVal (Pt := Pt) (e2eGsEnc x.1), x.2)) := rfl
  rw [hopt0]
  cases preOpt with
  | none => rfl
  | some val =>
    rcases val with ⟨s1, m, rCoins⟩
    obtain ⟨hgParty, htr1_le, hcp1_le⟩ := hPre s1 m rCoins rfl
    dsimp only [Option.map_some]
    set ρ₁ : Env [tPre, tIn] :=
      .cons (liftVal (Pt := Pt) (e2eGsEnc s1), (m, rCoins)) ρ₀
    rw [comp_eval_bind, hM.embedCoin_eq, compCoinToPrf_eval_eq_liftM]
    have hBOk : CryptoVerification.SpqrV1Sync.SendTotal.BOkTight
        ((kemTrackEnc (kemBridgeToRef tr)).st party) := hTrQ.bOk party
    have hSentLen : (kemTrackEnc (kemBridgeToRef tr)).sentB.length ≤ q := hTrQ.sentB_len
    have hstepEval :=
      Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDsl.stepKemFailSendPairC_eval
        (Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase.sessionEmbed
          ℓ Pt C K Dh encPt encT decT lam) q
        (I := CoinI)
        (hstTr C K Dh encPt encT decT lam (.fst .v1))
        (.fst (.snd .v1)) (.snd (.snd .v0)) ρ₁
        (kemTrackEnc (kemBridgeToRef tr)) party rCoins rfl rfl rfl hBOk hSentLen
    rw [hstepEval]
    dsimp only
    rw [CryptoGames.Ratchet.LibsignalSim.simStepKemFailSend_kemTrackEnc, ← kemBridgeToRef_stepSend]
    set tr' :=
      Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.stepKemFailSend C.F K tr party
        rCoins
    have hwithCand :
        ({ kemTrackEnc (kemBridgeToRef tr) with cand := (kemTrackEnc (kemBridgeToRef tr')).cand } :
          CryptoGames.Ratchet.LibsignalSim.SimKemFailTrack C.F) =
          kemTrackEnc (kemBridgeToRef { tr with cand := tr'.cand }) := rfl
    have hencEq : ∀ (t : CryptoGames.Ratchet.LibsignalSim.SimKemFailTrack C.F),
        Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase.kemTrackAtomicEnc
          (ℓ := ℓ) (Pt := Pt) t = kemTrackAtomicEnc (ℓ := ℓ) (Pt := Pt) t := fun _ => rfl
    rw [hwithCand, hencEq, hencEq]
    simp only [liftM_pure, pure_bind]
    let tTrPair : Ty ASig := .prod (kemTrackT ℓ Pt) (kemTrackT ℓ Pt)
    set ρ₂ : Env [tTrPair, tPre, tIn] :=
      .cons (kemTrackAtomicEnc (kemTrackEnc (kemBridgeToRef tr')),
             kemTrackAtomicEnc (kemTrackEnc (kemBridgeToRef { tr with cand := tr'.cand }))) ρ₁
    rw [comp_eval_caseOpt]
    have hcandEval :
        (trE_cand (.fst (Expr.v0 (O := AOps)))).eval ρ₂ =
          tr'.cand.map
            Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost.kemCandVecToBv := rfl
    rw [hcandEval]
    cases hcand : tr'.cand with
    | none =>
      simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      rw [comp_eval_bind_ret, comp_eval_bind, hM.embedCoin_eq, compCoinToPrf_eval_eq_liftM,
        wk1Comp_eval]
      let tPostE2E : Ty ESig := .prod (e2eGsTy ℓ)
        (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
          CryptoVerification.E2E.Costed.BV512))
      let argPost : tPostE2E.denote := (e2eGsEnc s1, (partyEnc party, (m, rCoins)))
      have hpostLift :
          (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
            (sendPostE2EC (ℓ := ℓ) (Pt := Pt) C K encT decT q isChall)).eval
            (.cons
              ((Expr.pair (O := AOps) (.fst .v1) (.pair (.fst (.snd .v2)) (.snd .v1))).eval ρ₂)
              .nil) =
          liftVal (Pt := Pt) <$>
            (sendPostE2EC (ℓ := ℓ) (Pt := Pt) C K encT decT q isChall).eval
              (.cons argPost .nil) := by
        convert liftCompCoins_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
          (sendPostE2EC (ℓ := ℓ) (Pt := Pt) C K encT decT q isChall) (.cons argPost .nil) using 2
        cases party <;> rfl
      rw [hpostLift, eval_sendPostE2EC C K encT decT idA idB q isChall s s1 party m rCoins
        hgParty htr1_le hcp1_le]
      simp only [map_pure, liftM_pure, pure_bind, comp_eval_ret]
      have hpBool : ReductionDsl.partyToBool party = partyEnc party := by cases party <;> rfl
      simp only [hop2BridgeHaltedEnc, hop2HaltedEnc, kemSessionBridgeToRef, hop2FullEnc,
        hstBase, hstWires, hstMk, stS, stAux, stChall, stMk,
        Expr.eval, Expr.v0, Expr.v2, Expr.v4, Env.get, List.map_cons, hpBool, liftVal, hcand,
        ρ₂, ρ₁, ρ₀]
      rfl
    | some p =>
      simp only [Option.map_some, Option.isSome_some, ↓reduceIte, comp_eval_ret]
      simp only [hop2BridgeHaltedEnc, hop2HaltedEnc, kemSessionBridgeToRef,
        hstBase, hstWires, hstMk, Expr.eval, Expr.v1, Expr.v3, Env.get, hcand, ρ₂, ρ₁, ρ₀]

theorem hop2StepTrackC_eval_and_inv
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      (extractPtPrfIface ℓ Pt))
    {stepOf : BitVec 256 → Pt → Hop2Comp Pt (BitVec 256)}
    (hM : Hop2EvalSpec M stepOf)
    (q qRem qep k : ℕ) (s : BitVec 256) (chall : BitVec 256 × BitVec 256)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (aux : Hop2Aux Pt)
    (tr : Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.KemFailTrackState C.F)
    (honestWires : List (Bytes × Party))
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (hQ : SmReachBounded C K q st) (hRem : SmReachBounded C K qRem st)
    (hAuxQ : Hop2AuxBounded q aux) (hAuxRem : Hop2AuxBounded qRem aux)
    (hTrQ : KemTrackDeliverInv C.F K q (kemTrackEnc (kemBridgeToRef tr)))
    (hTrRem : KemTrackDeliverInv C.F K qRem (kemTrackEnc (kemBridgeToRef tr)))
    (hWiresQ : honestWires.length ≤ q) (hWiresRem : honestWires.length ≤ qRem) :
    let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
    let hyb : Hop2Hyb Pt := ⟨k, chall, stepOf chall.1⟩
    (hop2StepTrackC C K Dh encPt encT decT lam M q qep k).eval
      (.cons (hop2BridgeHaltedEnc C (ℓ := ℓ) (Pt := Pt) s chall ((st, aux), (tr, honestWires)))
        (.cons ((e2eSessionCodec ℓ Pt).qenc sq) .nil)) =
      (fun out : ((CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range sq ×
            (GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt)) ×
            Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.KemFailSessionTrack C.F Bytes =>
        (liftVal (Pt := Pt)
          (smRenc (ℓ := ℓ) (stT := CryptoVerification.E2E.Costed.GhostStT) id sq out.1.1),
         hop2BridgeHaltedEnc C (ℓ := ℓ) (Pt := Pt) s chall (out.1.2, out.2))) <$>
        (((hop2ImplTrackHalted P K Dh encT decT qep s hyb (.inr sq)).run (st, aux)).run
          (tr, honestWires)) ∧
    (∀ r ∈ support
        (((hop2ImplTrackHalted P K Dh encT decT qep s hyb (.inr sq)).run (st, aux)).run
          (tr, honestWires)),
      SmReachBounded C K (qRem + 1) r.1.2.1 ∧
      Hop2AuxBounded (qRem + 1) r.1.2.2 ∧
      KemTrackDeliverInv C.F K (qRem + 1) (kemTrackEnc (kemBridgeToRef r.2.1)) ∧
      r.2.2.length ≤ qRem + 1) := by
  intro P hyb
  let CoinI := coinOnlyIface ℓ Pt
  let cfg : ConfigR (GhostState Bytes) (Plain ℓ) Bytes := configRefuseEarlyBobCorr decT encT
  let runC :
      Hop2Comp Pt
        (((unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range
            (.inr sq) ×
          (GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt)) ×
          Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.KemFailSessionTrack C.F Bytes) :=
    ((hop2ImplTrackHalted P K Dh encT decT qep s hyb (.inr sq)).run (st, aux)).run (tr, honestWires)
  change (hop2StepTrackC C K Dh encPt encT decT lam M q qep k).eval
      (.cons (hop2BridgeHaltedEnc C (ℓ := ℓ) (Pt := Pt) s chall ((st, aux), (tr, honestWires)))
        (.cons (t := smQT) (ReductionDsl.smQenc sq) .nil)) =
      (fun out =>
        (liftVal (Pt := Pt)
          (smRenc (ℓ := ℓ) (stT := CryptoVerification.E2E.Costed.GhostStT) id sq out.1.1),
         hop2BridgeHaltedEnc C (ℓ := ℓ) (Pt := Pt) s chall (out.1.2, out.2))) <$> runC ∧
    (∀ r ∈ support runC,
      SmReachBounded C K (qRem + 1) r.1.2.1 ∧
      Hop2AuxBounded (qRem + 1) r.1.2.2 ∧
      KemTrackDeliverInv C.F K (qRem + 1) (kemTrackEnc (kemBridgeToRef r.2.1)) ∧
      r.2.2.length ≤ qRem + 1)
  rcases sq with (((⟨party, m, optR⟩ | ⟨party, m0, m1, optR⟩) | ⟨party, c⟩) | ⟨party, c⟩) | party
  ·
    have hpBool : ReductionDsl.partyToBool party = partyEnc party := by cases party <;> rfl
    have hImplTr :
        runC =
          (((hop2LiftTrackHalted
              (Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.transmitRTrackHalted
                C.F K (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT)
                (party, m, optR))).run (st, aux)).run (tr, honestWires)) := rfl
    rw [hImplTr]
    refine ⟨?_, ?_⟩
    · dsimp only [hop2StepTrackC, ReductionDsl.smQenc]
      rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v1, Env.get]
      rw [comp_eval_bind_ret, comp_eval_bind, hM.embedCoin_eq, compCoinToPrf_eval_eq_liftM,
        wk1Comp_eval]
      let tTr : Ty ESig := .prod (e2eGsTy ℓ)
        (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
          (.opt CryptoVerification.E2E.Costed.BV512)))
      let argTr : tTr.denote := (e2eGsEnc st, (partyEnc party, (m, optR)))
      have hpreLift :
          (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
            (trPreE2EC (ℓ := ℓ) (Pt := Pt) C K encT decT qep)).eval
            (.cons (liftVal (Pt := Pt) (e2eGsEnc st),
              (ReductionDsl.partyToBool party, (m, optR))) .nil) =
          liftVal (Pt := Pt) <$>
            (trPreE2EC (ℓ := ℓ) (Pt := Pt) C K encT decT qep).eval (.cons argTr .nil) := by
        convert liftCompCoins_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
          (trPreE2EC (ℓ := ℓ) (Pt := Pt) C K encT decT qep) (.cons argTr .nil) using 2
        cases party <;> cases optR <;> rfl
      simp only [hstBase, stGs, hop2BridgeHaltedEnc, hop2HaltedEnc, hop2FullEnc,
        Expr.eval, Expr.v0, Env.get]
      rw [hpreLift, eval_trPreE2EC C K encT decT qep st party m optR, liftM_hop2_map]
      simp only [hop2LiftTrackHalted,
        Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.transmitRTrackHalted,
        StateT.run_mk, StateT.run_bind, StateT.run_get,
        map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      cases hok : (configRefuseEarlyBobCorr decT encT).sendOK st party
      · simp only [Bool.not_false, Bool.true_or, ↓reduceIte, liftM_pure, pure_bind]
        rw [comp_eval_bind_ret, wk1Comp_eval]
        simp only [Expr.eval, Expr.v2, Expr.v3, Env.get, hpBool]
        simpa [hop2BridgeHaltedEnc, hop2HaltedEnc, hop2FullEnc, smRenc, liftVal] using
          hop2SendAfterPreTrackC_eval C K Dh encPt encT decT idA idB lam M hM q false s chall
            st aux tr honestWires party none hTrQ (by intro _ _ _ h; cases h)
      · cases hwin : st.win
        · simp only [Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
            StateT.run_bind, stateT_lift_prob_run2, pure_bind, bind_assoc, liftM_bind]
          refine bind_congr fun ⟨rCoins, bad⟩ => ?_
          cases hep : st.epMgmt 3 qep party bad with
          | none =>
            simp only [liftM_pure, pure_bind]
            rw [comp_eval_bind_ret, wk1Comp_eval]
            simp only [Expr.eval, Expr.v2, Expr.v3, Env.get, hpBool]
            simpa [hop2BridgeHaltedEnc, hop2HaltedEnc, hop2FullEnc, smRenc, liftVal] using
              hop2SendAfterPreTrackC_eval C K Dh encPt encT decT idA idB lam M hM q false s chall
                st aux tr honestWires party none hTrQ (by intro _ _ _ h; cases h)
          | some s1 =>
            obtain ⟨hst1, htr1, hcp1⟩ := epMgmt_preserve_fields hep
            simp only [StateT.run_bind, stateT_lift_get_run2, liftM_pure, pure_bind]
            rw [comp_eval_bind_ret, wk1Comp_eval]
            simp only [Expr.eval, Expr.v2, Expr.v3, Env.get]
            have hpost := hop2SendAfterPreTrackC_eval C K Dh encPt encT decT idA idB lam M hM
              q false s chall st aux tr honestWires party (some (s1, (m, rCoins))) hTrQ
              (fun s1' m' r' hEq => by
                cases hEq
                exact ⟨hst1 ▸ hQ.reach.party party,
                  htr1 ▸ hQ.lists.trans_le,
                  hcp1 ▸ hQ.lists.dedupComp_le⟩)
            have hliftSome :
                liftVal (Pt := Pt)
                  (t := .opt (.prod (e2eGsTy ℓ)
                    (.prod CryptoVerification.E2E.Costed.PlainT
                      CryptoVerification.E2E.Costed.BV512)))
                  (some (e2eGsEnc s1, (m, rCoins))) =
                some (liftVal (Pt := Pt) (e2eGsEnc s1), (m, rCoins)) := rfl
            simp only [Option.map, hop2BridgeHaltedEnc, hop2HaltedEnc, hop2FullEnc] at hpost
            rw [hliftSome, hpost]
            by_cases hc :
                (Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.stepKemFailSend
                  C.F K tr party rCoins).cand.isSome
            · simp only [hc, ↓reduceIte, StateT.run_bind, stateT_lift_set_run2, StateT.run_pure,
                pure_bind, liftM_pure, smRenc, liftVal]
              rfl
            · simp only [hc, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
                stateT_lift_set_run2, StateT.run_pure, pure_bind, liftM_pure, smRenc, liftVal]
              rfl
        · simp only [Bool.not_true, Bool.false_or, ↓reduceIte, liftM_pure, pure_bind]
          rw [comp_eval_bind_ret, wk1Comp_eval]
          simp only [Expr.eval, Expr.v2, Expr.v3, Env.get, hpBool]
          simpa [hop2BridgeHaltedEnc, hop2HaltedEnc, hop2FullEnc, smRenc, liftVal] using
            hop2SendAfterPreTrackC_eval C K Dh encPt encT decT idA idB lam M hM q false s chall
              st aux tr honestWires party none hTrQ (by intro _ _ _ h; cases h)
    · intro r hr
      dsimp only [hop2LiftTrackHalted] at hr
      rw [StateT.run_mk, StateT.run_mk, mem_support_bind_iff] at hr
      obtain ⟨z, hz, hrEq⟩ := hr
      simp only [support_pure, Set.mem_singleton_iff] at hrEq
      subst hrEq
      rw [← liftComp_eq_liftM, support_liftComp] at hz
      have hSm : SmReachBounded C K (qRem + 1) z.1.2 := by
        rcases transmitRTrackHalted_support C.F K (sessionSchemeU P ℓ) 3 qep cfg
            (party, m, optR) st (tr, honestWires) hz with hzNone | hzTr
        · rw [hzNone]; exact hRem.mono (Nat.le_succ qRem)
        · exact smReachBounded_transmitR C K idA idB ℓ 3 qep qRem s cfg (party, m, optR) hRem hzTr
      have hTrW : KemTrackDeliverInv C.F K (qRem + 1) (kemTrackEnc (kemBridgeToRef z.2.1)) ∧
          z.2.2.length ≤ qRem + 1 := by
        unfold Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.transmitRTrackHalted at hz
        simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
        cases hok : (configRefuseEarlyBobCorr decT encT).sendOK st party
        · simp only [hok, Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure,
            Set.mem_singleton_iff] at hz
          subst hz
          exact ⟨hTrRem.mono (Nat.le_succ qRem), Nat.le_trans hWiresRem (Nat.le_succ qRem)⟩
        · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hz
          cases hwin : st.win
          · simp only [hwin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
              stateT_lift_prob_run2, bind_assoc, pure_bind, mem_support_bind_iff] at hz
            obtain ⟨⟨rCoins, bad⟩, -, hz⟩ := hz
            cases hep : st.epMgmt 3 qep party bad with
            | none =>
              simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz
              exact ⟨hTrRem.mono (Nat.le_succ qRem), Nat.le_trans hWiresRem (Nat.le_succ qRem)⟩
            | some s1 =>
              simp only [hep, StateT.run_bind, stateT_lift_get_run2, pure_bind] at hz
              cases hcand :
                  (Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.stepKemFailSend
                    C.F K tr party rCoins).cand.isSome
              · simp only [hcand, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
                  pure_bind, stateT_lift_set_run2, StateT.run_pure, support_pure,
                  Set.mem_singleton_iff] at hz
                subst hz
                refine ⟨?_, by simp only [List.length_cons]; exact Nat.add_le_add_right hWiresRem 1⟩
                rw [kemBridgeToRef_stepSend]
                exact kemTrackDeliverInv_stepSend C.F K qRem (kemBridgeToRef tr) party rCoins hTrRem
              · simp only [hcand, ↓reduceIte, StateT.run_bind, stateT_lift_set_run2, pure_bind,
                  StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
                subst hz
                exact ⟨kemTrackDeliverInv_withCand C.F K (qRem + 1) (kemBridgeToRef tr) _
                    (hTrRem.mono (Nat.le_succ qRem)),
                  Nat.le_trans hWiresRem (Nat.le_succ qRem)⟩
          · simp only [hwin, ↓reduceIte, StateT.run_pure, support_pure,
              Set.mem_singleton_iff] at hz
            subst hz
            exact ⟨hTrRem.mono (Nat.le_succ qRem), Nat.le_trans hWiresRem (Nat.le_succ qRem)⟩
      exact ⟨hSm, hAuxRem.mono (Nat.le_succ qRem), hTrW.1, hTrW.2⟩
  ·
    have hpBool : ReductionDsl.partyToBool party = partyEnc party := by cases party <;> rfl
    have hImplCh :
        runC =
          (((hop2LiftTrackHalted
              (Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.challRTrackHalted
                C.F K (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT)
                (party, m0, m1, optR))).run (st, aux)).run (tr, honestWires)) := rfl
    rw [hImplCh]
    refine ⟨?_, ?_⟩
    · have hchallAllowed :
          ∀ t, (configRefuseEarlyBobCorr decT encT :
            ConfigR (GhostState Bytes) (Plain ℓ) Bytes).base.challAllowedIn t = true :=
        fun _ => rfl
      have hchallMsg :
          ∀ t, (configRefuseEarlyBobCorr decT encT :
            ConfigR (GhostState Bytes) (Plain ℓ) Bytes).base.challMsg t = none :=
        fun _ => rfl
      dsimp only [hop2StepTrackC, ReductionDsl.smQenc]
      rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v1, Env.get]
      rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v0, Env.get]
      rw [comp_eval_bind_ret, comp_eval_bind, hM.embedCoin_eq, compCoinToPrf_eval_eq_liftM,
        wk1Comp_eval]
      let tCh : Ty ESig := .prod (e2eGsTy ℓ)
        (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
          (.prod CryptoVerification.E2E.Costed.PlainT
            (.opt CryptoVerification.E2E.Costed.BV512))))
      let argCh : tCh.denote := (e2eGsEnc st, (partyEnc party, (m0, (m1, optR))))
      have hpreLift :
          (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
            (chPreE2EC (ℓ := ℓ) (Pt := Pt) C K encT decT qep)).eval
            (.cons (liftVal (Pt := Pt) (e2eGsEnc st),
              (ReductionDsl.partyToBool party, (m0, (m1, optR)))) .nil) =
          liftVal (Pt := Pt) <$>
            (chPreE2EC (ℓ := ℓ) (Pt := Pt) C K encT decT qep).eval (.cons argCh .nil) := by
        convert liftCompCoins_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
          (chPreE2EC (ℓ := ℓ) (Pt := Pt) C K encT decT qep) (.cons argCh .nil) using 2
        cases party <;> cases optR <;> rfl
      simp only [hstBase, stGs, hop2BridgeHaltedEnc, hop2HaltedEnc, hop2FullEnc,
        Expr.eval, Expr.v2, Env.get]
      rw [hpreLift, eval_chPreE2EC C K encT decT qep st party m0 m1 optR, liftM_hop2_map]
      simp only [hop2LiftTrackHalted,
        Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.challRTrackHalted,
        StateT.run_mk, StateT.run_bind, StateT.run_get,
        map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      cases hok : (configRefuseEarlyBobCorr decT encT).sendOK st party
      · simp only [Bool.not_false, Bool.true_or, ↓reduceIte, liftM_pure, pure_bind]
        rw [comp_eval_bind_ret, wk1Comp_eval]
        simp only [Expr.eval, Expr.v4, Env.get, hpBool]
        simpa [hop2BridgeHaltedEnc, hop2HaltedEnc, hop2FullEnc, smRenc, liftVal] using
          hop2SendAfterPreTrackC_eval C K Dh encPt encT decT idA idB lam M hM q true s chall
            st aux tr honestWires party none hTrQ (by intro _ _ _ h; cases h)
      · cases hwin : st.win
        · simp only [Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
            StateT.run_bind, stateT_lift_prob_run2, pure_bind, bind_assoc, liftM_bind]
          refine bind_congr fun ⟨rCoins, bad⟩ => ?_
          cases hep : st.epMgmt 3 qep party bad with
          | none =>
            simp only [liftM_pure, pure_bind]
            rw [comp_eval_bind_ret, wk1Comp_eval]
            simp only [Expr.eval, Expr.v4, Env.get, hpBool]
            simpa [hop2BridgeHaltedEnc, hop2HaltedEnc, hop2FullEnc, smRenc, liftVal] using
              hop2SendAfterPreTrackC_eval C K Dh encPt encT decT idA idB lam M hM q true s chall
                st aux tr honestWires party none hTrQ (by intro _ _ _ h; cases h)
          | some s1 =>
            obtain ⟨hst1, htr1, hcp1⟩ := epMgmt_preserve_fields hep
            simp only [hchallAllowed, Bool.not_true, Bool.or_false, hchallMsg, Option.getD_none]
            cases hsafe : s1.safeCh 3 party
            · simp only [Bool.not_false, ↓reduceIte, liftM_pure, pure_bind]
              rw [comp_eval_bind_ret, wk1Comp_eval]
              simp only [Expr.eval, Expr.v4, Env.get, hpBool]
              simpa [hop2BridgeHaltedEnc, hop2HaltedEnc, hop2FullEnc, smRenc, liftVal] using
                hop2SendAfterPreTrackC_eval C K Dh encPt encT decT idA idB lam M hM q true s chall
                  st aux tr honestWires party none hTrQ (by intro _ _ _ h; cases h)
            · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                StateT.run_bind, stateT_lift_get_run2, liftM_pure, pure_bind]
              rw [comp_eval_bind_ret, wk1Comp_eval]
              simp only [Expr.eval, Expr.v4, Env.get]
              let mCh := if st.b then m1 else m0
              have hpost := hop2SendAfterPreTrackC_eval C K Dh encPt encT decT idA idB lam M hM
                q true s chall st aux tr honestWires party (some (s1, (mCh, rCoins))) hTrQ
                (fun s1' m' r' hEq => by
                  cases hEq
                  exact ⟨hst1 ▸ hQ.reach.party party,
                    htr1 ▸ hQ.lists.trans_le,
                    hcp1 ▸ hQ.lists.dedupComp_le⟩)
              have hliftSome :
                  liftVal (Pt := Pt)
                    (t := .opt (.prod (e2eGsTy ℓ)
                      (.prod CryptoVerification.E2E.Costed.PlainT
                        CryptoVerification.E2E.Costed.BV512)))
                    (some (e2eGsEnc s1, (mCh, rCoins))) =
                  some (liftVal (Pt := Pt) (e2eGsEnc s1), (mCh, rCoins)) := rfl
              simp only [Option.map, hop2BridgeHaltedEnc, hop2HaltedEnc, hop2FullEnc] at hpost
              rw [hliftSome, hpost]
              by_cases hc :
                  (Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.stepKemFailSend
                    C.F K tr party rCoins).cand.isSome
              · simp only [hc, ↓reduceIte, StateT.run_bind, stateT_lift_set_run2, StateT.run_pure,
                  pure_bind, liftM_pure, smRenc, liftVal]
                rfl
              · simp only [hc, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
                  stateT_lift_set_run2, StateT.run_pure, pure_bind, liftM_pure, smRenc, liftVal]
                rfl
        · simp only [Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte, liftM_pure,
            pure_bind]
          rw [comp_eval_bind_ret, wk1Comp_eval]
          simp only [Expr.eval, Expr.v4, Env.get, hpBool]
          simpa [hop2BridgeHaltedEnc, hop2HaltedEnc, hop2FullEnc, smRenc, liftVal] using
            hop2SendAfterPreTrackC_eval C K Dh encPt encT decT idA idB lam M hM q true s chall
              st aux tr honestWires party none hTrQ (by intro _ _ _ h; cases h)
    · intro r hr
      dsimp only [hop2LiftTrackHalted] at hr
      rw [StateT.run_mk, StateT.run_mk, mem_support_bind_iff] at hr
      obtain ⟨z, hz, hrEq⟩ := hr
      simp only [support_pure, Set.mem_singleton_iff] at hrEq
      subst hrEq
      rw [← liftComp_eq_liftM, support_liftComp] at hz
      have hSm : SmReachBounded C K (qRem + 1) z.1.2 := by
        rcases challRTrackHalted_support C.F K (sessionSchemeU P ℓ) 3 qep cfg
            (party, m0, m1, optR) st (tr, honestWires) hz with hzNone | hzCh
        · rw [hzNone]; exact hRem.mono (Nat.le_succ qRem)
        · exact smReachBounded_challR C K idA idB ℓ 3 qep qRem s cfg (party, m0, m1, optR) hRem hzCh
      have hTrW : KemTrackDeliverInv C.F K (qRem + 1) (kemTrackEnc (kemBridgeToRef z.2.1)) ∧
          z.2.2.length ≤ qRem + 1 := by
        unfold Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.challRTrackHalted at hz
        simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
        cases hok : (configRefuseEarlyBobCorr decT encT).sendOK st party
        · simp only [hok, Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure,
            Set.mem_singleton_iff] at hz
          subst hz
          exact ⟨hTrRem.mono (Nat.le_succ qRem), Nat.le_trans hWiresRem (Nat.le_succ qRem)⟩
        · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hz
          cases hwin : st.win
          · simp only [hwin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
              stateT_lift_prob_run2, bind_assoc, pure_bind, mem_support_bind_iff] at hz
            obtain ⟨⟨rCoins, bad⟩, -, hz⟩ := hz
            cases hep : st.epMgmt 3 qep party bad with
            | none =>
              simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz
              exact ⟨hTrRem.mono (Nat.le_succ qRem), Nat.le_trans hWiresRem (Nat.le_succ qRem)⟩
            | some s1 =>
              have hchallAllowed2 :
                  (configRefuseEarlyBobCorr decT encT :
                    ConfigR (GhostState Bytes) (Plain ℓ) Bytes).base.challAllowedIn
                      (s1.epoch party) = true := rfl
              simp only [hep, hchallAllowed2, Bool.not_true, Bool.or_false] at hz
              cases hsafe : s1.safeCh 3 party
              · simp only [hsafe, Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure,
                  Set.mem_singleton_iff] at hz
                subst hz
                exact ⟨hTrRem.mono (Nat.le_succ qRem), Nat.le_trans hWiresRem (Nat.le_succ qRem)⟩
              · simp only [hsafe, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                  StateT.run_bind, stateT_lift_get_run2, pure_bind] at hz
                cases hcand :
                    (Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.stepKemFailSend
                      C.F K tr party rCoins).cand.isSome
                · simp only [hcand, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
                    pure_bind, stateT_lift_set_run2, StateT.run_pure, support_pure,
                    Set.mem_singleton_iff] at hz
                  subst hz
                  refine ⟨?_, by simp only [List.length_cons]; exact Nat.add_le_add_right hWiresRem 1⟩
                  rw [kemBridgeToRef_stepSend]
                  exact kemTrackDeliverInv_stepSend C.F K qRem (kemBridgeToRef tr) party rCoins
                    hTrRem
                · simp only [hcand, ↓reduceIte, StateT.run_bind, stateT_lift_set_run2, pure_bind,
                    StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
                  subst hz
                  exact ⟨kemTrackDeliverInv_withCand C.F K (qRem + 1) (kemBridgeToRef tr) _
                      (hTrRem.mono (Nat.le_succ qRem)),
                    Nat.le_trans hWiresRem (Nat.le_succ qRem)⟩
          · simp only [hwin, ↓reduceIte, StateT.run_pure, support_pure,
              Set.mem_singleton_iff] at hz
            subst hz
            exact ⟨hTrRem.mono (Nat.le_succ qRem), Nat.le_trans hWiresRem (Nat.le_succ qRem)⟩
      exact ⟨hSm, hAuxRem.mono (Nat.le_succ qRem), hTrW.1, hTrW.2⟩
  ·
    have hdl := hop2DlArmC_eval_and_inv C K Dh encPt encT decT idA idB lam M hM
      q qRem k s chall st aux party c hQ hRem hAuxQ hAuxRem
    have hImplDl :
        runC =
          ((fun rs => (rs, updateKemFailOnDeliver C.F K (tr, honestWires) (party, c) rs.1)) <$>
            (CryptoVerification.E2E.hop2Deliver P Dh encT decT s hyb (party, c)).run (st, aux)) := by
      dsimp only [runC, hop2ImplTrackHalted]
      rw [hop2DeliverTrackHalted_run]
      rfl
    rw [hImplDl]
    have hFindEq :
        List.findIdx?
          (fun wp : Bytes × Party =>
            @BEq.beq Bytes instBEqOfDecidableEq wp.1 c && wp.2 == party.other)
          honestWires.reverse =
        honestWires.reverse.findIdx? (fun wp => wp.1 == c && wp.2 == party.other) := by
      congr 1; ext ⟨w, p⟩
      have hbeq : @BEq.beq Bytes instBEqOfDecidableEq w c = (w == c) :=
        Bool.eq_iff_iff.mpr (by simp only [beq_iff_eq])
      rw [hbeq]
    refine ⟨?_, ?_⟩
    · dsimp only [hop2StepTrackC, ReductionDsl.smQenc, smRenc]
      rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v1, Env.get]
      rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v0, Env.get]
      rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
      rw [comp_eval_bind_ret]
      have hpBool : ReductionDsl.partyToBool party = partyEnc party := by cases party <;> rfl
      rw [eval_findHonestWireIdxE C K Dh encPt encT decT lam q
        (hstWires C K Dh encPt encT decT lam .v3) (.fst (.var .zero)) (.snd (.var .zero)) _
        honestWires party c rfl (by exact hpBool) rfl hWiresQ,
        comp_eval_bind_ret, comp_eval_bind, wk1Comp_eval]
      simp only [hstBase, hop2BridgeHaltedEnc, hop2HaltedEnc, kemSessionBridgeToRef,
        Expr.eval, Expr.v4, Env.get, hpBool]
      rw [hdl.1]
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      refine bind_congr fun ⟨rr?, ga'⟩ => ?_
      rw [comp_eval_ret]
      simp only [CryptoGames.SM.pair_eval, hstMk, hstWires]
      rw [kemOnDeliverPostAtomicE_eval (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q
        (.fst .v3) .v2 (.fst (.snd (.fst (.var .zero))))
        (hstTr C K Dh encPt encT decT lam .v6) _
        party (honestWires.reverse.findIdx? (fun wp => wp.1 == c && wp.2 == party.other))
        rr? (kemBridgeToRef tr) rfl rfl
        (by rcases rr? with _ | (_ | ⟨_, _, _ | _⟩) <;> rfl) rfl hTrQ]
      simp only [Expr.eval, Expr.v6, Env.get]
      congr 1
      unfold updateKemFailOnDeliver
      dsimp only
      rw [hFindEq]
      cases rr? with
      | none => rfl
      | some rr =>
        cases rr with
        | rejected => rfl
        | accepted _ _ _ =>
          cases honestWires.reverse.findIdx? (fun wp => wp.1 == c && wp.2 == party.other) with
          | none => rfl
          | some j =>
            dsimp only
            rw [kemBridgeToRef_stepDeliver]
            rfl
    · intro r hr
      simp only [map_eq_bind_pure_comp, Function.comp_def, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff] at hr
      obtain ⟨rs, hrs, rfl⟩ := hr
      obtain ⟨hSm, hAux⟩ := hdl.2 rs hrs
      refine ⟨hSm, hAux, ?_, ?_⟩
      · unfold updateKemFailOnDeliver
        dsimp only
        rw [hFindEq]
        cases rs.1 with
        | none => exact hTrRem.mono (Nat.le_succ qRem)
        | some rr =>
          cases rr with
          | rejected => exact hTrRem.mono (Nat.le_succ qRem)
          | accepted _ _ _ =>
            cases honestWires.reverse.findIdx? (fun wp => wp.1 == c && wp.2 == party.other) with
            | none => exact hTrRem.mono (Nat.le_succ qRem)
            | some j =>
              dsimp only
              rw [kemBridgeToRef_stepDeliver]
              exact (kemTrackDeliverInv_step C.F K qRem (kemBridgeToRef tr) party j hTrRem).mono
                (Nat.le_succ qRem)
      · unfold updateKemFailOnDeliver
        split <;> exact Nat.le_trans hWiresRem (Nat.le_succ qRem)
  ·
    have hij := hop2IjArmC_eval_and_inv C K Dh encPt encT decT idA idB lam M hM
      q qRem qep k s chall st aux party c hQ hRem hAuxQ hAuxRem
    have hImplIj :
        runC =
          (((liftHop2NoTrackM (Pt := Pt) (ℓ := ℓ) (F := C.F)
              (CryptoVerification.E2E.hop2Inject P Dh encT decT qep s hyb (party, c))).run
            (st, aux)).run (tr, honestWires)) := rfl
    rw [hImplIj, liftHop2NoTrackM_run]
    refine ⟨?_, ?_⟩
    · dsimp only [hop2StepTrackC, ReductionDsl.smQenc, smRenc]
      rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v1, Env.get]
      rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v0, Env.get]
      rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
      rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
      rw [comp_eval_bind_ret, comp_eval_bind, wk1Comp_eval]
      have hpBool : ReductionDsl.partyToBool party = partyEnc party := by cases party <;> rfl
      simp only [hstBase, hstSessionTr, hop2BridgeHaltedEnc, hop2HaltedEnc, kemSessionBridgeToRef,
        Expr.eval, Expr.v4, Env.get, hpBool]
      rw [hij.1]
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, comp_eval_ret]
      refine bind_congr fun out => ?_
      simp only [Expr.eval, Expr.v6, Env.get]
    · intro r hr
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
      obtain ⟨rs, hrs, rfl⟩ := hr
      obtain ⟨hSm, hAux⟩ := hij.2 rs hrs
      exact ⟨hSm, hAux, hTrRem.mono (Nat.le_succ qRem),
        Nat.le_trans hWiresRem (Nat.le_succ qRem)⟩
  ·
    have hImplCr :
        runC =
          (((liftHop2NoTrackM (Pt := Pt) (ℓ := ℓ) (F := C.F)
              (hop2Lift (corrR (configRefuseEarlyBobCorr decT encT) party))).run
            (st, aux)).run (tr, honestWires)) := rfl
    rw [hImplCr, liftHop2NoTrackM_run]
    refine ⟨?_, ?_⟩
    · dsimp only [hop2StepTrackC, ReductionDsl.smQenc]
      rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v1, Env.get]
      rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v0, Env.get]
      rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
      rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
      rw [comp_eval_bind_ret, comp_eval_bind, hM.embedCoin_eq, compCoinToPrf_eval_eq_liftM,
        wk1Comp_eval]
      let tCr : Ty ESig := .prod (e2eGsTy ℓ) .bool
      let argCr : tCr.denote := (e2eGsEnc st, partyEnc party)
      have hcrLift :
          (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
            (drCrArmC (I := coinE2EIface CoinI) (P := zeroPqxdhPrims) (C := C) (K := K)
              (decT := decT) (encT := encT) q
              (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0))).eval
            (.cons (liftVal (Pt := Pt) (e2eGsEnc st), ReductionDsl.partyToBool party) .nil) =
          liftVal (Pt := Pt) <$>
            (drCrArmC (I := coinE2EIface CoinI) (P := zeroPqxdhPrims) (C := C) (K := K)
              (decT := decT) (encT := encT) q
              (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0)).eval (.cons argCr .nil) := by
        convert liftCompCoins_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
          (drCrArmC (I := coinE2EIface CoinI) (P := zeroPqxdhPrims) (C := C) (K := K)
            (decT := decT) (encT := encT) q
            (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0)) (.cons argCr .nil) using 2
        cases party <;> rfl
      dsimp only [Expr.v0] at hcrLift
      simp only [hstBase, hstSessionTr, stS, stGs, stAux, stChall, stMk,
        hop2BridgeHaltedEnc, hop2HaltedEnc, kemSessionBridgeToRef, hop2FullEnc,
        Expr.eval, Expr.v4, Env.get]
      rw [hcrLift]
      have hcr := drCrArmC_eval (I := coinE2EIface CoinI) (P := zeroPqxdhPrims) (C := C) (K := K)
        (decT := decT) (encT := encT) q
        (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0) (.cons argCr .nil)
        st party hQ.lists rfl rfl
      dsimp only [Expr.v0, CoinI] at hcr
      rw [hcr, coinE2E_coinOnly_liftP (ℓ := ℓ) (Pt := Pt), liftM_hop2_map, liftM_hop2_map]
      simp only [hop2Lift, StateT.run_mk, map_eq_bind_pure_comp, Function.comp_def,
        bind_assoc, pure_bind, comp_eval_ret, Prod.map, smRenc]
      refine bind_congr fun ⟨st?, s'⟩ => congrArg pure ?_
      cases st? <;> simp only [Expr.eval, Expr.v6, Env.get] <;> rfl
    · intro r hr
      simp only [hop2Lift, StateT.run_mk, bind_assoc, pure_bind,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
      obtain ⟨⟨st?, gs'⟩, hgs', rfl⟩ := hr
      rw [← liftComp_eq_liftM, support_liftComp] at hgs'
      exact ⟨smReachBounded_corrR C K ℓ qRem cfg party hRem hgs',
        hAuxRem.mono (Nat.le_succ qRem),
        hTrRem.mono (Nat.le_succ qRem),
        Nat.le_trans hWiresRem (Nat.le_succ qRem)⟩

end StepEval

end Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2Eval

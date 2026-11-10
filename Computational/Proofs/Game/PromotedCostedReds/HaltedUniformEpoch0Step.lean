/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.HaltedUniformEpoch0Init -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.DrSessionSim -- proof-setup: allow-public-import
import Computational.Proofs.Game.PromotedCostedReds.DrSessionSimSize
import Computational.Proofs.Game.PromotedCostedReds.SimFig8State
import Computational.Proofs.Game.PromotedCostedReds.KemFailRedSendCorrSub
public import Computational.Proofs.Game.PromotedCostedReds.KemFailRedSendCorrCost -- proof-setup: allow-public-import
import Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitnessSub
import Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost

/-!
# Tracker-Halted Step Handler for `uniformStart`

Constructs the 5-oracle step handler `r1OracleStepTrackC` over `atomicSessionOps` and
`coinOnlyIface` for `configR1OnCurve`, and proves its query, cost, size, and evaluation lemmas.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.HaltedUniformEpoch0Step

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Env Ops Iface Expr Comp
  bits atomicSig atomicSessionOps coinOnlyIface e2eSessionCodec
  BV256 BV512 B PlainT)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.Ratchet.LibsignalInst (ratchetKeyAdmissible configR1OnCurve)
open CryptoGames.Ratchet.LibsignalSim (kemTrackEnc)
open CryptoGames.SM (GameState samIfNec deliverR injectR corrR
  partyEnc posEnc orE pGet pSet pair_eval orE_eval pGet_eval)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey GhostState)
open CryptoGames.LibsignalSM.Proofs.Refinement (KemFailTrackState stepKemFailSend)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.E2E (Bytes liftStateT paramsIdsWithSpqr sessionSchemeFixedSpk)
open CryptoVerification.E2E.Costed (e2eSig e2eOps smQT smQenc smRT recvResultT recvResultEnc)
open Computational.Proofs.E2E.Dsl.SmReachInvParty (PartyReachInv)
open Computational.Proofs.E2E.Dsl.SmReachInv (dedupComp SmReachBounded)
open Computational.Proofs.E2E.Dsl.DrSessionSimSend (drSendC drSendC_queries drSendC_cost
  drSendC_eval)
open Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping (partyToBool_eq_partyEnc smRenc smRCorrE
  e2eGsTy e2eGsEnc e2eGsSt e2eGsB e2eGsWin e2eGsEpoch e2eGsIdx
  e2eSendOKE eval_e2eSendOKE cost_e2eSendOKE_le
  e2eEpMgmtE eval_e2eEpMgmtE cost_e2eEpMgmtE_le
  e2eSafeChE eval_e2eSafeChE cost_e2eSafeChE_le
  e2eRecordE eval_e2eRecordE cost_e2eRecordE_le
  e2eCorrAllowedE e2eInWindowE e2eAfterCorrAllowedE)
open Computational.Proofs.E2E.Dsl.SpqrSim (spqrDslHooks)
open Computational.Proofs.E2E.Dsl.DrSessionSim (mkE2ECoinSamplers
  e2eSamIfNec512C e2eSamIfNec512C_queries_zero e2eSamIfNec512C_cost e2eSamIfNec512C_eval
  drDlArmC drIjArmC drDlArmC_cost drIjArmC_cost drDlArmC_eval drIjArmC_eval)
open Computational.Proofs.Game.PromotedCostedReds.DrSessionSimSize (drSendC_spqr_size_le
  drDlArmC_spqr_size_le drIjArmC_spqr_size_le
  size_smRCorrE_le size_e2eSendOKE_le size_e2eEpMgmtE_le size_e2eSafeChE_le size_e2eRecordE_le
  size_e2eCorrAllowedE_le size_e2eInWindowE_le size_e2eAfterCorrAllowedE_le)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge (sessPureOp sessSpqrKemOp
  zeroPqxdhPrims liftTy liftVal coinE2EIface coinE2ESamplers
  liftCompCoins liftCompCoins_queries_zero liftCompCoins_cost liftCompCoins_eval renComp_cost)
open Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon (comp_eval_ret comp_eval_bind
  comp_eval_bind_ret comp_eval_ite comp_eval_caseOpt comp_eval_caseSum
  liftP_unif_eq_self liftVal_smQenc liftCompCoins_size_le renComp_size)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8State (sOpPure sOpSpqr eLet)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedInit (kemTrackT kemTrackAtomicEnc)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedSendCorrCost (boolOrE boolEqE
  trE_e trE_c trE_st trE_sentB trE_sendCtr trE_cand trMk
  bytes2EqLitE issue1275ScanStepE swapPairsStepE issue1275FixEsC honestExchangeFailsAtomicC
  encRandBvAtomicE isKeysUnsampledV1E isHeaderReceivedV1E ekSideIsAE nextKemCoinsAtomicE
  nextKemCandAtomicC stepPostKemSendE stepKemFailSendAtomicC
  stepKemFailSendAtomicC_queries_zero stepKemFailSendAtomicC_cost)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedSendCorrSub (stepKemFailSendAtomicC_eval)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitness (KemTrackDeliverInv
  kemOnDeliverPostAtomicE_eval)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitnessSub
  (kemOnDeliverPostAtomicE kemOnDeliverPostAtomicE_cost kemOnDeliverPostAtomicE_descBits_le)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost (kemCandVecToBv
  atomicSessionOpDescBits atomicExprDescBits atomicSessionOps_opSize_le varIdx
  expr_size_le_atomicExprDescBits)
open Computational.Proofs.Game.PromotedCostedReds.HaltedUniformEpoch0Init (callSub1C
  callSub1C_queries callSub1C_cost callSub1C_size callSub1C_eval
  transmitRSessionTrackHalted challRSessionTrackHalted deliverRSessionTrackHalted
  oracleImplRSessionTrackHalted sessionHaltedStTy kemSessionTrackEnc sessionHaltedEnc
  findRevHonestWiresIdxE findRevHonestWiresIdxE_eval findRevHonestWiresIdxE_cost
  findRevHonestWiresIdxE_size
  noAliceBelow10E r1CrArmC r1CrArmC_queries r1CrArmC_cost r1CrArmC_eval)

section StepHalted

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {C : Crypto} {K : MlKem}
  {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
  {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ESig" => e2eSig ℓ
local notation "EOps" => e2eOps ℓ zeroPqxdhPrims C K decT encT
local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

@[expose, reducible] def preSendInTy (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .prod (e2eGsTy ℓ)
    (.prod .bool
      (.prod CryptoVerification.E2E.Costed.PlainT
        (.prod (.opt CryptoVerification.E2E.Costed.PlainT)
          (.opt CryptoVerification.E2E.Costed.BV512))))

@[expose, reducible] def preSendOutTy (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .prod (e2eGsTy ℓ)
    (.prod .bool
      (.prod CryptoVerification.E2E.Costed.PlainT
        (.prod CryptoVerification.E2E.Costed.BV512 .bool)))

@[expose] def preSendE2EC (Δ qep : ℕ) :
    Comp EOps (coinE2EIface (coinOnlyIface ℓ Pt))
      [preSendInTy ℓ] (.opt (preSendOutTy ℓ)) :=
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT)
    (coinOnlyIface ℓ Pt)
  .ite (orE (.not (e2eSendOKE (.fst .v0) (.fst (.snd .v0)))) (e2eGsWin (.fst .v0)))
    (.ret .none)
    (.bind (e2eSamIfNec512C coins (.snd (.snd (.snd (.snd .v0)))))
      (.caseOpt (e2eEpMgmtE Δ qep (.fst .v1) (.fst (.snd .v1)) (.snd .v0))
        (.ret .none)
        (.caseOpt (.fst (.snd (.snd (.snd .v2))))
          (.ret (.some (.pair .v0
            (.pair (.fst (.snd .v2))
              (.pair (.fst (.snd (.snd .v2)))
                (.pair (.fst .v1) (.bool false)))))))
          (.ite (.not (e2eSafeChE Δ .v1 (.fst (.snd .v3))))
            (.ret .none)
            (.ret (.some (.pair .v1
              (.pair (.fst (.snd .v3))
                (.pair
                  (.ite (e2eGsB (.fst .v3)) .v0 (.fst (.snd (.snd .v3))))
                  (.pair (.fst .v2) (.bool true)))))))))))

theorem preSendE2EC_queries_zero (Δ qep : ℕ) (w : Empty → ℕ) :
    (preSendE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT)
      Δ qep).queries w (fun _ => 0) = 0 := by
  simp [preSendE2EC, Comp.queries, e2eSamIfNec512C_queries_zero]

theorem preSendE2EC_cost (Δ qep : ℕ) :
    (preSendE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT)
      Δ qep).cost ≤ 1500 + 2 * bits Δ + bits qep := by
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT)
    (coinOnlyIface ℓ Pt)
  have hok := cost_e2eSendOKE_le (ℓ := ℓ) (O' := EOps)
    (.fst .v0 : Expr EOps [preSendInTy ℓ] (e2eGsTy ℓ)) (.fst (.snd .v0))
  have hsam := e2eSamIfNec512C_cost coins
    (.snd (.snd (.snd (.snd .v0))) : Expr EOps [preSendInTy ℓ] (.opt CryptoVerification.E2E.Costed.BV512))
  have hep := cost_e2eEpMgmtE_le (ℓ := ℓ) (O' := EOps) Δ qep
    (.fst .v1 : Expr EOps [.prod CryptoVerification.E2E.Costed.BV512 .bool, preSendInTy ℓ] (e2eGsTy ℓ))
    (.fst (.snd .v1)) (.snd .v0)
  have hsafe := cost_e2eSafeChE_le (ℓ := ℓ) (O' := EOps) Δ
    (.v1 : Expr EOps [CryptoVerification.E2E.Costed.PlainT, e2eGsTy ℓ,
      .prod CryptoVerification.E2E.Costed.BV512 .bool, preSendInTy ℓ] (e2eGsTy ℓ))
    (.fst (.snd .v3))
  dsimp only [coins] at hsam
  simp only [preSendE2EC, orE, e2eGsWin, e2eGsB, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hok hsam hep hsafe ⊢
  omega

@[expose] def postSendE2EC (q Δ : ℕ) :
    Comp EOps (coinE2EIface (coinOnlyIface ℓ Pt))
      [preSendOutTy ℓ]
      (.prod (CryptoVerification.E2E.Costed.B 32) (e2eGsTy ℓ)) :=
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  .bind
    (drSendC hooks (coinE2EIface (coinOnlyIface ℓ Pt))
      (.pair (pGet (e2eGsSt (.fst .v0)) (.fst (.snd .v0)))
        (.pair (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0)))))))
    (let st' := Expr.fst .v0
     let ct' := Expr.snd .v0
     let s1 := Expr.fst .v1
     let p1 := Expr.fst (.snd .v1)
     let m1 := Expr.fst (.snd (.snd .v1))
     let isCh1 := Expr.snd (.snd (.snd (.snd .v1)))
     let posE := Expr.pair p1
       (.pair (pGet (e2eGsEpoch s1) p1) (.add (pGet (e2eGsIdx s1) p1) (.nat 1)))
     .ret (.pair ct' (e2eRecordE q Δ s1 p1 st' posE m1 ct' isCh1)))

theorem postSendE2EC_queries_zero (q Δ : ℕ) (w : Empty → ℕ) :
    (postSendE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT)
      q Δ).queries w (fun _ => 0) = 0 := by
  simp [postSendE2EC, Comp.queries, drSendC_queries]

theorem postSendE2EC_cost (q Δ : ℕ) :
    (postSendE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT)
      q Δ).cost ≤ 2470000 + 10 * (ℓ / 32 + 1) + 135 * q + bits Δ := by
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  have hsend := drSendC_cost hooks (coinE2EIface (coinOnlyIface ℓ Pt))
    (.pair (pGet (e2eGsSt (.fst .v0)) (.fst (.snd .v0)))
      (.pair (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0))))) :
      Expr EOps [preSendOutTy ℓ] _)
  let Γ1 : List (Ty ESig) :=
    [.prod CryptoVerification.E2E.Costed.GhostStT (CryptoVerification.E2E.Costed.B 32),
     preSendOutTy ℓ]
  have hrec := cost_e2eRecordE_le (ℓ := ℓ) (O' := EOps) (Γ := Γ1) q Δ
    (.fst .v1) (.fst (.snd .v1)) (.fst .v0)
    (.pair (.fst (.snd .v1))
      (.pair (pGet (e2eGsEpoch (.fst .v1)) (.fst (.snd .v1)))
        (.add (pGet (e2eGsIdx (.fst .v1)) (.fst (.snd .v1))) (.nat 1))))
    (.fst (.snd (.snd .v1))) (.snd .v0) (.snd (.snd (.snd (.snd .v1))))
  have hb1 : bits 1 = 1 := rfl
  dsimp only [hooks] at hsend
  simp only [postSendE2EC, pGet, e2eGsSt, e2eGsEpoch, e2eGsIdx, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, hb1] at hsend hrec ⊢
  omega

@[expose] def classifyQryE {Γ : List (Ty ASig)} (qryE : Expr AOps Γ (liftTy (Pt := Pt) smQT)) :
    Expr AOps Γ
      (.sum (.prod .bool (.prod PlainT (.prod (.opt PlainT) (.opt BV512))))
        (.sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool))) :=
  .caseSum qryE
    (.inl (.pair (.fst .v0) (.pair (.fst (.snd .v0)) (.pair .none (.snd (.snd .v0))))))
    (.caseSum .v0
      (.inl (.pair (.fst .v0)
        (.pair (.fst (.snd .v0))
          (.pair (.some (.fst (.snd (.snd .v0)))) (.snd (.snd (.snd .v0)))))))
      (.inr .v0))

@[expose, reducible] def sendSomeContC (q Δ : ℕ) :
    Comp AOps (coinOnlyIface ℓ Pt)
      [liftTy (Pt := Pt) (preSendOutTy ℓ),
       .opt (liftTy (Pt := Pt) (preSendOutTy ℓ)),
       .prod .bool (.prod PlainT (.prod (.opt PlainT) (.opt BV512))),
       sessionHaltedStTy ℓ Pt, liftTy (Pt := Pt) smQT]
      (.prod (liftTy (Pt := Pt) (smRT CryptoVerification.E2E.Costed.GhostStT))
        (sessionHaltedStTy ℓ Pt)) :=
  let noneWire : Expr AOps _ (liftTy (Pt := Pt) (smRT CryptoVerification.E2E.Costed.GhostStT)) :=
    .pair .none (.pair .none .none)
  .bind
    (stepKemFailSendAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) q
      (.fst (.snd .v3)) (.fst (.snd .v0)) (.fst (.snd (.snd (.snd .v0)))))
    (.caseOpt (trE_cand (.fst .v0))
      (.bind
        (callSub1C
          (liftCompCoins (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
            (decT := decT) (lam := lam) rfl
            (postSendE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT)
              (encT := encT) q Δ))
          .v1)
        (.ret (.pair
          (.pair (.some (.fst .v0)) (.pair .none .none))
          (.pair (.snd .v0)
            (.pair (.fst .v1)
              (.cons (.pair (.fst .v0) (.fst (.snd .v2))) (.snd (.snd .v5))))))))
      (.ret (.pair noneWire
        (.pair (.fst .v5) (.pair (.snd .v1) (.snd (.snd .v5)))))))

@[expose, reducible] def sendArmC (q Δ qep : ℕ) :
    Comp AOps (coinOnlyIface ℓ Pt)
      [.prod .bool (.prod PlainT (.prod (.opt PlainT) (.opt BV512))),
       sessionHaltedStTy ℓ Pt, liftTy (Pt := Pt) smQT]
      (.prod (liftTy (Pt := Pt) (smRT CryptoVerification.E2E.Costed.GhostStT))
        (sessionHaltedStTy ℓ Pt)) :=
  let noneWire : Expr AOps _ (liftTy (Pt := Pt) (smRT CryptoVerification.E2E.Costed.GhostStT)) :=
    .pair .none (.pair .none .none)
  .bind
    (callSub1C
      (liftCompCoins (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) rfl
        (preSendE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT) Δ qep))
      (.pair (.fst .v1) .v0))
    (.caseOpt .v0 (.ret (.pair noneWire .v2))
      (sendSomeContC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) q Δ))

/-- Tracker-halted 5-oracle step handler over `atomicSessionOps` for `configR1OnCurve`. -/
@[expose] def r1OracleStepTrackC (q Δ qep : ℕ) :
    Comp AOps (coinOnlyIface ℓ Pt)
      [sessionHaltedStTy ℓ Pt, liftTy (Pt := Pt) smQT]
      (.prod (liftTy (Pt := Pt) (smRT CryptoVerification.E2E.Costed.GhostStT))
        (sessionHaltedStTy ℓ Pt)) :=
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT)
    (coinOnlyIface ℓ Pt)
  .caseSum (classifyQryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) .v1)
    (sendArmC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) q Δ qep)
    (.caseSum .v0
      (.bind
        (.ret (findRevHonestWiresIdxE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam) q
          (.snd (.snd .v2)) (.fst .v0) (.snd .v0)))
        (.bind
          (callSub1C
            (liftCompCoins (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
              (decT := decT) (lam := lam) rfl
              (drDlArmC hooks coins q
                (Γ := [.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))])
                (.fst .v0) (.snd .v0)))
            (.pair (.fst .v3) .v1))
          (let tr' := kemOnDeliverPostAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
             (encT := encT) (decT := decT) (lam := lam) q
             (.fst .v2) .v1 (.fst (.snd (.fst .v0))) (.fst (.snd .v4))
           .ret (.pair (.fst .v0) (.pair (.snd .v0) (.pair tr' (.snd (.snd .v4))))))))
      (.caseSum .v0
        (.bind
          (callSub1C
            (liftCompCoins (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
              (decT := decT) (lam := lam) rfl
              (drIjArmC hooks coins q Δ qep
                (Γ := [.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))])
                (.fst .v0) (.snd .v0)))
            (.pair (.fst .v3) .v0))
          (.ret (.pair (.fst .v0) (.pair (.snd .v0) (.snd .v4)))))
        (.bind
          (callSub1C
            (liftCompCoins (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
              (decT := decT) (lam := lam) rfl
              (r1CrArmC (C := C) (K := K) (decT := decT) (encT := encT)
                (I := coinE2EIface (coinOnlyIface ℓ Pt)) q
                (Γ := [.prod (e2eGsTy ℓ) .bool]) (.fst .v0) (.snd .v0)))
            (.pair (.fst .v3) .v0))
          (.ret (.pair (.fst .v0) (.pair (.snd .v0) (.snd .v4)))))))

theorem r1OracleStepTrackC_queries_zero (q Δ qep : ℕ) (w : Empty → ℕ) :
    (r1OracleStepTrackC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q Δ qep).queries
      w (fun _ => 0) = 0 := by
  simp [r1OracleStepTrackC, sendArmC, sendSomeContC, Comp.queries, callSub1C_queries,
    liftCompCoins_queries_zero, stepKemFailSendAtomicC_queries_zero]

theorem r1OracleStepTrackC_cost (q Δ qep : ℕ) :
    (r1OracleStepTrackC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q Δ qep).cost ≤
      165000000 + 320 * (ℓ / 32 + 1) + 15000 * q + 96 * bits Δ + 32 * bits qep +
        32 * bits (qep + 1) := by
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT)
    (coinOnlyIface ℓ Pt)
  have hpreL := liftCompCoins_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
    (preSendE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT) Δ qep)
  have hpreE := preSendE2EC_cost (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
    (decT := decT) (encT := encT) Δ qep
  have hpostL := liftCompCoins_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
    (postSendE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT) q Δ)
  have hpostE := postSendE2EC_cost (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
    (decT := decT) (encT := encT) q Δ
  have hdlL := liftCompCoins_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
    (drDlArmC hooks coins q
      (.fst .v0 : Expr EOps [.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))] _)
      (.snd .v0))
  have hdlE := drDlArmC_cost hooks coins q
    (.fst .v0 : Expr EOps [.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))] _)
    (.snd .v0)
  have hijL := liftCompCoins_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
    (drIjArmC hooks coins q Δ qep
      (.fst .v0 : Expr EOps [.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))] _)
      (.snd .v0))
  have hijE := drIjArmC_cost hooks coins q Δ qep
    (.fst .v0 : Expr EOps [.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))] _)
    (.snd .v0)
  have hcrL := liftCompCoins_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
    (r1CrArmC (C := C) (K := K) (decT := decT) (encT := encT)
      (I := coinE2EIface (coinOnlyIface ℓ Pt)) q
      (.fst .v0 : Expr EOps [.prod (e2eGsTy ℓ) .bool] _) (.snd .v0))
  have hcrE := r1CrArmC_cost (C := C) (K := K) (decT := decT) (encT := encT)
    (I := coinE2EIface (coinOnlyIface ℓ Pt)) q
    (.fst .v0 : Expr EOps [.prod (e2eGsTy ℓ) .bool] _) (.snd .v0)
  let scTy : Ty ASig := .prod .bool (.prod PlainT (.prod (.opt PlainT) (.opt BV512)))
  let rest3Ty : Ty ASig := .sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool)
  let Γ_sc3 : List (Ty ASig) :=
    [liftTy (Pt := Pt) (preSendOutTy ℓ),
     .opt (liftTy (Pt := Pt) (preSendOutTy ℓ)),
     scTy, sessionHaltedStTy ℓ Pt, liftTy (Pt := Pt) smQT]
  have hkf := stepKemFailSendAtomicC_cost (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ_sc3) q
    (.fst (.snd .v3)) (.fst (.snd .v0)) (.fst (.snd (.snd (.snd .v0))))
  let Γ_dl0 : List (Ty ASig) :=
    [.prod .bool (B 32), rest3Ty, sessionHaltedStTy ℓ Pt, liftTy (Pt := Pt) smQT]
  have hfind := findRevHonestWiresIdxE_cost (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ_dl0) q
    (.snd (.snd .v2)) (.fst .v0) (.snd .v0)
  let Γ_dl2 : List (Ty ASig) :=
    [.prod (liftTy (Pt := Pt) (smRT CryptoVerification.E2E.Costed.GhostStT))
       (liftTy (Pt := Pt) (e2eGsTy ℓ)),
     .opt .nat, .prod .bool (B 32), rest3Ty, sessionHaltedStTy ℓ Pt, liftTy (Pt := Pt) smQT]
  have hdel := kemOnDeliverPostAtomicE_cost (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ_dl2) q
    (.fst .v2) .v1 (.fst (.snd (.fst .v0))) (.fst (.snd .v4))
  dsimp only [hooks, coins] at hdlL hdlE hijL hijE
  simp only [r1OracleStepTrackC, sendArmC, sendSomeContC, classifyQryE, callSub1C, trE_cand,
    Comp.cost, Expr.cost, renComp_cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5]
    at hpreL hpostL hdlL hdlE hijL hijE hcrL hcrE hkf hfind hdel ⊢
  omega

private theorem size_coinDraw256 {Γ : List (Ty ESig)} :
    ((coinE2ESamplers (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT)
      (coinOnlyIface ℓ Pt)).draw256 (Γ := Γ)).size ≤ 4 := by
  simp [coinE2ESamplers, mkE2ECoinSamplers, Comp.size, Expr.size]

private theorem size_coinDraw512 {Γ : List (Ty ESig)} :
    ((coinE2ESamplers (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT)
      (coinOnlyIface ℓ Pt)).draw512 (Γ := Γ)).size ≤ 4 := by
  simp [coinE2ESamplers, mkE2ECoinSamplers, Comp.size, Expr.size]

theorem size_noAliceBelow10E_le {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (pE : Expr EOps Γ .bool) :
    (noAliceBelow10E (C := C) (K := K) (decT := decT) (encT := encT) gsE pE).size ≤
      gsE.size + pE.size + 15 := by
  have hb10 : bits 10 = 4 := by decide
  simp only [noAliceBelow10E, e2eGsEpoch, Expr.size, hb10]; omega

theorem r1CrArmC_size_le {ι : Type} {T : OracleSpec ι} {I : Iface ESig T}
    (q : ℕ) {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (crArg : Expr EOps Γ .bool) :
    (r1CrArmC (C := C) (K := K) (decT := decT) (encT := encT) (I := I) q gsE crArg).size ≤
      gsE.size + crArg.size + 2 * bits q + 950 := by
  let t0 : Ty ESig := .prod (e2eGsTy ℓ) .bool
  have hallow := size_e2eCorrAllowedE_le (ℓ := ℓ) (O' := EOps) q
    (.fst .v0 : Expr EOps (t0 :: Γ) (e2eGsTy ℓ)) (.snd .v0)
  have hwin := size_e2eInWindowE_le (ℓ := ℓ) (O' := EOps)
    (.fst .v0 : Expr EOps (t0 :: Γ) (e2eGsTy ℓ)) (.snd .v0)
  have hcorrOK := size_noAliceBelow10E_le (C := C) (K := K) (decT := decT) (encT := encT)
    (.fst .v0 : Expr EOps (t0 :: Γ) (e2eGsTy ℓ)) (.snd .v0)
  have hafter := size_e2eAfterCorrAllowedE_le (ℓ := ℓ) (O' := EOps)
    (.fst .v0 : Expr EOps (t0 :: Γ) (e2eGsTy ℓ)) (.snd .v0)
  have hsm0 := size_smRCorrE_le (ℓ := ℓ) (O' := EOps) (Γ := t0 :: Γ)
    (stT := CryptoVerification.E2E.Costed.GhostStT) .none
  have hsm1 := size_smRCorrE_le (ℓ := ℓ) (O' := EOps) (Γ := t0 :: Γ)
    (stT := CryptoVerification.E2E.Costed.GhostStT)
    (.some (pGet (e2eGsSt (.fst .v0)) (.snd .v0)))
  simp only [r1CrArmC, orE, pGet, e2eGsSt, e2eGsWin, Comp.size, Expr.size,
    Expr.v0] at hallow hwin hcorrOK hafter hsm0 hsm1 ⊢
  omega

theorem preSendE2EC_size_le (Δ qep : ℕ) :
    (preSendE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT)
      Δ qep).size ≤ 2 * bits Δ + 2 * bits qep + 850 := by
  have hd := size_coinDraw512 (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT)
    (Γ := [preSendInTy ℓ])
  have hok := size_e2eSendOKE_le (ℓ := ℓ) (O' := EOps)
    (.fst .v0 : Expr EOps [preSendInTy ℓ] (e2eGsTy ℓ)) (.fst (.snd .v0))
  have hep := size_e2eEpMgmtE_le (ℓ := ℓ) (O' := EOps) Δ qep
    (.fst .v1 : Expr EOps [.prod CryptoVerification.E2E.Costed.BV512 .bool, preSendInTy ℓ] (e2eGsTy ℓ))
    (.fst (.snd .v1)) (.snd .v0)
  have hsafe := size_e2eSafeChE_le (ℓ := ℓ) (O' := EOps) Δ
    (.v1 : Expr EOps [CryptoVerification.E2E.Costed.PlainT, e2eGsTy ℓ,
      .prod CryptoVerification.E2E.Costed.BV512 .bool, preSendInTy ℓ] (e2eGsTy ℓ))
    (.fst (.snd .v3))
  simp only [preSendE2EC, e2eSamIfNec512C, orE, e2eGsWin, e2eGsB, Comp.size, Expr.size,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hok hep hsafe hd ⊢
  omega

theorem postSendE2EC_size_le (q Δ : ℕ) :
    (postSendE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT)
      q Δ).size ≤ 2 * bits q + bits Δ + 20500 := by
  have hsend := drSendC_spqr_size_le (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) (coinE2EIface (coinOnlyIface ℓ Pt))
    (.pair (pGet (e2eGsSt (.fst .v0)) (.fst (.snd .v0)))
      (.pair (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0))))) :
      Expr EOps [preSendOutTy ℓ] _)
  let Γ1 : List (Ty ESig) :=
    [.prod CryptoVerification.E2E.Costed.GhostStT (CryptoVerification.E2E.Costed.B 32),
     preSendOutTy ℓ]
  have hrec := size_e2eRecordE_le (ℓ := ℓ) (O' := EOps) (Γ := Γ1) q Δ
    (.fst .v1) (.fst (.snd .v1)) (.fst .v0)
    (.pair (.fst (.snd .v1))
      (.pair (pGet (e2eGsEpoch (.fst .v1)) (.fst (.snd .v1)))
        (.add (pGet (e2eGsIdx (.fst .v1)) (.fst (.snd .v1))) (.nat 1))))
    (.fst (.snd (.snd .v1))) (.snd .v0) (.snd (.snd (.snd (.snd .v1))))
  have hb1 : bits 1 = 1 := rfl
  simp only [postSendE2EC, pGet, e2eGsSt, e2eGsEpoch, e2eGsIdx, Comp.size, Expr.size,
    Expr.v0, Expr.v1, hb1] at hsend hrec ⊢
  omega

private theorem issue1275FixEsC_size_le {Γ : List (Ty ASig)} (esE : Expr AOps Γ (B 2080)) :
    (issue1275FixEsC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) esE).size ≤ esE.size + 400 := by
  have hb : bits 1 = 1 ∧ bits 2 = 2 ∧ bits 256 = 9 ∧ bits 1024 = 11 ∧ bits 1536 = 11 ∧
      bits 2048 = 12 := by decide
  have haP : ∀ (o : _root_.ReductionDsl.AtomicPureOp),
      (AOps).opSize (.inl (.inl (.inl (.inl o)))) = o.opSize := fun _ => rfl
  have hscan : (issue1275ScanStepE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := B 2080 :: Γ)).size ≤ 135 := by
    simp only [issue1275ScanStepE, bytes2EqLitE, boolOrE, eLet, sOpPure, sessPureOp,
      Expr.size, haP, _root_.ReductionDsl.AtomicPureOp.opSize, List.length_cons, List.length_nil,
      Expr.v0, Expr.v1, hb]; omega
  have hswap : (swapPairsStepE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam)
      (Γ := .prod (B 512) (.opt .bool) :: B 2080 :: Γ)).size ≤ 60 := by
    simp only [swapPairsStepE, sOpPure, sessPureOp, Expr.size, haP,
      _root_.ReductionDsl.AtomicPureOp.opSize, Expr.v0, hb]; omega
  dsimp only [issue1275FixEsC]
  generalize issue1275ScanStepE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := B 2080 :: Γ) = eScan at hscan ⊢
  generalize swapPairsStepE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := .prod (B 512) (.opt .bool) :: B 2080 :: Γ) = eSwap at hswap ⊢
  simp only [sOpPure, sessPureOp, Comp.size, Expr.size, haP,
    _root_.ReductionDsl.AtomicPureOp.opSize, List.length_nil, Expr.v0, Expr.v1, Expr.v2, hb]
  omega

private theorem stepKemFailSendAtomicC_size_le (q : ℕ) {Γ : List (Ty ASig)}
    (trE : Expr AOps Γ (kemTrackT ℓ Pt)) (qBE : Expr AOps Γ .bool) (rqE : Expr AOps Γ BV512) :
    (stepKemFailSendAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) q trE qBE rqE).size ≤
      trE.size + qBE.size + rqE.size + bits (q + 1) + 1200 := by
  let Γ0 := Ty.prod (kemTrackT ℓ Pt) (.prod .bool BV512) :: Γ
  let Γc := BV512 :: Ty.sum BV512 (.prod BV512 BV256) ::
    Ty.prod (kemTrackT ℓ Pt) (.prod .bool BV512) :: Γ0
  have hb1 : bits 1 = 1 := rfl
  have hb2 : bits 2 = 2 := rfl
  have haP : ∀ (o : _root_.ReductionDsl.AtomicPureOp),
      (AOps).opSize (.inl (.inl (.inl (.inl o)))) = o.opSize := fun _ => rfl
  have haS : ∀ (o : _root_.ReductionDsl.AtomicSpqrKemOp),
      (AOps).opSize (.inr o) = 0 := fun _ => rfl
  have hfix := issue1275FixEsC_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (Γ := .prod (B 960) (.prod (B 2080) BV256) ::
      .prod (_root_.ReductionDsl.AtomicSpqrKemOp.kem768FromSeed.cod ℓ Pt) BV256 :: Γc)
    (.fst (.snd .v0))
  have hcand : (nextKemCandAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (Γ := Γ0) (.fst .v0) (.fst (.snd .v0)) (.snd (.snd .v0))).size ≤
      650 := by
    dsimp only [nextKemCandAtomicC, honestExchangeFailsAtomicC, encRandBvAtomicE,
      isHeaderReceivedV1E, ekSideIsAE, boolEqE, trE_cand, trE_st, trE_e, trE_c, pGet]
    simp only [sOpPure, sOpSpqr, sessPureOp, sessSpqrKemOp, Comp.size, Expr.size, haP, haS,
      _root_.ReductionDsl.AtomicPureOp.opSize, List.length_cons, List.length_nil,
      Expr.v0, Expr.v1, Expr.v2, Expr.v3, hb1, hb2] at hfix ⊢
    omega
  have hpost : (stepPostKemSendE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) q (Γ := .opt (.prod BV512 BV256) :: Γ0)
      (.fst .v1) (.fst (.snd .v1)) (.snd (.snd .v1)) .v0).size ≤ bits (q + 1) + 450 := by
    dsimp only [stepPostKemSendE, nextKemCoinsAtomicE, isKeysUnsampledV1E, isHeaderReceivedV1E,
      encRandBvAtomicE, eLet, trMk, trE_e, trE_c, trE_st, trE_sentB, trE_sendCtr,
      trE_cand, pGet, pSet]
    dsimp only [sOpPure, sOpSpqr, sessPureOp, sessSpqrKemOp, Expr.size, Expr.v0, Expr.v1, Expr.v2]
    simp only [haP, haS, _root_.ReductionDsl.AtomicPureOp.opSize, List.length_cons, List.length_nil,
      hb1]
    omega
  dsimp only [stepKemFailSendAtomicC] at hcand hpost ⊢
  simp only [Comp.size, Expr.size, Expr.v0, Expr.v1] at hcand hpost ⊢
  omega

theorem r1OracleStepTrackC_size_le (q Δ qep : ℕ) :
    (r1OracleStepTrackC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q Δ qep).size ≤
      1650000 + 160 * bits q + bits (q + 1) + 50 * bits Δ + 20 * bits qep +
        10 * bits (qep + 1) := by
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) (coinOnlyIface ℓ Pt)
  have hpreL := liftCompCoins_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
    (preSendE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT) Δ qep)
  have hpreS := preSendE2EC_size_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT) Δ qep
  have hpostL := liftCompCoins_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
    (postSendE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT) q Δ)
  have hpostS := postSendE2EC_size_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT) q Δ
  let dlInTy : Ty ESig := .prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))
  have hdlL := liftCompCoins_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
    (drDlArmC hooks coins q (.fst .v0 : Expr EOps [dlInTy] _) (.snd .v0))
  have hdlS := drDlArmC_spqr_size_le coins (fun {_} => size_coinDraw256) q
    (.fst .v0 : Expr EOps [dlInTy] _) (.snd .v0)
  have hijL := liftCompCoins_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
    (drIjArmC hooks coins q Δ qep (.fst .v0 : Expr EOps [dlInTy] _) (.snd .v0))
  have hijS := drIjArmC_spqr_size_le coins (fun {_} => size_coinDraw256) q Δ qep
    (.fst .v0 : Expr EOps [dlInTy] _) (.snd .v0)
  have hcrL := liftCompCoins_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
    (r1CrArmC (C := C) (K := K) (decT := decT) (encT := encT) (I := coinE2EIface (coinOnlyIface ℓ Pt)) q
      (.fst .v0 : Expr EOps [.prod (e2eGsTy ℓ) .bool] _) (.snd .v0))
  have hcrS := r1CrArmC_size_le (C := C) (K := K) (decT := decT) (encT := encT)
    (I := coinE2EIface (coinOnlyIface ℓ Pt)) q (.fst .v0 : Expr EOps [.prod (e2eGsTy ℓ) .bool] _) (.snd .v0)
  let scTy : Ty ASig := .prod .bool (.prod PlainT (.prod (.opt PlainT) (.opt BV512)))
  let rest3Ty : Ty ASig := .sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool)
  let Γ_sc3 : List (Ty ASig) := [liftTy (Pt := Pt) (preSendOutTy ℓ),
    .opt (liftTy (Pt := Pt) (preSendOutTy ℓ)), scTy, sessionHaltedStTy ℓ Pt, liftTy (Pt := Pt) smQT]
  have hkf := stepKemFailSendAtomicC_size_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ_sc3) q
    (.fst (.snd .v3)) (.fst (.snd .v0)) (.fst (.snd (.snd (.snd .v0))))
  let Γ_dl0 : List (Ty ASig) := [.prod .bool (B 32), rest3Ty, sessionHaltedStTy ℓ Pt, liftTy (Pt := Pt) smQT]
  have hfind := findRevHonestWiresIdxE_size (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ_dl0) q
    (.snd (.snd .v2)) (.fst .v0) (.snd .v0)
  let Γ_dl2 : List (Ty ASig) :=
    [.prod (liftTy (Pt := Pt) (smRT CryptoVerification.E2E.Costed.GhostStT)) (liftTy (Pt := Pt) (e2eGsTy ℓ)),
     .opt .nat, .prod .bool (B 32), rest3Ty, sessionHaltedStTy ℓ Pt, liftTy (Pt := Pt) smQT]
  have hdel1 := expr_size_le_atomicExprDescBits atomicSessionOpDescBits
    (kemOnDeliverPostAtomicE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ_dl2) q
      (.fst .v2) .v1 (.fst (.snd (.fst .v0))) (.fst (.snd .v4)))
  have hdel2 := kemOnDeliverPostAtomicE_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
    (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ_dl2) q
    (.fst .v2) .v1 (.fst (.snd (.fst .v0))) (.fst (.snd .v4))
  have hb : bits 0 = 1 ∧ bits 1 = 1 ∧ bits 2 = 2 ∧ bits 4 = 3 := by decide
  simp only [atomicExprDescBits, Expr.v0, Expr.v1, Expr.v2, Expr.v4, varIdx, hb] at hdel2
  dsimp only [hooks, coins, dlInTy] at hdlL hdlS hijL hijS
  simp only [r1OracleStepTrackC, sendArmC, sendSomeContC, classifyQryE, callSub1C, trE_cand,
    Comp.size, Expr.size, renComp_size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5]
    at hpreL hpostL hdlL hdlS hijL hijS hcrL hcrS hkf hfind hdel1 ⊢
  omega

theorem postSendE2EC_eval (q Δ : ℕ) (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (s1 : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (P : Party) (mEff : Plain ℓ) (rCoins : BitVec 512) (isCh : Bool)
    (hgParty : PartyReachInv C K (s1.st P))
    (htr1_le : s1.trans.length ≤ q) (hcp1_le : (dedupComp s1.comp).length ≤ q) :
    (postSendE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT) q Δ).eval
      (.cons (e2eGsEnc s1, (partyEnc P, (mEff, (rCoins, isCh)))) .nil) =
      let out := (sessionSchemeFixedSpk
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins).send
        (s1.st P) mEff rCoins
      pure (out.2,
        e2eGsEnc (s1.record Δ P out.1 ⟨⟨P, s1.epoch P, s1.idx P + 1⟩, mEff, out.2⟩ isCh)) := by
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  unfold postSendE2EC
  rw [comp_eval_bind]
  set ρOut0 : Env [preSendOutTy ℓ] :=
    .cons (t := preSendOutTy ℓ) (e2eGsEnc s1, (partyEnc P, (mEff, (rCoins, isCh)))) .nil
  have hSendIn :
      (Expr.pair (pGet (e2eGsSt (.fst (Expr.v0 (O := EOps)))) (.fst (.snd .v0)))
        (.pair (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0)))))).eval ρOut0 =
      (s1.st P, (mEff, rCoins)) := by
    rw [pair_eval, pGet_eval _ _ ρOut0 s1.st P rfl rfl]; rfl
  have hgParty' : PartyReachInv C K
      ((Expr.pair (pGet (e2eGsSt (.fst (Expr.v0 (O := EOps)))) (.fst (.snd .v0)))
        (.pair (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0)))))).eval ρOut0).1 := by
    rw [hSendIn]; exact hgParty
  rw [drSendC_eval hooks (coinE2EIface (coinOnlyIface ℓ Pt)) _ ρOut0 idA idB spkCoins
    hgParty', hSendIn]
  simp only [pure_bind, comp_eval_ret]
  set out := (sessionSchemeFixedSpk
    (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins).send
    (s1.st P) mEff rCoins
  set ρOut1 : Env [.prod CryptoVerification.E2E.Costed.GhostStT (CryptoVerification.E2E.Costed.B 32),
      preSendOutTy ℓ] := .cons (t := .prod CryptoVerification.E2E.Costed.GhostStT (CryptoVerification.E2E.Costed.B 32)) out ρOut0
  have hpos :
      (Expr.pair (.fst (.snd (Expr.v1 (O := EOps))))
        (.pair (pGet (e2eGsEpoch (.fst .v1)) (.fst (.snd .v1)))
          (.add (pGet (e2eGsIdx (.fst .v1)) (.fst (.snd .v1))) (.nat 1)))).eval ρOut1 =
      posEnc ⟨P, s1.epoch P, s1.idx P + 1⟩ := by
    have hep1 : (pGet (e2eGsEpoch (.fst (Expr.v1 (O := EOps)))) (.fst (.snd .v1))).eval ρOut1 =
        s1.epoch P := pGet_eval (t := .nat) _ _ ρOut1 s1.epoch P rfl rfl
    have hidx1 : (pGet (e2eGsIdx (.fst (Expr.v1 (O := EOps)))) (.fst (.snd .v1))).eval ρOut1 =
        s1.idx P := pGet_eval (t := .nat) _ _ ρOut1 s1.idx P rfl rfl
    simp only [Expr.eval, hep1, hidx1]; rfl
  have hrec := eval_e2eRecordE q Δ (.fst (Expr.v1 (O := EOps))) (.fst (.snd .v1))
    (.fst .v0)
    (.pair (.fst (.snd .v1))
      (.pair (pGet (e2eGsEpoch (.fst .v1)) (.fst (.snd .v1)))
        (.add (pGet (e2eGsIdx (.fst .v1)) (.fst (.snd .v1))) (.nat 1))))
    (.fst (.snd (.snd .v1))) (.snd .v0) (.snd (.snd (.snd (.snd .v1))))
    ρOut1 s1 P ⟨P, s1.epoch P, s1.idx P + 1⟩
    htr1_le hcp1_le rfl rfl hpos
  simp only [Expr.eval, hrec]; rfl

private theorem sendSomeContC_eval (q Δ : ℕ) (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (st s1 : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (tr : KemFailTrackState C.F) (hw : List (Bytes × Party))
    (P : Party) (mEff : Plain ℓ) (rCoins : BitVec 512) (isCh : Bool)
    (v0 : (liftTy (Pt := Pt) (preSendOutTy ℓ)).denote)
    (vOpt : (Ty.opt (S := ASig) (liftTy (Pt := Pt) (preSendOutTy ℓ))).denote)
    (vReq : (Ty.prod (S := ASig) .bool (.prod PlainT (.prod (.opt PlainT) (.opt BV512)))).denote)
    (vSq : (liftTy (Pt := Pt) smQT).denote)
    (hv0 : v0 = liftVal (Pt := Pt) (t := preSendOutTy ℓ)
      (e2eGsEnc s1, (partyEnc P, (mEff, (rCoins, isCh)))))
    (hInv : KemTrackDeliverInv C.F K q (kemTrackEnc tr))
    (hgParty : PartyReachInv C K (s1.st P))
    (htr1_le : s1.trans.length ≤ q) (hcp1_le : (dedupComp s1.comp).length ≤ q) :
    (sendSomeContC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q Δ).eval
      (.cons v0 (.cons vOpt (.cons vReq
        (.cons (sessionHaltedEnc (ℓ := ℓ) (Pt := Pt) (st, (tr, hw))) (.cons vSq .nil))))) =
    let tr' := stepKemFailSend C.F K tr P rCoins
    if tr'.cand.isSome then
      pure (liftVal (Pt := Pt) (t := smRT CryptoVerification.E2E.Costed.GhostStT)
        ((none : Option Bytes), (none, none)),
        sessionHaltedEnc (ℓ := ℓ) (Pt := Pt) (st, ({ tr with cand := tr'.cand }, hw)))
    else
      let out := (sessionSchemeFixedSpk
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins).send
        (s1.st P) mEff rCoins
      pure (liftVal (Pt := Pt) (t := smRT CryptoVerification.E2E.Costed.GhostStT)
        (some out.2, (none, none)),
        sessionHaltedEnc (ℓ := ℓ) (Pt := Pt)
          (s1.record Δ P out.1 ⟨⟨P, s1.epoch P, s1.idx P + 1⟩, mEff, out.2⟩ isCh,
            (tr', (out.2, P) :: hw))) := by
  subst hv0
  have hSentLen : tr.sentB.length ≤ q := by simpa [kemTrackEnc] using hInv.sentB_len
  unfold sendSomeContC
  let ρCont := Env.cons (t := liftTy (Pt := Pt) (preSendOutTy ℓ))
    (liftVal (Pt := Pt) (t := preSendOutTy ℓ) (e2eGsEnc s1, (partyEnc P, (mEff, (rCoins, isCh)))))
    (.cons vOpt (.cons vReq
      (.cons (sessionHaltedEnc (ℓ := ℓ) (Pt := Pt) (st, (tr, hw))) (.cons vSq .nil))))
  have hStepTr := stepKemFailSendAtomicC_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) q
    (.fst (.snd .v3)) (.fst (.snd .v0)) (.fst (.snd (.snd (.snd .v0)))) ρCont
    tr P rCoins rfl
    (by simp [ρCont, liftVal, Expr.eval, Expr.v0])
    rfl (by simpa [kemTrackEnc] using hInv.bOk P) hSentLen
  have hStepCost :
      (stepKemFailSendAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) q
        (.fst (.snd .v3)) (.fst (.snd .v0)) (.fst (.snd (.snd (.snd .v0))))).eval ρCont =
      let tr' := stepKemFailSend C.F K tr P rCoins
      pure (kemTrackAtomicEnc (kemTrackEnc tr'),
            kemTrackAtomicEnc (kemTrackEnc { tr with cand := tr'.cand })) := hStepTr
  dsimp only [ρCont] at hStepCost
  rw [comp_eval_bind, hStepCost]; simp only [pure_bind]
  set tr' := stepKemFailSend C.F K tr P rCoins
  rw [comp_eval_caseOpt]
  cases hcand : tr'.cand with
  | some candVal =>
    have htrCand : (trE_cand (.fst .v0 : Expr AOps _ _)).eval
        (.cons (kemTrackAtomicEnc (kemTrackEnc tr'),
          kemTrackAtomicEnc (kemTrackEnc { tr with cand := some candVal })) ρCont) =
        some (kemCandVecToBv candVal) := by
      simp [ρCont, trE_cand, kemTrackAtomicEnc, kemTrackEnc, hcand, Expr.eval, Expr.v0]
    dsimp only [ρCont] at htrCand; rw [htrCand]
    simp [sessionHaltedEnc, kemSessionTrackEnc, liftVal, Expr.eval, Expr.v1, Expr.v5]
  | none =>
    have htrCand : (trE_cand (.fst .v0 : Expr AOps _ _)).eval
        (.cons (kemTrackAtomicEnc (kemTrackEnc tr'),
          kemTrackAtomicEnc (kemTrackEnc { tr with cand := none })) ρCont) = none := by
      simp [ρCont, trE_cand, kemTrackAtomicEnc, kemTrackEnc, hcand, Expr.eval, Expr.v0]
    dsimp only [ρCont] at htrCand; rw [htrCand, comp_eval_bind, callSub1C_eval]
    have hpostLift := liftCompCoins_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
      (postSendE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT) q Δ)
      (.cons (e2eGsEnc s1, (partyEnc P, (mEff, (rCoins, isCh)))) .nil)
    change (liftCompCoins rfl (postSendE2EC q Δ)).eval
        (.cons (liftVal (Pt := Pt) (t := preSendOutTy ℓ)
          (e2eGsEnc s1, (partyEnc P, (mEff, (rCoins, isCh))))) .nil) =
      liftVal (Pt := Pt) <$> (postSendE2EC q Δ).eval
        (.cons (e2eGsEnc s1, (partyEnc P, (mEff, (rCoins, isCh)))) .nil) at hpostLift
    have hv1 : (Expr.v1 : Expr AOps _ (liftTy (Pt := Pt) (preSendOutTy ℓ))).eval
        (.cons (t := .prod (kemTrackT ℓ Pt) (kemTrackT ℓ Pt))
          (kemTrackAtomicEnc (kemTrackEnc tr'),
            kemTrackAtomicEnc (kemTrackEnc { tr with cand := none })) ρCont) =
        liftVal (Pt := Pt) (t := preSendOutTy ℓ)
          (e2eGsEnc s1, (partyEnc P, (mEff, (rCoins, isCh)))) := rfl
    dsimp only [ρCont] at hv1
    rw [hv1, hpostLift, postSendE2EC_eval q Δ idA idB spkCoins s1 P mEff rCoins isCh
      hgParty htr1_le hcp1_le]
    simp [map_pure, sessionHaltedEnc, kemSessionTrackEnc,
      liftVal, Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v5]; rfl

private theorem epMgmt_preserve_fields {Δ qep : ℕ}
    {st s1 : GameState (GhostState Bytes) (Plain ℓ) Bytes} {party : Party} {bad : Bool}
    (hep : st.epMgmt Δ qep party bad = some s1) :
    s1.st = st.st ∧ s1.trans = st.trans ∧ s1.comp = st.comp := by
  unfold GameState.epMgmt at hep
  split_ifs at hep <;> simp only [Option.some.injEq] at hep <;> subst hep <;> exact ⟨rfl, rfl, rfl⟩

private theorem sendArmC_eval (q Δ qep : ℕ) (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (tr : KemFailTrackState C.F) (hw : List (Bytes × Party))
    (P : Party) (m0 : Plain ℓ) (m1? : Option (Plain ℓ)) (optR : Option (BitVec 512))
    (vSq : (liftTy (Pt := Pt) smQT).denote)
    (hReach : SmReachBounded C K q st)
    (hInv : KemTrackDeliverInv C.F K q (kemTrackEnc tr)) :
    (sendArmC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q Δ qep).eval
      (.cons (partyEnc P, (m0, (m1?, optR)))
        (.cons (sessionHaltedEnc (ℓ := ℓ) (Pt := Pt) (st, (tr, hw))) (.cons vSq .nil))) =
    let cfg := configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT)
    let sm := sessionSchemeFixedSpk
      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins
    let noneResp := (liftVal (Pt := Pt) (t := smRT CryptoVerification.E2E.Costed.GhostStT)
      ((none : Option Bytes), (none, none)),
      sessionHaltedEnc (ℓ := ℓ) (Pt := Pt) (st, (tr, hw)))
    if !(cfg.sendOK st P) || st.win then pure noneResp
    else
      samIfNec optR >>= fun (rCoins, bad) =>
      match st.epMgmt Δ qep P bad with
      | none => pure noneResp
      | some s1 =>
        match (match m1? with
          | none => some (m0, false)
          | some m1 => if s1.safeCh Δ P then some (if st.b then m1 else m0, true) else none) with
        | none => pure noneResp
        | some (mEff, isCh) =>
          let tr' := stepKemFailSend C.F K tr P rCoins
          if tr'.cand.isSome then
            pure (liftVal (Pt := Pt) (t := smRT CryptoVerification.E2E.Costed.GhostStT)
              ((none : Option Bytes), (none, none)),
              sessionHaltedEnc (ℓ := ℓ) (Pt := Pt) (st, ({ tr with cand := tr'.cand }, hw)))
          else
            let out := sm.send (s1.st P) mEff rCoins
            pure (liftVal (Pt := Pt) (t := smRT CryptoVerification.E2E.Costed.GhostStT)
              (some out.2, (none, none)),
              sessionHaltedEnc (ℓ := ℓ) (Pt := Pt)
                (s1.record Δ P out.1 ⟨⟨P, s1.epoch P, s1.idx P + 1⟩, mEff, out.2⟩ isCh,
                  (tr', (out.2, P) :: hw))) := by
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) (coinOnlyIface ℓ Pt)
  set cfg := configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT)
  have hlift : ∀ {α : Type} (p : ProbComp α),
      (coinE2EIface (coinOnlyIface ℓ Pt)).liftP p = p :=
    fun p => liftP_unif_eq_self _ (fun _ => rfl) p
  unfold sendArmC
  rw [comp_eval_bind, callSub1C_eval]
  have hpair0 :
      (Expr.pair (.fst .v1) .v0 : Expr AOps _ (liftTy (Pt := Pt) (preSendInTy ℓ))).eval
        (.cons (partyEnc P, (m0, (m1?, optR)))
          (.cons (sessionHaltedEnc (ℓ := ℓ) (Pt := Pt) (st, (tr, hw))) (.cons vSq .nil))) =
      liftVal (Pt := Pt) (t := preSendInTy ℓ) (e2eGsEnc st, (partyEnc P, (m0, (m1?, optR)))) := by
    cases P <;> cases m1? <;> cases optR <;> rfl
  rw [hpair0]
  have hpreLift := liftCompCoins_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
    (preSendE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT) Δ qep)
    (.cons (e2eGsEnc st, (partyEnc P, (m0, (m1?, optR)))) .nil)
  change (liftCompCoins rfl (preSendE2EC Δ qep)).eval
      (.cons (liftVal (Pt := Pt) (t := preSendInTy ℓ)
        (e2eGsEnc st, (partyEnc P, (m0, (m1?, optR))))) .nil) =
    liftVal (Pt := Pt) <$>
      (preSendE2EC Δ qep).eval (.cons (e2eGsEnc st, (partyEnc P, (m0, (m1?, optR)))) .nil)
    at hpreLift
  rw [hpreLift]; unfold preSendE2EC
  set ρE1 : Env [preSendInTy ℓ] :=
    .cons (t := preSendInTy ℓ) (e2eGsEnc st, (partyEnc P, (m0, (m1?, optR)))) .nil
  have hSendOK : (e2eSendOKE (.fst (Expr.v0 (O := EOps))) (.fst (.snd .v0))).eval ρE1 =
      cfg.sendOK st P :=
    eval_e2eSendOKE decT encT (.fst .v0) (.fst (.snd .v0)) ρE1 st P rfl rfl
  have hWin : (e2eGsWin (.fst (Expr.v0 (O := EOps)))).eval ρE1 = st.win := rfl
  rw [comp_eval_ite]; simp only [orE_eval, Expr.eval, hSendOK, hWin]
  by_cases hbad : !(cfg.sendOK st P) || st.win
  · simp [hbad, liftVal, Expr.eval, Expr.v0, Expr.v2]
  · simp only [hbad, ↓reduceIte, Bool.false_eq_true, comp_eval_bind,
      e2eSamIfNec512C_eval (coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT)
        (coinOnlyIface ℓ Pt)),
      hlift, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    have hsamEq : ((Expr.snd (.snd (.snd (.snd (Expr.v0 (O := EOps)))))).eval ρE1) = optR := rfl
    rw [hsamEq]
    change (samIfNec optR >>= _) = (samIfNec optR >>= _)
    refine bind_congr fun ⟨rCoins, bad⟩ => ?_
    set ρE2 : Env [.prod CryptoVerification.E2E.Costed.BV512 .bool, preSendInTy ℓ] :=
      .cons (t := .prod CryptoVerification.E2E.Costed.BV512 .bool) (rCoins, bad) ρE1
    have hep : (e2eEpMgmtE Δ qep (.fst (Expr.v1 (O := EOps))) (.fst (.snd .v1)) (.snd .v0)).eval
        ρE2 = (st.epMgmt Δ qep P bad).map e2eGsEnc :=
      eval_e2eEpMgmtE Δ qep (.fst .v1) (.fst (.snd .v1)) (.snd .v0) ρE2 st P rfl rfl
    rw [comp_eval_caseOpt, hep]
    cases hepEq : st.epMgmt Δ qep P bad with
    | none =>
      simp [liftVal, Expr.eval, Expr.v0, Expr.v2]
    | some s1 =>
      simp only [Option.map_some]
      obtain ⟨hst1, htr1, hcp1⟩ := epMgmt_preserve_fields hepEq
      cases m1? with
      | none =>
        rw [comp_eval_caseOpt]
        change (Comp.ret (O := EOps) _).eval _ >>= _ = _
        simp only [comp_eval_ret, pure_bind]
        rw [comp_eval_caseOpt]
        exact sendSomeContC_eval q Δ idA idB spkCoins st s1 tr hw P m0 rCoins false _ _ _ _ rfl
          hInv (hst1 ▸ hReach.reach.party P) (htr1 ▸ hReach.lists.trans_le)
          (hcp1 ▸ hReach.lists.dedupComp_le)
      | some m1 =>
        rw [comp_eval_caseOpt]
        set ρE3 : Env [CryptoVerification.E2E.Costed.PlainT, e2eGsTy ℓ,
            .prod CryptoVerification.E2E.Costed.BV512 .bool, preSendInTy ℓ] :=
          .cons (t := CryptoVerification.E2E.Costed.PlainT) m1
            (.cons (t := e2eGsTy ℓ) (e2eGsEnc s1) ρE2)
        change (Comp.ite (O := EOps) (.not (e2eSafeChE Δ .v1 (.fst (.snd .v3)))) _ _).eval
            ρE3 >>= _ = _
        have hSafe : (e2eSafeChE Δ (.v1 : Expr EOps _ _) (.fst (.snd .v3))).eval ρE3 =
            s1.safeCh Δ P :=
          eval_e2eSafeChE Δ .v1 (.fst (.snd .v3)) ρE3 s1 P rfl rfl
        rw [comp_eval_ite]; simp only [Expr.eval, hSafe]
        by_cases hsafe : s1.safeCh Δ P
        · simp only [hsafe, Bool.not_true, Bool.false_eq_true, ↓reduceIte, comp_eval_ret, pure_bind]
          set mCh := if st.b then m1 else m0
          have hmCh :
              ((Expr.pair (.v1 : Expr EOps _ _)
                (.pair (.fst (.snd .v3))
                  (.pair (.ite (e2eGsB (.fst .v3)) .v0 (.fst (.snd (.snd .v3))))
                    (.pair (.fst .v2) (.bool true))))).some).eval ρE3 =
              some (e2eGsEnc s1, (partyEnc P, (mCh, (rCoins, true)))) := by
            simp [ρE3, ρE2, ρE1, mCh, e2eGsB, e2eGsEnc, Expr.eval, Expr.v0, Expr.v1, Expr.v2,
              Expr.v3]
          rw [hmCh, comp_eval_caseOpt]
          exact sendSomeContC_eval q Δ idA idB spkCoins st s1 tr hw P mCh rCoins true _ _ _ _ rfl
            hInv (hst1 ▸ hReach.reach.party P) (htr1 ▸ hReach.lists.trans_le)
            (hcp1 ▸ hReach.lists.dedupComp_le)
        · simp [hsafe, liftVal, Expr.eval, Expr.v0, Expr.v2]

private theorem eval_v0_cons {Γ : List (Ty ASig)} {t : Ty ASig} (x : t.denote) (ρ : Env Γ) :
    (Expr.v0 : Expr AOps (t :: Γ) t).eval (.cons x ρ) = x := rfl

private theorem liftStateT_run_state {σ τ α : Type}
    (x : StateT σ ProbComp α) (s : σ) (t : τ) :
    ((liftStateT x : StateT σ (StateT τ ProbComp) α).run s).run t =
      (x.run s >>= fun a => pure (a, t)) := rfl

theorem r1OracleStepTrackC_eval (q Δ qep : ℕ)
    (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (tr : KemFailTrackState C.F) (hw : List (Bytes × Party))
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (hReach : SmReachBounded C K q st)
    (hInv : KemTrackDeliverInv C.F K q (kemTrackEnc tr))
    (hHw : hw.length ≤ q) :
    (r1OracleStepTrackC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q Δ qep).eval
      (.cons (sessionHaltedEnc (ℓ := ℓ) (Pt := Pt) (st, (tr, hw)))
        (.cons ((e2eSessionCodec ℓ Pt).qenc sq) .nil)) =
      (do
        let ((ans, st'), ts') ←
          ((oracleImplRSessionTrackHalted C.F K
            (sessionSchemeFixedSpk
              (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins)
            Δ qep (configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT)) sq).run
            st).run (tr, hw)
        pure (liftVal (Pt := Pt)
          (smRenc (ℓ := ℓ) (stT := CryptoVerification.E2E.Costed.GhostStT) id sq ans),
          sessionHaltedEnc (ℓ := ℓ) (Pt := Pt) (st', ts'))) := by
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT)
    (coinOnlyIface ℓ Pt)
  let sm := sessionSchemeFixedSpk
    (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins
  let cfg : CryptoGames.SM.ConfigR (GhostState Bytes) (Plain ℓ) Bytes :=
    configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT)
  have hlift : ∀ {α : Type} (p : ProbComp α),
      (coinE2EIface (coinOnlyIface ℓ Pt)).liftP p = p :=
    fun p => liftP_unif_eq_self _ (fun _ => rfl) p
  rw [← liftVal_smQenc Pt sq]
  unfold r1OracleStepTrackC
  rcases sq with (((⟨P, m, optR⟩ | ⟨P, m0, m1, optR⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | P
  ·
    have hcls :
        (classifyQryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) .v1).eval
          (.cons (sessionHaltedEnc (ℓ := ℓ) (Pt := Pt) (st, (tr, hw)))
            (.cons (liftVal (Pt := Pt) (smQenc (St := GhostState Bytes) (.inl (.inl (.inl (.inl (P, m, optR))))))) .nil)) =
        .inl (partyEnc P, (m, (none, optR))) := by
      cases P <;> cases optR <;> rfl
    rw [comp_eval_caseSum, hcls]; dsimp only
    rw [sendArmC_eval q Δ qep idA idB spkCoins st tr hw P m none optR _
      hReach hInv]
    change _ = (do
      let ((ans, st'), ts') ←
        ((transmitRSessionTrackHalted C.F K sm Δ qep cfg (P, m, optR)).run st).run (tr, hw)
      pure (liftVal (Pt := Pt)
        (smRenc (ℓ := ℓ) (stT := CryptoVerification.E2E.Costed.GhostStT) id
          (.inl (.inl (.inl (.inl (P, m, optR))))) ans),
        sessionHaltedEnc (ℓ := ℓ) (Pt := Pt) (st', ts')))
    unfold transmitRSessionTrackHalted
    by_cases hok : cfg.sendOK st P
    · by_cases hwin : st.win
      · simp [cfg, hok, hwin, smRenc]
      · simp only [cfg, hok, hwin, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_monadLift, monadLift_self,
          bind_assoc, pure_bind]
        change (samIfNec optR >>= _) = (samIfNec optR >>= _)
        refine bind_congr fun ⟨rCoins, bad⟩ => ?_
        cases st.epMgmt Δ qep P bad with
        | none => simp [smRenc]
        | some s1 =>
          by_cases hcand : (stepKemFailSend C.F K tr P rCoins).cand.isSome <;>
            simp [hcand, sm, StateT.run_bind, StateT.run_lift,
              StateT.run_get, StateT.run_set, smRenc]
    · simp [cfg, hok, smRenc]
  ·
    have hchallAllowed : ∀ t,
        (configR1OnCurve (St := GhostState Bytes) (Msg := Plain ℓ)
          (ratchetKeyAdmissible protoSignalCodec decT encT)).base.challAllowedIn t = true :=
      fun _ => rfl
    have hchallMsg : ∀ t,
        (configR1OnCurve (St := GhostState Bytes) (Msg := Plain ℓ)
          (ratchetKeyAdmissible protoSignalCodec decT encT)).base.challMsg t = none :=
      fun _ => rfl
    have hcls :
        (classifyQryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) .v1).eval
          (.cons (sessionHaltedEnc (ℓ := ℓ) (Pt := Pt) (st, (tr, hw)))
            (.cons (liftVal (Pt := Pt) (smQenc (St := GhostState Bytes) (.inl (.inl (.inl (.inr (P, m0, m1, optR))))))) .nil)) =
        .inl (partyEnc P, (m0, (some m1, optR))) := by
      cases P <;> cases optR <;> rfl
    rw [comp_eval_caseSum, hcls]; dsimp only
    rw [sendArmC_eval q Δ qep idA idB spkCoins st tr hw P m0 (some m1)
      optR _ hReach hInv]
    change _ = (do
      let ((ans, st'), ts') ←
        ((challRSessionTrackHalted C.F K sm Δ qep cfg (P, m0, m1, optR)).run st).run (tr, hw)
      pure (liftVal (Pt := Pt)
        (smRenc (ℓ := ℓ) (stT := CryptoVerification.E2E.Costed.GhostStT) id
          (.inl (.inl (.inl (.inr (P, m0, m1, optR))))) ans),
        sessionHaltedEnc (ℓ := ℓ) (Pt := Pt) (st', ts')))
    unfold challRSessionTrackHalted
    by_cases hok : cfg.sendOK st P
    · by_cases hwin : st.win
      · simp [cfg, hok, hwin, smRenc]
      · simp only [cfg, hok, hwin, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_monadLift, monadLift_self,
          bind_assoc, pure_bind]
        change (samIfNec optR >>= _) = (samIfNec optR >>= _)
        refine bind_congr fun ⟨rCoins, bad⟩ => ?_
        cases st.epMgmt Δ qep P bad with
        | none => simp [smRenc]
        | some s1 =>
          simp only [hchallAllowed, Bool.not_true, Bool.or_false]
          by_cases hsafe : s1.safeCh Δ P
          · simp only [hsafe, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hchallMsg,
              Option.getD_none]
            by_cases hcand : (stepKemFailSend C.F K tr P rCoins).cand.isSome <;>
              simp [hcand, sm, StateT.run_bind, StateT.run_lift,
                StateT.run_get, StateT.run_set, smRenc]
          · simp [hsafe, smRenc]
    · simp [cfg, hok, smRenc]
  ·
    have hcls :
        (classifyQryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) .v1).eval
          (.cons (sessionHaltedEnc (ℓ := ℓ) (Pt := Pt) (st, (tr, hw)))
            (.cons (liftVal (Pt := Pt) (smQenc (St := GhostState Bytes) (.inl (.inl (.inr (Q, w)))))) .nil)) =
        .inr (.inl (partyEnc Q, w)) := by
      cases Q <;> rfl
    rw [comp_eval_caseSum, hcls]; dsimp only; rw [comp_eval_caseSum, eval_v0_cons]; dsimp only
    rw [comp_eval_bind_ret]
    have hfind := findRevHonestWiresIdxE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) q
      (.snd (.snd .v2)) (.fst .v0) (.snd .v0)
      (.cons (partyEnc Q, w)
        (.cons (t := .sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool))
          (.inl (partyEnc Q, w))
          (.cons (sessionHaltedEnc (ℓ := ℓ) (Pt := Pt) (st, (tr, hw)))
            (.cons (liftVal (Pt := Pt) (smQenc (St := GhostState Bytes) (.inl (.inl (.inr (Q, w)))))) .nil))))
      hw Q w hHw rfl rfl rfl
    rw [hfind, comp_eval_bind, callSub1C_eval]
    let cDl := drDlArmC hooks coins q
      (Γ := [.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))])
      (.fst .v0) (.snd .v0)
    have hdlLift := liftCompCoins_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl cDl
      (.cons (e2eGsEnc st, (partyEnc Q, w)) .nil)
    change (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl cDl).eval
        (.cons (liftVal (Pt := Pt) (e2eGsEnc st), (partyEnc Q, w)) .nil) =
      liftVal (Pt := Pt) <$>
        cDl.eval (.cons (e2eGsEnc st, (partyEnc Q, w)) .nil) at hdlLift
    have hdlEval := drDlArmC_eval hooks coins q
      (.fst .v0 : Expr EOps [.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))] _)
      (.snd .v0) (.cons (e2eGsEnc st, (partyEnc Q, w)) .nil)
      idA idB spkCoins st Q w hReach rfl rfl
    rw [show (Expr.pair (.fst .v3) .v1 : Expr AOps _ _).eval _ =
      (liftVal (Pt := Pt) (e2eGsEnc st), (partyEnc Q, w)) from rfl]
    dsimp only [cDl] at hdlLift
    rw [hdlLift, hdlEval, hlift]
    change _ = (do
      let ((ans, st'), ts') ←
        ((deliverRSessionTrackHalted C.F K sm cfg (Q, w)).run st).run (tr, hw)
      pure (liftVal (Pt := Pt)
        (smRenc (ℓ := ℓ) (stT := CryptoVerification.E2E.Costed.GhostStT) id
          (.inl (.inl (.inr (Q, w)))) ans),
        sessionHaltedEnc (ℓ := ℓ) (Pt := Pt) (st', ts')))
    unfold deliverRSessionTrackHalted
    simp only [StateT.run_bind, StateT.run_lift, StateT.run_get, liftStateT_run_state,
      map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    refine bind_congr fun ⟨rr?, st'⟩ => ?_
    rw [comp_eval_ret]
    let j? := hw.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other)
    have hdel := kemOnDeliverPostAtomicE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) q
      (.fst .v2) .v1 (.fst (.snd (.fst .v0))) (.fst (.snd .v4))
      (.cons (liftVal (Pt := Pt) (t := .prod (smRT CryptoVerification.E2E.Costed.GhostStT) (e2eGsTy ℓ))
          ((none, (rr?.map recvResultEnc, none)), e2eGsEnc st'))
        (.cons (t := .opt .nat) j? (.cons (t := .prod .bool (B 32)) (partyEnc Q, w)
          (.cons (t := .sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool))
            (.inl (partyEnc Q, w))
            (.cons (sessionHaltedEnc (ℓ := ℓ) (Pt := Pt) (st, (tr, hw)))
              (.cons (liftVal (Pt := Pt) (smQenc (St := GhostState Bytes) (.inl (.inl (.inr (Q, w)))))) .nil))))))
      Q j? rr? tr (by simp [Expr.eval, Expr.v2]) rfl
      (by cases rr? with
          | none => rfl
          | some rr => cases rr with | rejected => rfl | accepted _ _ m? => cases m? <;> rfl)
      rfl hInv
    dsimp only [Prod.map]
    simp only [Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v4, Env.get] at hdel ⊢
    rw [hdel]; dsimp only [j?]; simp only [Bool.beq_eq_decide_eq]
    generalize List.findIdx? _ hw.reverse = k?
    cases rr? with
    | none => simp [StateT.run_pure, sessionHaltedEnc, kemSessionTrackEnc, liftVal, smRenc]; rfl
    | some rr =>
      cases rr with
      | rejected => simp [StateT.run_pure, sessionHaltedEnc, kemSessionTrackEnc, liftVal, smRenc]; rfl
      | accepted e i m? =>
        cases k? with
        | none => cases m? <;> (simp [StateT.run_pure, sessionHaltedEnc, kemSessionTrackEnc, liftVal, smRenc]; rfl)
        | some j =>
          cases m? <;> (simp [StateT.run_map, StateT.run_lift, StateT.run_modify,
            sessionHaltedEnc, kemSessionTrackEnc, liftVal, smRenc]; rfl)
  ·
    have hcls :
        (classifyQryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) .v1).eval
          (.cons (sessionHaltedEnc (ℓ := ℓ) (Pt := Pt) (st, (tr, hw)))
            (.cons (liftVal (Pt := Pt) (smQenc (St := GhostState Bytes) (.inl (.inr (Q, w))))) .nil)) =
        .inr (.inr (.inl (partyEnc Q, w))) := by cases Q <;> rfl
    rw [comp_eval_caseSum, hcls]; dsimp only
    rw [comp_eval_caseSum, eval_v0_cons]; dsimp only
    rw [comp_eval_caseSum, eval_v0_cons]; dsimp only
    rw [comp_eval_bind, callSub1C_eval]
    let cIj := drIjArmC hooks coins q Δ qep
      (Γ := [.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))])
      (.fst .v0) (.snd .v0)
    have hijLift := liftCompCoins_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl cIj
      (.cons (e2eGsEnc st, (partyEnc Q, w)) .nil)
    change (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl cIj).eval
        (.cons (liftVal (Pt := Pt) (e2eGsEnc st), (partyEnc Q, w)) .nil) =
      liftVal (Pt := Pt) <$> cIj.eval (.cons (e2eGsEnc st, (partyEnc Q, w)) .nil) at hijLift
    have hijEval := drIjArmC_eval hooks coins q Δ qep
      (.fst .v0 : Expr EOps [.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))] _)
      (.snd .v0) (.cons (e2eGsEnc st, (partyEnc Q, w)) .nil) idA idB spkCoins st Q w hReach rfl rfl
    rw [show (Expr.pair (.fst .v3) .v0 : Expr AOps _ _).eval _ =
      (liftVal (Pt := Pt) (e2eGsEnc st), (partyEnc Q, w)) from rfl]
    dsimp only [cIj] at hijLift
    rw [hijLift, hijEval, hlift]
    change _ = (do
      let ((ans, st'), ts') ←
        (((liftStateT (injectR sm Δ qep cfg (Q, w)) :
          StateT _ (StateT _ ProbComp) _).run st).run (tr, hw))
      pure (liftVal (Pt := Pt)
        (smRenc (ℓ := ℓ) (stT := CryptoVerification.E2E.Costed.GhostStT) id (.inl (.inr (Q, w))) ans),
        sessionHaltedEnc (ℓ := ℓ) (Pt := Pt) (st', ts')))
    simp only [liftStateT_run_state, map_eq_bind_pure_comp, Function.comp_def, bind_assoc,
      pure_bind, comp_eval_ret]
    refine bind_congr fun ⟨rr?, st'⟩ => ?_
    cases rr? with
    | none => rfl
    | some rr => cases rr with | rejected => rfl | accepted _ _ m? => cases m? <;> rfl
  ·
    have hcls :
        (classifyQryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) .v1).eval
          (.cons (sessionHaltedEnc (ℓ := ℓ) (Pt := Pt) (st, (tr, hw)))
            (.cons (liftVal (Pt := Pt) (smQenc (St := GhostState Bytes) (.inr P))) .nil)) =
        .inr (.inr (.inr (partyEnc P))) := by cases P <;> rfl
    rw [comp_eval_caseSum, hcls]; dsimp only
    rw [comp_eval_caseSum, eval_v0_cons]; dsimp only
    rw [comp_eval_caseSum, eval_v0_cons]; dsimp only
    rw [comp_eval_bind, callSub1C_eval]
    let cCr := r1CrArmC (C := C) (K := K) (decT := decT) (encT := encT)
      (I := coinE2EIface (coinOnlyIface ℓ Pt)) q (Γ := [.prod (e2eGsTy ℓ) .bool]) (.fst .v0) (.snd .v0)
    have hcrLift := liftCompCoins_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl cCr
      (.cons (e2eGsEnc st, partyEnc P) .nil)
    change (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl cCr).eval
        (.cons (liftVal (Pt := Pt) (e2eGsEnc st), partyEnc P) .nil) =
      liftVal (Pt := Pt) <$> cCr.eval (.cons (e2eGsEnc st, partyEnc P) .nil) at hcrLift
    have hcrEval := r1CrArmC_eval (C := C) (K := K) (decT := decT) (encT := encT)
      (I := coinE2EIface (coinOnlyIface ℓ Pt)) q
      (.fst .v0 : Expr EOps [.prod (e2eGsTy ℓ) .bool] _) (.snd .v0)
      (.cons (e2eGsEnc st, partyEnc P) .nil) st P hReach.lists rfl rfl
    rw [show (Expr.pair (.fst .v3) .v0 : Expr AOps _ _).eval _ =
      (liftVal (Pt := Pt) (e2eGsEnc st), partyEnc P) from rfl]
    dsimp only [cCr] at hcrLift
    rw [hcrLift, hcrEval, hlift]
    change _ = (do
      let ((ans, st'), ts') ←
        (((liftStateT (corrR cfg P) : StateT _ (StateT _ ProbComp) _).run st).run (tr, hw))
      pure (liftVal (Pt := Pt)
        (smRenc (ℓ := ℓ) (stT := CryptoVerification.E2E.Costed.GhostStT) id (.inr P) ans),
        sessionHaltedEnc (ℓ := ℓ) (Pt := Pt) (st', ts')))
    simp only [liftStateT_run_state, map_eq_bind_pure_comp, Function.comp_def, bind_assoc,
      pure_bind, comp_eval_ret]
    refine bind_congr fun ⟨st?, st'⟩ => ?_
    cases st? <;> rfl

end StepHalted

end Computational.Proofs.Game.PromotedCostedReds.HaltedUniformEpoch0Step

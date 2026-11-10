/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.UniformStartDistinguisherProg
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalSim
import Computational.Proofs.Game.PromotedCostedReds.DrSessionSimSize
import Computational.Proofs.ReductionDsl.SizeBudgetBridge

/-!
# Promoted `CostedReduction` Witness for `epoch0Distinguisher`

Constructs `epoch0Red`, the `ReductionDsl.CostedReduction` witness over `atomicSessionOps` and
`coinOnlyIface` for `epoch0Distinguisher`, and proves `GRedBounded` and exact `.eval` agreement
for bounded-query adversaries.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.Epoch0DistinguisherProg

open OracleSpec OracleComp
open _root_.ReductionDsl (Ty Var Env Ops Iface Expr Comp CostedReduction bits bits_mono
  reductionSizeBudget handlerImpl atomicSig atomicSessionOps coinOnlyIface e2eSessionCodec BV256)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.Ratchet (RootKey)
open CryptoGames.Ratchet.LibsignalInst (libsignalSessionSchemeFromEpoch0Keys ratchetKeyAdmissible)
open CryptoGames.Ratchet.LibsignalSim (configEpoch0Distinguisher epoch0Distinguisher)
open CryptoGames.SM (GameState initState injectR corrR oracleImplR runR MakesAtMostQueries
  inWindow partyEnc posTy posEnc orE isSomeE otherE pGet
  pair_eval some_eval orE_eval isSomeE_eval otherE_eval pGet_eval ite_eval)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey GhostState)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.LibsignalSession (ratchetCostBudget GRedBounded)
open CryptoVerification.E2E (Bytes paramsIdsWithSpqr paramsV1 sessionSchemeFixedSpk)
open CryptoVerification.E2E.Costed (e2eSig e2eOps E2EPureOp GhostStT PlainT B
  BV512 smQT smQenc smRT gRedBounded_of_bounds)
open Computational.Proofs.E2E.Dsl.TablesHonest (e2ePureOp eval_e2ePureOp
  cost_e2ePureOp size_e2ePureOp)
open Computational.Proofs.E2E.Dsl.SmReachInvParty (PartyReachInv)
open Computational.Proofs.E2E.Dsl.SmReachInv (SmReachBounded smReachBounded_oracleImplR)
open Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping (partyToBool_eq_partyEnc
  smRenc recvResultRejE recvResultAccE smRRecvE smRCorrE
  eval_recvResultRejE eval_recvResultAccE eval_smRRecvE eval_smRCorrE
  cost_recvResultRejE cost_recvResultAccE cost_smRRecvE cost_smRCorrE
  ratchetKeyAdmissibleE eval_ratchetKeyAdmissibleE cost_ratchetKeyAdmissibleE
  e2eGsTy e2eGsEnc e2eGsSt e2eGsWin e2eGsMaxAcc e2eGsCorrs
  e2eGsSetWin eval_e2eGsSetWin cost_e2eGsSetWin_le
  e2eSafeInjE eval_e2eSafeInjE cost_e2eSafeInjE_le
  e2eInTransitE eval_e2eInTransitE cost_e2eInTransitE_le
  e2eAcceptE eval_e2eAcceptE cost_e2eAcceptE_le
  e2eTrivialE eval_e2eTrivialE cost_e2eTrivialE_le
  e2eCorrAllowedE eval_e2eCorrAllowedE cost_e2eCorrAllowedE_le
  e2eInWindowE eval_e2eInWindowE cost_e2eInWindowE_le
  e2eAfterCorrAllowedE eval_e2eAfterCorrAllowedE cost_e2eAfterCorrAllowedE_le)
open Computational.Proofs.E2E.Dsl.SpqrSim (spqrDslHooks)
open Computational.Proofs.E2E.Dsl.DrSessionSimHooks (SpqrDslHooks gpCEps)
open Computational.Proofs.E2E.Dsl.DrSessionSimRecv (drRecvOutT
  drReceiveC drReceiveC_queries drReceiveC_cost drReceiveC_eval)
open Computational.Proofs.E2E.Dsl.DrSessionSim (E2ECoinSamplers mkE2ECoinSamplers
  drTrArmC drChArmC drDlArmC
  drTrArmC_queries_zero drChArmC_queries_zero drDlArmC_queries_zero
  drTrArmC_cost drChArmC_cost drDlArmC_cost
  drTrArmC_eval drChArmC_eval drDlArmC_eval)
open Computational.Proofs.Game.PromotedCostedReds.DrSessionSimSize (drReceiveC_spqr_size_le
  size_ratchetKeyAdmissibleE size_e2eGsSetWin_le size_e2eSafeInjE_le size_e2eAcceptE_le
  size_e2eTrivialE_le size_e2eCorrAllowedE_le size_e2eAfterCorrAllowedE_le
  size_e2eInWindowE_le size_e2eInTransitE_le
  drTrArmC_spqr_size_le drChArmC_spqr_size_le drDlArmC_spqr_size_le)
open Computational.Proofs.Game.PromotedCostedReds.AtomicOpsHonest (atomicSessionOps_sizeHonest
  atomicSamplers_sizeHonest)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge (zeroPqxdhPrims
  liftTy liftVal liftExpr liftExpr_cost liftExpr_eval coinE2EIface coinE2ESamplers
  liftCompCoins liftCompCoins_queries_zero liftCompCoins_cost liftCompCoins_eval)
open Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon (eval_eq_simulateQ_of_enc
  isQueryBoundP_of_makesAtMostQueries liftP_unif_eq_self liftVal_smQenc
  liftExpr_size_le liftCompCoins_size_le
  initEpoch0GsC initEpoch0GsC_queries_zero initEpoch0GsC_cost initEpoch0GsC_size_le
  initEpoch0GsC_eval
  epoch0InitImpl smReachBounded_epoch0InitImpl oracleImplR_epoch0Keys_eq_fixedSpk
  bits_succ_le session_cost_le_ratchetCostBudget
  dummyBoolSessionRed dummyBoolSessionRed_totalQueries dummyBoolSessionRed_totalCost_le
  dummyBoolSessionRed_size dummyBoolSessionRed_size_le)
open Computational.Proofs.Game.PromotedCostedReds.UniformStartDistinguisherProg (noAliceBelow10E
  eval_noAliceBelow10E cost_noAliceBelow10E_le size_noAliceBelow10E_le)
open Computational.Proofs.ReductionDsl.SizeBudgetBridge (size_le_budget_of_log_cost)

private theorem liftP_pure {S0 : ReductionDsl.Sig} {ι : Type} {T : OracleSpec ι}
    (I : Iface S0 T) {α : Type} (a : α) :
    I.liftP (pure a) = pure a := by
  simp [Iface.liftP]

private theorem liftP_bind {S0 : ReductionDsl.Sig} {ι : Type} {T : OracleSpec ι}
    (I : Iface S0 T) {α β : Type} (oa : ProbComp α) (f : α → ProbComp β) :
    I.liftP (oa >>= f) = I.liftP oa >>= fun x => I.liftP (f x) := by
  simp [Iface.liftP]

private theorem q_add_eleven_le_ratchetCostBudget (q qep' : ℕ) :
    q + 11 ≤ ratchetCostBudget q qep' := by
  have h := session_cost_le_ratchetCostBudget q qep' 100 (400 * q) 0 0 0
    (by omega) (by omega) (by omega) (by omega) (by omega)
  omega



/-! ## Step handlers and finish predicate -/

section StepE2E

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

local notation "ESig" => e2eSig ℓ
local notation "EOps" => e2eOps ℓ zeroPqxdhPrims C K decT encT

def epoch0CorrOKE {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (pE : Expr EOps Γ .bool) : Expr EOps Γ .bool :=
  .and (noAliceBelow10E gsE pE)
    (.not (.and (.not pE)
      (.anyB 5 (gpCEps (e2ePureOp .ghostStateSplit (.fst (e2eGsSt gsE)))) (.eqN .v0 (.nat 0)))))

theorem eval_epoch0CorrOKE {q : ℕ} {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (pE : Expr EOps Γ .bool) (ρ : Env Γ)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (party : Party)
    (h : SmReachBounded C K q st)
    (hgs : gsE.eval ρ = e2eGsEnc st) (hp : pE.eval ρ = partyEnc party) :
    (epoch0CorrOKE (C := C) (K := K) (decT := decT) (encT := encT) gsE pE).eval ρ =
      (configEpoch0Distinguisher (ratchetKeyAdmissible protoSignalCodec decT encT)).corrOK
        st party := by
  have h10 := eval_noAliceBelow10E (C := C) (K := K) (decT := decT) (encT := encT)
    gsE pE ρ st party hgs hp
  have hlen : (st.st .A).chainEpochs.length ≤ 5 := by
    rw [h.reach.alice.aligned]
    exact h.reach.alice.receiverChains_le_five
  have hceps :
      (gpCEps (e2ePureOp (P := zeroPqxdhPrims) (C := C) (K := K) (decT := decT) (encT := encT)
        .ghostStateSplit (.fst (e2eGsSt gsE)))).eval ρ = (st.st .A).chainEpochs := by
    simp [gpCEps, eval_e2ePureOp, E2EPureOp.eval, CryptoVerification.E2E.Costed.ghostSplitEval,
      e2eGsSt, e2eGsEnc, hgs, Expr.eval]
  have hany :
      (Expr.anyB 5
        (gpCEps (e2ePureOp (P := zeroPqxdhPrims) (C := C) (K := K) (decT := decT) (encT := encT)
          .ghostStateSplit (.fst (e2eGsSt gsE))))
        (.eqN .v0 (.nat 0))).eval ρ = (st.st .A).chainEpochs.contains 0 := by
    simp only [Expr.eval, hceps, List.take_of_length_le hlen, Expr.v0, Env.get]
    have hbeq : (fun x : ℕ => decide (x = 0)) = (0 == ·) := by
      funext x
      rcases Nat.eq_zero_or_pos x with rfl | hx
      · rfl
      · rw [decide_eq_false (by omega), beq_eq_false_iff_ne.mpr (by omega)]
    rw [hbeq, List.any_beq]
  unfold epoch0CorrOKE configEpoch0Distinguisher
  change ((noAliceBelow10E (C := C) (K := K) (decT := decT) (encT := encT) gsE pE).eval ρ &&
      !(!(pE.eval ρ) &&
        (Expr.anyB 5
          (gpCEps (e2ePureOp (P := zeroPqxdhPrims) (C := C) (K := K) (decT := decT) (encT := encT)
            .ghostStateSplit (.fst (e2eGsSt gsE))))
          (.eqN .v0 (.nat 0))).eval ρ)) = _
  rw [h10, hany, hp]
  cases party <;> rfl

theorem cost_epoch0CorrOKE_le {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (pE : Expr EOps Γ .bool) :
    (epoch0CorrOKE (C := C) (K := K) (decT := decT) (encT := encT) gsE pE).cost ≤
      2 * gsE.cost + 2 * pE.cost + 80 := by
  have h10 := cost_noAliceBelow10E_le (C := C) (K := K) (decT := decT) (encT := encT) gsE pE
  have hb0 : bits 0 = 1 := by decide
  simp only [epoch0CorrOKE, gpCEps, e2eGsSt, cost_e2ePureOp, E2EPureOp.cost, Expr.cost,
    Expr.v0, hb0]
  omega

theorem size_epoch0CorrOKE_le {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (pE : Expr EOps Γ .bool) :
    (epoch0CorrOKE (C := C) (K := K) (decT := decT) (encT := encT) gsE pE).size ≤
      2 * gsE.size + 2 * pE.size + 50 := by
  have h10 := size_noAliceBelow10E_le (C := C) (K := K) (decT := decT) (encT := encT) gsE pE
  have hp := size_e2ePureOp (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) .ghostStateSplit (.fst (e2eGsSt gsE))
  have hb0 : bits 0 = 1 := by decide
  have hb5 : bits 5 = 3 := by decide
  simp only [epoch0CorrOKE, gpCEps, e2eGsSt, E2EPureOp.opSize, Expr.size, Expr.v0, hb0, hb5]
    at hp ⊢
  omega

def epoch0IjArmC (hooks : SpqrDslHooks ℓ zeroPqxdhPrims C K decT encT)
    {ι : Type} {T : OracleSpec ι} {I : Iface ESig T}
    (coins : E2ECoinSamplers ℓ zeroPqxdhPrims C K decT encT I)
    (q Δ qep : ℕ) {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (ijArg : Expr EOps Γ (.prod .bool (B 32))) :
    Comp EOps I Γ (.prod (smRT GhostStT) (e2eGsTy ℓ)) :=
  .bind (.ret (.pair gsE ijArg))
    (let gs0 : Expr EOps _ (e2eGsTy ℓ) := .fst .v0
     let p0 : Expr EOps _ .bool := .fst (.snd .v0)
     let c0 : Expr EOps _ (B 32) := .snd (.snd .v0)
     let refuseCond : Expr EOps _ .bool :=
       orE (e2eGsWin gs0)
         (orE (isSomeE (e2eInTransitE q gs0 (otherE p0) c0))
           (orE (.not (e2eSafeInjE Δ gs0)) (.not (ratchetKeyAdmissibleE c0))))
     .ite refuseCond
       (.ret (.pair (smRRecvE .none) gs0))
       (.bind coins.draw256
         (.bind (drReceiveC hooks I
             (.pair (pGet (e2eGsSt (.fst .v1)) (.fst (.snd .v1)))
               (.pair (.snd (.snd .v1)) .v0)))
           (.caseOpt .v0
             (.ret (.pair (smRRecvE (.some recvResultRejE)) (.fst .v2)))
             (let st' : Expr EOps _ GhostStT := .fst .v0
              let t' : Expr EOps _ .nat := .fst (.snd .v0)
              let i' : Expr EOps _ .nat := .fst (.snd (.snd .v0))
              let m' : Expr EOps _ PlainT := .snd (.snd (.snd .v0))
              let gs3 : Expr EOps _ (e2eGsTy ℓ) := .fst .v3
              let p3 : Expr EOps _ .bool := .fst (.snd .v3)
              .ite (.lt (.nat (qep + 1)) t')
                (.ret (.pair (smRRecvE (.some recvResultRejE)) gs3))
                (let posE : Expr EOps _ posTy := .pair (otherE p3) (.pair t' i')
                 .ite (e2eTrivialE q Δ gs3 posE)
                   (.ret (.pair (smRRecvE (.some (recvResultAccE t' i' (.some m'))))
                     (e2eAcceptE q gs3 p3 st' posE)))
                   (.ret (.pair (smRRecvE (.some recvResultRejE))
                     (.ite (.eqN t' (.nat 0))
                       (e2eGsSetWin gs3 (.bool true)) gs3)))))))))

theorem epoch0IjArmC_queries_zero (hooks : SpqrDslHooks ℓ zeroPqxdhPrims C K decT encT)
    {ι : Type} {T : OracleSpec ι} {I : Iface ESig T}
    (coins : E2ECoinSamplers ℓ zeroPqxdhPrims C K decT encT I)
    (q Δ qep : ℕ) {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (ijArg : Expr EOps Γ (.prod .bool (B 32)))
    (w : I.Tag → ℕ) :
    (epoch0IjArmC hooks coins q Δ qep gsE ijArg).queries w (fun _ => 0) = 0 := by
  simp [epoch0IjArmC, Comp.queries, coins.draw256_queries_zero, drReceiveC_queries]

theorem epoch0IjArmC_cost (hooks : SpqrDslHooks ℓ zeroPqxdhPrims C K decT encT)
    {ι : Type} {T : OracleSpec ι} {I : Iface ESig T}
    (coins : E2ECoinSamplers ℓ zeroPqxdhPrims C K decT encT I)
    (q Δ qep : ℕ) {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (ijArg : Expr EOps Γ (.prod .bool (B 32))) :
    (epoch0IjArmC hooks coins q Δ qep gsE ijArg).cost ≤
      gsE.cost + ijArg.cost + 5105250 + 10 * (ℓ / 32 + 1) + 420 * q +
        2 * bits Δ + bits (qep + 1) := by
  let t0 : Ty ESig := .prod (e2eGsTy ℓ) (.prod .bool (B 32))
  let tOut : Ty ESig := drRecvOutT ℓ
  let tQuad : Ty ESig := .prod GhostStT (.prod .nat (.prod .nat PlainT))
  let Γ0 := t0 :: Γ
  let Γ1 : List (Ty ESig) := CryptoVerification.E2E.Costed.BV256 :: Γ0
  let Γ2 := tOut :: Γ1
  let Γ3 := tQuad :: Γ2
  have hinTr := cost_e2eInTransitE_le (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) q
    (.fst .v0 : Expr EOps Γ0 (e2eGsTy ℓ)) (otherE (.fst (.snd .v0))) (.snd (.snd .v0))
  have hsafe := cost_e2eSafeInjE_le (ℓ := ℓ) (O' := EOps) Δ
    (.fst .v0 : Expr EOps Γ0 (e2eGsTy ℓ))
  have hdraw := coins.draw256_cost (Γ := Γ0)
  have hrecv := drReceiveC_cost hooks I
    (.pair (pGet (e2eGsSt (.fst .v1)) (.fst (.snd .v1))) (.pair (.snd (.snd .v1)) .v0) :
      Expr EOps Γ1 (.prod GhostStT (.prod (B 32) CryptoVerification.E2E.Costed.BV256)))
  have htriv := cost_e2eTrivialE_le (ℓ := ℓ) (O' := EOps) q Δ
    (.fst .v3 : Expr EOps Γ3 (e2eGsTy ℓ))
    (.pair (otherE (.fst (.snd .v3))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hacc := cost_e2eAcceptE_le (ℓ := ℓ) (O' := EOps) q
    (.fst .v3 : Expr EOps Γ3 (e2eGsTy ℓ)) (.fst (.snd .v3)) (.fst .v0)
    (.pair (otherE (.fst (.snd .v3))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hsetW := cost_e2eGsSetWin_le (ℓ := ℓ) (O' := EOps)
    (.fst .v3 : Expr EOps Γ3 (e2eGsTy ℓ)) (.bool true)
  have hb0 : bits 0 = 1 := by decide
  simp only [epoch0IjArmC, orE, isSomeE, otherE, pGet, e2eGsSt, e2eGsWin,
    cost_ratchetKeyAdmissibleE, cost_smRRecvE,
    cost_recvResultRejE, cost_recvResultAccE, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, hb0] at hinTr hsafe hdraw hrecv htriv hacc hsetW ⊢
  omega

theorem epoch0IjArmC_spqr_size_le
    {ι : Type} {T : OracleSpec ι} {I : Iface ESig T}
    (coins : E2ECoinSamplers ℓ zeroPqxdhPrims C K decT encT I)
    (h256 : ∀ {Γ'}, (coins.draw256 (Γ := Γ')).size ≤ 4)
    (q Δ qep : ℕ) {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (ijArg : Expr EOps Γ (.prod .bool (B 32))) :
    (epoch0IjArmC (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) coins q Δ qep gsE ijArg).size ≤
      gsE.size + ijArg.size + 6 * bits q + 2 * bits Δ + bits (qep + 1) + 79000 := by
  let t0 : Ty ESig := .prod (e2eGsTy ℓ) (.prod .bool (B 32))
  let tOut : Ty ESig := drRecvOutT ℓ
  let tQuad : Ty ESig := .prod GhostStT (.prod .nat (.prod .nat PlainT))
  let Γ0 := t0 :: Γ
  let Γ1 : List (Ty ESig) := CryptoVerification.E2E.Costed.BV256 :: Γ0
  let Γ2 := tOut :: Γ1
  let Γ3 := tQuad :: Γ2
  have hinTr := size_e2eInTransitE_le (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) q
    (.fst .v0 : Expr EOps Γ0 (e2eGsTy ℓ)) (otherE (.fst (.snd .v0))) (.snd (.snd .v0))
  have hsafe := size_e2eSafeInjE_le (ℓ := ℓ) (O' := EOps) Δ
    (.fst .v0 : Expr EOps Γ0 (e2eGsTy ℓ))
  have hdraw := h256 (Γ' := Γ0)
  have hrecv := drReceiveC_spqr_size_le (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) I
    (.pair (pGet (e2eGsSt (.fst .v1)) (.fst (.snd .v1))) (.pair (.snd (.snd .v1)) .v0) :
      Expr EOps Γ1 (.prod GhostStT (.prod (B 32) CryptoVerification.E2E.Costed.BV256)))
  have htriv := size_e2eTrivialE_le (ℓ := ℓ) (O' := EOps) q Δ
    (.fst .v3 : Expr EOps Γ3 (e2eGsTy ℓ))
    (.pair (otherE (.fst (.snd .v3))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hacc := size_e2eAcceptE_le (ℓ := ℓ) (O' := EOps) q
    (.fst .v3 : Expr EOps Γ3 (e2eGsTy ℓ)) (.fst (.snd .v3)) (.fst .v0)
    (.pair (otherE (.fst (.snd .v3))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hsetW := size_e2eGsSetWin_le (ℓ := ℓ) (O' := EOps)
    (.fst .v3 : Expr EOps Γ3 (e2eGsTy ℓ)) (.bool true)
  have hb0 : bits 0 = 1 := by decide
  simp only [epoch0IjArmC, orE, isSomeE, otherE, pGet, e2eGsSt, e2eGsWin,
    size_ratchetKeyAdmissibleE, smRRecvE, recvResultRejE, recvResultAccE,
    Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, hb0]
    at hinTr hsafe hdraw hrecv htriv hacc hsetW ⊢
  omega

theorem epoch0IjArmC_eval (hooks : SpqrDslHooks ℓ zeroPqxdhPrims C K decT encT)
    {ι : Type} {T : OracleSpec ι} {I : Iface ESig T}
    (coins : E2ECoinSamplers ℓ zeroPqxdhPrims C K decT encT I)
    (q Δ qep : ℕ) {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (ijArg : Expr EOps Γ (.prod .bool (B 32))) (ρ : Env Γ)
    (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (party : Party) (c : Bytes)
    (h : SmReachBounded C K q st)
    (hgs : gsE.eval ρ = e2eGsEnc st) (harg : ijArg.eval ρ = (partyEnc party, c)) :
    (epoch0IjArmC hooks coins q Δ qep gsE ijArg).eval ρ =
      Prod.map (fun rr => (none, (rr.map CryptoVerification.E2E.Costed.recvResultEnc, none)))
        e2eGsEnc <$>
        I.liftP ((injectR
          (sessionSchemeFixedSpk
            (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins)
          Δ qep (configEpoch0Distinguisher (ratchetKeyAdmissible protoSignalCodec decT encT))
          (party, c)).run st) := by
  set sm := sessionSchemeFixedSpk
    (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins
  set cfg : CryptoGames.SM.ConfigR (GhostState Bytes) (Plain ℓ) Bytes :=
    configEpoch0Distinguisher (ratchetKeyAdmissible protoSignalCodec decT encT)
  have hinjFull : ∀ t, cfg.base.injectFull t = (t == 0) := fun _ => rfl
  have hinjOK : cfg.injOK = ratchetKeyAdmissible protoSignalCodec decT encT := rfl
  unfold epoch0IjArmC injectR
  dsimp only [Comp.eval]
  rw [pair_eval, hgs, harg, pure_bind]
  let t0 : Ty ESig := .prod (e2eGsTy ℓ) (.prod .bool (B 32))
  set ρ₁ := Env.cons (t := t0) (e2eGsEnc st, (partyEnc party, c)) ρ
  have hOther : (otherE (.fst (.snd (Expr.v0 (O := EOps))))).eval ρ₁ = partyEnc party.other := by
    rw [otherE_eval]
    cases party <;> rfl
  have hInTr := eval_e2eInTransitE (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) q (.fst .v0) (otherE (.fst (.snd .v0))) (.snd (.snd .v0))
    ρ₁ st party.other h.lists.trans_le rfl hOther
  have hc1 : (Expr.snd (.snd (Expr.v0 (O := EOps)))).eval ρ₁ = c := rfl
  rw [hc1] at hInTr
  have hSafeInj : (e2eSafeInjE Δ (.fst (Expr.v0 (O := EOps)))).eval ρ₁ = st.safeInj Δ :=
    eval_e2eSafeInjE Δ (.fst .v0) ρ₁ st rfl
  have hAdm : (ratchetKeyAdmissibleE (P := zeroPqxdhPrims) (C := C) (K := K)
      (decT := decT) (encT := encT) (.snd (.snd .v0))).eval ρ₁ = cfg.injOK c := by
    rw [eval_ratchetKeyAdmissibleE, hc1, hinjOK]
  have hRefuse :
      (orE (e2eGsWin (.fst (Expr.v0 (O := EOps))))
        (orE (isSomeE (e2eInTransitE q (.fst .v0) (otherE (.fst (.snd .v0))) (.snd (.snd .v0))))
          (orE (.not (e2eSafeInjE Δ (.fst .v0)))
            (.not (ratchetKeyAdmissibleE (.snd (.snd .v0))))))).eval ρ₁ =
      (st.win || (st.inTransit party.other c).isSome || !st.safeInj Δ || !cfg.injOK c) := by
    simp only [orE_eval, isSomeE_eval, Expr.eval, hInTr, hSafeInj, hAdm, Option.isSome_map]
    simp [ρ₁, e2eGsWin, e2eGsEnc, Expr.eval, Expr.v0, Bool.or_assoc]
  rw [hRefuse]
  by_cases href : st.win || (st.inTransit party.other c).isSome || !st.safeInj Δ || !cfg.injOK c
  · simp only [href, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure,
      pure_bind, liftP_pure, map_pure, Prod.map]
    rfl
  · simp only [href, Bool.false_eq_true, ↓reduceIte, coins.draw256_eval,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      pure_bind, bind_assoc, liftP_bind, map_bind]
    refine bind_congr fun rc => ?_
    set ρ₂ := Env.cons (t := CryptoVerification.E2E.Costed.BV256) rc ρ₁
    have hRecvIn :
        (Expr.pair (pGet (e2eGsSt (.fst (Expr.v1 (O := EOps)))) (.fst (.snd .v1)))
          (.pair (.snd (.snd .v1)) .v0)).eval ρ₂ =
        (st.st party, (c, rc)) := by
      rw [pair_eval, pGet_eval _ _ ρ₂ st.st party rfl rfl]
      rfl
    have hgParty : PartyReachInv C K
        ((Expr.pair (pGet (e2eGsSt (.fst (Expr.v1 (O := EOps)))) (.fst (.snd .v1)))
          (.pair (.snd (.snd .v1)) .v0)).eval ρ₂).1 := by
      rw [hRecvIn]
      exact h.reach.party party
    rw [drReceiveC_eval hooks I _ ρ₂ idA idB spkCoins hgParty, hRecvIn]
    simp only [pure_bind]
    cases hrecv : sm.receive (st.st party) c rc with
    | none =>
      have hv0 : (Expr.v0 (O := EOps)).eval (Env.cons (t := drRecvOutT ℓ) none ρ₂) = none := rfl
      rw [hv0]
      simp only [StateT.run_pure, liftP_pure, map_pure, Prod.map]
      rfl
    | some quad =>
      rcases quad with ⟨st', t', i', m'⟩
      have hv0 : (Expr.v0 (O := EOps)).eval
          (Env.cons (t := drRecvOutT ℓ) (some (st', (t', (i', m')))) ρ₂) =
          some (st', (t', (i', m'))) := rfl
      rw [hv0]
      dsimp only
      let tQuad : Ty ESig := .prod GhostStT (.prod .nat (.prod .nat PlainT))
      set ρ₃ := Env.cons (t := tQuad) (st', (t', (i', m')))
        (Env.cons (t := drRecvOutT ℓ) (some (st', (t', (i', m')))) ρ₂)
      have hlt : (Expr.lt (.nat (qep + 1)) (.fst (.snd (Expr.v0 (O := EOps))))).eval ρ₃ =
          decide (qep + 1 < t') := rfl
      rw [hlt]
      by_cases hqep : qep + 1 < t'
      · simp only [hqep, decide_true, ↓reduceIte, StateT.run_pure, liftP_pure,
          map_pure, Prod.map]
        rfl
      · simp only [hqep, decide_false, Bool.false_eq_true, ↓reduceIte]
        have hpos3 :
            (Expr.pair (otherE (.fst (.snd (Expr.v3 (O := EOps)))))
              (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0))))).eval ρ₃ =
            posEnc ⟨party.other, t', i'⟩ := by
          have ho3 : (otherE (.fst (.snd (Expr.v3 (O := EOps))))).eval ρ₃ =
              partyEnc party.other := by
            rw [otherE_eval]
            cases party <;> rfl
          simp only [Expr.eval, ho3]
          rfl
        have hTriv := eval_e2eTrivialE q Δ (.fst (Expr.v3 (O := EOps)))
          (.pair (otherE (.fst (.snd .v3))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
          ρ₃ st ⟨party.other, t', i'⟩ h.lists rfl hpos3
        rw [hTriv]
        by_cases htriv : st.trivial Δ ⟨party.other, t', i'⟩
        · simp only [htriv, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
            pure_bind, liftP_pure, map_pure, Prod.map]
          have hAcc := eval_e2eAcceptE q (.fst (Expr.v3 (O := EOps))) (.fst (.snd .v3)) (.fst .v0)
            (.pair (otherE (.fst (.snd .v3))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
            ρ₃ st party ⟨party.other, t', i'⟩ h.lists rfl rfl hpos3
          simp only [pair_eval, eval_smRRecvE, some_eval, eval_recvResultAccE, hAcc]
          rfl
        · simp only [htriv, Bool.false_eq_true, ↓reduceIte, hinjFull]
          have heq0 : (Expr.eqN (.fst (.snd (Expr.v0 (O := EOps)))) (.nat 0)).eval ρ₃ =
              (t' == 0) := rfl
          by_cases ht0 : t' == 0
          · simp only [ht0, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
              pure_bind, liftP_pure, map_pure, Prod.map]
            have hSetWin := eval_e2eGsSetWin (.fst (Expr.v3 (O := EOps))) (.bool true) ρ₃ st rfl
            simp only [pair_eval, eval_smRRecvE, some_eval, eval_recvResultRejE,
              ite_eval, heq0, ht0, ↓reduceIte, hSetWin]
            rfl
          · simp only [ht0, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
              liftP_pure, map_pure, Prod.map]
            simp only [pair_eval, eval_smRRecvE, some_eval, eval_recvResultRejE,
              ite_eval, heq0, ht0, Bool.false_eq_true, ↓reduceIte]
            rfl

def epoch0CrArmC {ι : Type} {T : OracleSpec ι} {I : Iface ESig T}
    (q : ℕ) {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (crArg : Expr EOps Γ .bool) :
    Comp EOps I Γ (.prod (smRT GhostStT) (e2eGsTy ℓ)) :=
  .bind (.ret (.pair gsE crArg))
    (let gs0 : Expr EOps _ (e2eGsTy ℓ) := .fst .v0
     let p0 : Expr EOps _ .bool := .snd .v0
     let refuseCond : Expr EOps _ .bool :=
       orE (e2eGsWin gs0)
         (orE (.not (e2eCorrAllowedE q gs0 p0))
           (orE (e2eInWindowE gs0 p0) (.not (epoch0CorrOKE gs0 p0))))
     .ite refuseCond
       (.ret (.pair (smRCorrE .none) gs0))
       (.ret (.pair (smRCorrE (.some (pGet (e2eGsSt gs0) p0)))
         (e2eAfterCorrAllowedE gs0 p0))))

theorem epoch0CrArmC_queries {ι : Type} {T : OracleSpec ι} {I : Iface ESig T}
    (q : ℕ) {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (crArg : Expr EOps Γ .bool)
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    (epoch0CrArmC (C := C) (K := K) (decT := decT) (encT := encT) (I := I) q gsE crArg).queries
      w ws = 0 := by
  simp [epoch0CrArmC, Comp.queries]

theorem epoch0CrArmC_cost {ι : Type} {T : OracleSpec ι} {I : Iface ESig T}
    (q : ℕ) {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (crArg : Expr EOps Γ .bool) :
    (epoch0CrArmC (C := C) (K := K) (decT := decT) (encT := encT) (I := I) q gsE crArg).cost ≤
      gsE.cost + crArg.cost + 75 * q + 650 := by
  let t0 : Ty ESig := .prod (e2eGsTy ℓ) .bool
  have hallow := cost_e2eCorrAllowedE_le (ℓ := ℓ) (O' := EOps) q
    (.fst .v0 : Expr EOps (t0 :: Γ) (e2eGsTy ℓ)) (.snd .v0)
  have hwin := cost_e2eInWindowE_le (ℓ := ℓ) (O' := EOps)
    (.fst .v0 : Expr EOps (t0 :: Γ) (e2eGsTy ℓ)) (.snd .v0)
  have hcorrOK := cost_epoch0CorrOKE_le (C := C) (K := K) (decT := decT) (encT := encT)
    (.fst .v0 : Expr EOps (t0 :: Γ) (e2eGsTy ℓ)) (.snd .v0)
  have hafter := cost_e2eAfterCorrAllowedE_le (ℓ := ℓ) (O' := EOps)
    (.fst .v0 : Expr EOps (t0 :: Γ) (e2eGsTy ℓ)) (.snd .v0)
  simp only [epoch0CrArmC, orE, pGet, e2eGsSt, e2eGsWin, cost_smRCorrE, Comp.cost, Expr.cost,
    Expr.v0] at hallow hwin hcorrOK hafter ⊢
  omega

theorem epoch0CrArmC_size_le {ι : Type} {T : OracleSpec ι} {I : Iface ESig T}
    (q : ℕ) {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (crArg : Expr EOps Γ .bool) :
    (epoch0CrArmC (C := C) (K := K) (decT := decT) (encT := encT) (I := I) q gsE crArg).size ≤
      gsE.size + crArg.size + 2 * bits q + 900 := by
  let t0 : Ty ESig := .prod (e2eGsTy ℓ) .bool
  have hallow := size_e2eCorrAllowedE_le (ℓ := ℓ) (O' := EOps) q
    (.fst .v0 : Expr EOps (t0 :: Γ) (e2eGsTy ℓ)) (.snd .v0)
  have hwin := size_e2eInWindowE_le (ℓ := ℓ) (O' := EOps)
    (.fst .v0 : Expr EOps (t0 :: Γ) (e2eGsTy ℓ)) (.snd .v0)
  have hcorrOK := size_epoch0CorrOKE_le (C := C) (K := K) (decT := decT) (encT := encT)
    (.fst .v0 : Expr EOps (t0 :: Γ) (e2eGsTy ℓ)) (.snd .v0)
  have hafter := size_e2eAfterCorrAllowedE_le (ℓ := ℓ) (O' := EOps)
    (.fst .v0 : Expr EOps (t0 :: Γ) (e2eGsTy ℓ)) (.snd .v0)
  simp only [epoch0CrArmC, orE, pGet, e2eGsSt, e2eGsWin, smRCorrE, Comp.size, Expr.size,
    Expr.v0] at hallow hwin hcorrOK hafter ⊢
  omega

theorem epoch0CrArmC_eval {ι : Type} {T : OracleSpec ι} {I : Iface ESig T}
    (q : ℕ) {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (crArg : Expr EOps Γ .bool) (ρ : Env Γ)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (party : Party)
    (h : SmReachBounded C K q st)
    (hgs : gsE.eval ρ = e2eGsEnc st) (harg : crArg.eval ρ = partyEnc party) :
    (epoch0CrArmC (C := C) (K := K) (decT := decT) (encT := encT) (I := I) q gsE crArg).eval ρ =
      Prod.map (fun st? => (none, (none, st?))) e2eGsEnc <$>
        I.liftP ((corrR (configEpoch0Distinguisher (ratchetKeyAdmissible protoSignalCodec decT encT))
          party).run st) := by
  set cfg : CryptoGames.SM.ConfigR (GhostState Bytes) (Plain ℓ) Bytes :=
    configEpoch0Distinguisher (ratchetKeyAdmissible protoSignalCodec decT encT)
  have hr1 : cfg.r1 = true := rfl
  unfold epoch0CrArmC corrR
  simp only [Comp.eval, Expr.eval, hgs, harg, pure_bind]
  let t0 : Ty ESig := .prod (e2eGsTy ℓ) .bool
  set ρ₁ := Env.cons (t := t0) (e2eGsEnc st, partyEnc party) ρ
  have hAllow := eval_e2eCorrAllowedE q (.fst (Expr.v0 (O := EOps))) (.snd .v0)
    ρ₁ st party h.lists rfl rfl
  have hInWin := eval_e2eInWindowE (.fst (Expr.v0 (O := EOps))) (.snd .v0)
    ρ₁ st party rfl rfl
  have hCorrOK :
      (epoch0CorrOKE (C := C) (K := K) (decT := decT) (encT := encT)
        (.fst .v0) (.snd .v0)).eval ρ₁ = cfg.corrOK st party :=
    eval_epoch0CorrOKE (.fst .v0) (.snd .v0) ρ₁ st party h rfl rfl
  have hRefuse :
      (orE (e2eGsWin (.fst (Expr.v0 (O := EOps))))
        (orE (.not (e2eCorrAllowedE q (.fst .v0) (.snd .v0)))
          (orE (e2eInWindowE (.fst .v0) (.snd .v0))
            (.not (epoch0CorrOKE (.fst .v0) (.snd .v0)))))).eval ρ₁ =
      (st.win || !st.corrAllowed party || (cfg.r1 && inWindow st party) ||
        !cfg.corrOK st party) := by
    simp only [orE_eval, Expr.eval, hAllow, hInWin, hCorrOK, hr1, Bool.true_and]
    simp [ρ₁, e2eGsWin, e2eGsEnc, Expr.eval, Expr.v0, Bool.or_assoc]
  rw [hRefuse]
  by_cases href :
      st.win || !st.corrAllowed party || (cfg.r1 && inWindow st party) || !cfg.corrOK st party
  · simp only [href, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure,
      pure_bind, liftP_pure, map_pure, Prod.map]
    rfl
  · simp only [href, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      StateT.run_set, StateT.run_pure, pure_bind, liftP_pure, map_pure, Prod.map]
    have hallowTrue : st.corrAllowed party = true := by
      cases hc : st.corrAllowed party
      · simp [hc] at href
      · rfl
    have hAfter := eval_e2eAfterCorrAllowedE (.fst (Expr.v0 (O := EOps))) (.snd .v0)
      ρ₁ st party hallowTrue rfl rfl
    have hpGet := pGet_eval (e2eGsSt (.fst (Expr.v0 (O := EOps)))) (.snd .v0)
      ρ₁ st.st party rfl rfl
    simp only [eval_smRCorrE, some_eval, hpGet, hAfter]

/-- Combined 5-oracle step handler for `configEpoch0Distinguisher` over `EOps`. -/
def epoch0OracleStepE2EC (q Δ qep : ℕ) {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (qryE : Expr EOps Γ smQT) :
    Comp EOps (coinE2EIface (coinOnlyIface ℓ Pt)) Γ (.prod (smRT GhostStT) (e2eGsTy ℓ)) :=
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) (coinOnlyIface ℓ Pt)
  .bind (.ret (.pair gsE qryE))
    (.caseSum (.snd .v0)
      (drTrArmC hooks coins q Δ qep (.fst .v1) .v0)
      (.caseSum .v0
        (drChArmC hooks coins q Δ qep (.fst .v2) .v0)
        (.caseSum .v0
          (drDlArmC hooks coins q (.fst .v3) .v0)
          (.caseSum .v0
            (epoch0IjArmC hooks coins q Δ qep (.fst .v4) .v0)
            (epoch0CrArmC q (.fst .v4) .v0)))))

theorem epoch0OracleStepE2EC_queries_zero (q Δ qep : ℕ) {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (qryE : Expr EOps Γ smQT) (w : Empty → ℕ) :
    (epoch0OracleStepE2EC (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT)
      q Δ qep gsE qryE).queries w (fun _ => 0) = 0 := by
  simp [epoch0OracleStepE2EC, Comp.queries, drTrArmC_queries_zero, drChArmC_queries_zero,
    drDlArmC_queries_zero, epoch0IjArmC_queries_zero, epoch0CrArmC_queries]

theorem epoch0OracleStepE2EC_cost (q Δ qep : ℕ) {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (qryE : Expr EOps Γ smQT) :
    (epoch0OracleStepE2EC (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT)
      q Δ qep gsE qryE).cost ≤
      gsE.cost + qryE.cost + 5106000 + 10 * (ℓ / 32 + 1) + 420 * q +
        3 * bits Δ + bits qep + bits (qep + 1) := by
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) (coinOnlyIface ℓ Pt)
  let tTop : Ty ESig := .prod (e2eGsTy ℓ) smQT
  let r1T : Ty ESig :=
    .sum (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))
      (.sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool))
  let r2T : Ty ESig := .sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool)
  let r3T : Ty ESig := .sum (.prod .bool (B 32)) .bool
  have htr := drTrArmC_cost hooks coins q Δ qep
    (.fst .v1 : Expr EOps (.prod .bool (.prod PlainT (.opt BV512)) :: tTop :: Γ) (e2eGsTy ℓ)) .v0
  have hch := drChArmC_cost hooks coins q Δ qep
    (.fst .v2 : Expr EOps
      (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))) :: r1T :: tTop :: Γ)
      (e2eGsTy ℓ)) .v0
  have hdl := drDlArmC_cost hooks coins q
    (.fst .v3 : Expr EOps (.prod .bool (B 32) :: r2T :: r1T :: tTop :: Γ) (e2eGsTy ℓ)) .v0
  have hij := epoch0IjArmC_cost hooks coins q Δ qep
    (.fst .v4 : Expr EOps (.prod .bool (B 32) :: r3T :: r2T :: r1T :: tTop :: Γ) (e2eGsTy ℓ)) .v0
  have hcr := epoch0CrArmC_cost (C := C) (K := K) (decT := decT) (encT := encT)
    (I := coinE2EIface (coinOnlyIface ℓ Pt)) q
    (.fst .v4 : Expr EOps (.bool :: r3T :: r2T :: r1T :: tTop :: Γ) (e2eGsTy ℓ)) .v0
  dsimp only [hooks, coins] at htr hch hdl hij
  simp only [epoch0OracleStepE2EC, Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    Expr.v4] at htr hch hdl hij hcr ⊢
  omega

theorem epoch0OracleStepE2EC_size_le (q Δ qep : ℕ) {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (qryE : Expr EOps Γ smQT) :
    (epoch0OracleStepE2EC (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT)
      q Δ qep gsE qryE).size ≤
      gsE.size + qryE.size + 17 * bits q + 7 * bits Δ + 4 * bits qep +
        bits (qep + 1) + 200000 := by
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) (coinOnlyIface ℓ Pt)
  have hc256 : ∀ {Γ'}, (coins.draw256 (Γ := Γ')).size ≤ 4 := fun {_} => by
    simp only [coins, coinE2ESamplers, mkE2ECoinSamplers, Comp.size, Expr.size]; omega
  have hc512 : ∀ {Γ'}, (coins.draw512 (Γ := Γ')).size ≤ 4 := fun {_} => by
    simp only [coins, coinE2ESamplers, mkE2ECoinSamplers, Comp.size, Expr.size]; omega
  let tTop : Ty ESig := .prod (e2eGsTy ℓ) smQT
  let r1T : Ty ESig :=
    .sum (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))
      (.sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool))
  let r2T : Ty ESig := .sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool)
  let r3T : Ty ESig := .sum (.prod .bool (B 32)) .bool
  have htr := drTrArmC_spqr_size_le (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) coins hc512 q Δ qep
    (.fst .v1 : Expr EOps (.prod .bool (.prod PlainT (.opt BV512)) :: tTop :: Γ) (e2eGsTy ℓ)) .v0
  have hch := drChArmC_spqr_size_le (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) coins hc512 q Δ qep
    (.fst .v2 : Expr EOps
      (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))) :: r1T :: tTop :: Γ)
      (e2eGsTy ℓ)) .v0
  have hdl := drDlArmC_spqr_size_le (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) coins hc256 q
    (.fst .v3 : Expr EOps (.prod .bool (B 32) :: r2T :: r1T :: tTop :: Γ) (e2eGsTy ℓ)) .v0
  have hij := epoch0IjArmC_spqr_size_le (C := C) (K := K) (decT := decT) (encT := encT)
    coins hc256 q Δ qep
    (.fst .v4 : Expr EOps (.prod .bool (B 32) :: r3T :: r2T :: r1T :: tTop :: Γ) (e2eGsTy ℓ)) .v0
  have hcr := epoch0CrArmC_size_le (C := C) (K := K) (decT := decT) (encT := encT)
    (I := coinE2EIface (coinOnlyIface ℓ Pt)) q
    (.fst .v4 : Expr EOps (.bool :: r3T :: r2T :: r1T :: tTop :: Γ) (e2eGsTy ℓ)) .v0
  dsimp only [coins] at htr hch hdl hij
  simp only [epoch0OracleStepE2EC, Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    Expr.v4] at htr hch hdl hij hcr ⊢
  omega

theorem epoch0OracleStepE2EC_eval (q Δ qep : ℕ) {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (qryE : Expr EOps Γ smQT) (ρ : Env Γ)
    (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (h : SmReachBounded C K q st)
    (hgs : gsE.eval ρ = e2eGsEnc st) (hqry : qryE.eval ρ = smQenc sq) :
    (epoch0OracleStepE2EC (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT)
      q Δ qep gsE qryE).eval ρ =
      Prod.map (smRenc (stT := GhostStT) id sq) e2eGsEnc <$>
        (coinE2EIface (coinOnlyIface ℓ Pt)).liftP ((oracleImplR
          (sessionSchemeFixedSpk
            (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins)
          Δ qep (configEpoch0Distinguisher (ratchetKeyAdmissible protoSignalCodec decT encT))
          sq).run st) := by
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) (coinOnlyIface ℓ Pt)
  unfold epoch0OracleStepE2EC
  simp only [Comp.eval, Expr.eval, hgs, hqry, pure_bind]
  rcases sq with (((⟨party, m, optR⟩ | ⟨party, m0, m1, optR⟩) | ⟨party, c⟩) | ⟨party, c⟩) | party
  · dsimp only [smQenc, partyToBool_eq_partyEnc]
    exact drTrArmC_eval hooks coins q Δ qep _ _ _ idA idB spkCoins st party m optR h rfl rfl
  · dsimp only [smQenc, partyToBool_eq_partyEnc]
    exact drChArmC_eval hooks coins q Δ qep _ _ _ idA idB spkCoins st party m0 m1 optR h rfl rfl
  · dsimp only [smQenc, partyToBool_eq_partyEnc]
    exact drDlArmC_eval hooks coins q _ _ _ idA idB spkCoins st party c h rfl rfl
  · dsimp only [smQenc, partyToBool_eq_partyEnc]
    exact epoch0IjArmC_eval hooks coins q Δ qep _ _ _ idA idB spkCoins st party c h rfl rfl
  · dsimp only [smQenc, partyToBool_eq_partyEnc, Expr.v0, Expr.eval, Env.get]
    refine Eq.trans (epoch0CrArmC_eval (C := C) (K := K) (decT := decT) (encT := encT)
      (I := coinE2EIface (coinOnlyIface ℓ Pt)) q _ _ _ st party h ?_ ?_) ?_
    · rfl
    · rfl
    · dsimp only [oracleImplR]
      congr 1
      funext ⟨st?, s'⟩
      cases st? <;> rfl

def epoch0FinishE (q : ℕ) : Expr EOps [e2eGsTy ℓ, .bool] .bool :=
  .and (orE (.lt (.nat 0) (.tget (.fst (e2eGsMaxAcc .v0)) (.nat 0))) (e2eGsWin .v0))
    (.not (.anyB q (e2eGsCorrs .v0) (.and (.fst .v0) (.eqN (.snd .v0) (.nat 0)))))

theorem eval_epoch0FinishE (q : ℕ)
    (s : GameState (GhostState Bytes) (Plain ℓ) Bytes) (b' : Bool)
    (hcorrs : s.corrs.length ≤ q) :
    (epoch0FinishE (C := C) (K := K) (decT := decT) (encT := encT) q).eval
      (.cons (e2eGsEnc s) (.cons b' .nil)) =
      ((decide (0 < s.maxAcc .A 0) || s.win) && !(s.corrs.contains (.B, 0))) := by
  have hlen : (s.corrs.map (fun pe => (partyEnc pe.1, pe.2))).length ≤ q := by
    simpa using hcorrs
  have hany :
      ((s.corrs.map (fun pe => (partyEnc pe.1, pe.2))).take q).any
        (fun x => x.1 && decide (x.2 = 0)) = s.corrs.contains (.B, 0) := by
    rw [List.take_of_length_le hlen, List.any_map]
    have hpred :
        ((fun x : Bool × ℕ => x.1 && decide (x.2 = 0)) ∘ fun pe : Party × ℕ =>
          (partyEnc pe.1, pe.2)) = ((.B, 0) == ·) := by
      funext ⟨p, ep⟩
      rcases p with _ | _
      · rfl
      · rcases Nat.eq_zero_or_pos ep with rfl | hep
        · rfl
        · have h1 : decide (ep = 0) = false := decide_eq_false (by omega)
          have h2 : ((0 : ℕ) == ep) = false :=
            beq_eq_false_iff_ne.mpr (show (0 : ℕ) ≠ ep by omega)
          change (true && decide (ep = 0)) = ((Party.B == Party.B) && ((0 : ℕ) == ep))
          rw [h1, h2]
          rfl
    rw [hpred, List.any_beq]
  simp only [epoch0FinishE, orE_eval, e2eGsMaxAcc, e2eGsWin, e2eGsCorrs, e2eGsEnc,
    Expr.eval, Expr.v0, Env.get, hany]

theorem cost_epoch0FinishE_le (q : ℕ) :
    (epoch0FinishE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q).cost ≤
      12 * q + 150 := by
  have hb0 : bits 0 = 1 := by decide
  simp only [epoch0FinishE, orE, e2eGsMaxAcc, e2eGsWin, e2eGsCorrs, Expr.cost, Expr.v0, hb0]
  omega

theorem size_epoch0FinishE_le (q : ℕ) :
    (epoch0FinishE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q).size ≤
      bits q + 50 := by
  have hb0 : bits 0 = 1 := by decide
  simp only [epoch0FinishE, orE, e2eGsMaxAcc, e2eGsWin, e2eGsCorrs, Expr.size, Expr.v0, hb0]
  omega

end StepE2E

/-! ## Promoted `CostedReduction` definition -/

section Reduction

variable (C : Crypto) (K : MlKem) {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (idA idB : IdentityKey) (lam : Pt) (ℓ q qep : ℕ)

def epoch0RedReal :
    CostedReduction (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (coinOnlyIface ℓ Pt)
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (e2eSessionCodec ℓ Pt) (.prod BV256 BV256) .unit .bool .bool where
  σ := liftTy (Pt := Pt) (e2eGsTy ℓ)
  init := initEpoch0GsC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB
  handle := liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
    (epoch0OracleStepE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT)
      q (2 + 1) qep (Γ := [e2eGsTy ℓ, smQT]) .v0 .v1)
  finish := .ret (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (epoch0FinishE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q))

/-- Promoted `CostedReduction` witness for `epoch0Distinguisher`. -/
def epoch0Red :
    CostedReduction (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (coinOnlyIface ℓ Pt)
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (e2eSessionCodec ℓ Pt) (.prod BV256 BV256) .unit .bool .bool :=
  if ℓ < 10 ^ 6 then
    epoch0RedReal C K Dh encPt encT decT idA idB lam ℓ q qep
  else
    dummyBoolSessionRed (coinOnlyIface ℓ Pt) (.prod BV256 BV256)

/-! ## Cost, size, and `GRedBounded` bounds -/

theorem epoch0Red_totalQueries_zero :
    (epoch0Red C K Dh encPt encT decT idA idB lam ℓ q qep).totalQueries
      Empty.elim (fun _ => 0) q = 0 := by
  unfold epoch0Red
  split_ifs with hℓ
  · simp [epoch0RedReal, CostedReduction.totalQueries, initEpoch0GsC_queries_zero,
      liftCompCoins_queries_zero, Comp.queries]
  · exact dummyBoolSessionRed_totalQueries _ _ _ _ _

theorem epoch0Red_totalCost_le {qep' : ℕ} (hqep : qep ≤ qep') :
    (epoch0Red C K Dh encPt encT decT idA idB lam ℓ q qep).totalCost q ≤
      ratchetCostBudget q qep' := by
  unfold epoch0Red
  split_ifs with hℓ
  · let stepE2E := epoch0OracleStepE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT)
      q (2 + 1) qep (Γ := [e2eGsTy ℓ, smQT]) .v0 .v1
    let finE2E := epoch0FinishE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q
    have hinit := initEpoch0GsC_cost (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB
    have hstep1 := liftCompCoins_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl stepE2E
    have hstep2 : stepE2E.cost ≤ 5106010 + 10 * (ℓ / 32 + 1) + 420 * q +
        3 * bits (2 + 1) + bits qep + bits (qep + 1) := by
      have h := epoch0OracleStepE2EC_cost (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
        (decT := decT) (encT := encT) q (2 + 1) qep (Γ := [e2eGsTy ℓ, smQT]) .v0 .v1
      simp only [Expr.v0, Expr.v1, Expr.cost] at h
      dsimp only [stepE2E, Expr.v0, Expr.v1]
      omega
    have hfin1 := liftExpr_cost (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) finE2E
    have hfin2 : finE2E.cost ≤ 12 * q + 150 :=
      cost_epoch0FinishE_le (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q
    have hb3 : bits (2 + 1) = 2 := by decide
    have hbQep1 : bits qep ≤ bits qep' := bits_mono hqep
    have hbQep2 : bits (qep + 1) ≤ bits qep' + 1 :=
      (bits_succ_le qep).trans (Nat.add_le_add_right (bits_mono hqep) 1)
    have hdiv : ℓ / 32 + 1 ≤ 31251 := by omega
    have hhandle :
        max 1 ((epoch0RedReal C K Dh encPt encT decT idA idB lam ℓ q qep).handle.cost + 16) ≤
          173600000 + 13440 * q + 64 * bits qep' := by
      change max 1 ((liftCompCoins rfl stepE2E).cost + 16) ≤
        173600000 + 13440 * q + 64 * bits qep'
      omega
    have hmul :
        q * max 1 ((epoch0RedReal C K Dh encPt encT decT idA idB lam ℓ q qep).handle.cost + 16) ≤
          q * (173600000 + 13440 * q + 64 * bits qep') :=
      Nat.mul_le_mul_left q hhandle
    have hinit_le :
        (epoch0RedReal C K Dh encPt encT decT idA idB lam ℓ q qep).init.cost ≤ 3020000 := by
      change (initEpoch0GsC idA idB).cost ≤ 3020000
      omega
    have hfin_le :
        (epoch0RedReal C K Dh encPt encT decT idA idB lam ℓ q qep).finish.cost ≤ 5000 + 400 * q := by
      change (Comp.ret (liftExpr finE2E)).cost ≤ 5000 + 400 * q
      simp only [Comp.cost]
      omega
    have htot :
        (epoch0RedReal C K Dh encPt encT decT idA idB lam ℓ q qep).totalCost q ≤
          3020000 + q * (173600000 + 13440 * q + 64 * bits qep') + (5000 + 400 * q) := by
      dsimp only [CostedReduction.totalCost, coinOnlyIface, e2eSessionCodec]
      omega
    exact htot.trans (session_cost_le_ratchetCostBudget q qep' 3020000 (5000 + 400 * q)
      173600000 13440 64 (by omega) (by omega) (by omega) (by omega) (by omega))
  · exact dummyBoolSessionRed_totalCost_le _ rfl _ q qep'

theorem epoch0Red_size_raw_le :
    (epoch0Red C K Dh encPt encT decT idA idB lam ℓ q qep).size ≤
      1810000 + 162 * bits q + 36 * bits qep + 9 * bits (qep + 1) := by
  unfold epoch0Red
  split_ifs with hℓ
  · let stepE2E := epoch0OracleStepE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
      (decT := decT) (encT := encT) q (2 + 1) qep (Γ := [e2eGsTy ℓ, smQT]) .v0 .v1
    let finE2E := epoch0FinishE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q
    have hinit := initEpoch0GsC_size_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB
    have hstep1 := liftCompCoins_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl stepE2E
    have hstep2 : stepE2E.size ≤ 200002 + 17 * bits q + 7 * bits (2 + 1) +
        4 * bits qep + bits (qep + 1) := by
      have h := epoch0OracleStepE2EC_size_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
        (decT := decT) (encT := encT) q (2 + 1) qep (Γ := [e2eGsTy ℓ, smQT]) .v0 .v1
      simp only [Expr.v0, Expr.v1, Expr.size] at h
      dsimp only [stepE2E, Expr.v0, Expr.v1]
      omega
    have hfin1 := liftExpr_size_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) finE2E
    have hfin2 : finE2E.size ≤ bits q + 50 :=
      size_epoch0FinishE_le (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q
    have hb3 : bits (2 + 1) = 2 := by decide
    dsimp only [epoch0RedReal, CostedReduction.size, Comp.size]
    change (initEpoch0GsC idA idB).size + (liftCompCoins rfl stepE2E).size +
      ((liftExpr finE2E).size + 1) ≤
      1810000 + 162 * bits q + 36 * bits qep + 9 * bits (qep + 1)
    omega
  · rw [dummyBoolSessionRed_size]
    omega

theorem epoch0Red_size_le_of_clamp {qep' : ℕ}
    (hqep_B : qep + 1 ≤ ratchetCostBudget q qep') :
    (epoch0Red C K Dh encPt encT decT idA idB lam ℓ q qep).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep') := by
  have hraw := epoch0Red_size_raw_le C K Dh encPt encT decT idA idB lam ℓ q qep
  have hqB : q + 11 ≤ ratchetCostBudget q qep' := q_add_eleven_le_ratchetCostBudget q qep'
  have hbq : bits q ≤ bits (ratchetCostBudget q qep') := bits_mono (by omega)
  have hbqep : bits qep ≤ bits (ratchetCostBudget q qep') := bits_mono (by omega)
  have hbqep1 : bits (qep + 1) ≤ bits (ratchetCostBudget q qep') := bits_mono hqep_B
  have hsz :
      (epoch0Red C K Dh encPt encT decT idA idB lam ℓ q qep).size ≤
        1810000 + 207 * bits (ratchetCostBudget q qep') := by
    omega
  exact size_le_budget_of_log_cost (by decide) (by decide) hsz

theorem epoch0Red_size_le {qep' : ℕ} (hqep_q : qep ≤ q + 10) :
    (epoch0Red C K Dh encPt encT decT idA idB lam ℓ q qep).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep') := by
  have hqB := q_add_eleven_le_ratchetCostBudget q qep'
  exact epoch0Red_size_le_of_clamp C K Dh encPt encT decT idA idB lam ℓ q qep (by omega)

theorem epoch0Red_gRedBounded_of_clamp {qep' : ℕ}
    (hqep : qep ≤ qep') (hqep_B : qep + 1 ≤ ratchetCostBudget q qep') :
    GRedBounded (epoch0Red C K Dh encPt encT decT idA idB lam ℓ q qep)
      Empty.elim (fun _ => 0) q 0 (ratchetCostBudget q qep') :=
  gRedBounded_of_bounds _ Empty.elim (fun _ => 0) q 0 (ratchetCostBudget q qep')
    (epoch0Red_totalCost_le C K Dh encPt encT decT idA idB lam ℓ q qep hqep)
    (epoch0Red_size_le_of_clamp C K Dh encPt encT decT idA idB lam ℓ q qep hqep_B)
    (Nat.le_of_eq (epoch0Red_totalQueries_zero C K Dh encPt encT decT idA idB lam ℓ q qep))
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (atomicSamplers_sizeHonest ℓ Pt)

theorem epoch0Red_gRedBounded_of_le {qep' : ℕ}
    (hqep_q : qep ≤ q + 10) (hqep : qep ≤ qep') :
    GRedBounded (epoch0Red C K Dh encPt encT decT idA idB lam ℓ q qep)
      Empty.elim (fun _ => 0) q 0 (ratchetCostBudget q qep') :=
  gRedBounded_of_bounds _ Empty.elim (fun _ => 0) q 0 (ratchetCostBudget q qep')
    (epoch0Red_totalCost_le C K Dh encPt encT decT idA idB lam ℓ q qep hqep)
    (epoch0Red_size_le C K Dh encPt encT decT idA idB lam ℓ q qep hqep_q)
    (Nat.le_of_eq (epoch0Red_totalQueries_zero C K Dh encPt encT decT idA idB lam ℓ q qep))
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (atomicSamplers_sizeHonest ℓ Pt)

/-- `GRedBounded` for `epoch0Red` at `ratchetCostBudget q qep` under `qep ≤ q + 10`. -/
theorem epoch0Red_gRedBounded (hqep : qep ≤ q + 10) :
    GRedBounded (epoch0Red C K Dh encPt encT decT idA idB lam ℓ q qep)
      Empty.elim (fun _ => 0) q 0 (ratchetCostBudget q qep) :=
  epoch0Red_gRedBounded_of_le C K Dh encPt encT decT idA idB lam ℓ q qep hqep (Nat.le_refl qep)

theorem epoch0Red_gRedBounded_succ (hqep : qep ≤ q + 10) :
    GRedBounded (epoch0Red C K Dh encPt encT decT idA idB lam ℓ q qep)
      Empty.elim (fun _ => 0) q 0 (ratchetCostBudget q (qep + 1)) :=
  epoch0Red_gRedBounded_of_le C K Dh encPt encT decT idA idB lam ℓ q qep hqep (Nat.le_succ qep)

/-! ## Evaluation equivalence -/

theorem epoch0Red_eval
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (rc : RootKey × BitVec 256)
    (hA : MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    (epoch0Red C K Dh encPt encT decT idA idB lam ℓ q qep).eval (fun _ => A) rc =
      epoch0Distinguisher (paramsV1 C K idA idB) ℓ
        (ratchetKeyAdmissible protoSignalCodec decT encT) qep A rc := by
  unfold epoch0Red
  simp only [hℓ, ↓reduceIte]
  set cfg := configEpoch0Distinguisher (ratchetKeyAdmissible protoSignalCodec decT encT)
  set sm := libsignalSessionSchemeFromEpoch0Keys (paramsV1 C K idA idB) ℓ rc.1 rc.2
  let so : QueryImpl (unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes) ProbComp) :=
    (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes) ProbComp) +
      oracleImplR sm 3 qep cfg
  let enc : GameState (GhostState Bytes) (Plain ℓ) Bytes →
      (liftTy (Pt := Pt) (e2eGsTy ℓ)).denote :=
    fun st => liftVal (Pt := Pt) (e2eGsEnc st)
  let Inv : ℕ → GameState (GhostState Bytes) (Plain ℓ) Bytes → Prop :=
    fun m st => m ≤ q ∧ SmReachBounded C K (q - m) st
  have hsim := eval_eq_simulateQ_of_enc
    (epoch0RedReal C K Dh encPt encT decT idA idB lam ℓ q qep)
    enc Inv
    (epoch0InitImpl C K idA idB ℓ)
    so
    (fun s₁ _ => pure ((decide (0 < s₁.maxAcc .A 0) || s₁.win) && !(s₁.corrs.contains (.B, 0))))
    q rc
    (initEpoch0GsC_eval idA idB rc)
    (fun r hr => by
      refine ⟨Nat.le_refl q, ?_⟩
      rw [Nat.sub_self]
      exact smReachBounded_epoch0InitImpl C K idA idB ℓ rc hr)
    (fun n s => rfl)
    (fun m sq s hs => by
      have hreachQ : SmReachBounded C K q s := hs.2.mono (by omega)
      have horacle := oracleImplR_epoch0Keys_eq_fixedSpk C K idA idB ℓ 3 qep rc 0 cfg
      refine ⟨?_, ?_⟩
      · change (do
            let p ← (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
              (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
              (epoch0OracleStepE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT)
                q (2 + 1) qep (Γ := [e2eGsTy ℓ, smQT]) .v0 .v1)).eval
              (.cons (enc s) (.cons ((e2eSessionCodec ℓ Pt).qenc sq) .nil))
            pure ((e2eSessionCodec ℓ Pt).rdec sq p.1, p.2)) =
          Prod.map id enc <$> (oracleImplR sm 3 qep cfg sq).run s
        have hev := liftCompCoins_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
          (epoch0OracleStepE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT)
            q (2 + 1) qep (Γ := [e2eGsTy ℓ, smQT]) .v0 .v1)
          (.cons (e2eGsEnc s) (.cons (smQenc (St := GhostState Bytes) sq) .nil))
        change (liftCompCoins rfl
            (epoch0OracleStepE2EC q (2 + 1) qep (Γ := [e2eGsTy ℓ, smQT]) .v0 .v1)).eval
            (.cons (enc s) (.cons (liftVal (Pt := Pt) (smQenc (St := GhostState Bytes) sq)) .nil)) =
          liftVal (Pt := Pt) <$>
            (epoch0OracleStepE2EC q (2 + 1) qep (Γ := [e2eGsTy ℓ, smQT]) .v0 .v1).eval
              (.cons (e2eGsEnc s) (.cons (smQenc (St := GhostState Bytes) sq) .nil)) at hev
        rw [liftVal_smQenc] at hev
        have hstepE2E := epoch0OracleStepE2EC_eval (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
          (decT := decT) (encT := encT) q (2 + 1) qep
          (.v0 : Expr (e2eOps ℓ zeroPqxdhPrims C K decT encT) [e2eGsTy ℓ, smQT] (e2eGsTy ℓ)) .v1
          (.cons (e2eGsEnc s) (.cons (smQenc (St := GhostState Bytes) sq) .nil))
          idA idB 0 s sq hreachQ rfl rfl
        rw [hev, hstepE2E, liftP_unif_eq_self _ (fun _ => rfl), ← horacle]
        simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
        refine bind_congr fun ⟨ans, s'⟩ => congrArg pure ?_
        change ((e2eSessionCodec ℓ Pt).rdec sq
            (liftVal (Pt := Pt) (smRenc (stT := GhostStT) id sq ans)), enc s') = (ans, enc s')
        rcases sq with (((_ | _) | _) | _) | _ <;> rcases ans with _ | v <;> (try rfl) <;>
          rcases v with _ | ⟨_, _, _ | _⟩ <;> rfl
      · intro r hr
        dsimp only [so, Sum.elim_inr] at hr
        rw [horacle] at hr
        have hr' := smReachBounded_oracleImplR C K idA idB ℓ 3 qep (q - (m + 1)) 0 cfg sq hs.2 hr
        refine ⟨by omega, ?_⟩
        have heq : q - (m + 1) + 1 = q - m := by omega
        exact heq ▸ hr')
    (fun s₁ b' hs => by
      dsimp only [epoch0RedReal, Comp.eval]
      have hsub : q - 0 = q := Nat.sub_zero q
      have hreachQ : SmReachBounded C K q s₁ := hsub ▸ hs.2
      have hev := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam)
        (epoch0FinishE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)
        (.cons (e2eGsEnc s₁) (.cons b' .nil))
      change (liftExpr (epoch0FinishE q)).eval (.cons (enc s₁) (.cons b' .nil)) = _ at hev
      rw [hev, eval_epoch0FinishE q s₁ b' hreachQ.lists.corrs_le]
      rfl)
    (fun {m n} s hmn hn => ⟨by omega, hn.2.mono (by omega)⟩)
    (fun _ => A)
    (fun _ => isQueryBoundP_of_makesAtMostQueries hA)
  rw [hsim]
  unfold epoch0Distinguisher runR epoch0InitImpl
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun _ => bind_congr fun _ => bind_congr fun ⟨_, _⟩ => rfl

end Reduction

end Computational.Proofs.Game.PromotedCostedReds.Epoch0DistinguisherProg

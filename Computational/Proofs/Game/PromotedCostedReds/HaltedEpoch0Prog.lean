/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.KemFailRedInit -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitness -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.HaltedEpoch0Step -- proof-setup: allow-public-import
public import Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.DrSessionSim -- proof-setup: allow-public-import
public import Computational.Specifications.Game.StatementPqOomFlag
import Computational.Proofs.E2E.Dsl.StartAndExtSmAux
import Computational.Proofs.Game.PromotedCostedReds.DrSessionSimSize
import Computational.Proofs.Game.PromotedCostedReds.Epoch0DistinguisherProg
import Computational.Proofs.Game.PromotedCostedReds.SimFig8State
import Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost
import Computational.Proofs.Game.PromotedCostedReds.KemFailRedInitCost
import Computational.Proofs.Game.PromotedCostedReds.KemFailRedSendCorrSub
import Computational.Proofs.Game.PromotedCostedReds.KemFailRedSendCorrCost
import Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitnessSub
import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds
import Computational.Proofs.ReductionDsl.SizeBudgetBridge
import Computational.Proofs.E2E.ComposedPrefixHelpers
import VCVio.OracleComp.SimSemantics.SimulateQ
import VCVio.EvalDist.Monad.Basic

/-!
# Tracker-Halted Promoted `CostedReduction` Witness for `epoch0Distinguisher`

Constructs `epoch0DistinguisherProgHalted`, the `KemFailTrackState`-halted `CostedReduction`
witness over `atomicSessionOps` and `coinOnlyIface` for `epoch0DistinguisherTrackHalted`, and
proves `GRedBounded` and exact `.eval` agreement.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.HaltedEpoch0Prog

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Ops Iface Expr Comp CostedReduction bits
  reductionSizeBudget handlerImpl bind_congr_of_mem_support'
  atomicSig atomicSessionOps coinOnlyIface e2eSessionCodec
  U32 U64 BV256 BV512 B GhostStT PlainT UniformSamplerTag AtomicPureOp)
open CryptoGames (Party SMSchemeR)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open PRGScheme (PRGAdversary)
open CryptoGames.Ratchet.LibsignalInst (libsignalSessionSchemeFromEpoch0Keys ratchetKeyAdmissible)
open CryptoGames.Ratchet.LibsignalSim (configEpoch0Distinguisher kemTrackEnc)
open CryptoGames.SM (Pos Record RecvResult GameState ConfigR Adversary
  initState inWindow samIfNec transmitR transmitImpl challR challImpl deliverR injectR corrR
  oracleImplR spec MakesAtMostQueries
  partyEnc posTy posEnc orE boolEq isSomeE otherE pGet pSet
  letE_eval ite_eval pair_eval some_eval orE_eval boolEq_eval isSomeE_eval otherE_eval pGet_eval)
open CryptoGames.LibsignalSession (Params Crypto ShaCompress IdentityKey PublicKey RootKey GhostState)
open CryptoGames.LibsignalSM.Proofs.Refinement (KemFailTrackState initKemFailTrack
  stepKemFailSend stepKemFailDeliver)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.LibsignalSession (ratchetCostBudget GRedBounded)
open CryptoVerification.E2E (Bytes configRefuseEarlyBobCorr liftStateT paramsIdsWithSpqr paramsV1
  sessionSchemeFixedSpk)
open CryptoVerification.E2E.HeadlineU (sample_prod_bindU)
open CryptoVerification.E2E.Costed (e2eSig e2eOps smQT smQenc smRT recvResultEnc
  partyToBool E2EPureOp E2EUnifBase e2eSamplers gRedBounded_of_bounds)
open Computational.Proofs.E2E.Dsl.TablesHonest (e2ePureOp e2eCryptoOp size_e2ePureOp
  size_e2eCryptoOp)
open Computational.Proofs.E2E.Dsl.PqxdhSimTypes (v eLet eCaseOpt)
open Computational.Proofs.E2E.Dsl.StartAndExtSmAux (initFixedSpkBobE initFixedSpkAliceE
  initFixedSpkGsE eval_initFixedSpkGsE cost_initFixedSpkGsE)
open Computational.Proofs.E2E.Dsl.SmReachInvParty (PartyReachInv)
open Computational.Proofs.E2E.Dsl.SmReachInv (dedupComp SmReachBounded smReachBounded_initState
  smReachBounded_oracleImplR)
open Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping (partyToBool_eq_partyEnc smRenc
  e2eGsTy e2eGsEnc)
open Computational.Proofs.E2E.Dsl.SpqrSim (spqrDslHooks)
open Computational.Proofs.E2E.Dsl.DrSessionSim (drDlArmC drDlArmC_eval)
open Computational.Proofs.Game.PromotedCostedReds.Epoch0DistinguisherProg (epoch0IjArmC
  epoch0IjArmC_eval epoch0CrArmC epoch0CrArmC_eval)
open Computational.Proofs.Game.PromotedCostedReds.AtomicOpsHonest (atomicSessionOps_sizeHonest
  atomicSamplers_sizeHonest)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge (sessPureOp sessSpqrKemOp
  zeroPqxdhPrims liftTy liftBaseVal liftVal liftEnv coinE2EIface coinE2ESamplers
  liftCompCoins liftCompCoins_queries_zero liftCompCoins_cost liftCompCoins_eval)
open Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon (comp_eval_ret comp_eval_bind
  comp_eval_bind_ret comp_eval_ite comp_eval_caseOpt comp_eval_caseSum
  eval_eq_simulateQ_of_enc isQueryBoundP_of_makesAtMostQueries liftP_unif_eq_self
  liftVal_smQenc e2eSessionCodec_rdec_liftVal_smRenc liftCompCoins_size_le
  idKeyLitE idKeyPairLitE eval_idKeyPairLitE cost_idKeyPairLitE size_idKeyPairLitE
  oracleImplR_epoch0Keys_eq_fixedSpk
  bits_succ_le session_cost_le_ratchetCostBudget
  dummyBoolSessionRed dummyBoolSessionRed_totalQueries dummyBoolSessionRed_totalCost_le
  dummyBoolSessionRed_size)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedInit (kemTrackT kemTrackAtomicEnc
  initV1BraidStAtomicE initKemTrackAtomicE initKemTrackAtomicE_eval kemTrackEnc_initKemFailTrack)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedInitCost (initKemTrackAtomicE_cost)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedSendCorrCost (trE_cand
  stepKemFailSendAtomicC)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedSendCorrSub (stepKemFailSendAtomicC_eval)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitness (KemTrackDeliverInv
  KemTrackDeliverInv.mono kemTrackDeliverInv_init kemTrackDeliverInv_step
  kemTrackDeliverInv_stepSend kemOnDeliverPostAtomicE_eval)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitnessSub
  (kemOnDeliverPostAtomicE)
open Computational.Proofs.ReductionDsl.SizeBudgetBridge (bits_mono size_le_budget_of_log_cost)
open Computational.Proofs.Game.PromotedCostedReds.HaltedEpoch0Step (headRen call1C call1C_eval
  findRevHonestWiresIdxE findRevHonestWiresIdxE_eval
  preSendInTy preSendOutTy preSendE2EC preSendModel preSendE2EC_eval
  postSendInTy postSendE2EC postSendE2EC_eval
  smRATy smRWireAE sendReqATy sendOrChallTrackC dlArmTrackC liftGsArmTrackC
  epoch0OracleStepTrackC epoch0OracleStepTrackC_queries_zero
  epoch0OracleStepTrackC_cost epoch0OracleStepTrackC_size_le
  epoch0HaltedFinishE cost_epoch0HaltedFinishE_le size_epoch0HaltedFinishE_le
  eval_epoch0HaltedFinishE flatSt2 simulateQ_run_flatSt2)

export Computational.Proofs.Game.PromotedCostedReds.HaltedEpoch0Step
  (kemSessionTrackT epoch0HaltedStTy kemSessionTrackEnc epoch0HaltedEnc)

/-! ## Shallow `KemFailSessionTrack` R-game oracles -/

section ShallowTrackHalted

/-- Per-session `O(1)` braid tracker paired with prepend-only honest `(wire, sender)` pairs. -/
abbrev KemFailSessionTrack (F : ShaCompress) (C : Type) : Type := KemFailTrackState F × List (C × Party)

@[expose] def initKemFailSessionTrack (F : ShaCompress) (C : Type) (pqrKey : BitVec 256) : KemFailSessionTrack F C :=
  (initKemFailTrack F pqrKey, [])

abbrev libsignalSessionPqrOf (k : RootKey × BitVec 256 × BitVec 256 × BitVec 256) : BitVec 256 := k.2.2.2

@[expose] noncomputable def transmitRSessionTrackHalted {Key St Msg RCoins C : Type}
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    QueryImpl ((Party × Msg × Option (BitVec 512)) →ₒ Option C)
      (StateT (GameState St Msg C) (StateT (KemFailSessionTrack F C) ProbComp)) := fun ⟨P, m, r⟩ => do
  let s ← get
  if !(cfg.sendOK s P) then return none
  if s.win then return none
  let (coins, bad) ← StateT.lift (liftM (samIfNec r : ProbComp (BitVec 512 × Bool)))
  match s.epMgmt Δ qep P bad with
  | none => return none
  | some s₁ =>
    let (tr, hw) ← StateT.lift get
    let tr' := stepKemFailSend F K tr P coins
    if tr'.cand.isSome then StateT.lift (set ({ tr with cand := tr'.cand }, hw)); return none
    else
      let out := sm.send (s₁.st P) m coins
      set (s₁.record Δ P out.1 ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, out.2⟩ false)
      StateT.lift (set (tr', (out.2, P) :: hw)); return some out.2

@[expose] noncomputable def challRSessionTrackHalted {Key St Msg RCoins C : Type}
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    QueryImpl ((Party × Msg × Msg × Option (BitVec 512)) →ₒ Option C)
      (StateT (GameState St Msg C) (StateT (KemFailSessionTrack F C) ProbComp)) := fun ⟨P, m₀, m₁, r⟩ => do
  let s ← get
  if !(cfg.sendOK s P) then return none
  if s.win then return none
  let (coins, bad) ← StateT.lift (liftM (samIfNec r : ProbComp (BitVec 512 × Bool)))
  match s.epMgmt Δ qep P bad with
  | none => return none
  | some s₁ =>
    if !(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P)) then return none
    let (tr, hw) ← StateT.lift get
    let tr' := stepKemFailSend F K tr P coins
    if tr'.cand.isSome then StateT.lift (set ({ tr with cand := tr'.cand }, hw)); return none
    else
      let m := (cfg.base.challMsg (s₁.epoch P)).getD (if s.b then m₁ else m₀)
      let out := sm.send (s₁.st P) m coins
      set (s₁.record Δ P out.1 ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, out.2⟩ true)
      StateT.lift (set (tr', (out.2, P) :: hw)); return some out.2

@[expose] noncomputable def deliverRSessionTrackHalted {Key St Msg RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C) (cfg : ConfigR St Msg C) :
    QueryImpl ((Party × C) →ₒ Option (RecvResult Msg))
      (StateT (GameState St Msg C) (StateT (KemFailSessionTrack F C) ProbComp)) := fun ⟨Q, w⟩ => do
  let (_, hw) ← StateT.lift get
  let j? := hw.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other)
  let res ← liftStateT (deliverR sm cfg (Q, w))
  match res, j? with
  | some (.accepted _ _ _), some j => StateT.lift (modify fun (tr, hw') => (stepKemFailDeliver F K tr Q j, hw'))
  | _, _ => pure ()
  return res

/-- Full 5-oracle `KemFailSessionTrack`-halted R-game implementation. -/
@[expose] noncomputable def oracleImplRSessionTrackHalted {Key St Msg RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    QueryImpl (spec St Msg (BitVec 512) C)
      (StateT (GameState St Msg C) (StateT (KemFailSessionTrack F C) ProbComp)) :=
  transmitRSessionTrackHalted F K sm Δ qep cfg + challRSessionTrackHalted F K sm Δ qep cfg +
    deliverRSessionTrackHalted F K sm cfg +
    ((fun q => liftStateT (injectR sm Δ qep cfg q)) :
      QueryImpl ((Party × C) →ₒ Option (RecvResult Msg)) (StateT (GameState St Msg C) (StateT (KemFailSessionTrack F C) ProbComp))) +
    ((fun P => liftStateT (corrR cfg P)) :
      QueryImpl (Party →ₒ Option St) (StateT (GameState St Msg C) (StateT (KemFailSessionTrack F C) ProbComp)))

@[expose] noncomputable def runRSessionTrackHalted {Key St Msg RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType RCoins]
    (pqrOf : Key → BitVec 256) (F : ShaCompress) (K : MlKem)
    (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (b : Bool) (A : Adversary St Msg (BitVec 512) C) :
    ProbComp ((Bool × GameState St Msg C) × KemFailSessionTrack F C) := do
  let k ← ($ᵗ Key : ProbComp Key)
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (GameState St Msg C) (StateT (KemFailSessionTrack F C) ProbComp)) +
    oracleImplRSessionTrackHalted F K sm Δ qep cfg
  ((simulateQ impl A).run (initState sm.sendPart k b)).run (initKemFailSessionTrack F C (pqrOf k))

/-- Online `KemFailSessionTrack`-halted `epoch0Distinguisher` on `(rk0, ck0)`. -/
@[expose] noncomputable def epoch0DistinguisherTrackHalted
    (P : Params Bytes (BitVec 512)) (K : MlKem) (ℓ : ℕ) (onImage : Bytes → Bool) (qep : ℕ)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    PRGAdversary (RootKey × BitVec 256) := fun rc => do
  let b ← ($ᵗ Bool : ProbComp Bool)
  let ((_, s), _) ← runRSessionTrackHalted libsignalSessionPqrOf P.C.F K
    (libsignalSessionSchemeFromEpoch0Keys P ℓ rc.1 rc.2) 3 qep (configEpoch0Distinguisher onImage) b A
  return (decide (0 < s.maxAcc .A 0) || s.win) && !(s.corrs.contains (.B, 0))

end ShallowTrackHalted

/-! ## Combined DSL state and halted initializer -/

section InitHalted

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
  {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ESig" => e2eSig ℓ
local notation "EOps" => e2eOps ℓ zeroPqxdhPrims C K decT encT
local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

@[expose] def initEpoch0GsWithPqrE2EC (idA idB : IdentityKey) :
    Comp EOps (coinE2EIface (coinOnlyIface ℓ Pt))
      [.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256]
      (.prod (e2eGsTy ℓ) CryptoVerification.E2E.Costed.BV256) :=
  .bind (Comp.sample (I := coinE2EIface (coinOnlyIface ℓ Pt)) UniformSamplerTag.bool .unit)
    (.bind (Comp.sample (I := coinE2EIface (coinOnlyIface ℓ Pt)) (UniformSamplerTag.base .bv256) .unit)
      (.bind (Comp.sample (I := coinE2EIface (coinOnlyIface ℓ Pt)) (UniformSamplerTag.base .bv256) .unit)
        (.bind (Comp.sample (I := coinE2EIface (coinOnlyIface ℓ Pt)) (UniformSamplerTag.base .bv256) .unit)
          (.bind (Comp.sample (I := coinE2EIface (coinOnlyIface ℓ Pt)) (UniformSamplerTag.base .bv256) .unit)
            (.ret (.pair (initFixedSpkGsE (idKeyPairLitE idA idB)
                (.pair (.var (.succ (.succ .zero))) (.pair
                  (.pair (.var (.succ (.succ (.succ (.succ (.succ .zero))))))
                    (.pair (.var (.succ .zero)) (.var .zero)))
                  (.var (.succ (.succ (.succ (.succ .zero)))))))) (.var .zero)))))))

@[expose] def initEpoch0GsTrackC (idA idB : IdentityKey) :
    Comp AOps (coinOnlyIface ℓ Pt) [.prod BV256 BV256] (.prod .unit (epoch0HaltedStTy ℓ Pt)) :=
  .bind (liftCompCoins (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) rfl
      (initEpoch0GsWithPqrE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT) idA idB))
    (.ret (.pair .unit (.pair (.fst .v0) (.pair
      (initKemTrackAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (.snd .v0)) .nil))))

theorem initEpoch0GsTrackC_queries_zero (idA idB : IdentityKey) (w : Empty → ℕ) :
    (initEpoch0GsTrackC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB).queries w (fun _ => 0) = 0 := by
  simp only [initEpoch0GsTrackC, Comp.queries, liftCompCoins_queries_zero, Nat.add_zero]

@[expose] noncomputable def epoch0TrackInitImpl (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (ℓ : ℕ) (rc : RootKey × BitVec 256) :
    ProbComp (Unit × (GameState (GhostState Bytes) (Plain ℓ) Bytes × KemFailSessionTrack C.F Bytes)) := do
  let b ← ($ᵗ Bool : ProbComp Bool)
  let k ← ($ᵗ (RootKey × BitVec 256 × BitVec 256 × BitVec 256) : ProbComp _)
  return ((), (initState (libsignalSessionSchemeFromEpoch0Keys (paramsV1 C K idA idB) ℓ rc.1 rc.2).sendPart k b,
    initKemFailSessionTrack C.F Bytes k.2.2.2))

theorem initEpoch0GsTrackC_cost (idA idB : IdentityKey) :
    (initEpoch0GsTrackC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB).cost ≤ 3020000 := by
  have h1 := liftCompCoins_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
    (initEpoch0GsWithPqrE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT) idA idB)
  let Γ5 : List (Ty ESig) :=
    [Ty.base E2EUnifBase.bv256.sort, Ty.base E2EUnifBase.bv256.sort, Ty.base E2EUnifBase.bv256.sort,
     Ty.base E2EUnifBase.bv256.sort, .bool, .prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256]
  have hids := cost_idKeyPairLitE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) (Γ := Γ5) idA idB
  have hgs := cost_initFixedSpkGsE (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K) (decT := decT) (encT := encT)
    (Γ := Γ5) (idKeyPairLitE idA idB) (.pair (.var (.succ (.succ .zero))) (.pair
      (.pair (.var (.succ (.succ (.succ (.succ (.succ .zero)))))) (.pair (.var (.succ .zero)) (.var .zero)))
      (.var (.succ (.succ (.succ (.succ .zero)))))))
  have htr := initKemTrackAtomicE_cost (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    (Γ := [.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) BV256, .prod BV256 BV256]) (.snd .v0)
  dsimp only [initEpoch0GsTrackC, initEpoch0GsWithPqrE2EC] at h1 ⊢
  simp only [Comp.cost, Expr.cost, Expr.v0, coinE2EIface, e2eSamplers,
    _root_.ReductionDsl.unifSamplers, E2EUnifBase.cost] at hgs h1 htr ⊢; omega

theorem initEpoch0GsTrackC_size_le (idA idB : IdentityKey) :
    (initEpoch0GsTrackC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB).size ≤ 5200 := by
  have h1 := liftCompCoins_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
    (initEpoch0GsWithPqrE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT) idA idB)
  have h2 : (initEpoch0GsWithPqrE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT) idA idB).size ≤ 550 := by
    simp only [initEpoch0GsWithPqrE2EC, initFixedSpkGsE, initFixedSpkAliceE, initFixedSpkBobE,
      size_idKeyPairLitE, eLet, eCaseOpt, v, size_e2ePureOp, size_e2eCryptoOp,
      E2EPureOp.opSize, Comp.size, Expr.size, show bits 0 = 1 from rfl]; omega
  have h3 : (initKemTrackAtomicE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (Γ := [.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) BV256, .prod BV256 BV256]) (.snd .v0)).size ≤ 130 := by
    have haP : ∀ (o : _root_.ReductionDsl.AtomicPureOp),
        (AOps).opSize (.inl (.inl (.inl (.inl o)))) = o.opSize := fun _ => rfl
    have haS : ∀ (o : _root_.ReductionDsl.AtomicSpqrKemOp),
        (AOps).opSize (.inr o) = 0 := fun _ => rfl
    simp only [initKemTrackAtomicE, initV1BraidStAtomicE, SimFig8State.eLet, sessPureOp,
      sessSpqrKemOp, Expr.size, haP, haS, _root_.ReductionDsl.AtomicPureOp.opSize, List.length_nil,
      Expr.v0, show bits 0 = 1 from rfl]; omega
  dsimp only [initEpoch0GsTrackC]; simp only [Comp.size, Expr.size, Expr.v0] at h3 ⊢; omega

theorem initEpoch0GsTrackC_eval (idA idB : IdentityKey) (rc : RootKey × BitVec 256) :
    (initEpoch0GsTrackC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB).eval (.cons rc .nil) =
      Prod.map id (epoch0HaltedEnc (ℓ := ℓ) (Pt := Pt)) <$> epoch0TrackInitImpl C K idA idB ℓ rc := by
  dsimp only [initEpoch0GsTrackC]; rw [SessionProgCommon.comp_eval_bind]
  have hev := liftCompCoins_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
    (initEpoch0GsWithPqrE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT) idA idB) (.cons rc .nil)
  change (liftCompCoins rfl (initEpoch0GsWithPqrE2EC idA idB)).eval (.cons rc .nil) =
    liftVal (Pt := Pt) <$> (initEpoch0GsWithPqrE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
      (decT := decT) (encT := encT) idA idB).eval (.cons rc .nil) at hev
  rw [hev]
  have hlift : ∀ {α : Type} (p : ProbComp α), (coinE2EIface (coinOnlyIface ℓ Pt)).liftP p = p :=
    fun p => liftP_unif_eq_self _ (fun _ => rfl) p
  unfold initEpoch0GsWithPqrE2EC epoch0TrackInitImpl
  simp only [Comp.eval, hlift, e2eSamplers, _root_.ReductionDsl.unifSamplers,
    map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  refine bind_congr fun b => ?_; rw [sample_prod_bindU]
  refine bind_congr fun k0 => ?_; rw [sample_prod_bindU]
  refine bind_congr fun spk => ?_; rw [sample_prod_bindU]
  refine bind_congr fun ac => bind_congr fun pqr => ?_
  have hgs : (initFixedSpkGsE (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K) (decT := decT) (encT := encT)
        (idKeyPairLitE idA idB) (.pair (.var (.succ (.succ .zero))) (.pair
          (.pair (.var (.succ (.succ (.succ (.succ (.succ .zero)))))) (.pair (.var (.succ .zero)) (.var .zero)))
          (.var (.succ (.succ (.succ (.succ .zero)))))))).eval
        (.cons pqr (.cons ac (.cons spk (.cons k0 (.cons b (.cons rc .nil)))))) =
      e2eGsEnc (initState (libsignalSessionSchemeFromEpoch0Keys (paramsV1 C K idA idB) ℓ rc.1 rc.2).sendPart
        (k0, spk, ac, pqr) b) := by
    have h := eval_initFixedSpkGsE (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K) (decT := decT) (encT := encT)
      (idKeyPairLitE idA idB) (.pair (.var (.succ (.succ .zero))) (.pair
        (.pair (.var (.succ (.succ (.succ (.succ (.succ .zero)))))) (.pair (.var (.succ .zero)) (.var .zero)))
        (.var (.succ (.succ (.succ (.succ .zero)))))))
      (.cons pqr (.cons ac (.cons spk (.cons k0 (.cons b (.cons rc .nil))))))
    rw [eval_idKeyPairLitE] at h; exact h
  exact congrArg pure (Prod.ext rfl (Prod.ext (congrArg (liftVal (Pt := Pt)) hgs) (Prod.ext
    ((initKemTrackAtomicE_eval (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (.snd .v0) _).trans
      (congrArg kemTrackAtomicEnc (kemTrackEnc_initKemFailTrack C.F pqr).symm)) rfl)))

theorem epoch0TrackInitImpl_inv (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (ℓ : ℕ)
    (rc : RootKey × BitVec 256)
    {r : Unit × (GameState (GhostState Bytes) (Plain ℓ) Bytes × KemFailSessionTrack C.F Bytes)}
    (hr : r ∈ support (epoch0TrackInitImpl C K idA idB ℓ rc)) :
    SmReachBounded C K 0 r.2.1 ∧ KemTrackDeliverInv C.F K 0 (kemTrackEnc r.2.2.1) ∧ r.2.2.2.length ≤ 0 := by
  unfold epoch0TrackInitImpl at hr
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨b, -, ⟨k0, ⟨spk, ac, pqr⟩⟩, -, rfl⟩ := hr
  exact ⟨smReachBounded_initState C K idA idB ℓ spk ((rc.1, rc.2), (ac, pqr)) b,
    kemTrackDeliverInv_init C.F K 0 pqr, Nat.le_refl 0⟩

end InitHalted

@[local simp] private theorem liftStateT_run_state {σ τ α : Type}
    (x : StateT σ ProbComp α) (s : σ) (t : τ) :
    ((liftStateT x : StateT σ (StateT τ ProbComp) α).run s).run t = (x.run s >>= fun a => pure (a, t)) := rfl

/-! ## Step evaluation theorems -/

section StepHalted

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
  {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ESig" => e2eSig ℓ
local notation "EOps" => e2eOps ℓ zeroPqxdhPrims C K decT encT
local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

private theorem epMgmt_preserve_fields {Δ qep : ℕ}
    {st s1 : GameState (GhostState Bytes) (Plain ℓ) Bytes} {party : Party} {bad : Bool}
    (hep : st.epMgmt Δ qep party bad = some s1) :
    s1.st = st.st ∧ s1.trans = st.trans ∧ s1.comp = st.comp := by
  unfold GameState.epMgmt at hep
  by_cases hs : party.sendsIn (st.epoch party + 1) = true
  · simp only [hs, ↓reduceIte] at hep
    by_cases hq : qep < st.epoch party + 1; · simp [hq] at hep
    simp only [hq, ↓reduceIte] at hep
    by_cases hb : (bad && !st.safeCh Δ party) = true <;>
      simp only [hb, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hep <;> subst hep <;> exact ⟨rfl, rfl, rfl⟩
  · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hep
    by_cases hq : qep < st.epoch party; · simp [hq] at hep
    simp only [hq, ↓reduceIte, Option.some.injEq] at hep; subst hep; exact ⟨rfl, rfl, rfl⟩

private theorem trE_cand_isSome (tr : KemFailTrackState C.F) :
    ((kemTrackAtomicEnc (ℓ := ℓ) (Pt := Pt) (kemTrackEnc tr)).2.2.2.2.2).isSome = tr.cand.isSome := by
  rcases h : tr.cand with _ | ⟨_, _⟩ <;> simp [kemTrackEnc, kemTrackAtomicEnc, h]

theorem sendOrChallTrackC_eval (q Δ qep : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (epoch0HaltedStTy ℓ Pt)) (reqE : Expr AOps Γ (sendReqATy ℓ Pt)) (ρ : Env Γ)
    (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (ts : KemFailSessionTrack C.F Bytes)
    (party : Party) (m0 m1 : Plain ℓ) (optR : Option (BitVec 512)) (isChall : Bool)
    (hReach : SmReachBounded C K q st) (hTrInv : KemTrackDeliverInv C.F K q (kemTrackEnc ts.1))
    (hst : stE.eval ρ = epoch0HaltedEnc (st, ts))
    (hreq : reqE.eval ρ = (partyEnc party, (m0, (m1, (optR, isChall))))) :
    (sendOrChallTrackC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) q Δ qep stE reqE).eval ρ =
      (fun ⟨⟨w?, st'⟩, ts'⟩ => ((w?, (none, none)), epoch0HaltedEnc (st', ts'))) <$>
        (if isChall then
          (((challRSessionTrackHalted C.F K
            (sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins)
            Δ qep (configEpoch0Distinguisher (ratchetKeyAdmissible protoSignalCodec decT encT))
            (party, m0, m1, optR)).run st).run ts)
        else
          (((transmitRSessionTrackHalted C.F K
            (sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins)
            Δ qep (configEpoch0Distinguisher (ratchetKeyAdmissible protoSignalCodec decT encT))
            (party, m0, optR)).run st).run ts)) := by
  set sm := sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) (coinOnlyIface ℓ Pt)
  let inPre := (e2eGsEnc st, (partyEnc party, (m0, (m1, (optR, isChall)))))
  unfold sendOrChallTrackC; rw [comp_eval_bind_ret]
  have hp0 : (Expr.pair stE reqE).eval ρ = (epoch0HaltedEnc (st, ts), inPre.2) := by simp only [inPre, Expr.eval, hst, hreq]
  rw [hp0, comp_eval_bind, call1C_eval]
  set ρ₁ := Env.cons (t := .prod (epoch0HaltedStTy ℓ Pt) (sendReqATy ℓ Pt)) (epoch0HaltedEnc (st, ts), inPre.2) ρ
  have hPreLift : (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT)
      (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
      (preSendE2EC (coinE2ESamplers (coinOnlyIface ℓ Pt)) Δ qep (Γ := [preSendInTy ℓ]) .v0)).eval
      (.cons (liftVal (Pt := Pt) (t := preSendInTy ℓ) inPre) .nil) = _ :=
    liftCompCoins_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT)
      (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl (preSendE2EC coins Δ qep (Γ := [preSendInTy ℓ]) .v0) (.cons inPre .nil)
  have hEnvPre : ((Expr.pair (O := AOps) (.fst (.fst .v0)) (.snd .v0)).eval ρ₁) = liftVal (Pt := Pt) (t := preSendInTy ℓ) inPre := by
    cases optR <;> simp [ρ₁, inPre, epoch0HaltedEnc, Expr.eval, Expr.v0, liftVal, liftBaseVal]
  rw [hEnvPre, hPreLift, preSendE2EC_eval coins Δ qep (Γ := [preSendInTy ℓ]) .v0 (.cons inPre .nil)
    st party m0 m1 optR isChall rfl, liftP_unif_eq_self _ (fun _ => rfl)]
  set cfg := configEpoch0Distinguisher (ratchetKeyAdmissible protoSignalCodec decT encT)
  simp only [preSendModel, transmitRSessionTrackHalted, challRSessionTrackHalted]
  by_cases href : !cfg.sendOK st party || st.win
  · simp only [href, ↓reduceIte, Option.map_none, liftVal, map_pure, pure_bind,
      Comp.eval, Expr.eval, Expr.v0, Expr.v1, smRWireAE, ρ₁]
    rcases hok : cfg.sendOK st party with _ | _
    · rcases isChall with _ | _ <;> simp [hok, StateT.run_bind, StateT.run_get, StateT.run_pure]
    · have hwin : st.win = true := by cases h : st.win with | false => simp [h, hok] at href | true => rfl
      rcases isChall with _ | _ <;> simp [hok, hwin, StateT.run_bind, StateT.run_get, StateT.run_pure]
  · have hok : cfg.sendOK st party = true := by cases h : cfg.sendOK st party with | false => simp [h] at href | true => rfl
    have hwin : st.win = false := by cases h : st.win with | false => rfl | true => simp [h, hok] at href
    simp only [hok, hwin, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_monadLift, monadLift_self,
      map_bind, bind_assoc, pure_bind]
    have hIteBind : ∀ {α β : Type} (p : Prop) [Decidable p] (m : ProbComp α) (f g : α → ProbComp β),
        (if p then m >>= f else m >>= g) = (m >>= fun a => if p then f a else g a) := by
      intro _ _ _ _ _ _ _; split_ifs <;> rfl
    rw [hIteBind, map_bind]
    refine bind_congr fun ⟨rCoins, bad⟩ => ?_
    cases hep : st.epMgmt Δ qep party bad with
    | none =>
      rcases isChall with _ | _ <;>
        simp [liftVal, smRWireAE, Comp.eval, Expr.eval, Expr.v0, Expr.v1, ρ₁, StateT.run_pure]
    | some s1 =>
      obtain ⟨hst1, htr1, hcp1⟩ := epMgmt_preserve_fields hep
      have hAllowed : cfg.base.challAllowedIn (s1.epoch party) = true := rfl
      have hChallMsg : cfg.base.challMsg (s1.epoch party) = none := rfl
      by_cases hChRef : isChall && !(s1.safeCh Δ party)
      · have hisCh : isChall = true := by cases h : isChall with | false => simp [h] at hChRef | true => rfl
        have hsafeF : s1.safeCh Δ party = false := by cases h : s1.safeCh Δ party with | false => rfl | true => simp [h, hisCh] at hChRef
        subst hisCh
        simp [hsafeF, hAllowed, liftVal, smRWireAE, Comp.eval, Expr.eval, Expr.v0, Expr.v1, ρ₁, StateT.run_pure]
      · set mEff : Plain ℓ := if isChall then (if st.b then m1 else m0) else m0
        have hLiftSome : liftVal (Pt := Pt) (t := preSendOutTy ℓ) (some (e2eGsEnc s1, (mEff, rCoins))) =
            some (liftVal (Pt := Pt) (e2eGsEnc s1), (mEff, rCoins)) := rfl
        simp only [hChRef, Bool.false_eq_true, ↓reduceIte, Option.map_some, map_pure, pure_bind]
        rw [hLiftSome, comp_eval_caseOpt]; simp only [Expr.eval, Expr.v0, Env.get]
        set ρ₂ := Env.cons (t := .prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (.prod (PlainT (ℓ := ℓ) (Pt := Pt)) BV512))
          (liftVal (Pt := Pt) (e2eGsEnc s1), (mEff, rCoins))
          (Env.cons (t := liftTy (Pt := Pt) (preSendOutTy ℓ)) (some (liftVal (Pt := Pt) (e2eGsEnc s1), (mEff, rCoins))) ρ₁)
        rw [comp_eval_bind]
        have hStepTr : (stepKemFailSendAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam) q
            (.fst (.snd (.fst .v2))) (.fst (.snd .v2)) (.snd (.snd (.var .zero)))).eval ρ₂ = _ :=
          stepKemFailSendAtomicC_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam) q
            (.fst (.snd (.fst .v2))) (.fst (.snd .v2)) (.snd (.snd .v0)) ρ₂
            ts.1 party rCoins rfl (by simp [ρ₂, ρ₁, inPre, Expr.eval, Expr.v2])
            rfl (by simpa [kemTrackEnc] using hTrInv.bOk party) (by simpa [kemTrackEnc] using hTrInv.sentB_len)
        rw [hStepTr, pure_bind, comp_eval_ite]
        set tr' := stepKemFailSend C.F K ts.1 party rCoins
        set ρ₃ := Env.cons (t := .prod (kemTrackT ℓ Pt) (kemTrackT ℓ Pt))
          (kemTrackAtomicEnc (kemTrackEnc tr'), kemTrackAtomicEnc (kemTrackEnc { ts.1 with cand := tr'.cand })) ρ₂
        have hCandCond : (isSomeE (trE_cand (.fst (Expr.var (O := AOps) .zero)))).eval ρ₃ = tr'.cand.isSome := by
          rw [isSomeE_eval]; exact trE_cand_isSome tr'
        rw [hCandCond]
        by_cases hcand : tr'.cand.isSome
        · rcases isChall with _ | _
          · simp [hcand, tr', smRWireAE, epoch0HaltedEnc, kemSessionTrackEnc, ρ₃, ρ₂, ρ₁, Comp.eval, Expr.eval, Expr.v3,
              StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_set]
          · have hsafeT : s1.safeCh Δ party = true := by cases h : s1.safeCh Δ party with | false => simp [h] at hChRef | true => rfl
            simp [hcand, hsafeT, hAllowed, tr', smRWireAE, epoch0HaltedEnc, kemSessionTrackEnc, ρ₃, ρ₂, ρ₁, Comp.eval, Expr.eval, Expr.v3,
              StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_set]
        · simp only [hcand, Bool.false_eq_true, ↓reduceIte, comp_eval_bind, call1C_eval]
          let cPostE := postSendE2EC hooks (coinE2EIface (coinOnlyIface ℓ Pt)) q Δ (Γ := [postSendInTy ℓ]) (.var .zero)
          let inPost := (e2eGsEnc s1, (partyEnc party, (mEff, (rCoins, isChall))))
          have hPostLift : (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT)
              (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
              (postSendE2EC (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) (coinE2EIface (coinOnlyIface ℓ Pt)) q Δ (Γ := [postSendInTy ℓ]) (.var .zero))).eval
              (.cons (liftVal (Pt := Pt) (t := postSendInTy ℓ) inPost) .nil) = _ :=
            liftCompCoins_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT)
              (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl cPostE (.cons inPost .nil)
          have hEnvPost : ((Expr.pair (O := AOps) (.fst .v1) (.pair (.fst (.snd .v3)) (.pair (.fst (.snd .v1))
              (.pair (.snd (.snd .v1)) (.snd (.snd (.snd (.snd (.snd .v3))))))))).eval ρ₃) = liftVal (Pt := Pt) (t := postSendInTy ℓ) inPost := by
            simp [ρ₃, ρ₂, ρ₁, inPost, inPre, epoch0HaltedEnc, Expr.eval, Expr.v1, Expr.v3, liftVal, liftBaseVal]
          have hPostEv := postSendE2EC_eval hooks (coinE2EIface (coinOnlyIface ℓ Pt)) q Δ
            (Γ := [postSendInTy ℓ]) (.var .zero) (.cons inPost .nil) idA idB spkCoins s1 party mEff rCoins isChall
            (by cases party; exact hst1 ▸ hReach.reach.alice; exact hst1 ▸ hReach.reach.bob)
            (htr1 ▸ hReach.lists.trans_le) (hcp1 ▸ hReach.lists.dedupComp_le) rfl
          have hLiftOut : ∀ (ct : Bytes) (gsE : (e2eGsTy ℓ).denote),
              liftVal (Pt := Pt) (t := .prod (CryptoVerification.E2E.Costed.B 32) (e2eGsTy ℓ)) (ct, gsE) =
                (ct, liftVal (Pt := Pt) gsE) := fun _ _ => rfl
          rw [hEnvPost, hPostLift, hPostEv]; simp only [map_pure, hLiftOut, pure_bind]
          rcases isChall with _ | _
          · simp [hcand, tr', mEff, sm, inPre, smRWireAE, epoch0HaltedEnc, kemSessionTrackEnc, ρ₃, ρ₂, ρ₁, Comp.eval, Expr.eval, Expr.v1, Expr.v4,
              StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_set]
          · have hsafeT : s1.safeCh Δ party = true := by cases h : s1.safeCh Δ party with | false => simp [h] at hChRef | true => rfl
            simp [hcand, hsafeT, hAllowed, hChallMsg, tr', mEff, sm, inPre, smRWireAE, epoch0HaltedEnc, kemSessionTrackEnc, ρ₃, ρ₂, ρ₁, Comp.eval, Expr.eval, Expr.v1, Expr.v4,
              StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_set]

private theorem liftVal_smRRecv (rr? : Option (RecvResult (Plain ℓ))) :
    (liftVal (Pt := Pt) (t := smRT (CryptoVerification.E2E.Costed.GhostStT))
      (none, (rr?.map recvResultEnc, none))).2.1 = rr?.map _root_.ReductionDsl.recvResultEnc := by
  rcases rr? with _ | (_ | ⟨_, _, _ | _⟩) <;> rfl

theorem dlArmTrackC_eval (q : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (epoch0HaltedStTy ℓ Pt)) (dlArg : Expr AOps Γ (.prod .bool (B 32))) (ρ : Env Γ)
    (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (ts : KemFailSessionTrack C.F Bytes)
    (party : Party) (w : Bytes)
    (hReach : SmReachBounded C K q st) (hTrInv : KemTrackDeliverInv C.F K q (kemTrackEnc ts.1)) (hHw : ts.2.length ≤ q)
    (hst : stE.eval ρ = epoch0HaltedEnc (st, ts)) (harg : dlArg.eval ρ = (partyEnc party, w)) :
    (dlArmTrackC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) q stE dlArg).eval ρ =
      (fun ⟨⟨rr?, st'⟩, ts'⟩ =>
        (liftVal (Pt := Pt) (t := smRT CryptoVerification.E2E.Costed.GhostStT) (none, (rr?.map recvResultEnc, none)),
         epoch0HaltedEnc (st', ts'))) <$>
        (((deliverRSessionTrackHalted C.F K
          (sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins)
          (configEpoch0Distinguisher (ratchetKeyAdmissible protoSignalCodec decT encT))
          (party, w)).run st).run ts) := by
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) (coinOnlyIface ℓ Pt)
  let cDlE := drDlArmC hooks coins q
    (Γ := [.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))]) (.fst .v0) (.snd .v0)
  unfold dlArmTrackC deliverRSessionTrackHalted; rw [comp_eval_bind_ret]
  have hp0 : (Expr.pair stE dlArg).eval ρ = (epoch0HaltedEnc (st, ts), (partyEnc party, w)) := by
    simp only [Expr.eval, hst, harg]
  rw [hp0, comp_eval_bind_ret]
  set ρ₁ := Env.cons (t := .prod (epoch0HaltedStTy ℓ Pt) (.prod .bool (B 32))) (epoch0HaltedEnc (st, ts), (partyEnc party, w)) ρ
  have hFind := findRevHonestWiresIdxE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) q
    (.snd (.snd (.fst .v0))) (.fst (.snd .v0)) (.snd (.snd .v0)) ρ₁ ts.2 party w hHw rfl rfl rfl
  rw [hFind, comp_eval_bind, call1C_eval]
  set j? := ts.2.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == party.other)
  set ρ₂ := Env.cons (t := .opt .nat) j? ρ₁
  have hDlLift : (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
      (drDlArmC (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) (coinE2ESamplers (coinOnlyIface ℓ Pt)) q
        (Γ := [.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))]) (.fst .v0) (.snd .v0))).eval
      (.cons (liftVal (Pt := Pt) (t := .prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32)))
        (e2eGsEnc st, (partyEnc party, w))) .nil) = _ :=
    liftCompCoins_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
      cDlE (.cons (e2eGsEnc st, (partyEnc party, w)) .nil)
  have hEnvDl : ((Expr.pair (O := AOps) (.fst (.fst .v1)) (.snd .v1)).eval ρ₂) =
      liftVal (Pt := Pt) (t := .prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32)))
        (e2eGsEnc st, (partyEnc party, w)) := by
    simp [ρ₂, ρ₁, epoch0HaltedEnc, Expr.eval, Expr.v1, liftVal, liftBaseVal]
  rw [hEnvDl, hDlLift, drDlArmC_eval hooks coins q (Γ := [.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))])
    (.fst .v0) (.snd .v0) (.cons (e2eGsEnc st, (partyEnc party, w)) .nil) idA idB spkCoins
    st party w hReach rfl rfl, liftP_unif_eq_self _ (fun _ => rfl)]
  have hCfgEq : deliverR (sessionSchemeFixedSpk
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins)
      (configRefuseEarlyBobCorr decT encT) (party, w) =
    deliverR (sessionSchemeFixedSpk
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins)
      (configEpoch0Distinguisher (ratchetKeyAdmissible protoSignalCodec decT encT)) (party, w) := rfl
  rw [hCfgEq]
  simp only [StateT.run_bind, StateT.run_lift, StateT.run_get, liftStateT_run_state,
    map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  refine bind_congr fun ⟨rr?, st'⟩ => ?_
  set ansA := liftVal (Pt := Pt) (t := smRT CryptoVerification.E2E.Costed.GhostStT) (none, (rr?.map recvResultEnc, none))
  set ρ₃ := Env.cons (t := .prod (smRATy ℓ Pt) (liftTy (Pt := Pt) (e2eGsTy ℓ))) (ansA, liftVal (Pt := Pt) (e2eGsEnc st')) ρ₂
  have hPost := kemOnDeliverPostAtomicE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) q
    (.fst (.snd .v2)) .v1 (.fst (.snd (.fst .v0))) (.fst (.snd (.fst .v2))) ρ₃ party j? rr? ts.1
    (by simp [ρ₃, ρ₂, ρ₁, Expr.eval, Expr.v2]) rfl
    (by simpa [ρ₃, ansA, Expr.eval, Expr.v0, Env.get] using liftVal_smRRecv (Pt := Pt) rr?) rfl hTrInv
  have hρ3 : Env.cons (liftVal (Pt := Pt) (t := .prod (smRT CryptoVerification.E2E.Costed.GhostStT) (e2eGsTy ℓ))
      (Prod.map (fun rr => (none, Option.map recvResultEnc rr, none)) e2eGsEnc (rr?, st'))) ρ₂ = ρ₃ := rfl
  have hFindEq : ts.2.reverse.findIdx? (fun wp => @BEq.beq Bytes (@instBEqOfDecidableEq Bytes inferInstance) wp.1 w && wp.2 == party.other) = j? := by
    congr 1; funext ⟨w', p'⟩
    have hbeq : @BEq.beq Bytes (@instBEqOfDecidableEq Bytes inferInstance) w' w = (w' == w) := by
      change decide (w' = w) = (w' == w)
      rw [Bool.eq_iff_iff, decide_eq_true_eq, beq_iff_eq]
    rw [hbeq]
  rw [comp_eval_ret, hρ3, hFindEq]
  dsimp only [Expr.eval]; rw [hPost]
  simp only [ansA, epoch0HaltedEnc, kemSessionTrackEnc, ρ₃, ρ₂, ρ₁, Expr.eval, Expr.v0, Expr.v2]
  rcases rr? with _ | (_ | ⟨_, _, _⟩) <;> rcases j? with _ | j <;>
    (simp [StateT.run_modify, StateT.run_pure]; rfl)

theorem liftGsArmTrackC_eval {argT : Ty ESig}
    (cArmE : Comp EOps (coinE2EIface (coinOnlyIface ℓ Pt)) [.prod (e2eGsTy ℓ) argT]
      (.prod (smRT CryptoVerification.E2E.Costed.GhostStT) (e2eGsTy ℓ)))
    {Γ : List (Ty ASig)} (stE : Expr AOps Γ (epoch0HaltedStTy ℓ Pt))
    (argE : Expr AOps Γ (liftTy (Pt := Pt) argT)) (ρ : Env Γ)
    {Ans : Type} (encAns : Ans → (smRT CryptoVerification.E2E.Costed.GhostStT).denote)
    (m : StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes) ProbComp Ans)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (ts : KemFailSessionTrack C.F Bytes) (argV : argT.denote)
    (hst : stE.eval ρ = epoch0HaltedEnc (st, ts)) (harg : argE.eval ρ = liftVal (Pt := Pt) argV)
    (hcArm : cArmE.eval (.cons (e2eGsEnc st, argV) .nil) =
      Prod.map encAns e2eGsEnc <$> (coinE2EIface (coinOnlyIface ℓ Pt)).liftP (m.run st)) :
    (liftGsArmTrackC (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl cArmE) stE argE).eval ρ =
      (fun ⟨⟨ans, st'⟩, ts'⟩ =>
        (liftVal (Pt := Pt) (t := smRT CryptoVerification.E2E.Costed.GhostStT) (encAns ans),
         epoch0HaltedEnc (st', ts'))) <$>
        (((liftStateT m : StateT _ (StateT (KemFailSessionTrack C.F Bytes) ProbComp) Ans).run st).run ts) := by
  unfold liftGsArmTrackC; rw [comp_eval_bind_ret]
  have hp0 : (Expr.pair stE argE).eval ρ = (epoch0HaltedEnc (st, ts), liftVal (Pt := Pt) argV) := by
    simp only [Expr.eval, hst, harg]
  rw [hp0, comp_eval_bind, call1C_eval]
  set ρ₁ := Env.cons (t := .prod (epoch0HaltedStTy ℓ Pt) (liftTy (Pt := Pt) argT))
    (epoch0HaltedEnc (st, ts), liftVal (Pt := Pt) argV) ρ
  have hLift : (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl cArmE).eval
      (.cons (liftVal (Pt := Pt) (t := .prod (e2eGsTy ℓ) argT) (e2eGsEnc st, argV)) .nil) = _ :=
    liftCompCoins_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl cArmE (.cons (e2eGsEnc st, argV) .nil)
  have hEnv : ((Expr.pair (O := AOps) (.fst (.fst .v0)) (.snd .v0)).eval ρ₁) =
      liftVal (Pt := Pt) (t := .prod (e2eGsTy ℓ) argT) (e2eGsEnc st, argV) := by
    simp [ρ₁, epoch0HaltedEnc, Expr.eval, Expr.v0, liftVal]
  rw [hEnv, hLift, hcArm, liftP_unif_eq_self _ (fun _ => rfl)]
  simp only [liftStateT_run_state, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, comp_eval_ret]
  exact bind_congr fun ⟨_, _⟩ => rfl

theorem epoch0OracleStepTrackC_eval (q Δ qep : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (epoch0HaltedStTy ℓ Pt)) (qryE : Expr AOps Γ (liftTy (Pt := Pt) smQT)) (ρ : Env Γ)
    (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (ts : KemFailSessionTrack C.F Bytes)
    (sq : (spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (hReach : SmReachBounded C K q st) (hTrInv : KemTrackDeliverInv C.F K q (kemTrackEnc ts.1)) (hHw : ts.2.length ≤ q)
    (hst : stE.eval ρ = epoch0HaltedEnc (st, ts))
    (hqry : qryE.eval ρ = liftVal (Pt := Pt) (smQenc (St := GhostState Bytes) sq)) :
    (epoch0OracleStepTrackC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) q Δ qep stE qryE).eval ρ =
      (fun ⟨⟨ans, st'⟩, ts'⟩ =>
        (liftVal (Pt := Pt) (t := smRT CryptoVerification.E2E.Costed.GhostStT) (smRenc id sq ans),
         epoch0HaltedEnc (st', ts'))) <$>
        (((oracleImplRSessionTrackHalted C.F K
          (sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins)
          Δ qep (configEpoch0Distinguisher (ratchetKeyAdmissible protoSignalCodec decT encT)) sq).run st).run ts) := by
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) (coinOnlyIface ℓ Pt)
  unfold epoch0OracleStepTrackC; rw [comp_eval_bind_ret]
  have hp0 : (Expr.pair stE qryE).eval ρ =
      (epoch0HaltedEnc (st, ts), liftVal (Pt := Pt) (smQenc (St := GhostState Bytes) sq)) := by
    simp only [Expr.eval, hst, hqry]
  rw [hp0]
  rcases sq with (((⟨party, m, optR⟩ | ⟨party, m0, m1, optR⟩) | ⟨party, w⟩) | ⟨party, w⟩) | party
  · simp only [comp_eval_caseSum, smQenc, liftVal, liftBaseVal, partyToBool_eq_partyEnc, Expr.eval, Expr.v0, Env.get]
    rw [sendOrChallTrackC_eval q Δ qep _ _ _ idA idB spkCoins st ts party m m optR false hReach hTrInv rfl
      (by cases optR <;> rfl)]
    change _ = _ <$> (((transmitRSessionTrackHalted C.F K _ Δ qep _ (party, m, optR)).run st).run ts)
    dsimp only [Bool.false_eq_true, ↓reduceIte]; congr 1; funext ⟨⟨w?, _⟩, _⟩; cases w? <;> rfl
  · simp only [comp_eval_caseSum, smQenc, liftVal, liftBaseVal, partyToBool_eq_partyEnc, Expr.eval, Expr.v0, Env.get]
    rw [sendOrChallTrackC_eval q Δ qep _ _ _ idA idB spkCoins st ts party m0 m1 optR true hReach hTrInv rfl
      (by cases optR <;> rfl)]
    change _ = _ <$> (((challRSessionTrackHalted C.F K _ Δ qep _ (party, m0, m1, optR)).run st).run ts)
    dsimp only [↓reduceIte]; congr 1; funext ⟨⟨w?, _⟩, _⟩; cases w? <;> rfl
  · simp only [comp_eval_caseSum, smQenc, liftVal, liftBaseVal, partyToBool_eq_partyEnc, Expr.eval, Expr.v0, Env.get]
    exact dlArmTrackC_eval q _ _ _ idA idB spkCoins st ts party w hReach hTrInv hHw rfl rfl
  · simp only [comp_eval_caseSum, smQenc, liftVal, liftBaseVal, partyToBool_eq_partyEnc, Expr.eval, Expr.v0, Env.get]
    exact liftGsArmTrackC_eval
      (epoch0IjArmC hooks coins q Δ qep (Γ := [.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))]) (.fst .v0) (.snd .v0))
      _ _ _ (smRenc id (.inl (.inr (party, w)))) (injectR _ Δ qep _ (party, w)) st ts (partyEnc party, w)
      rfl rfl (epoch0IjArmC_eval hooks coins q Δ qep _ _ _ idA idB spkCoins st party w hReach rfl rfl)
  · simp only [comp_eval_caseSum, smQenc, liftVal, liftBaseVal, partyToBool_eq_partyEnc, Expr.eval, Expr.v0, Env.get]
    refine Eq.trans (liftGsArmTrackC_eval (epoch0CrArmC (C := C) (K := K) (decT := decT) (encT := encT)
        (I := coinE2EIface (coinOnlyIface ℓ Pt)) q (Γ := [.prod (e2eGsTy ℓ) .bool]) (.fst .v0) (.snd .v0))
      _ _ _ (fun st? => (none, (none, st?))) (corrR _ party) st ts (partyEnc party) rfl rfl
      (epoch0CrArmC_eval (C := C) (K := K) (decT := decT) (encT := encT)
        (I := coinE2EIface (coinOnlyIface ℓ Pt)) q _ _ _ st party hReach rfl rfl)) ?_
    dsimp only [oracleImplRSessionTrackHalted, Sum.elim_inr]; congr 1; funext ⟨⟨st?, _⟩, _⟩; cases st? <;> rfl

theorem oracleImplRSessionTrackHalted_inv (idA idB : IdentityKey) (spkCoins : BitVec 256) (qep n : ℕ)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (ts : KemFailSessionTrack C.F Bytes)
    (sq : (spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (hReach : SmReachBounded C K n st) (hTrInv : KemTrackDeliverInv C.F K n (kemTrackEnc ts.1)) (hHw : ts.2.length ≤ n) :
    ∀ w ∈ support (((oracleImplRSessionTrackHalted C.F K
      (sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins)
      3 qep (configEpoch0Distinguisher (ratchetKeyAdmissible protoSignalCodec decT encT)) sq).run st).run ts),
      SmReachBounded C K (n + 1) w.1.2 ∧ KemTrackDeliverInv C.F K (n + 1) (kemTrackEnc w.2.1) ∧ w.2.2.length ≤ n + 1 := by
  rcases ts with ⟨tr, hw⟩
  set sm := sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins
  set cfg := configEpoch0Distinguisher (ratchetKeyAdmissible protoSignalCodec decT encT)
  have hKeep : SmReachBounded C K (n + 1) st ∧ KemTrackDeliverInv C.F K (n + 1) (kemTrackEnc tr) ∧ hw.length ≤ n + 1 :=
    ⟨hReach.mono (Nat.le_succ n), hTrInv.mono (Nat.le_succ n), Nat.le_trans hHw (Nat.le_succ n)⟩
  intro out hout; rcases out with ⟨⟨ans, st'⟩, ⟨tr', hw'⟩⟩
  rcases sq with (((⟨P, m, optR⟩ | ⟨P, m0, m1, optR⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | P
  · change ((ans, st'), tr', hw') ∈ support (((transmitRSessionTrackHalted C.F K sm 3 qep cfg (P, m, optR)).run st).run (tr, hw)) at hout
    unfold transmitRSessionTrackHalted at hout
    by_cases hok : cfg.sendOK st P
    · by_cases hwin : st.win
      · simp [hok, hwin, StateT.run_bind, StateT.run_get, StateT.run_pure] at hout; rcases hout with ⟨⟨_, rfl⟩, rfl, rfl⟩; exact hKeep
      · simp only [hok, hwin, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_lift,
          StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc, mem_support_bind_iff] at hout
        obtain ⟨⟨coins, bad⟩, hsam, hout⟩ := hout
        cases hep : st.epMgmt 3 qep P bad with
        | none => simp [hep, StateT.run_pure] at hout; rcases hout with ⟨⟨_, rfl⟩, rfl, rfl⟩; exact hKeep
        | some s1 =>
          simp only [hep, StateT.run_bind, StateT.run_lift, StateT.run_get, pure_bind, bind_assoc] at hout
          by_cases hc : (stepKemFailSend C.F K tr P coins).cand.isSome
          · simp [hc, StateT.run_bind, StateT.run_lift, StateT.run_set, StateT.run_pure, -bind_pure_comp] at hout
            rcases hout with ⟨⟨_, rfl⟩, rfl, rfl⟩
            exact ⟨hReach.mono (Nat.le_succ n), KemTrackDeliverInv.mono ⟨hTrInv.sentB_len, hTrInv.bOk, hTrInv.sentB_deser⟩ (Nat.le_succ n),
              Nat.le_trans hHw (Nat.le_succ n)⟩
          · simp [hc, StateT.run_bind, StateT.run_lift, StateT.run_set, StateT.run_pure, -bind_pure_comp] at hout
            rcases hout with ⟨⟨rfl, rfl⟩, rfl, rfl⟩
            have hmem : (some (sm.send (s1.st P) m coins).2,
                s1.record 3 P (sm.send (s1.st P) m coins).1 ⟨⟨P, s1.epoch P, s1.idx P + 1⟩, m, (sm.send (s1.st P) m coins).2⟩ false) ∈
                support ((oracleImplR sm 3 qep cfg (.inl (.inl (.inl (.inl (P, m, optR)))))).run st) := by
              change _ ∈ support ((transmitR sm 3 qep cfg (P, m, optR)).run st); unfold transmitR transmitImpl
              simp only [StateT.run_bind, StateT.run_get, hok, hwin, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc, mem_support_bind_iff]
              exact ⟨(coins, bad), hsam, by simp [hep, StateT.run_set]; exact ⟨rfl, rfl⟩⟩
            exact ⟨smReachBounded_oracleImplR C K idA idB ℓ 3 qep n spkCoins cfg (.inl (.inl (.inl (.inl (P, m, optR))))) hReach hmem,
              kemTrackDeliverInv_stepSend C.F K n tr P coins hTrInv, Nat.succ_le_succ hHw⟩
    · simp [hok, StateT.run_bind, StateT.run_get, StateT.run_pure] at hout; rcases hout with ⟨⟨_, rfl⟩, rfl, rfl⟩; exact hKeep
  · change ((ans, st'), tr', hw') ∈ support (((challRSessionTrackHalted C.F K sm 3 qep cfg (P, m0, m1, optR)).run st).run (tr, hw)) at hout
    unfold challRSessionTrackHalted at hout
    by_cases hok : cfg.sendOK st P
    · by_cases hwin : st.win
      · simp [hok, hwin, StateT.run_bind, StateT.run_get, StateT.run_pure] at hout; rcases hout with ⟨⟨_, rfl⟩, rfl, rfl⟩; exact hKeep
      · simp only [hok, hwin, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_lift,
          StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc, mem_support_bind_iff] at hout
        obtain ⟨⟨coins, bad⟩, hsam, hout⟩ := hout
        cases hep : st.epMgmt 3 qep P bad with
        | none => simp [hep, StateT.run_pure] at hout; rcases hout with ⟨⟨_, rfl⟩, rfl, rfl⟩; exact hKeep
        | some s1 =>
          by_cases hsc : !(s1.safeCh 3 P) || !(cfg.base.challAllowedIn (s1.epoch P))
          · simp [hep, hsc, StateT.run_pure] at hout; rcases hout with ⟨⟨_, rfl⟩, rfl, rfl⟩; exact hKeep
          · simp only [hep, hsc, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift, StateT.run_get, pure_bind, bind_assoc] at hout
            by_cases hc : (stepKemFailSend C.F K tr P coins).cand.isSome
            · simp [hc, StateT.run_bind, StateT.run_lift, StateT.run_set, StateT.run_pure, -bind_pure_comp] at hout
              rcases hout with ⟨⟨_, rfl⟩, rfl, rfl⟩
              exact ⟨hReach.mono (Nat.le_succ n), KemTrackDeliverInv.mono ⟨hTrInv.sentB_len, hTrInv.bOk, hTrInv.sentB_deser⟩ (Nat.le_succ n),
                Nat.le_trans hHw (Nat.le_succ n)⟩
            · simp [hc, StateT.run_bind, StateT.run_lift, StateT.run_set, StateT.run_pure, -bind_pure_comp] at hout
              rcases hout with ⟨⟨rfl, rfl⟩, rfl, rfl⟩
              set mUse := (cfg.base.challMsg (s1.epoch P)).getD (if st.b then m1 else m0)
              have hmem : (some (sm.send (s1.st P) mUse coins).2,
                  s1.record 3 P (sm.send (s1.st P) mUse coins).1 ⟨⟨P, s1.epoch P, s1.idx P + 1⟩, mUse, (sm.send (s1.st P) mUse coins).2⟩ true) ∈
                  support ((oracleImplR sm 3 qep cfg (.inl (.inl (.inl (.inr (P, m0, m1, optR)))))).run st) := by
                change _ ∈ support ((challR sm 3 qep cfg (P, m0, m1, optR)).run st); unfold challR challImpl
                simp only [StateT.run_bind, StateT.run_get, hok, hwin, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                  StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc, mem_support_bind_iff]
                exact ⟨(coins, bad), hsam, by simp [hep, hsc, mUse, StateT.run_set]; exact ⟨rfl, rfl⟩⟩
              exact ⟨smReachBounded_oracleImplR C K idA idB ℓ 3 qep n spkCoins cfg (.inl (.inl (.inl (.inr (P, m0, m1, optR))))) hReach hmem,
                kemTrackDeliverInv_stepSend C.F K n tr P coins hTrInv, Nat.succ_le_succ hHw⟩
    · simp [hok, StateT.run_bind, StateT.run_get, StateT.run_pure] at hout; rcases hout with ⟨⟨_, rfl⟩, rfl, rfl⟩; exact hKeep
  · change ((ans, st'), tr', hw') ∈ support (((deliverRSessionTrackHalted C.F K sm cfg (Q, w)).run st).run (tr, hw)) at hout
    unfold deliverRSessionTrackHalted at hout
    simp only [StateT.run_bind, StateT.run_lift, StateT.run_get, liftStateT_run_state, pure_bind, bind_assoc, mem_support_bind_iff] at hout
    obtain ⟨⟨res, s1⟩, hdl, hout⟩ := hout
    have hReach1 := smReachBounded_oracleImplR C K idA idB ℓ 3 qep n spkCoins cfg (.inl (.inl (.inr (Q, w)))) hReach hdl
    cases res with
    | none => simp [StateT.run_pure] at hout; rcases hout with ⟨⟨_, rfl⟩, rfl, rfl⟩; exact ⟨hReach1, hKeep.2⟩
    | some rr =>
      cases rr with
      | rejected => simp [StateT.run_pure] at hout; rcases hout with ⟨⟨_, rfl⟩, rfl, rfl⟩; exact ⟨hReach1, hKeep.2⟩
      | accepted e i m? =>
        cases hj : List.findIdx? (fun wp => @BEq.beq Bytes (@instBEqOfDecidableEq Bytes inferInstance) wp.1 w && wp.2 == Q.other) hw.reverse with
        | none => rw [hj] at hout; simp [StateT.run_pure] at hout; rcases hout with ⟨⟨_, rfl⟩, rfl, rfl⟩; exact ⟨hReach1, hKeep.2⟩
        | some j =>
          rw [hj] at hout; simp [StateT.run_bind, StateT.run_lift, StateT.run_modify, StateT.run_pure, -bind_pure_comp] at hout
          rcases hout with ⟨⟨_, rfl⟩, rfl, rfl⟩
          exact ⟨hReach1, (kemTrackDeliverInv_step C.F K n tr Q j hTrInv).mono (Nat.le_succ n), Nat.le_trans hHw (Nat.le_succ n)⟩
  · change ((ans, st'), tr', hw') ∈ support (((liftStateT (injectR sm 3 qep cfg (Q, w)) :
        StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes) (StateT (KemFailSessionTrack C.F Bytes) ProbComp) _).run st).run (tr, hw)) at hout
    simp only [liftStateT_run_state, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
    obtain ⟨⟨res, s1⟩, hij, h0⟩ := hout; cases h0
    exact ⟨smReachBounded_oracleImplR C K idA idB ℓ 3 qep n spkCoins cfg (.inl (.inr (Q, w))) hReach hij, hKeep.2⟩
  · change ((ans, st'), tr', hw') ∈ support (((liftStateT (corrR cfg P) :
        StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes) (StateT (KemFailSessionTrack C.F Bytes) ProbComp) _).run st).run (tr, hw)) at hout
    simp only [liftStateT_run_state, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
    obtain ⟨⟨res, s1⟩, hcr, h0⟩ := hout; cases h0
    exact ⟨smReachBounded_oracleImplR C K idA idB ℓ 3 qep n spkCoins cfg (.inr P) hReach hcr, hKeep.2⟩

end StepHalted

/-! ## Promoted tracker-halted `CostedReduction` and `GRedBounded` -/

section Reduction

variable (C : Crypto) (K : MlKem) {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (idA idB : IdentityKey) (lam : Pt) (ℓ q qep : ℕ)

@[expose] def epoch0DistinguisherProgHaltedReal :
    CostedReduction (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (coinOnlyIface ℓ Pt)
      (spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) (e2eSessionCodec ℓ Pt) (.prod BV256 BV256) .unit .bool .bool where
  σ := epoch0HaltedStTy ℓ Pt
  init := initEpoch0GsTrackC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB
  handle := epoch0OracleStepTrackC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q (2 + 1) qep (Γ := [epoch0HaltedStTy ℓ Pt, liftTy (Pt := Pt) smQT]) .v0 .v1
  finish := .ret (epoch0HaltedFinishE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q)

/-- Tracker-halted promoted `CostedReduction` witness for `epoch0DistinguisherTrackHalted`. -/
@[expose] def epoch0DistinguisherProgHalted :
    CostedReduction (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (coinOnlyIface ℓ Pt)
      (spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) (e2eSessionCodec ℓ Pt) (.prod BV256 BV256) .unit .bool .bool :=
  if ℓ < 10 ^ 6 then epoch0DistinguisherProgHaltedReal C K Dh encPt encT decT idA idB lam ℓ q qep
  else dummyBoolSessionRed (coinOnlyIface ℓ Pt) (.prod BV256 BV256)

abbrev epoch0RedHalted := epoch0DistinguisherProgHalted C K (Pt := Pt) Dh encPt encT decT idA idB lam ℓ q qep

theorem epoch0DistinguisherProgHalted_totalQueries_zero :
    (epoch0DistinguisherProgHalted C K Dh encPt encT decT idA idB lam ℓ q qep).totalQueries Empty.elim (fun _ => 0) q = 0 := by
  unfold epoch0DistinguisherProgHalted; split_ifs with hℓ
  · simp [epoch0DistinguisherProgHaltedReal, CostedReduction.totalQueries,
      initEpoch0GsTrackC_queries_zero, epoch0OracleStepTrackC_queries_zero, Comp.queries]
  · exact dummyBoolSessionRed_totalQueries _ _ _ _ _

theorem epoch0DistinguisherProgHalted_totalCost_le {qep' : ℕ} (hqep : qep ≤ qep') :
    (epoch0DistinguisherProgHalted C K Dh encPt encT decT idA idB lam ℓ q qep).totalCost q ≤ ratchetCostBudget q qep' := by
  unfold epoch0DistinguisherProgHalted; split_ifs with hℓ
  · unfold epoch0DistinguisherProgHaltedReal CostedReduction.totalCost
    have hinit := initEpoch0GsTrackC_cost (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB
    have hstep := epoch0OracleStepTrackC_cost (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q (2 + 1) qep (Γ := [epoch0HaltedStTy ℓ Pt, liftTy (Pt := Pt) smQT]) .v0 .v1
    conv at hstep => rhs; simp only [Expr.v0, Expr.v1, Expr.cost]
    have hfin := cost_epoch0HaltedFinishE_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q
    have hb3 : bits (2 + 1) = 2 := by decide
    have hbQep1 : bits qep ≤ bits qep' := bits_mono hqep
    have hbQep2 : bits (qep + 1) ≤ bits qep' + 1 := (bits_succ_le qep).trans (Nat.add_le_add_right (bits_mono hqep) 1)
    have hdiv : ℓ / 32 + 1 ≤ 31251 := by omega
    have hstep_le : (epoch0OracleStepTrackC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q (2 + 1) qep
        (Γ := [epoch0HaltedStTy ℓ Pt, liftTy (Pt := Pt) smQT]) .v0 .v1).cost ≤
        173599984 + 13440 * q + 64 * bits qep' := hstep.trans (by omega)
    have hH_le : max (coinOnlyIface ℓ Pt).uCost
        ((epoch0OracleStepTrackC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q (2 + 1) qep
          (Γ := [epoch0HaltedStTy ℓ Pt, liftTy (Pt := Pt) smQT]) .v0 .v1).cost + (e2eSessionCodec ℓ Pt).codecCost) ≤
        173600000 + 13440 * q + 64 * bits qep' := by
      dsimp only [coinOnlyIface, e2eSessionCodec]
      exact max_le (by omega) ((Nat.add_le_add_right hstep_le 16).trans (by omega))
    have hF_le : (Comp.ret (I := coinOnlyIface ℓ Pt) (epoch0HaltedFinishE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q)).cost ≤ 5000 + 400 * q := by dsimp only [Comp.cost]; omega
    exact (Nat.add_le_add (Nat.add_le_add hinit (Nat.mul_le_mul_left q hH_le)) hF_le).trans
      (session_cost_le_ratchetCostBudget q qep' 3020000 (5000 + 400 * q) 173600000 13440 64
        (by omega) (by omega) (by omega) (by omega) (by omega))
  · exact dummyBoolSessionRed_totalCost_le _ rfl _ q qep'

theorem epoch0DistinguisherProgHalted_size_raw_le :
    (epoch0DistinguisherProgHalted C K Dh encPt encT decT idA idB lam ℓ q qep).size ≤
      1840000 + 171 * bits q + 2 * bits (q + 1) + 36 * bits qep + 9 * bits (qep + 1) := by
  unfold epoch0DistinguisherProgHalted; split_ifs with hℓ
  · have hinit := initEpoch0GsTrackC_size_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB
    have hstep := epoch0OracleStepTrackC_size_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q (2 + 1) qep (Γ := [epoch0HaltedStTy ℓ Pt, liftTy (Pt := Pt) smQT]) .v0 .v1
    conv at hstep => rhs; simp only [Expr.v0, Expr.v1, Expr.size]
    have hfin := size_epoch0HaltedFinishE_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q
    have hb3 : bits (2 + 1) = 2 := by decide
    change (initEpoch0GsTrackC idA idB).size + (epoch0OracleStepTrackC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q (2 + 1) qep (Γ := [epoch0HaltedStTy ℓ Pt, liftTy (Pt := Pt) smQT]) .v0 .v1).size +
      ((epoch0HaltedFinishE q).size + 1) ≤ _; omega
  · rw [dummyBoolSessionRed_size]; omega

private theorem q_add_eleven_le_ratchetCostBudget (q' qep' : ℕ) : q' + 11 ≤ ratchetCostBudget q' qep' := by
  have := session_cost_le_ratchetCostBudget q' qep' 100 (400 * q') 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega); omega

theorem epoch0DistinguisherProgHalted_size_le_of_clamp {qep' : ℕ} (hqep_B : qep + 1 ≤ ratchetCostBudget q qep') :
    (epoch0DistinguisherProgHalted C K Dh encPt encT decT idA idB lam ℓ q qep).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep') := by
  have hraw := epoch0DistinguisherProgHalted_size_raw_le C K Dh encPt encT decT idA idB lam ℓ q qep
  have hqB := q_add_eleven_le_ratchetCostBudget q qep'
  have hbq : bits q ≤ bits (ratchetCostBudget q qep') := bits_mono (by omega)
  have hbq1 : bits (q + 1) ≤ bits (ratchetCostBudget q qep') := bits_mono (by omega)
  have hbqep : bits qep ≤ bits (ratchetCostBudget q qep') := bits_mono (by omega)
  have hbqep1 : bits (qep + 1) ≤ bits (ratchetCostBudget q qep') := bits_mono hqep_B
  exact size_le_budget_of_log_cost (by decide) (by decide) (show
    (epoch0DistinguisherProgHalted C K Dh encPt encT decT idA idB lam ℓ q qep).size ≤ 1840000 + 218 * bits (ratchetCostBudget q qep') by omega)

theorem epoch0DistinguisherProgHalted_size_le {qep' : ℕ} (hqep_q : qep ≤ q + 10) :
    (epoch0DistinguisherProgHalted C K Dh encPt encT decT idA idB lam ℓ q qep).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep') := by
  have hqB := q_add_eleven_le_ratchetCostBudget q qep'
  exact epoch0DistinguisherProgHalted_size_le_of_clamp C K Dh encPt encT decT idA idB lam ℓ q qep (by omega)

theorem epoch0DistinguisherProgHalted_gRedBounded_of_clamp {qep' : ℕ}
    (hqep : qep ≤ qep') (hqep_B : qep + 1 ≤ ratchetCostBudget q qep') :
    GRedBounded (epoch0DistinguisherProgHalted C K Dh encPt encT decT idA idB lam ℓ q qep)
      Empty.elim (fun _ => 0) q 0 (ratchetCostBudget q qep') :=
  gRedBounded_of_bounds _ Empty.elim (fun _ => 0) q 0 (ratchetCostBudget q qep')
    (epoch0DistinguisherProgHalted_totalCost_le C K Dh encPt encT decT idA idB lam ℓ q qep hqep)
    (epoch0DistinguisherProgHalted_size_le_of_clamp C K Dh encPt encT decT idA idB lam ℓ q qep hqep_B)
    (Nat.le_of_eq (epoch0DistinguisherProgHalted_totalQueries_zero C K Dh encPt encT decT idA idB lam ℓ q qep))
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam) (atomicSamplers_sizeHonest ℓ Pt)

theorem epoch0DistinguisherProgHalted_gRedBounded_of_le {qep' : ℕ} (hqep_q : qep ≤ q + 10) (hqep : qep ≤ qep') :
    GRedBounded (epoch0DistinguisherProgHalted C K Dh encPt encT decT idA idB lam ℓ q qep)
      Empty.elim (fun _ => 0) q 0 (ratchetCostBudget q qep') :=
  epoch0DistinguisherProgHalted_gRedBounded_of_clamp C K Dh encPt encT decT idA idB lam ℓ q qep hqep
    (by have := q_add_eleven_le_ratchetCostBudget q qep'; omega)

theorem epoch0DistinguisherProgHalted_gRedBounded (hqep : qep ≤ q + 10) :
    GRedBounded (epoch0DistinguisherProgHalted C K Dh encPt encT decT idA idB lam ℓ q qep)
      Empty.elim (fun _ => 0) q 0 (ratchetCostBudget q qep) :=
  epoch0DistinguisherProgHalted_gRedBounded_of_le C K Dh encPt encT decT idA idB lam ℓ q qep hqep (Nat.le_refl qep)

theorem epoch0DistinguisherProgHalted_gRedBounded_succ (hqep : qep ≤ q + 10) :
    GRedBounded (epoch0DistinguisherProgHalted C K Dh encPt encT decT idA idB lam ℓ q qep)
      Empty.elim (fun _ => 0) q 0 (ratchetCostBudget q (qep + 1)) :=
  epoch0DistinguisherProgHalted_gRedBounded_of_le C K Dh encPt encT decT idA idB lam ℓ q qep hqep (Nat.le_succ qep)

/-! ## Evaluation agreement with `epoch0DistinguisherTrackHalted` -/

private theorem flatSt2_run {S₁ S₂ : Type} {m : Type → Type} [Functor m] {α : Type}
    (c : StateT S₁ (StateT S₂ m) α) (s : S₁ × S₂) :
    (flatSt2 c).run s = (fun ⟨⟨a, s₁'⟩, s₂'⟩ => (a, (s₁', s₂'))) <$> ((c.run s.1).run s.2) := by
  rcases s with ⟨_, _⟩; rfl

theorem epoch0DistinguisherProgHalted_eval
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (rc : RootKey × BitVec 256) (hA : MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    (epoch0DistinguisherProgHalted C K Dh encPt encT decT idA idB lam ℓ q qep).eval (fun _ => A) rc =
      epoch0DistinguisherTrackHalted (paramsV1 C K idA idB) K ℓ
        (ratchetKeyAdmissible protoSignalCodec decT encT) qep A rc := by
  unfold epoch0DistinguisherProgHalted; simp only [hℓ, ↓reduceIte]
  set cfg := configEpoch0Distinguisher (ratchetKeyAdmissible protoSignalCodec decT encT)
  set sm := libsignalSessionSchemeFromEpoch0Keys (paramsV1 C K idA idB) ℓ rc.1 rc.2
  set smF := sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ 0
  have hSmEq : oracleImplRSessionTrackHalted C.F K sm 3 qep cfg =
      oracleImplRSessionTrackHalted C.F K smF 3 qep cfg := rfl
  let MRef := StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes) (StateT (KemFailSessionTrack C.F Bytes) ProbComp)
  let impl2 : QueryImpl (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) MRef :=
    (QueryImpl.ofLift unifSpec ProbComp).liftTarget MRef + oracleImplRSessionTrackHalted C.F K sm 3 qep cfg
  let so : QueryImpl (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes × KemFailSessionTrack C.F Bytes) ProbComp) :=
    fun qy => flatSt2 (impl2 qy)
  let Inv : ℕ → GameState (GhostState Bytes) (Plain ℓ) Bytes × KemFailSessionTrack C.F Bytes → Prop :=
    fun m s => m ≤ q ∧ SmReachBounded C K (q - m) s.1 ∧
      KemTrackDeliverInv C.F K (q - m) (kemTrackEnc s.2.1) ∧ s.2.2.length ≤ q - m
  have hsim := eval_eq_simulateQ_of_enc
    (epoch0DistinguisherProgHaltedReal C K Dh encPt encT decT idA idB lam ℓ q qep)
    (epoch0HaltedEnc (ℓ := ℓ) (Pt := Pt)) Inv (epoch0TrackInitImpl C K idA idB ℓ) so
    (fun s _ => pure ((decide (0 < s.1.maxAcc .A 0) || s.1.win) && !(s.1.corrs.contains (.B, 0))))
    q rc (initEpoch0GsTrackC_eval idA idB rc)
    (fun r hr => by simpa [Inv, Nat.sub_self] using epoch0TrackInitImpl_inv C K idA idB ℓ rc hr)
    (fun n ⟨s₁, s₂⟩ => by
      dsimp only [so]
      rw [show impl2 (.inl n) = (QueryImpl.ofLift unifSpec ProbComp).liftTarget MRef n from rfl, flatSt2_run]
      simp only [QueryImpl.liftTarget, map_eq_bind_pure_comp, Function.comp_def]; rfl)
    (fun m sq s hs => by
      have hInr : impl2 (.inr sq) = oracleImplRSessionTrackHalted C.F K sm 3 qep cfg sq := rfl
      refine ⟨?_, ?_⟩
      · change (do
            let p ← (epoch0OracleStepTrackC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
              (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q (2 + 1) qep
              (Γ := [epoch0HaltedStTy ℓ Pt, liftTy (Pt := Pt) smQT]) .v0 .v1).eval
              (.cons (epoch0HaltedEnc s) (.cons ((e2eSessionCodec ℓ Pt).qenc sq) .nil))
            pure ((e2eSessionCodec ℓ Pt).rdec sq p.1, p.2)) =
          Prod.map id (epoch0HaltedEnc (ℓ := ℓ) (Pt := Pt)) <$> (so (.inr sq)).run s
        have hstepEv := epoch0OracleStepTrackC_eval (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
          (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q (2 + 1) qep
          (Γ := [epoch0HaltedStTy ℓ Pt, liftTy (Pt := Pt) smQT]) .v0 .v1
          (.cons (epoch0HaltedEnc s) (.cons ((e2eSessionCodec ℓ Pt).qenc sq) .nil))
          idA idB 0 s.1 s.2 sq (hs.2.1.mono (by omega)) (hs.2.2.1.mono (by omega))
          (hs.2.2.2.trans (by omega)) rfl (liftVal_smQenc (Pt := Pt) sq).symm
        dsimp only [so]; rw [hInr, hSmEq, flatSt2_run, hstepEv]
        simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
        refine bind_congr fun ⟨⟨ans, s'⟩, ts'⟩ => congrArg pure ?_
        exact Prod.ext (e2eSessionCodec_rdec_liftVal_smRenc (Pt := Pt) sq ans) rfl
      · intro r hr
        dsimp only [so] at hr; rw [hInr, hSmEq, flatSt2_run] at hr
        simp only [map_eq_bind_pure_comp, Function.comp_def, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hr
        obtain ⟨w, hw, rfl⟩ := hr
        have hinv := oracleImplRSessionTrackHalted_inv idA idB 0 qep (q - (m + 1)) s.1 s.2 sq
          hs.2.1 hs.2.2.1 hs.2.2.2 w hw
        have heq : q - (m + 1) + 1 = q - m := by omega
        exact ⟨by omega, heq ▸ hinv.1, heq ▸ hinv.2.1, heq ▸ hinv.2.2⟩)
    (fun s b' hs => by
      dsimp only [epoch0DistinguisherProgHaltedReal, Comp.eval]
      have hsub : q - 0 = q := Nat.sub_zero q
      rw [eval_epoch0HaltedFinishE q s.1 s.2 b' (hsub ▸ hs.2.1).lists.corrs_le])
    (fun {m n} s hmn hn => ⟨by omega, hn.2.1.mono (by omega), hn.2.2.1.mono (by omega), by omega⟩)
    (fun _ => A) (fun _ => isQueryBoundP_of_makesAtMostQueries hA)
  rw [hsim]; unfold epoch0DistinguisherTrackHalted runRSessionTrackHalted epoch0TrackInitImpl
  simp only [bind_assoc, pure_bind]; refine bind_congr fun b => bind_congr fun k => ?_
  rw [simulateQ_run_flatSt2]
  change (do
      let x ← (simulateQ so A).run _
      pure ((decide (0 < x.2.1.maxAcc .A 0) || x.2.1.win) && !(x.2.1.corrs.contains (.B, 0)))) =
    (do
      let y ← (fun ⟨a, ⟨s₁', s₂'⟩⟩ => ((a, s₁'), s₂')) <$> (simulateQ so A).run _
      pure ((decide (0 < y.1.2.maxAcc .A 0) || y.1.2.win) && !(y.1.2.corrs.contains (.B, 0))))
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  exact bind_congr fun ⟨_, _, _⟩ => rfl

abbrev BridgeTrackState (F : ShaCompress) :=
  Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.KemFailTrackState F

@[expose] def refToBridgeTrack {F : ShaCompress} (t : KemFailTrackState F) : BridgeTrackState F :=
  ⟨t.e, t.auth, t.c, t.st, t.sentB, t.sendCtr, t.cand⟩

private theorem refToBridgeTrack_stepSend {F : ShaCompress} (tr : KemFailTrackState F) (P : Party) (r : BitVec 512) :
    refToBridgeTrack (stepKemFailSend F K tr P r) =
      Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.stepKemFailSend F K (refToBridgeTrack tr) P r := by
  have hp : CryptoGames.LibsignalSM.Proofs.Refinement.kemBraidParty P =
      Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.kemBraidParty P := by cases P <;> rfl
  rcases tr with ⟨e, auth, c, st, sentB, sendCtr, cand⟩
  unfold stepKemFailSend Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.stepKemFailSend
  rw [hp]; dsimp only [refToBridgeTrack]
  rcases CryptoVerification.LibsignalSpqrV1.States.send K (st P)
    (CryptoVerification.LibsignalSpqrV1.coinBytes r) with _ | ⟨out, _⟩ <;> rfl

private theorem refToBridgeTrack_stepDeliver {F : ShaCompress} (tr : KemFailTrackState F) (Q : Party) (j : ℕ) :
    refToBridgeTrack (stepKemFailDeliver F K tr Q j) =
      Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.stepKemFailDeliver F K (refToBridgeTrack tr) Q j := by
  rcases tr with ⟨e, auth, c, st, sentB, sendCtr, cand⟩
  unfold stepKemFailDeliver Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.stepKemFailDeliver
  dsimp only [refToBridgeTrack]
  cases h1 : sentB[j]? with
  | none => rfl
  | some mp =>
    rcases mp with ⟨m, _⟩; dsimp only
    cases h2 : CryptoVerification.LibsignalSpqrV1.States.recv K (st Q) m with
    | error _ => rfl
    | ok out =>
      dsimp only
      by_cases hm : m = CryptoVerification.SpqrV1Sync.Braid.noneMsg (e + 1#64)
      · cases c <;> simp [hm]
      · simp [hm]

theorem epoch0DistinguisherProgHalted_eval_bridge
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (rc : RootKey × BitVec 256) (hA : MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    (epoch0DistinguisherProgHalted C K Dh encPt encT decT idA idB lam ℓ q qep).eval (fun _ => A) rc =
      (do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let ((_, s), _) ←
          Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.runRTrackHalted
            Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.libsignalSessionPqrOf
            C.F K (libsignalSessionSchemeFromEpoch0Keys (paramsV1 C K idA idB) ℓ rc.1 rc.2) 3 qep
            (configEpoch0Distinguisher (ratchetKeyAdmissible protoSignalCodec decT encT)) b A
        return (decide (0 < s.maxAcc .A 0) || s.win) && !(s.corrs.contains (.B, 0))) := by
  rw [epoch0DistinguisherProgHalted_eval C K Dh encPt encT decT idA idB lam ℓ q qep A rc hA hℓ]
  unfold epoch0DistinguisherTrackHalted runRSessionTrackHalted
    Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.runRTrackHalted
  simp only [bind_assoc]; refine bind_congr fun b => bind_congr fun k => ?_
  set sm := libsignalSessionSchemeFromEpoch0Keys (paramsV1 C K idA idB) ℓ rc.1 rc.2
  set cfg := configEpoch0Distinguisher (ratchetKeyAdmissible protoSignalCodec decT encT)
  let MRef := StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes) (StateT (KemFailSessionTrack C.F Bytes) ProbComp)
  let MBr := StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (StateT (Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.KemFailSessionTrack C.F Bytes) ProbComp)
  have hsim : ∀ {α : Type}
      (oa : OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) α)
      (s : GameState (GhostState Bytes) (Plain ℓ) Bytes) (ts : KemFailSessionTrack C.F Bytes),
      (((simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget MBr +
          Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.oracleImplRTrackHalted
            C.F K sm 3 qep cfg) oa).run s).run (refToBridgeTrack ts.1, ts.2)) =
      Prod.map id (Prod.map refToBridgeTrack id) <$>
        (((simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget MRef +
            oracleImplRSessionTrackHalted C.F K sm 3 qep cfg) oa).run s).run ts) := by
    intro α oa; induction oa using OracleComp.inductionOn with
    | pure a => intro s ⟨tr, hw⟩; simp
    | query_bind qy cont ih =>
      intro s ts
      have h1 : (((((QueryImpl.ofLift unifSpec ProbComp).liftTarget MBr +
            Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.oracleImplRTrackHalted
              C.F K sm 3 qep cfg) qy).run s).run (refToBridgeTrack ts.1, ts.2)) =
          Prod.map id (Prod.map refToBridgeTrack id) <$>
            (((((QueryImpl.ofLift unifSpec ProbComp).liftTarget MRef +
                oracleImplRSessionTrackHalted C.F K sm 3 qep cfg) qy).run s).run ts) := by
        rcases qy with n | (((⟨P, m, r⟩ | ⟨P, m0, m1, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | P
        · change (((QueryImpl.ofLift unifSpec ProbComp).liftTarget MBr n).run s).run (refToBridgeTrack ts.1, ts.2) =
            Prod.map id (Prod.map refToBridgeTrack id) <$>
              (((QueryImpl.ofLift unifSpec ProbComp).liftTarget MRef n).run s).run ts
          rcases ts with ⟨tr, hw⟩
          simp only [QueryImpl.liftTarget, map_eq_bind_pure_comp, Function.comp_def]; rfl
        · change (((Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.transmitRTrackHalted
              C.F K sm 3 qep cfg (P, m, r)).run s).run (refToBridgeTrack ts.1, ts.2)) =
            Prod.map id (Prod.map refToBridgeTrack id) <$>
              (((transmitRSessionTrackHalted C.F K sm 3 qep cfg (P, m, r)).run s).run ts)
          unfold Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.transmitRTrackHalted transmitRSessionTrackHalted
          rcases ts with ⟨tr, hw⟩
          by_cases h1 : cfg.sendOK s P
          · by_cases h2 : s.win
            · simp [h1, h2]
            · simp only [h1, h2, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
                StateT.run_lift, StateT.run_monadLift, monadLift_self, map_bind, bind_assoc, pure_bind]
              refine bind_congr fun ⟨coins, bad⟩ => ?_
              cases s.epMgmt 3 qep P bad with
              | none => simp
              | some s1 =>
                simp only [StateT.run_bind, StateT.run_lift, StateT.run_get, bind_assoc, pure_bind,
                  ← refToBridgeTrack_stepSend (K := K) tr P coins]
                have hc : (refToBridgeTrack (stepKemFailSend C.F K tr P coins)).cand.isSome =
                    (stepKemFailSend C.F K tr P coins).cand.isSome := rfl
                rw [hc]; split_ifs <;> simp [refToBridgeTrack]
          · simp [h1]
        · change (((Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.challRTrackHalted
              C.F K sm 3 qep cfg (P, m0, m1, r)).run s).run (refToBridgeTrack ts.1, ts.2)) =
            Prod.map id (Prod.map refToBridgeTrack id) <$>
              (((challRSessionTrackHalted C.F K sm 3 qep cfg (P, m0, m1, r)).run s).run ts)
          unfold Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.challRTrackHalted challRSessionTrackHalted
          rcases ts with ⟨tr, hw⟩
          by_cases h1 : cfg.sendOK s P
          · by_cases h2 : s.win
            · simp [h1, h2]
            · simp only [h1, h2, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
                StateT.run_lift, StateT.run_monadLift, monadLift_self, map_bind, bind_assoc, pure_bind]
              refine bind_congr fun ⟨coins, bad⟩ => ?_
              cases s.epMgmt 3 qep P bad with
              | none => simp
              | some s1 =>
                by_cases h3 : !(s1.safeCh 3 P) || !(cfg.base.challAllowedIn (s1.epoch P)); · simp [h3]
                simp only [h3, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
                  StateT.run_get, bind_assoc, pure_bind, ← refToBridgeTrack_stepSend (K := K) tr P coins]
                have hc : (refToBridgeTrack (stepKemFailSend C.F K tr P coins)).cand.isSome =
                    (stepKemFailSend C.F K tr P coins).cand.isSome := rfl
                rw [hc]; split_ifs <;> simp [refToBridgeTrack]
          · simp [h1]
        · change (((Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.deliverRTrackHalted
              C.F K sm cfg (Q, w)).run s).run (refToBridgeTrack ts.1, ts.2)) =
            Prod.map id (Prod.map refToBridgeTrack id) <$>
              (((deliverRSessionTrackHalted C.F K sm cfg (Q, w)).run s).run ts)
          unfold Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.deliverRTrackHalted deliverRSessionTrackHalted
          rcases ts with ⟨tr, hw⟩
          simp only [StateT.run_bind, StateT.run_lift, StateT.run_get,
            liftStateT_run_state, map_bind, bind_assoc, pure_bind]
          refine bind_congr fun ⟨res, s'⟩ => ?_
          generalize (List.findIdx? _ hw.reverse) = j?
          rcases res with _ | (_ | ⟨_, _, _⟩)
          · simp
          · simp
          · rcases j? with _ | j
            · simp
            · simp [StateT.run_map, StateT.run_lift, StateT.run_modify,
                ← refToBridgeTrack_stepDeliver (K := K) tr Q j]
        · change (((liftStateT (injectR sm 3 qep cfg (Q, w)) : MBr _).run s).run (refToBridgeTrack ts.1, ts.2)) =
            Prod.map id (Prod.map refToBridgeTrack id) <$> (((liftStateT (injectR sm 3 qep cfg (Q, w)) : MRef _).run s).run ts)
          rcases ts with ⟨tr, hw⟩; simp only [liftStateT_run_state, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]; rfl
        · change (((liftStateT (corrR cfg P) : MBr _).run s).run (refToBridgeTrack ts.1, ts.2)) =
            Prod.map id (Prod.map refToBridgeTrack id) <$> (((liftStateT (corrR cfg P) : MRef _).run s).run ts)
          rcases ts with ⟨tr, hw⟩; simp only [liftStateT_run_state, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]; rfl
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        StateT.run_bind, h1, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      refine bind_congr fun ⟨⟨u, s'⟩, ts'⟩ => ?_
      dsimp only [Prod.map, id_eq]; rw [ih u s' ts']; simp only [Prod.map, id_eq, map_eq_bind_pure_comp, Function.comp_def]
  have hInit : (Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.initKemFailTrack
      C.F (Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.libsignalSessionPqrOf k),
      ([] : List (Bytes × Party))) =
    (refToBridgeTrack (initKemFailSessionTrack C.F Bytes (libsignalSessionPqrOf k)).1,
      (initKemFailSessionTrack C.F Bytes (libsignalSessionPqrOf k)).2) := rfl
  rw [hInit, hsim A]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  exact bind_congr fun ⟨⟨_, _⟩, _, _⟩ => rfl

end Reduction

end Computational.Proofs.Game.PromotedCostedReds.HaltedEpoch0Prog

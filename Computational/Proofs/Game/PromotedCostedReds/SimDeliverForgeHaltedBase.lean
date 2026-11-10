/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStep -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeBase
public import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanOracle -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.KemFailRedInit -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.KemFailRedSendCorrSub -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitness -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.KemFailBadHalted -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon -- proof-setup: allow-public-import

/-!
# Base DSL Definitions for Online-Halted `simDeliverForge`

Defines the raw state `dfHaltedT`, the hybrid simulation relation `DFHaltedStateRel`, the
tracker-halted costed reduction `simDeliverForgeRedProgHalted`, and its sanitized semantic oracle
`simDeliverForgeOracleSanTrackHalted`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedBase

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ops Iface Ty Expr Comp Var CostedReduction
  atomicSig atomicSessionOps fig8SmIfaceDF e2eSessionCodec
  UniformSamplerTag AtomicUnifBase SMTagDF
  GhostStT PlainT BV256 BV512 U32 B smQT smRT lpubT fig8CtT recvResultT)
open _root_.CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.SM (pGet noBobSendInEpoch0)
open CryptoGames.SM.Construction.DeliverForge
  (AdversaryDF AdversaryCompDF specDF transmitQueryDF challQueryDF)
open CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart)
open CryptoGames.Ratchet.LibsignalSim
  (Fig8St Fig8C kemTrackEnc mkPub toWire
   deliverForgeSemHook scPostSendPure semDrawSendCoins semSendHook)
open CryptoGames.Ratchet.LibsignalSimC (LibsignalToModularSchemeSimState initSimC)
open CryptoGames.LibsignalSession (Crypto ShaCompress IdentityKey PublicKey GhostState Params)
open Computational.Proofs.Game.PromotedCostedReds.SanOracleCore (semRecvHookS semCorrHookTGB)
open CryptoGames.LibsignalSM.Proofs.Refinement
  (KemFailTrackState initKemFailTrack stepKemFailSend stepKemFailDeliver)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (Bytes paramsV1)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge
  (sessSpqrKemOp atomicDraw256)
open Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon (dummyBoolSessionRed)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost (simMirT initSimCE)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8State
  (eLet mWin mEpoch mIdx mSafeChE mEpMgmtE mNoBobEpoch0E
   ssMir ssPq ssPn ssUnackA ssHonest ssStopped scBase)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8WireSnap
  (optBytesLitE mkPubAtomicC)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanOracle
  (dfFullT dfFullDec)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStepSendCorrCost
  (dfOrE dfIsSomeE dfNatNeE dfSmRNoneE dfIdxPredU32E dfPostSendStateE)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStepSendCorr
  (simDeliverForgeSendCorrSpec)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStepRecvFwd (dfRecvHookC)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedInit
  (kemTrackT kemTrackAtomicEnc initKemTrackAtomicE)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedSendCorrSub
  (boolEqE trE_e trE_c trE_st trE_cand ekSideIsAE isHeaderReceivedV1E
   encRandBvAtomicE stepPostKemSendE)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitnessSub
  (findRevHonestIdxE kemOnDeliverPostAtomicE)
open Computational.Proofs.Game.PromotedCostedReds.KemFailBadHalted (honestExchangeFailsPolyC)

noncomputable section

@[expose, reducible] def dfHaltedT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (dfFullT ℓ Pt) (kemTrackT ℓ Pt)

/-- Relates a raw `(dfHaltedT ℓ Pt).denote` state to `((sC, sent), tr)` by decoding the first
component with `dfFullDec` and encoding the second with `kemTrackAtomicEnc ∘ kemTrackEnc`. -/
@[expose] def DFHaltedStateRel {ℓ : ℕ} {Pt : Type} {F : ShaCompress}
    (s_abs : (LibsignalToModularSchemeSimState Bytes Pt ℓ × List (Fig8C Pt)) ×
      KemFailTrackState F)
    (s_raw : (dfHaltedT ℓ Pt).denote) : Prop :=
  dfFullDec s_raw.1 = s_abs.1 ∧
    s_raw.2 = kemTrackAtomicEnc (ℓ := ℓ) (Pt := Pt) (kemTrackEnc s_abs.2)

/-! ## Interface-polymorphic braid send step -/

section DslProgram

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {ℓ : ℕ} {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
local notation "DFIface" => fig8SmIfaceDF ℓ Pt

@[expose] def nextKemCandPolyC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)}
    (trE : Expr AOps Γ (kemTrackT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (rqE : Expr AOps Γ BV512) :
    Comp AOps I Γ (.opt (.prod BV512 BV256)) :=
  .bind (.ret (.pair trE (.pair qBE rqE)))
    (let tr0 : Expr AOps _ (kemTrackT ℓ Pt) := .fst .v0
     let q0 : Expr AOps _ .bool := .fst (.snd .v0)
     .caseOpt (trE_cand tr0)
       (let v1Q := pGet (trE_st tr0) q0
        let cond :=
          Expr.and
            (boolEqE
              (ekSideIsAE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
                (decT := decT) (lam := lam) (trE_e tr0))
              q0)
            (isHeaderReceivedV1E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
              (decT := decT) (lam := lam) v1Q)
        .ite cond
          (.caseSum (trE_c tr0)
            (.ret .none)
            (.caseSum .v0
              (let rq2 := Expr.snd (.snd .v2)
               let mBv := encRandBvAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                 (encT := encT) (decT := decT) (lam := lam) rq2
               .bind
                 (honestExchangeFailsPolyC (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                   (encT := encT) (decT := decT) (lam := lam) .v0 mBv)
                 (.ret
                   (.ite .v0
                     (.some
                       (.pair .v1
                         (encRandBvAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                           (encT := encT) (decT := decT) (lam := lam) (.snd (.snd .v3)))))
                     .none)))
              (.ret .none)))
          (.ret .none))
       (.ret (.some .v0)))

@[expose] def stepKemFailSendPolyC (q : ℕ) {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)}
    (trE : Expr AOps Γ (kemTrackT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (rqE : Expr AOps Γ BV512) :
    Comp AOps I Γ (.prod (kemTrackT ℓ Pt) (kemTrackT ℓ Pt)) :=
  .bind (.ret (.pair trE (.pair qBE rqE)))
    (.bind
      (nextKemCandPolyC (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) (.fst .v0) (.fst (.snd .v0)) (.snd (.snd .v0)))
      (.ret
        (stepPostKemSendE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) q (.fst .v1) (.fst (.snd .v1)) (.snd (.snd .v1)) .v0)))

/-! ## Tracker-halted costed reduction -/

@[expose] def dfDrawRqC {Γ : List (Ty ASig)}
    (rE : Expr AOps Γ (.opt (BV512 (ℓ := ℓ) (Pt := Pt)))) :
    Comp AOps DFIface Γ (BV512 (ℓ := ℓ) (Pt := Pt)) :=
  .caseOpt rE
    (.sample (I := DFIface) (UniformSamplerTag.base AtomicUnifBase.bv512) .unit)
    (.ret .v0)

@[expose] def dfDrawRcOptC {Γ : List (Ty ASig)}
    (rE : Expr AOps Γ (.opt (BV512 (ℓ := ℓ) (Pt := Pt)))) :
    Comp AOps DFIface Γ (.opt (BV256 (ℓ := ℓ) (Pt := Pt))) :=
  .caseOpt rE
    (.ret .none)
    (.bind (.sample (I := DFIface) (UniformSamplerTag.base AtomicUnifBase.bv256) .unit)
      (.ret (.some .v0)))

@[expose, reducible] def dfSendHaltedInpT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (dfHaltedT ℓ Pt)
    (.prod .bool
      (.prod (PlainT (ℓ := ℓ) (Pt := Pt))
        (.prod (.opt (PlainT (ℓ := ℓ) (Pt := Pt))) (.opt (BV512 (ℓ := ℓ) (Pt := Pt))))))

/-- Tracker-halted `.send` (`transmit` and `chall`) step computation over `dfHaltedT ℓ Pt`, latching
`cand` and returning `none` as soon as `tr'.cand.isSome`. -/
@[expose] def dfSendStepHaltedC (idA idB : IdentityKey) (qep q : ℕ) {Γ : List (Ty ASig)}
    (stHaltedE : Expr AOps Γ (dfHaltedT ℓ Pt))
    (qE : Expr AOps Γ .bool)
    (m0E : Expr AOps Γ (PlainT (ℓ := ℓ) (Pt := Pt)))
    (chalE : Expr AOps Γ (.opt (PlainT (ℓ := ℓ) (Pt := Pt))))
    (rE : Expr AOps Γ (.opt (BV512 (ℓ := ℓ) (Pt := Pt)))) :
    Comp AOps DFIface Γ
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) (GhostStT (ℓ := ℓ) (Pt := Pt)))
        (dfHaltedT ℓ Pt)) :=
  let inpT := dfSendHaltedInpT ℓ Pt
  let trPairT : Ty ASig := .prod (kemTrackT ℓ Pt) (kemTrackT ℓ Pt)
  let pubPairT : Ty ASig := .prod (B (ℓ := ℓ) (Pt := Pt) 32) (lpubT (ℓ := ℓ) (Pt := Pt))
  let Γ0 := inpT :: Γ
  let inp0 : Expr AOps Γ0 inpT := .v0
  let hst0 : Expr AOps Γ0 (dfHaltedT ℓ Pt) := .fst inp0
  let dfSt0 : Expr AOps Γ0 (dfFullT ℓ Pt) := .fst hst0
  let q0 : Expr AOps Γ0 .bool := .fst (.snd inp0)
  let r0 : Expr AOps Γ0 (.opt (BV512 (ℓ := ℓ) (Pt := Pt))) := .snd (.snd (.snd (.snd inp0)))
  let base0 := scBase (.fst dfSt0)
  let mir0 := ssMir base0
  let earlyGuard :=
    dfOrE (ssStopped base0) (dfOrE (mWin mir0) (.not (mNoBobEpoch0E mir0 q0)))
  let Γ1 := simMirT ℓ Pt :: Γ0
  let s1 : Expr AOps Γ1 (simMirT ℓ Pt) := .v0
  let inp1 : Expr AOps Γ1 inpT := .v1
  let hst1 : Expr AOps Γ1 (dfHaltedT ℓ Pt) := .fst inp1
  let q1 : Expr AOps Γ1 .bool := .fst (.snd inp1)
  let chal1 : Expr AOps Γ1 (.opt (PlainT (ℓ := ℓ) (Pt := Pt))) := .fst (.snd (.snd (.snd inp1)))
  let r1 : Expr AOps Γ1 (.opt (BV512 (ℓ := ℓ) (Pt := Pt))) := .snd (.snd (.snd (.snd inp1)))
  let Γ2 := BV512 (ℓ := ℓ) (Pt := Pt) :: Γ1
  let rq2 : Expr AOps Γ2 (BV512 (ℓ := ℓ) (Pt := Pt)) := .v0
  let inp2 : Expr AOps Γ2 inpT := .v2
  let tr2 : Expr AOps Γ2 (kemTrackT ℓ Pt) := .snd (.fst inp2)
  let q2 : Expr AOps Γ2 .bool := .fst (.snd inp2)
  let Γ3 := trPairT :: Γ2
  let trPair3 : Expr AOps Γ3 trPairT := .v0
  let inp3 : Expr AOps Γ3 inpT := .v3
  let dfSt3 : Expr AOps Γ3 (dfFullT ℓ Pt) := .fst (.fst inp3)
  let r3 : Expr AOps Γ3 (.opt (BV512 (ℓ := ℓ) (Pt := Pt))) := .snd (.snd (.snd (.snd inp3)))
  let Γ4 := Ty.opt (BV256 (ℓ := ℓ) (Pt := Pt)) :: Γ3
  let s1_4 : Expr AOps Γ4 (simMirT ℓ Pt) := .v3
  let inp4 : Expr AOps Γ4 inpT := .var (.succ (.succ (.succ (.succ .zero))))
  let dfSt4 : Expr AOps Γ4 (dfFullT ℓ Pt) := .fst (.fst inp4)
  let q4 : Expr AOps Γ4 .bool := .fst (.snd inp4)
  let base4 := scBase (.fst dfSt4)
  let mir4 := ssMir base4
  let pn4 : Expr AOps Γ4 (U32 (ℓ := ℓ) (Pt := Pt)) :=
    .ite (dfNatNeE (pGet (mEpoch s1_4) q4) (pGet (mEpoch mir4) q4))
      (dfIdxPredU32E (pGet (mIdx mir4) q4))
      (pGet (ssPn base4) q4)
  let Γ5 := U32 (ℓ := ℓ) (Pt := Pt) :: Γ4
  let pn5 : Expr AOps Γ5 (U32 (ℓ := ℓ) (Pt := Pt)) := .v0
  let rq5 : Expr AOps Γ5 (BV512 (ℓ := ℓ) (Pt := Pt)) := .v3
  let inp5 : Expr AOps Γ5 inpT := .var (.succ (.succ (.succ (.succ (.succ .zero)))))
  let dfSt5 : Expr AOps Γ5 (dfFullT ℓ Pt) := .fst (.fst inp5)
  let q5 : Expr AOps Γ5 .bool := .fst (.snd inp5)
  let base5 := scBase (.fst dfSt5)
  let addr5 :=
    Expr.ite (.and (.not q5) (ssUnackA base5))
      (optBytesLitE (paramsV1 C K idA idB).addrAB)
      .none
  let Γ6 := Ty.opt pubPairT :: Γ5
  let optPub6 : Expr AOps Γ6 (.opt pubPairT) := .v0
  let trPair6 : Expr AOps Γ6 trPairT := .v3
  let inp6 : Expr AOps Γ6 inpT :=
    .var (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))
  let Γ7 := pubPairT :: Γ6
  let pub7 : Expr AOps Γ7 (lpubT (ℓ := ℓ) (Pt := Pt)) := .snd .v0
  let rc7 : Expr AOps Γ7 (.opt (BV256 (ℓ := ℓ) (Pt := Pt))) := .v3
  let inp7 : Expr AOps Γ7 inpT :=
    .var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))
  let q7 : Expr AOps Γ7 .bool := .fst (.snd inp7)
  let m0_7 : Expr AOps Γ7 (PlainT (ℓ := ℓ) (Pt := Pt)) := .fst (.snd (.snd inp7))
  let chal7 : Expr AOps Γ7 (.opt (PlainT (ℓ := ℓ) (Pt := Pt))) := .fst (.snd (.snd (.snd inp7)))
  let Γ7c := PlainT (ℓ := ℓ) (Pt := Pt) :: Γ7
  let m1_7c : Expr AOps Γ7c (PlainT (ℓ := ℓ) (Pt := Pt)) := .v0
  let pub7c : Expr AOps Γ7c (lpubT (ℓ := ℓ) (Pt := Pt)) := .snd .v1
  let rc7c : Expr AOps Γ7c (.opt (BV256 (ℓ := ℓ) (Pt := Pt))) :=
    .var (.succ (.succ (.succ (.succ .zero))))
  let inp7c : Expr AOps Γ7c inpT :=
    .var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))
  let q7c : Expr AOps Γ7c .bool := .fst (.snd inp7c)
  let m0_7c : Expr AOps Γ7c (PlainT (ℓ := ℓ) (Pt := Pt)) := .fst (.snd (.snd inp7c))
  let Γ8 := Ty.opt (fig8CtT (ℓ := ℓ) (Pt := Pt)) :: Γ7
  let res8 : Expr AOps Γ8 (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))) := .v0
  let trPair8 : Expr AOps Γ8 trPairT :=
    .var (.succ (.succ (.succ (.succ (.succ .zero)))))
  let inp8 : Expr AOps Γ8 inpT :=
    .var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))
  let Γ9 := fig8CtT (ℓ := ℓ) (Pt := Pt) :: Γ8
  let c9 : Expr AOps Γ9 (fig8CtT (ℓ := ℓ) (Pt := Pt)) := .v0
  let pq'9 : Expr AOps Γ9 (B (ℓ := ℓ) (Pt := Pt) 32) := .fst .v2
  let pn9 : Expr AOps Γ9 (U32 (ℓ := ℓ) (Pt := Pt)) :=
    .var (.succ (.succ (.succ (.succ .zero))))
  let s1_9 : Expr AOps Γ9 (simMirT ℓ Pt) :=
    .var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))
  let inp9 : Expr AOps Γ9 inpT :=
    .var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))
  let post9 := dfPostSendStateE idA idB (.fst (.fst inp9)) s1_9
    (.fst (.snd inp9)) (.fst (.snd (.snd inp9)))
    (dfIsSomeE (.fst (.snd (.snd (.snd inp9))))) pq'9 pn9 c9
  let trFull10 : Expr AOps
      (Ty.prod (smRT (ℓ := ℓ) (Pt := Pt) (GhostStT (ℓ := ℓ) (Pt := Pt))) (dfFullT ℓ Pt) :: Γ9)
      (kemTrackT ℓ Pt) :=
    .fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))
  .bind (.ret (.pair stHaltedE (.pair qE (.pair m0E (.pair chalE rE)))))
    (.ite earlyGuard
      (.ret (.pair dfSmRNoneE hst0))
      (.caseOpt (mEpMgmtE qep mir0 q0 (dfIsSomeE r0))
        (.ret (.pair dfSmRNoneE hst0))
        (.ite (.and (dfIsSomeE chal1) (.not (mSafeChE s1 q1)))
          (.ret (.pair dfSmRNoneE hst1))
          (.bind (dfDrawRqC r1)
            (.bind (stepKemFailSendPolyC q (I := DFIface) tr2 q2 rq2)
              (.ite (dfIsSomeE (trE_cand (.fst trPair3)))
                (.ret (.pair dfSmRNoneE (.pair dfSt3 (.snd trPair3))))
                (.bind (dfDrawRcOptC r3)
                  (.bind (.ret pn4)
                    (.bind
                      (mkPubAtomicC DFIface
                        (.pair (pGet (ssPq base5) q5) (.pair rq5 (.pair pn5 addr5))))
                      (.caseOpt optPub6
                        (.ret (.pair dfSmRNoneE (.pair (.fst (.fst inp6)) (.snd trPair6))))
                        (.bind
                          (.caseOpt chal7
                            (.query (I := DFIface) (g := SMTagDF.tr)
                              (.pair q7 (.pair (.pair pub7 m0_7) rc7)))
                            (.query (I := DFIface) (g := SMTagDF.ch)
                              (.pair q7c
                                (.pair (.pair pub7c m0_7c) (.pair (.pair pub7c m1_7c) rc7c)))))
                          (.caseOpt res8
                            (.ret (.pair dfSmRNoneE (.pair (.fst (.fst inp8)) (.snd trPair8))))
                            (.ret (eLet post9
                              (.pair (.fst .v0) (.pair (.snd .v0) trFull10))))))))))))))))

@[expose, reducible] def wkTop1CompH {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ : List (Ty S)} {a t : Ty S} (c : Comp O I [a] t) : Comp O I (a :: Γ) t :=
  Comp.renameM
    (fun ⦃_⦄ v => match v with
      | .zero => .zero
      | .succ w => nomatch w) c

@[expose] def smRRecvPackEH {O' : Ops ASig} {Γ : List (Ty ASig)}
    (rrE : Expr O' Γ (.opt (recvResultT (ℓ := ℓ) (Pt := Pt)))) :
    Expr O' Γ (smRT (ℓ := ℓ) (Pt := Pt) (GhostStT (ℓ := ℓ) (Pt := Pt))) :=
  .pair .none (.pair rrE .none)

abbrev dfSendArgTH (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod .bool (.prod (PlainT (ℓ := ℓ) (Pt := Pt))
    (.prod (.opt (PlainT (ℓ := ℓ) (Pt := Pt))) (.opt (BV512 (ℓ := ℓ) (Pt := Pt)))))

abbrev dfRecvArgTH (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod .bool (.prod (B (ℓ := ℓ) (Pt := Pt) 32) .bool)

abbrev dfClassTH (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .sum (dfSendArgTH ℓ Pt) (.sum (dfRecvArgTH ℓ Pt) .bool)

@[expose] def classifySmQEH {O' : Ops ASig} {Γ : List (Ty ASig)}
    (qE : Expr O' Γ (smQT (ℓ := ℓ) (Pt := Pt))) :
    Expr O' Γ (dfClassTH ℓ Pt) :=
  .caseSum qE
    (.inl (.pair (.fst (.var .zero))
      (.pair (.fst (.snd (.var .zero)))
        (.pair .none (.snd (.snd (.var .zero)))))))
    (.caseSum (.var .zero)
      (.inl (.pair (.fst (.var .zero))
        (.pair (.fst (.snd (.var .zero)))
          (.pair (.some (.fst (.snd (.snd (.var .zero)))))
            (.snd (.snd (.snd (.var .zero))))))))
      (.caseSum (.var .zero)
        (.inr (.inl (.pair (.fst (.var .zero)) (.pair (.snd (.var .zero)) (.bool true)))))
        (.caseSum (.var .zero)
          (.inr (.inl (.pair (.fst (.var .zero)) (.pair (.snd (.var .zero)) (.bool false)))))
          (.inr (.inr (.var .zero))))))

@[expose] def dfStepHaltedC (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIfaceDF ℓ Pt)
      [dfHaltedT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) (GhostStT (ℓ := ℓ) (Pt := Pt))) (dfHaltedT ℓ Pt)) :=
  let sc := simDeliverForgeSendCorrSpec ℓ C K idA idB Dh encPt encT decT lam qep q
  .caseSum (classifySmQEH (.var (.succ .zero)))
    (dfSendStepHaltedC idA idB qep q (.var (.succ .zero))
      (.fst (.var .zero))
      (.fst (.snd (.var .zero)))
      (.fst (.snd (.snd (.var .zero))))
      (.snd (.snd (.snd (.var .zero)))))
    (.caseSum (.var .zero)
      (.bind
        (.ret
          (findRevHonestIdxE q
            (ssHonest (scBase (.fst (.fst (.var (.succ (.succ .zero)))))))
            (.fst (.var .zero))
            (.fst (.snd (.var .zero)))))
        (.bind
          (.bind (.ret (.pair (.fst (.var (.succ (.succ (.succ .zero))))) (.var (.succ .zero))))
            (wkTop1CompH (dfRecvHookC C K idA idB Dh encPt encT decT lam qep q)))
          (.ret
            (.pair (smRRecvPackEH (.fst (.var .zero)))
              (.pair (.snd (.var .zero))
                (.ite (.snd (.snd (.var (.succ (.succ .zero)))))
                  (kemOnDeliverPostAtomicE q
                    (.fst (.var (.succ (.succ .zero))))
                    (.var (.succ .zero))
                    (.fst (.var .zero))
                    (.snd (.var (.succ (.succ (.succ (.succ .zero)))))))
                  (.snd (.var (.succ (.succ (.succ (.succ .zero))))))))))))
      (.bind (sc.corrC (.fst (.var (.succ (.succ .zero)))) (.var .zero))
        (.ret (.pair (.fst (.var .zero))
          (.pair (.snd (.var .zero))
            (.snd (.var (.succ (.succ (.succ .zero))))))))))

@[expose] def simDeliverForgeInitHaltedC (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) :
    Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIfaceDF ℓ Pt)
      [.unit] (.prod .unit (dfHaltedT ℓ Pt)) :=
  .bind (atomicDraw256 (I := fig8SmIfaceDF ℓ Pt) rfl)
    (.ret (.pair .unit
      (.pair
        (.pair
          (initSimCE
            (sessSpqrKemOp .spqrV1InitOp (.pair (.bool true) (.var .zero)))
            (sessSpqrKemOp .spqrV1InitOp (.pair (.bool false) (.var .zero))))
          .nil)
        (initKemTrackAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam) (.var .zero)))))

@[expose] def simDeliverForgeFinishHaltedC (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) :
    Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIfaceDF ℓ Pt)
      [dfHaltedT ℓ Pt, .bool] .bool :=
  .ret (.var (.succ .zero))

end DslProgram

/-- Online tracker-halted `simDeliverForge` `CostedReduction` over `atomicSessionOps` and
`fig8SmIfaceDF`, falling back to `dummyBoolSessionRed` when `¬ (ℓ < 10 ^ 6)`. -/
@[expose] def simDeliverForgeRedProgHalted {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) :
    CostedReduction
      (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (fig8SmIfaceDF ℓ Pt)
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (e2eSessionCodec ℓ Pt) .unit .unit .bool .bool :=
  if _hℓ : ℓ < 10 ^ 6 then
    { σ := dfHaltedT ℓ Pt
      init := simDeliverForgeInitHaltedC C K Dh encPt encT decT lam
      handle := dfStepHaltedC ℓ C K idA idB Dh encPt encT decT lam qep q
      finish := simDeliverForgeFinishHaltedC C K Dh encPt encT decT lam }
  else
    dummyBoolSessionRed (fig8SmIfaceDF ℓ Pt) .unit

/-! ## Sanitized tracker-halted semantic oracle -/

@[expose] def semSendTrackHalted {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt))
    (tr : KemFailTrackState P.C.F) (Q : Party) (m₀ : Plain ℓ)
    (chal : Option (Plain ℓ)) (r : Option (BitVec 512)) :
    AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)
      (Option Bytes ×
        ((LibsignalToModularSchemeSimState PQ Pt ℓ × List (Fig8C Pt)) ×
          KemFailTrackState P.C.F)) :=
  if sC.base.stopped || sC.base.mir.win || !(noBobSendInEpoch0 sC.base.mir Q) then
    pure (none, ((sC, ex), tr))
  else
    match sC.base.mir.epMgmt 3 qep Q r.isSome with
    | none => pure (none, ((sC, ex), tr))
    | some s₁ =>
      if chal.isSome && !(s₁.safeCh 3 Q) then
        pure (none, ((sC, ex), tr))
      else do
        let rq ← (match r with
          | some rq => pure rq
          | none => liftM ($ᵗ (BitVec 512) : ProbComp (BitVec 512)))
        let tr' := stepKemFailSend P.C.F K tr Q rq
        if tr'.cand.isSome then
          pure (none, ((sC, ex), { tr with cand := tr'.cand }))
        else do
          let rc ← (match r with
            | some _ => some <$> (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)))
            | none => pure none)
          let pn := if s₁.epoch Q ≠ sC.base.mir.epoch Q then
            BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q
          match mkPub (P := P) sC.base Q rq pn with
          | none => pure (none, ((sC, ex), { tr with cand := tr'.cand }))
          | some (pq', pub) => do
            let res ← (match chal with
              | none => transmitQueryDF (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
                  (Coins := BitVec 256) (C := Fig8C Pt) Q (pub, m₀) rc
              | some m₁ => challQueryDF (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
                  (Coins := BitVec 256) (C := Fig8C Pt) Q (pub, m₀) (pub, m₁) rc)
            match res with
            | none => pure (none, ((sC, ex), { tr with cand := tr'.cand }))
            | some c =>
              pure (some (toWire c),
                ((scPostSendPure P Dh encPt encT lam sC s₁ Q m₀ chal.isSome pq' pn c, c :: ex),
                 tr'))

/-- Sanitized tracker-halted `DeliverForge` semantic query implementation. -/
@[expose] def simDeliverForgeOracleSanTrackHalted {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B T Kc Bsk : ℕ) :
    QueryImpl (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes)
      (StateT
        ((LibsignalToModularSchemeSimState PQ Pt ℓ × List (Fig8C Pt)) × KemFailTrackState P.C.F)
        (AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)))
  | .inl n => StateT.lift
    (query (spec := unifSpec + specDF (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) (.inl n))
  | .inr (.inl (.inl (.inl (.inl (Q, m, r))))) => StateT.mk fun ⟨⟨sC, ex⟩, tr⟩ =>
    semSendTrackHalted P K Dh encPt encT lam qep sC ex tr Q m none r
  | .inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))) => StateT.mk fun ⟨⟨sC, ex⟩, tr⟩ =>
    semSendTrackHalted P K Dh encPt encT lam qep sC ex tr Q m₀ (some m₁) r
  | .inr (.inl (.inl (.inr (Q, w)))) => StateT.mk fun ⟨⟨sC, ex⟩, tr⟩ => do
    let j? := sC.base.honest.reverse.findIdx? (fun wc =>
      wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
    let (res, s') ← semRecvHookS P Dh encPt encT decT lam T Kc
      (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ)) qep B sC ex Q w true
    let tr' := match res, j? with
      | some (.accepted _ _ _), some j => stepKemFailDeliver P.C.F K tr Q j
      | _, _ => tr
    return (res, (s', tr'))
  | .inr (.inl (.inr (Q, w))) => StateT.mk fun ⟨⟨sC, ex⟩, tr⟩ => do
    let (res, s') ← semRecvHookS P Dh encPt encT decT lam T Kc
      (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ)) qep B sC ex Q w false
    return (res, (s', tr))
  | .inr (.inr Q) => StateT.mk fun ⟨⟨sC, ex⟩, tr⟩ => do
    let (res, s') ← semCorrHookTGB P Dh encT
      (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ)) Bsk sC ex Q
    return (res, (s', tr))

abbrev simDeliverForgeOracleSanQTrackHalted {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) :=
  simDeliverForgeOracleSanTrackHalted (ℓ := ℓ) P K Dh encPt encT decT lam
    qep (2 ^ 32) (50000 * q) (25001 * q + 25000) (25000 * q)

/-- Sanitized counterpart of `simDeliverForgeTrackHalted`, running
`simDeliverForgeOracleSanTrackHalted` from `((initSimC ..., []), initKemFailTrack P.C.F pqrKey)`. -/
@[expose] def simDeliverForgeClampSanTrackHalted {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B T Kc Bsk : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes) :
    AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt) :=
  show AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt) Bool
  from do
    let pqrKey ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
      AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)
        (BitVec 256))
    let sC₀ := initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
    let tr₀ := initKemFailTrack P.C.F pqrKey
    (simulateQ (simDeliverForgeOracleSanTrackHalted P K Dh encPt encT decT lam qep B T Kc Bsk) A).run'
      ((sC₀, []), tr₀)

abbrev simDeliverForgeClampSanQTrackHalted {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes) :=
  simDeliverForgeClampSanTrackHalted P K ℓ Dh encPt encT decT lam
    qep (2 ^ 32) (50000 * q) (25001 * q + 25000) (25000 * q) A

private theorem mem_support_semDrawSendCoins_none {PQC Pt : Type} [DecidableEq Pt]
    [SampleableType PQC] {ℓ : ℕ} (rq : PQC) :
    (rq, (none : Option (BitVec 256))) ∈
      support (semDrawSendCoins (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)) none) := by
  have hmem_unif : rq ∈ support ($ᵗ PQC : ProbComp PQC) := by
    rw [OracleComp.mem_support_iff_prEvent_ne_zero]
    intro h0
    exact (SampleableType.prEvent_uniformSample_eq_zero_iff (fun y => y = rq)).mp h0 rq rfl
  have hsupp_lift : ∀ (mx : ProbComp PQC),
      rq ∈ support mx →
      rq ∈ support (liftM mx :
        OracleComp (unifSpec + CryptoGames.SM.specDF (CryptoGames.Ratchet.LibsignalSim.SimFig8St Pt)
          (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
          (CryptoGames.Ratchet.LibsignalSim.SimFig8C Pt)) PQC) := by
    intro mx hmx
    change rq ∈ support (liftComp mx _)
    induction mx using OracleComp.inductionOn with
    | pure a =>
      simp only [support_pure, Set.mem_singleton_iff] at hmx
      subst hmx
      simp only [liftComp_pure, support_pure, Set.mem_singleton_iff]
    | query_bind t k ih =>
      rw [mem_support_bind_iff] at hmx
      obtain ⟨u, _, hk⟩ := hmx
      simp only [liftComp_bind, liftComp_query, OracleQuery.cont_query, id_map,
        OracleQuery.input_query, mem_support_bind_iff]
      exact ⟨u, OracleComp.mem_support_query _ u, ih u hk⟩
  dsimp only [semDrawSendCoins, deliverForgeSemHook]
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
  exact ⟨rq, hsupp_lift ($ᵗ PQC) hmem_unif, rfl⟩

private theorem mem_support_semSendHook_deliverForge {PQ PQC Pt : Type} [DecidableEq Pt]
    [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt))
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC)
    (s₁ : CryptoGames.SM.GameState Unit (Plain ℓ) Bytes)
    (rq : PQC) (rc : Option (BitVec 256)) (pq' : PQ) (pub : LibsignalMsgPublicPart)
    (c : Fig8C Pt)
    (h1 : ¬(sC.base.stopped || sC.base.mir.win || !(noBobSendInEpoch0 sC.base.mir Q)) = true)
    (hep : sC.base.mir.epMgmt 3 qep Q r.isSome = some s₁)
    (h2 : ¬(chal.isSome && !(s₁.safeCh 3 Q)) = true)
    (hrc_none : r = none → rc = none)
    (hrc_some : ∀ rq₀, r = some rq₀ → rq = rq₀ ∧
      rc ∈ support (some <$> (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
        AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)
          (BitVec 256))))
    (hpub : mkPub (P := P) sC.base Q rq
      (if s₁.epoch Q ≠ sC.base.mir.epoch Q then
        BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q) = some (pq', pub))
    (hres : some c ∈ support (match chal with
      | none => transmitQueryDF (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
          (Coins := BitVec 256) (C := Fig8C Pt) Q (pub, m₀) rc
      | some m₁ => challQueryDF (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
          (Coins := BitVec 256) (C := Fig8C Pt) Q (pub, m₀) (pub, m₁) rc)) :
    (some (toWire c),
      (scPostSendPure P Dh encPt encT lam sC s₁ Q m₀ chal.isSome pq'
        (if s₁.epoch Q ≠ sC.base.mir.epoch Q then
          BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q) c, c :: ex)) ∈
      support (semSendHook P Dh encPt encT lam
        (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)) qep sC ex Q m₀ chal r) := by
  have hdraw : (rq, rc) ∈ support (semDrawSendCoins
      (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)) r) := by
    cases r with
    | none =>
      have hrc0 := hrc_none rfl
      subst hrc0
      exact mem_support_semDrawSendCoins_none (PQC := PQC) (Pt := Pt) (ℓ := ℓ) rq
    | some rq₀ =>
      obtain ⟨hrq, hrc⟩ := hrc_some rq₀ rfl
      subst hrq
      rw [map_eq_bind_pure_comp] at hrc
      simp only [Function.comp_def, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hrc
      obtain ⟨rc₀, hrc₀, rfl⟩ := hrc
      dsimp only [semDrawSendCoins, deliverForgeSemHook]
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
      exact ⟨rc₀, hrc₀, rfl⟩
  dsimp only [semSendHook]
  simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, hep, mem_support_bind_iff]
  refine ⟨(rq, rc), hdraw, ?_⟩
  dsimp only [deliverForgeSemHook]
  refine ⟨(ex, ex), by simp only [support_pure, Set.mem_singleton_iff], ?_⟩
  simp only [hpub, mem_support_bind_iff]
  refine ⟨(some c, c :: ex), ?_, ?_⟩
  · cases chal with
    | none =>
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
      exact ⟨some c, hres, rfl⟩
    | some m₁ =>
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
      exact ⟨some c, hres, rfl⟩
  · simp only [support_pure, Set.mem_singleton_iff]

theorem semSendTrackHalted_support {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt))
    (tr : KemFailTrackState P.C.F) (Q : Party) (m₀ : Plain ℓ)
    (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    {rr : Option Bytes} {sC' : LibsignalToModularSchemeSimState PQ Pt ℓ}
    {ex' : List (Fig8C Pt)} {tr_out : KemFailTrackState P.C.F}
    (hmem : (rr, ((sC', ex'), tr_out)) ∈
      support (semSendTrackHalted P K Dh encPt encT lam qep sC ex tr Q m₀ chal r)) :
    (rr = none ∧ sC' = sC ∧ ex' = ex ∧
      (tr_out = tr ∨ ∃ rq, tr_out = { tr with cand := (stepKemFailSend P.C.F K tr Q rq).cand })) ∨
    (∃ rq, (rr, (sC', ex')) ∈ support (semSendHook P Dh encPt encT lam
        (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ)) qep sC ex Q m₀ chal r) ∧
      tr_out = stepKemFailSend P.C.F K tr Q rq) := by
  dsimp only [semSendTrackHalted] at hmem
  by_cases h1 : (sC.base.stopped || sC.base.mir.win || !(noBobSendInEpoch0 sC.base.mir Q)) = true
  · simp only [h1, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hmem
    injection hmem with hrr hp
    injection hp with hs htr
    injection hs with hsC hex
    exact Or.inl ⟨hrr, hsC, hex, Or.inl htr⟩
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hmem
    rcases hep : sC.base.mir.epMgmt 3 qep Q r.isSome with _ | s₁
    · simp only [hep, support_pure, Set.mem_singleton_iff] at hmem
      injection hmem with hrr hp
      injection hp with hs htr
      injection hs with hsC hex
      exact Or.inl ⟨hrr, hsC, hex, Or.inl htr⟩
    · simp only [hep] at hmem
      by_cases h2 : (chal.isSome && !(s₁.safeCh 3 Q)) = true
      · simp only [h2, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hmem
        injection hmem with hrr hp
        injection hp with hs htr
        injection hs with hsC hex
        exact Or.inl ⟨hrr, hsC, hex, Or.inl htr⟩
      · simp only [h2, Bool.false_eq_true, ↓reduceIte, mem_support_bind_iff] at hmem
        obtain ⟨rq, hrq, hmem⟩ := hmem
        by_cases hcand : (stepKemFailSend P.C.F K tr Q rq).cand.isSome = true
        · simp only [hcand, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hmem
          injection hmem with hrr hp
          injection hp with hs htr
          injection hs with hsC hex
          exact Or.inl ⟨hrr, hsC, hex, Or.inr ⟨rq, htr⟩⟩
        · simp only [hcand, Bool.false_eq_true, ↓reduceIte, mem_support_bind_iff] at hmem
          obtain ⟨rc, hrc, hmem⟩ := hmem
          set pn := if s₁.epoch Q ≠ sC.base.mir.epoch Q then
            BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q
          rcases hpub : mkPub (P := P) sC.base Q rq pn with _ | ⟨pq', pub⟩
          · simp only [hpub, support_pure, Set.mem_singleton_iff] at hmem
            injection hmem with hrr hp
            injection hp with hs htr
            injection hs with hsC hex
            exact Or.inl ⟨hrr, hsC, hex, Or.inr ⟨rq, htr⟩⟩
          · simp only [hpub, mem_support_bind_iff] at hmem
            obtain ⟨res, hres, hmem⟩ := hmem
            rcases res with _ | c
            · simp only [support_pure, Set.mem_singleton_iff] at hmem
              injection hmem with hrr hp
              injection hp with hs htr
              injection hs with hsC hex
              exact Or.inl ⟨hrr, hsC, hex, Or.inr ⟨rq, htr⟩⟩
            · simp only [support_pure, Set.mem_singleton_iff] at hmem
              injection hmem with hrr hp
              injection hp with hs htr
              injection hs with hsC hex
              subst hrr; subst hsC; subst hex
              refine Or.inr ⟨rq, ?_, htr⟩
              exact mem_support_semSendHook_deliverForge P Dh encPt encT lam qep sC ex Q m₀
                chal r s₁ rq rc pq' pub c h1 hep h2
                (by rintro rfl; simp only [support_pure, Set.mem_singleton_iff] at hrc; exact hrc)
                (by rintro rq₀ rfl; simp only [support_pure, Set.mem_singleton_iff] at hrq
                    exact ⟨hrq, hrc⟩)
                hpub hres

end

end Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedBase

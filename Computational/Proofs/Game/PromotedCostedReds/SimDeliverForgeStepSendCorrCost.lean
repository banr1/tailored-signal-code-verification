/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SanOracleCore
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8WireSnap
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8SanCoupling
public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEClamp2
import Computational.Proofs.Game.PromotedCostedReds.SimFig8Crypto

/-!
# Send and Corrupt Step Programs and Cost Bounds for `SimDeliverForge`

Defines the atomic `.send` (`dfSendStepC`) and `.corrupt` (`dfCorrStepC`) step computations for
`SimDeliverForge` over `fig8SmIfaceDF`, together with query, step-cost, and description-bit bounds.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStepSendCorrCost

open _root_.ReductionDsl (Ty Expr Comp Ops atomicSig atomicSessionOps fig8SmIfaceDF
  UniformSamplerTag AtomicUnifBase SMTagDF
  GhostStT PlainT BV256 BV512 U32 B smRT fig8CtT fig8CtOfV fig8StT lpubT ckaStT fsSendStT)
open CryptoGames.Ratchet.LibsignalSim (Fig8C)
open CryptoGames.Ratchet.LibsignalSimC (LibsignalToModularSchemeSimState)
open CryptoGames.CKA (DHFun)
open CryptoGames.SM (pGet pSet sendsInE)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalSession (ratchetCostBudget)
open CryptoVerification.E2E (Bytes paramsV1)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost
  (simFullT simFullDec simMirT simBaseT keptT sentEntryT snapT)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8State
  (sOpPure sOpPtEnc sOpGrp eLet mWin mEpoch mIdx mSafeChE mEpMgmtE mRecordE
   mCorrAllowedFastE mAfterCorrFastE mInWinE mNoBobEpoch0E mNoSpkCorrE
   revealSpkChainsE toGhostE
   ssMir ssPq ssPn ssUnackA ssHonest ssChains ssAmb ssStopped ssMk
   scBase scKept scSent scSnaps scMk)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8WireSnap
  (optBytesLitE mkPubAtomicC mkPubAtomicC_queries toWireAtomicE)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept
  (f8Id f8VS f8Gamma f8Tcur keptOfStAtomicE keptSendAtomicE)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost
  (atomicSessionOpDescBits atomicExprDescBits atomicCompDescBits)

noncomputable section

/-- Combined `(sC, sent)` state type in `atomicSig ℓ Pt` for `SimDeliverForge`. -/
@[reducible] def dfSendCorrStateT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (simFullT ℓ Pt) (.list (fig8CtT (ℓ := ℓ) (Pt := Pt)))

@[reducible] def dfSendCorrStateDec {ℓ : ℕ} {Pt : Type} (v : (dfSendCorrStateT ℓ Pt).denote) :
    LibsignalToModularSchemeSimState Bytes Pt ℓ × List (Fig8C Pt) :=
  (simFullDec v.1, v.2.map fig8CtOfV)

section Helpers

variable {ℓ : ℕ} {Pt : Type}

local notation "ASig" => atomicSig ℓ Pt

def dfOrE {O' : Ops ASig} {Γ : List (Ty ASig)} (a b : Expr O' Γ .bool) : Expr O' Γ .bool :=
  .ite a (.bool true) b

def dfIsSomeE {O' : Ops ASig} {Γ : List (Ty ASig)} {a : Ty ASig}
    (e : Expr O' Γ (.opt a)) : Expr O' Γ .bool :=
  .caseOpt e (.bool false) (.bool true)

def dfNatNeE {O' : Ops ASig} {Γ : List (Ty ASig)} (a b : Expr O' Γ .nat) : Expr O' Γ .bool :=
  eLet (.pair a b) (dfOrE (.lt (.fst .v0) (.snd .v0)) (.lt (.snd .v0) (.fst .v0)))

def dfSmRNoneE {O' : Ops ASig} {Γ : List (Ty ASig)} :
    Expr O' Γ (smRT (ℓ := ℓ) (Pt := Pt) (GhostStT (ℓ := ℓ) (Pt := Pt))) :=
  .pair .none (.pair .none .none)

def dfSmRSendSomeE {O' : Ops ASig} {Γ : List (Ty ASig)}
    (wE : Expr O' Γ (B (ℓ := ℓ) (Pt := Pt) 32)) :
    Expr O' Γ (smRT (ℓ := ℓ) (Pt := Pt) (GhostStT (ℓ := ℓ) (Pt := Pt))) :=
  .pair (.some wE) (.pair .none .none)

def dfSmRCorrSomeE {O' : Ops ASig} {Γ : List (Ty ASig)}
    (ghE : Expr O' Γ (GhostStT (ℓ := ℓ) (Pt := Pt))) :
    Expr O' Γ (smRT (ℓ := ℓ) (Pt := Pt) (GhostStT (ℓ := ℓ) (Pt := Pt))) :=
  .pair .none (.pair .none (.some ghE))

end Helpers

section StepComps

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {ℓ : ℕ} {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
local notation "DFIface" => fig8SmIfaceDF ℓ Pt

def dfIdxPredU32E {Γ : List (Ty ASig)} (idxE : Expr AOps Γ .nat) :
    Expr AOps Γ (U32 (ℓ := ℓ) (Pt := Pt)) :=
  eLet idxE
    (.ite (.lt .v0 (.nat 1))
      (sOpPure (.u32Lit 0#32) .unit)
      (sOpPure .u32Sub
        (.pair (sOpPure .u32OfNat .v0) (sOpPure (.u32Lit 1#32) .unit))))

def dfDrawSendCoinsC {Γ : List (Ty ASig)}
    (rE : Expr AOps Γ (.opt (BV512 (ℓ := ℓ) (Pt := Pt)))) :
    Comp AOps DFIface Γ
      (.prod (BV512 (ℓ := ℓ) (Pt := Pt)) (.opt (BV256 (ℓ := ℓ) (Pt := Pt)))) :=
  .caseOpt rE
    (.bind (.sample (I := DFIface) (UniformSamplerTag.base AtomicUnifBase.bv512) .unit)
      (.ret (.pair .v0 .none)))
    (.bind (.sample (I := DFIface) (UniformSamplerTag.base AtomicUnifBase.bv256) .unit)
      (.ret (.pair .v1 (.some .v0))))

@[reducible] def dfPostSendArgT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (dfSendCorrStateT ℓ Pt)
    (.prod (simMirT ℓ Pt)
      (.prod .bool
        (.prod (PlainT (ℓ := ℓ) (Pt := Pt))
          (.prod .bool
            (.prod (B (ℓ := ℓ) (Pt := Pt) 32)
              (.prod (U32 (ℓ := ℓ) (Pt := Pt)) (fig8CtT (ℓ := ℓ) (Pt := Pt))))))))

def dfPostSendStateE (idA idB : IdentityKey) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (dfSendCorrStateT ℓ Pt))
    (s1E : Expr AOps Γ (simMirT ℓ Pt))
    (qE : Expr AOps Γ .bool)
    (m0E : Expr AOps Γ (PlainT (ℓ := ℓ) (Pt := Pt)))
    (isChallE : Expr AOps Γ .bool)
    (pq'E : Expr AOps Γ (B (ℓ := ℓ) (Pt := Pt) 32))
    (pnE : Expr AOps Γ (U32 (ℓ := ℓ) (Pt := Pt)))
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    Expr AOps Γ
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) (GhostStT (ℓ := ℓ) (Pt := Pt)))
        (dfSendCorrStateT ℓ Pt)) :=
  let argT := dfPostSendArgT ℓ Pt
  let Γ1 := argT :: Γ
  let arg0 : Expr AOps Γ1 argT := .v0
  let c0 : Expr AOps Γ1 (fig8CtT (ℓ := ℓ) (Pt := Pt)) :=
    .snd (.snd (.snd (.snd (.snd (.snd (.snd arg0))))))
  let Γ2 := B (ℓ := ℓ) (Pt := Pt) 32 :: Γ1
  let w0 : Expr AOps Γ2 (B (ℓ := ℓ) (Pt := Pt) 32) := .v0
  let st1 : Expr AOps Γ2 argT := .v1
  let sC1 : Expr AOps Γ2 (simFullT ℓ Pt) := .fst (.fst st1)
  let ex1 : Expr AOps Γ2 (.list (fig8CtT (ℓ := ℓ) (Pt := Pt))) := .snd (.fst st1)
  let base1 : Expr AOps Γ2 (simBaseT ℓ Pt) := scBase sC1
  let s1' : Expr AOps Γ2 (simMirT ℓ Pt) := .fst (.snd st1)
  let q1 : Expr AOps Γ2 .bool := .fst (.snd (.snd st1))
  let m1 : Expr AOps Γ2 (PlainT (ℓ := ℓ) (Pt := Pt)) := .fst (.snd (.snd (.snd st1)))
  let isCh1 : Expr AOps Γ2 .bool := .fst (.snd (.snd (.snd (.snd st1))))
  let pq'1 : Expr AOps Γ2 (B (ℓ := ℓ) (Pt := Pt) 32) :=
    .fst (.snd (.snd (.snd (.snd (.snd st1)))))
  let pn1 : Expr AOps Γ2 (U32 (ℓ := ℓ) (Pt := Pt)) :=
    .fst (.snd (.snd (.snd (.snd (.snd (.snd st1))))))
  let c1 : Expr AOps Γ2 (fig8CtT (ℓ := ℓ) (Pt := Pt)) :=
    .snd (.snd (.snd (.snd (.snd (.snd (.snd st1))))))
  let posE := Expr.pair q1 (.pair (pGet (mEpoch s1') q1) (.add (pGet (mIdx s1') q1) (.nat 1)))
  let recE := Expr.pair posE (.pair m1 w0)
  let mir' := mRecordE s1' q1 recE isCh1
  let base' := ssMk mir'
    (pSet (ssPq base1) q1 pq'1)
    (pSet (ssPn base1) q1 pn1)
    (ssUnackA base1)
    (.cons (.pair w0 c1) (ssHonest base1))
    (ssChains base1)
    (ssAmb base1)
    (ssStopped base1)
  let keptQ : Expr AOps Γ2 (keptT ℓ Pt) := pGet (scKept sC1) q1
  let Γ3 := fig8StT (ℓ := ℓ) (Pt := Pt) :: Γ2
  let stFig3 : Expr AOps Γ3 (fig8StT (ℓ := ℓ) (Pt := Pt)) := .v0
  let arg3 : Expr AOps Γ3 argT := .v2
  let Γ4 := fsSendStT (ℓ := ℓ) (Pt := Pt) :: Γ3
  let vs4 : Expr AOps Γ4 (fsSendStT (ℓ := ℓ) (Pt := Pt)) := .v0
  let arg4 : Expr AOps Γ4 argT := .var (.succ (.succ (.succ .zero)))
  let c4 : Expr AOps Γ4 (fig8CtT (ℓ := ℓ) (Pt := Pt)) :=
    .snd (.snd (.snd (.snd (.snd (.snd (.snd arg4))))))
  let sent' : Expr AOps Γ2 (.list (sentEntryT ℓ Pt)) :=
    .caseOpt (.fst keptQ)
      (scSent sC1)
      (.ite (sendsInE (f8Id stFig3) (.add (f8Tcur stFig3) (.nat 1)))
        (scSent (.fst (.fst arg3)))
        (.caseOpt (f8VS stFig3)
          (scSent (.fst (.fst arg3)))
          (.cons (.pair c4 vs4) (scSent (.fst (.fst arg4))))))
  let kept' := pSet (scKept sC1) q1
    (keptSendAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB keptQ)
  let sC' := scMk base' kept' sent' (scSnaps sC1)
  eLet (.pair stE (.pair s1E (.pair qE (.pair m0E (.pair isChallE (.pair pq'E (.pair pnE cE)))))))
    (eLet (toWireAtomicE c0)
      (.pair (dfSmRSendSomeE w0) (.pair sC' (.cons c1 ex1))))

@[reducible] def dfSendInpT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (dfSendCorrStateT ℓ Pt)
    (.prod .bool
      (.prod (PlainT (ℓ := ℓ) (Pt := Pt))
        (.prod (.opt (PlainT (ℓ := ℓ) (Pt := Pt))) (.opt (BV512 (ℓ := ℓ) (Pt := Pt))))))

/-- Atomic `.send` step computation for `SimDeliverForge` handling transmit and challenge queries. -/
def dfSendStepC (idA idB : IdentityKey) (qep : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (dfSendCorrStateT ℓ Pt))
    (qE : Expr AOps Γ .bool)
    (m0E : Expr AOps Γ (PlainT (ℓ := ℓ) (Pt := Pt)))
    (chalE : Expr AOps Γ (.opt (PlainT (ℓ := ℓ) (Pt := Pt))))
    (rE : Expr AOps Γ (.opt (BV512 (ℓ := ℓ) (Pt := Pt)))) :
    Comp AOps DFIface Γ
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) (GhostStT (ℓ := ℓ) (Pt := Pt)))
        (dfSendCorrStateT ℓ Pt)) :=
  let inpT := dfSendInpT ℓ Pt
  let coinsT : Ty ASig := .prod (BV512 (ℓ := ℓ) (Pt := Pt)) (.opt (BV256 (ℓ := ℓ) (Pt := Pt)))
  let pubPairT : Ty ASig := .prod (B (ℓ := ℓ) (Pt := Pt) 32) (lpubT (ℓ := ℓ) (Pt := Pt))
  let Γ0 := inpT :: Γ
  let inp0 : Expr AOps Γ0 inpT := .v0
  let st0 : Expr AOps Γ0 (dfSendCorrStateT ℓ Pt) := .fst inp0
  let q0 : Expr AOps Γ0 .bool := .fst (.snd inp0)
  let r0 : Expr AOps Γ0 (.opt (BV512 (ℓ := ℓ) (Pt := Pt))) := .snd (.snd (.snd (.snd inp0)))
  let base0 := scBase (.fst st0)
  let mir0 := ssMir base0
  let earlyGuard :=
    dfOrE (ssStopped base0) (dfOrE (mWin mir0) (.not (mNoBobEpoch0E mir0 q0)))
  let Γ1 := simMirT ℓ Pt :: Γ0
  let s1 : Expr AOps Γ1 (simMirT ℓ Pt) := .v0
  let inp1 : Expr AOps Γ1 inpT := .v1
  let st1 : Expr AOps Γ1 (dfSendCorrStateT ℓ Pt) := .fst inp1
  let q1 : Expr AOps Γ1 .bool := .fst (.snd inp1)
  let chal1 : Expr AOps Γ1 (.opt (PlainT (ℓ := ℓ) (Pt := Pt))) := .fst (.snd (.snd (.snd inp1)))
  let r1 : Expr AOps Γ1 (.opt (BV512 (ℓ := ℓ) (Pt := Pt))) := .snd (.snd (.snd (.snd inp1)))
  let Γ2 := coinsT :: Γ1
  let s1_2 : Expr AOps Γ2 (simMirT ℓ Pt) := .v1
  let inp2 : Expr AOps Γ2 inpT := .v2
  let st2 : Expr AOps Γ2 (dfSendCorrStateT ℓ Pt) := .fst inp2
  let q2 : Expr AOps Γ2 .bool := .fst (.snd inp2)
  let base2 := scBase (.fst st2)
  let mir2 := ssMir base2
  let pn2 : Expr AOps Γ2 (U32 (ℓ := ℓ) (Pt := Pt)) :=
    .ite (dfNatNeE (pGet (mEpoch s1_2) q2) (pGet (mEpoch mir2) q2))
      (dfIdxPredU32E (pGet (mIdx mir2) q2))
      (pGet (ssPn base2) q2)
  let Γ3 := U32 (ℓ := ℓ) (Pt := Pt) :: Γ2
  let pn3 : Expr AOps Γ3 (U32 (ℓ := ℓ) (Pt := Pt)) := .v0
  let rq3 : Expr AOps Γ3 (BV512 (ℓ := ℓ) (Pt := Pt)) := .fst .v1
  let inp3 : Expr AOps Γ3 inpT := .var (.succ (.succ (.succ .zero)))
  let st3 : Expr AOps Γ3 (dfSendCorrStateT ℓ Pt) := .fst inp3
  let q3 : Expr AOps Γ3 .bool := .fst (.snd inp3)
  let base3 := scBase (.fst st3)
  let addr3 :=
    Expr.ite (.and (.not q3) (ssUnackA base3))
      (optBytesLitE (paramsV1 C K idA idB).addrAB)
      .none
  let Γ4 := Ty.opt pubPairT :: Γ3
  let optPub4 : Expr AOps Γ4 (.opt pubPairT) := .v0
  let inp4 : Expr AOps Γ4 inpT := .var (.succ (.succ (.succ (.succ .zero))))
  let Γ5 := pubPairT :: Γ4
  let pub5 : Expr AOps Γ5 (lpubT (ℓ := ℓ) (Pt := Pt)) := .snd .v0
  let rc5 : Expr AOps Γ5 (.opt (BV256 (ℓ := ℓ) (Pt := Pt))) :=
    .snd (.var (.succ (.succ (.succ .zero))))
  let inp5 : Expr AOps Γ5 inpT := .var (.succ (.succ (.succ (.succ (.succ .zero)))))
  let q5 : Expr AOps Γ5 .bool := .fst (.snd inp5)
  let m0_5 : Expr AOps Γ5 (PlainT (ℓ := ℓ) (Pt := Pt)) := .fst (.snd (.snd inp5))
  let chal5 : Expr AOps Γ5 (.opt (PlainT (ℓ := ℓ) (Pt := Pt))) := .fst (.snd (.snd (.snd inp5)))
  let Γ5c := PlainT (ℓ := ℓ) (Pt := Pt) :: Γ5
  let m1_6 : Expr AOps Γ5c (PlainT (ℓ := ℓ) (Pt := Pt)) := .v0
  let pub6 : Expr AOps Γ5c (lpubT (ℓ := ℓ) (Pt := Pt)) := .snd .v1
  let rc6 : Expr AOps Γ5c (.opt (BV256 (ℓ := ℓ) (Pt := Pt))) :=
    .snd (.var (.succ (.succ (.succ (.succ .zero)))))
  let inp6 : Expr AOps Γ5c inpT :=
    .var (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))
  let q6 : Expr AOps Γ5c .bool := .fst (.snd inp6)
  let m0_6 : Expr AOps Γ5c (PlainT (ℓ := ℓ) (Pt := Pt)) := .fst (.snd (.snd inp6))
  let Γ6 := Ty.opt (fig8CtT (ℓ := ℓ) (Pt := Pt)) :: Γ5
  let res6 : Expr AOps Γ6 (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))) := .v0
  let inp6_none : Expr AOps Γ6 inpT :=
    .var (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))
  let Γ7 := fig8CtT (ℓ := ℓ) (Pt := Pt) :: Γ6
  let c7 : Expr AOps Γ7 (fig8CtT (ℓ := ℓ) (Pt := Pt)) := .v0
  let pq'7 : Expr AOps Γ7 (B (ℓ := ℓ) (Pt := Pt) 32) := .fst (.var (.succ (.succ .zero)))
  let pn7 : Expr AOps Γ7 (U32 (ℓ := ℓ) (Pt := Pt)) :=
    .var (.succ (.succ (.succ (.succ .zero))))
  let s1_7 : Expr AOps Γ7 (simMirT ℓ Pt) :=
    .var (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))
  let inp7 : Expr AOps Γ7 inpT :=
    .var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))
  .bind (.ret (.pair stE (.pair qE (.pair m0E (.pair chalE rE)))))
    (.ite earlyGuard
      (.ret (.pair dfSmRNoneE st0))
      (.caseOpt (mEpMgmtE qep mir0 q0 (dfIsSomeE r0))
        (.ret (.pair dfSmRNoneE st0))
        (.ite (.and (dfIsSomeE chal1) (.not (mSafeChE s1 q1)))
          (.ret (.pair dfSmRNoneE st1))
          (.bind (dfDrawSendCoinsC r1)
            (.bind (.ret pn2)
              (.bind (mkPubAtomicC DFIface (.pair (pGet (ssPq base3) q3) (.pair rq3 (.pair pn3 addr3))))
                (.caseOpt optPub4
                  (.ret (.pair dfSmRNoneE (.fst inp4)))
                  (.bind
                    (.caseOpt chal5
                      (.query (I := DFIface) (g := SMTagDF.tr) (.pair q5 (.pair (.pair pub5 m0_5) rc5)))
                      (.query (I := DFIface) (g := SMTagDF.ch)
                        (.pair q6 (.pair (.pair pub6 m0_6) (.pair (.pair pub6 m1_6) rc6)))))
                    (.caseOpt res6
                      (.ret (.pair dfSmRNoneE (.fst inp6_none)))
                      (.ret (dfPostSendStateE idA idB
                        (.fst inp7) s1_7 (.fst (.snd inp7)) (.fst (.snd (.snd inp7)))
                        (dfIsSomeE (.fst (.snd (.snd (.snd inp7))))) pq'7 pn7 c7)))))))))))

def dfPostCorrStateE (idA idB : IdentityKey) (q : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (dfSendCorrStateT ℓ Pt))
    (qE : Expr AOps Γ .bool)
    (fig8stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) :
    Expr AOps Γ
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) (GhostStT (ℓ := ℓ) (Pt := Pt)))
        (dfSendCorrStateT ℓ Pt)) :=
  eLet (.pair stE (.pair qE fig8stE))
    (let st0 : Expr AOps _ (dfSendCorrStateT ℓ Pt) := .fst .v0
     let sC0 : Expr AOps _ (simFullT ℓ Pt) := .fst st0
     let base0 : Expr AOps _ (simBaseT ℓ Pt) := scBase sC0
     let mir0 : Expr AOps _ (simMirT ℓ Pt) := ssMir base0
     let q0 : Expr AOps _ .bool := .fst (.snd .v0)
     let fig8st0 : Expr AOps _ (fig8StT (ℓ := ℓ) (Pt := Pt)) := .snd (.snd .v0)
     let chainsE :=
       Expr.ite (.and q0 (.lt (.snd (mEpoch mir0)) (.nat 1)))
         (.caseSum (f8Gamma fig8st0)
           (ssChains (scBase (.fst (.fst .v1))))
           (.pair
             (revealSpkChainsE
               (.fst (ssChains (scBase (.fst (.fst .v1)))))
               (sOpPtEnc .ptEncPk (sOpGrp .ptDh (.pair .v0 (sOpGrp .ptBase .unit)))))
             (.snd (ssChains (scBase (.fst (.fst .v1)))))))
         (ssChains base0)
     eLet chainsE
       (let cs1 := Expr.v0
        let st1 : Expr AOps _ (dfSendCorrStateT ℓ Pt) := .fst .v1
        let sC1 : Expr AOps _ (simFullT ℓ Pt) := .fst st1
        let base1 : Expr AOps _ (simBaseT ℓ Pt) := scBase sC1
        let mir1 : Expr AOps _ (simMirT ℓ Pt) := ssMir base1
        let q1 : Expr AOps _ .bool := .fst (.snd .v1)
        let fig8st1 : Expr AOps _ (fig8StT (ℓ := ℓ) (Pt := Pt)) := .snd (.snd .v1)
        let baseForGhost := ssMk mir1 (ssPq base1) (ssPn base1) (ssUnackA base1)
          .nil cs1 (ssAmb base1) (ssStopped base1)
        eLet (toGhostE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
            (decT := decT) (lam := lam) idA idB (25000 * q) baseForGhost q1 fig8st1)
          (let gh2 : Expr AOps _ (GhostStT (ℓ := ℓ) (Pt := Pt)) := .v0
           let cs2 := Expr.v1
           let st2 : Expr AOps _ (dfSendCorrStateT ℓ Pt) := .fst .v2
           let sC2 : Expr AOps _ (simFullT ℓ Pt) := .fst st2
           let ex2 : Expr AOps _ (.list (fig8CtT (ℓ := ℓ) (Pt := Pt))) := .snd st2
           let base2 : Expr AOps _ (simBaseT ℓ Pt) := scBase sC2
           let mir2 : Expr AOps _ (simMirT ℓ Pt) := ssMir base2
           let q2 : Expr AOps _ .bool := .fst (.snd .v2)
           let fig8st2 : Expr AOps _ (fig8StT (ℓ := ℓ) (Pt := Pt)) := .snd (.snd .v2)
           let base' := ssMk (mAfterCorrFastE q mir2 q2) (ssPq base2) (ssPn base2) (ssUnackA base2)
             (ssHonest base2) cs2 (ssAmb base2) (ssStopped base2)
           let kept' := pSet (scKept sC2) q2 (keptOfStAtomicE fig8st2)
           let snaps' := Expr.cons (.pair q2 (.pair (pGet (mEpoch mir2) q2) gh2)) (scSnaps sC2)
           let sC' := scMk base' kept' (scSent sC2) snaps'
           .pair (dfSmRCorrSomeE gh2) (.pair sC' ex2))))

/-- Atomic `.corrupt` step computation for `SimDeliverForge` matching `semCorrHookTGB`. -/
def dfCorrStepC (idA idB : IdentityKey) (q : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (dfSendCorrStateT ℓ Pt))
    (qE : Expr AOps Γ .bool) :
    Comp AOps DFIface Γ
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) (GhostStT (ℓ := ℓ) (Pt := Pt)))
        (dfSendCorrStateT ℓ Pt)) :=
  .bind (.ret (.pair stE qE))
    (let st0 : Expr AOps _ (dfSendCorrStateT ℓ Pt) := .fst .v0
     let q0 : Expr AOps _ .bool := .snd .v0
     let base0 := scBase (.fst st0)
     let mir0 := ssMir base0
     let corrGuard :=
       dfOrE (ssStopped base0)
         (dfOrE (mWin mir0)
           (dfOrE (.not (mCorrAllowedFastE q mir0 q0))
             (dfOrE (mInWinE mir0 q0) (.not (mNoSpkCorrE mir0 q0)))))
     .ite corrGuard
       (.ret (.pair dfSmRNoneE st0))
       (.bind (.query (I := DFIface) (g := SMTagDF.cr) q0)
         (.caseOpt .v0
           (.ret (.pair dfSmRNoneE (.fst .v1)))
           (.ret (dfPostCorrStateE idA idB q (.fst .v2) (.snd .v2) .v0)))))

end StepComps

section StaticBounds

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
  (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (lam : Pt) (qep q : ℕ)

theorem dfSendStepC_queries {Γ : List (Ty (atomicSig ℓ Pt))}
    (stE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (dfSendCorrStateT ℓ Pt))
    (qE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .bool)
    (m0E : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ PlainT)
    (chalE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (.opt PlainT))
    (rE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (.opt BV512)) :
    (dfSendStepC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB qep stE qE m0E chalE rE).queries
      (fun _ => 1) (fun _ => 0) ≤ 1 := by
  simp [dfSendStepC, dfDrawSendCoinsC, Comp.queries, mkPubAtomicC_queries]

theorem dfCorrStepC_queries {Γ : List (Ty (atomicSig ℓ Pt))}
    (stE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (dfSendCorrStateT ℓ Pt))
    (qE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .bool) :
    (dfCorrStepC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB q stE qE).queries
      (fun _ => 1) (fun _ => 0) ≤ 1 := by
  simp [dfCorrStepC, Comp.queries]

private theorem hb0_bits : _root_.ReductionDsl.bits 0 = 1 :=
  Computational.Proofs.Game.PromotedCostedReds.SimFig8State.bits_zero
private theorem hb1_bits : _root_.ReductionDsl.bits 1 = 1 :=
  Computational.Proofs.Game.PromotedCostedReds.SimFig8State.bits_eq_of_bounds
    (by omega) (by omega) (by omega) (by omega)
private theorem hb2_bits : _root_.ReductionDsl.bits 2 = 2 :=
  Computational.Proofs.Game.PromotedCostedReds.SimFig8State.bits_eq_of_bounds
    (by omega) (by omega) (by omega) (by omega)
private theorem hb3_bits : _root_.ReductionDsl.bits 3 = 2 :=
  Computational.Proofs.Game.PromotedCostedReds.SimFig8State.bits_eq_of_bounds
    (by omega) (by omega) (by omega) (by omega)
private theorem hb4_bits : _root_.ReductionDsl.bits 4 = 3 :=
  Computational.Proofs.Game.PromotedCostedReds.SimFig8State.bits_eq_of_bounds
    (by omega) (by omega) (by omega) (by omega)
private theorem hb5_bits : _root_.ReductionDsl.bits 5 = 3 :=
  Computational.Proofs.Game.PromotedCostedReds.SimFig8State.bits_eq_of_bounds
    (by omega) (by omega) (by omega) (by omega)
private theorem hb6_bits : _root_.ReductionDsl.bits 6 = 3 :=
  Computational.Proofs.Game.PromotedCostedReds.SimFig8State.bits_eq_of_bounds
    (by omega) (by omega) (by omega) (by omega)
private theorem hb7_bits : _root_.ReductionDsl.bits 7 = 3 :=
  Computational.Proofs.Game.PromotedCostedReds.SimFig8State.bits_eq_of_bounds
    (by omega) (by omega) (by omega) (by omega)
private theorem hb32_nat : _root_.ReductionDsl.bits 32 = 6 :=
  Computational.Proofs.Game.PromotedCostedReds.SimFig8State.bits_eq_of_bounds
    (by omega) (by omega) (by omega) (by omega)
private theorem hb32_pnat : _root_.ReductionDsl.bits ((32 : ℕ+) : ℕ) = 6 := hb32_nat

omit [SampleableType Pt] in
private theorem dfPostCorrStateE_cost {Γ : List (Ty (atomicSig ℓ Pt))}
    (stE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (dfSendCorrStateT ℓ Pt))
    (qE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .bool)
    (fig8stE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ
      (fig8StT (ℓ := ℓ) (Pt := Pt))) :
    (dfPostCorrStateE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB q stE qE fig8stE).cost ≤
      stE.cost + qE.cost + fig8stE.cost + 1630000 + 25002000 * q := by
  let AOps := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
  let gcT := Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost.ghostChainT ℓ Pt
  let T0 := Ty.prod (dfSendCorrStateT ℓ Pt) (.prod .bool (fig8StT (ℓ := ℓ) (Pt := Pt)))
  let Tc := Ty.prod (.list gcT) (.list gcT)
  let Γ0 := T0 :: Γ
  let Γr := BV256 (ℓ := ℓ) (Pt := Pt) :: Γ0
  let Γ1 := Tc :: Γ0
  let Γ2 := GhostStT (ℓ := ℓ) (Pt := Pt) :: Γ1
  let pkE : Expr AOps Γr (_root_.ReductionDsl.PK (ℓ := ℓ) (Pt := Pt)) :=
    sOpPtEnc (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) .ptEncPk
      (sOpGrp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) .ptDh
        (.pair .v0
          (sOpGrp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
            (decT := decT) (lam := lam) .ptBase .unit)))
  have hrev := Computational.Proofs.Game.PromotedCostedReds.SimFig8State.cost_revealSpkChainsE
    (.fst (ssChains (scBase (.fst (.fst (.v1 : Expr AOps Γr _)))))) pkE
  dsimp only [AOps, Γ0, Γr, pkE, ssChains, scBase, Expr.v0, Expr.v1] at hrev
  simp only [Computational.Proofs.Game.PromotedCostedReds.SimFig8State.cost_sOpPtEnc,
    Computational.Proofs.Game.PromotedCostedReds.SimFig8State.cost_sOpGrp,
    _root_.ReductionDsl.AtomicGroupOp.cost, Expr.cost] at hrev
  let b1 : Expr AOps Γ1 (simBaseT ℓ Pt) := scBase (.fst (.fst .v1))
  let baseForGhost : Expr AOps Γ1 (simBaseT ℓ Pt) :=
    ssMk (ssMir b1) (ssPq b1) (ssPn b1) (ssUnackA b1) .nil .v0 (ssAmb b1) (ssStopped b1)
  have htg := Computational.Proofs.Game.PromotedCostedReds.SimFig8State.cost_toGhostE
    (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (25000 * q) baseForGhost
    (.fst (.snd .v1)) (.snd (.snd .v1))
  have hmc := Computational.Proofs.Game.PromotedCostedReds.SimFig8State.cost_mAfterCorrFastE
    q (ssMir (scBase (.fst (.fst (.v2 : Expr AOps Γ2 _))))) (.fst (.snd .v2))
  have hkp := Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept.keptOfStAtomicE_cost
    (.snd (.snd (.v2 : Expr AOps Γ2 _)))
  dsimp only [AOps, gcT, T0, Tc, Γ0, Γ1, Γ2, b1, baseForGhost, scBase, ssMir, ssPq, ssPn,
    ssUnackA, ssAmb, ssStopped, ssMk, Expr.v0, Expr.v1, Expr.v2, Expr.cost] at htg hmc hkp
  dsimp only [dfPostCorrStateE, dfSmRCorrSomeE, pGet, pSet, scBase, scKept, scSent, scSnaps, scMk,
    ssChains, ssMir, ssPq, ssPn, ssUnackA, ssHonest, ssAmb, ssStopped, ssMk, mEpoch, f8Gamma,
    Expr.v0, Expr.v1, Expr.v2]
  generalize revealSpkChainsE (ℓ := ℓ) (Pt := Pt) _ _ = erev at hrev ⊢
  generalize toGhostE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) _ _ _ _ _ _ = etg at htg ⊢
  generalize mAfterCorrFastE (ℓ := ℓ) (Pt := Pt) _ _ _ = emc at hmc ⊢
  generalize keptOfStAtomicE (ℓ := ℓ) (Pt := Pt) _ = ekp at hkp ⊢
  simp only [Computational.Proofs.Game.PromotedCostedReds.SimFig8State.cost_eLet,
    Expr.cost, hb1_bits]
  omega

omit [SampleableType Pt] in
private theorem dfIdxPredU32E_cost {Γ : List (Ty (atomicSig ℓ Pt))}
    (idxE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .nat) :
    (dfIdxPredU32E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idxE).cost ≤ idxE.cost + 50 := by
  simp only [dfIdxPredU32E,
    Computational.Proofs.Game.PromotedCostedReds.SimFig8State.cost_eLet,
    Computational.Proofs.Game.PromotedCostedReds.SimFig8State.cost_sOpPure,
    _root_.ReductionDsl.AtomicPureOp.cost, Expr.v0, Expr.cost, hb1_bits]
  omega

private theorem dfDrawSendCoinsC_cost {Γ : List (Ty (atomicSig ℓ Pt))}
    (rE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (.opt BV512)) :
    (dfDrawSendCoinsC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) rE).cost ≤ rE.cost + 50 := by
  dsimp only [dfDrawSendCoinsC, fig8SmIfaceDF, _root_.ReductionDsl.atomicSamplers,
    _root_.ReductionDsl.unifSamplers, _root_.ReductionDsl.AtomicUnifBase.cost,
    Expr.v0, Expr.v1, Comp.cost, Expr.cost]
  omega

omit [SampleableType Pt] in
private theorem dfPostSendStateE_cost (hℓ : ℓ < 10 ^ 6) {Γ : List (Ty (atomicSig ℓ Pt))}
    (stE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (dfSendCorrStateT ℓ Pt))
    (s1E : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (simMirT ℓ Pt))
    (qE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .bool)
    (m0E : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ PlainT)
    (isChallE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .bool)
    (pq'E : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (B 32))
    (pnE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ U32)
    (cE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ
      (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (dfPostSendStateE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB stE s1E qE m0E isChallE pq'E pnE cE).cost ≤
      stE.cost + s1E.cost + qE.cost + m0E.cost + isChallE.cost + pq'E.cost + pnE.cost +
        cE.cost + 700000 := by
  let AOps := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
  let Γ1 := dfPostSendArgT ℓ Pt :: Γ
  let Γ2 := B (ℓ := ℓ) (Pt := Pt) 32 :: Γ1
  have hw := Computational.Proofs.Game.PromotedCostedReds.SimFig8WireSnap.toWireAtomicE_cost
    (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    (Γ := Γ1) (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))))
  let s1' : Expr AOps Γ2 (simMirT ℓ Pt) := .fst (.snd .v1)
  let q1 : Expr AOps Γ2 .bool := .fst (.snd (.snd .v1))
  let recE : Expr AOps Γ2
      (Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost.simRecT ℓ Pt) :=
    .pair (.pair q1 (.pair (pGet (mEpoch s1') q1) (.add (pGet (mIdx s1') q1) (.nat 1))))
      (.pair (.fst (.snd (.snd (.snd .v1)))) .v0)
  have hmr := Computational.Proofs.Game.PromotedCostedReds.SimFig8State.cost_mRecordE
    s1' q1 recE (.fst (.snd (.snd (.snd (.snd .v1)))))
  have hks := Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept.keptSendAtomicE_cost
    (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    idA idB (Γ := Γ2) (pGet (scKept (.fst (.fst .v1))) q1)
  dsimp only [AOps, Γ1, Γ2, s1', q1, recE, pGet, mEpoch, mIdx, scKept,
    Expr.v0, Expr.v1, Expr.cost] at hw hmr hks
  simp only [hb1_bits] at hmr
  dsimp only [dfPostSendStateE, dfSmRSendSomeE, pGet, pSet, sendsInE,
    scBase, scKept, scSent, scSnaps, scMk,
    ssMir, ssPq, ssPn, ssUnackA, ssHonest, ssChains, ssAmb, ssStopped, ssMk,
    mEpoch, mIdx, f8Id, f8VS, f8Tcur, Expr.v0, Expr.v1, Expr.v2]
  generalize toWireAtomicE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) _ = ew at hw ⊢
  generalize mRecordE (ℓ := ℓ) (Pt := Pt) _ _ _ _ = emr at hmr ⊢
  generalize keptSendAtomicE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) _ _ _ = eks at hks ⊢
  simp only [Computational.Proofs.Game.PromotedCostedReds.SimFig8State.cost_eLet,
    Expr.cost, hb0_bits, hb1_bits, hb2_bits]
  omega

theorem dfSendStepC_cost (hℓ : ℓ < 10 ^ 6) {Γ : List (Ty (atomicSig ℓ Pt))}
    (stE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (dfSendCorrStateT ℓ Pt))
    (qE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .bool)
    (m0E : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ PlainT)
    (chalE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (.opt PlainT))
    (rE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (.opt BV512)) :
    (dfSendStepC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB qep stE qE m0E chalE rE).cost ≤
      stE.cost + qE.cost + m0E.cost + chalE.cost + rE.cost +
        20000000 + 30000000 * q + 512 * _root_.ReductionDsl.bits (qep + 1) := by
  have hbqep : _root_.ReductionDsl.bits qep ≤ _root_.ReductionDsl.bits (qep + 1) :=
    _root_.ReductionDsl.bits_mono (Nat.le_succ qep)
  let AOps := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
  let DFIface := fig8SmIfaceDF ℓ Pt
  let inpT := dfSendInpT ℓ Pt
  let coinsT : Ty (atomicSig ℓ Pt) := .prod BV512 (.opt BV256)
  let pubPairT : Ty (atomicSig ℓ Pt) := .prod (B 32) (lpubT (ℓ := ℓ) (Pt := Pt))
  let Γ0 := inpT :: Γ
  let Γ1 := simMirT ℓ Pt :: Γ0
  let Γ2 := coinsT :: Γ1
  let Γ3 := U32 (ℓ := ℓ) (Pt := Pt) :: Γ2
  let Γ4 := Ty.opt pubPairT :: Γ3
  let Γ5 := pubPairT :: Γ4
  let Γ6 := Ty.opt (fig8CtT (ℓ := ℓ) (Pt := Pt)) :: Γ5
  let Γ7 := fig8CtT (ℓ := ℓ) (Pt := Pt) :: Γ6
  let mir0 : Expr AOps Γ0 (simMirT ℓ Pt) := ssMir (scBase (.fst (.fst .v0)))
  let q0 : Expr AOps Γ0 .bool := .fst (.snd .v0)
  have hmnb := Computational.Proofs.Game.PromotedCostedReds.SimFig8State.cost_mNoBobEpoch0E mir0 q0
  have hmep := Computational.Proofs.Game.PromotedCostedReds.SimFig8State.cost_mEpMgmtE
    qep mir0 q0 (dfIsSomeE (.snd (.snd (.snd (.snd .v0)))))
  have hmsc := Computational.Proofs.Game.PromotedCostedReds.SimFig8State.cost_mSafeChE
    (O' := AOps) (Γ := Γ1) .v0 (.fst (.snd .v1))
  have hdsc := dfDrawSendCoinsC_cost ℓ C K Dh encPt encT decT lam
    (Γ := Γ1) (.snd (.snd (.snd (.snd .v1))))
  let pn2 : Expr AOps Γ2 U32 :=
    .ite (dfNatNeE (pGet (mEpoch .v1) (.fst (.snd .v2)))
        (pGet (mEpoch (ssMir (scBase (.fst (.fst .v2))))) (.fst (.snd .v2))))
      (dfIdxPredU32E (pGet (mIdx (ssMir (scBase (.fst (.fst .v2))))) (.fst (.snd .v2))))
      (pGet (ssPn (scBase (.fst (.fst .v2)))) (.fst (.snd .v2)))
  have hpn2 : pn2.cost ≤ 150 := by
    have hidx := dfIdxPredU32E_cost ℓ C K Dh encPt encT decT lam
      (Γ := Γ2) (pGet (mIdx (ssMir (scBase (.fst (.fst .v2))))) (.fst (.snd .v2)))
    dsimp only [AOps, inpT, coinsT, Γ0, Γ1, Γ2, pn2, dfNatNeE, dfOrE, pGet, mEpoch, mIdx,
      ssPn, ssMir, scBase, Expr.v0, Expr.v1, Expr.v2, Expr.cost] at hidx ⊢
    generalize dfIdxPredU32E (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) _ = eidx at hidx ⊢
    simp only [Computational.Proofs.Game.PromotedCostedReds.SimFig8State.cost_eLet, Expr.cost]
    omega
  let base3 : Expr AOps Γ3 (simBaseT ℓ Pt) :=
    scBase (.fst (.fst (.var (.succ (.succ (.succ .zero))))))
  let q3 : Expr AOps Γ3 .bool := .fst (.snd (.var (.succ (.succ (.succ .zero)))))
  let addr3 : Expr AOps Γ3 (.opt (B 32)) :=
    .ite (.and (.not q3) (ssUnackA base3)) (optBytesLitE (paramsV1 C K idA idB).addrAB) .none
  have hpub : (mkPubAtomicC DFIface
      (.pair (pGet (ssPq base3) q3) (.pair (.fst .v1) (.pair .v0 addr3)))).cost ≤ 2144300 := by
    have hm := Computational.Proofs.Game.PromotedCostedReds.SimFig8WireSnap.mkPubAtomicC_cost
      (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      DFIface (Γ := Γ3) (.pair (pGet (ssPq base3) q3) (.pair (.fst .v1) (.pair .v0 addr3)))
    have hab := Computational.Proofs.Game.PromotedCostedReds.SimFig8WireSnap.optBytesLitE_cost
      (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      (Γ := Γ3) (paramsV1 C K idA idB).addrAB 36
      (Computational.Proofs.Game.PromotedCostedReds.SimFig8Crypto.serializedPartyAddresses_len_le_36
        .A .B)
    dsimp only [AOps, DFIface, inpT, coinsT, Γ0, Γ1, Γ2, Γ3, base3, q3, addr3,
      pGet, ssPq, ssUnackA, scBase, Expr.v0, Expr.v1] at hm hab ⊢
    generalize optBytesLitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) _ = eab at hab hm ⊢
    simp only [Expr.cost] at hm ⊢
    omega
  let inp7 : Expr AOps Γ7 inpT :=
    .var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))
  have hpost := dfPostSendStateE_cost ℓ C K idA idB Dh encPt encT decT lam hℓ (Γ := Γ7)
    (.fst inp7) (.var (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))
    (.fst (.snd inp7)) (.fst (.snd (.snd inp7)))
    (dfIsSomeE (.fst (.snd (.snd (.snd inp7)))))
    (.fst (.var (.succ (.succ .zero)))) (.var (.succ (.succ (.succ (.succ .zero))))) .v0
  dsimp only [AOps, DFIface, inpT, coinsT, pubPairT, Γ0, Γ1, Γ2, Γ3, Γ4, Γ5, Γ6, Γ7,
    mir0, q0, pn2, base3, q3, addr3, inp7, dfSendStepC, dfOrE, dfIsSomeE, dfSmRNoneE,
    ssStopped, mWin, ssMir, scBase, Expr.v0, Expr.v1, Expr.v2]
    at hmnb hmep hmsc hdsc hpn2 hpub hpost ⊢
  generalize mNoBobEpoch0E (ℓ := ℓ) (Pt := Pt) _ _ = emnb at hmnb ⊢
  generalize mEpMgmtE (ℓ := ℓ) (Pt := Pt) _ _ _ _ = emep at hmep ⊢
  generalize mSafeChE (ℓ := ℓ) (Pt := Pt) _ _ = emsc at hmsc ⊢
  generalize dfDrawSendCoinsC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) _ = cdsc at hdsc ⊢
  generalize (Expr.ite (dfNatNeE _ _) _ _ :
    Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) _ _) = epn2 at hpn2 ⊢
  generalize mkPubAtomicC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) _ _ = cpub at hpub ⊢
  generalize dfPostSendStateE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) _ _ _ _ _ _ _ _ _ _ = epost at hpost ⊢
  simp only [Comp.cost, Expr.cost] at hmnb hmep hmsc hdsc hpn2 hpub hpost ⊢
  omega

theorem dfCorrStepC_cost (hℓ : ℓ < 10 ^ 6) {Γ : List (Ty (atomicSig ℓ Pt))}
    (stE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (dfSendCorrStateT ℓ Pt))
    (qE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .bool) :
    (dfCorrStepC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB q stE qE).cost ≤
      stE.cost + qE.cost + 20000000 + 30000000 * q := by
  let _ := hℓ
  let AOps := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
  let Γ0 := Ty.prod (dfSendCorrStateT ℓ Pt) .bool :: Γ
  let Γ2 := fig8StT (ℓ := ℓ) (Pt := Pt) :: Ty.opt (fig8StT (ℓ := ℓ) (Pt := Pt)) :: Γ0
  let mir0 : Expr AOps Γ0 (simMirT ℓ Pt) := ssMir (scBase (.fst (.fst .v0)))
  let q0 : Expr AOps Γ0 .bool := .snd .v0
  have h1 := Computational.Proofs.Game.PromotedCostedReds.SimFig8State.cost_mCorrAllowedFastE
    q mir0 q0
  have h2 := Computational.Proofs.Game.PromotedCostedReds.SimFig8State.cost_mInWinE mir0 q0
  have h3 := Computational.Proofs.Game.PromotedCostedReds.SimFig8State.cost_mNoSpkCorrE mir0 q0
  have hpost := dfPostCorrStateE_cost ℓ C K idA idB Dh encPt encT decT lam q
    (Γ := Γ2) (.fst .v2) (.snd .v2) .v0
  dsimp only [AOps, Γ0, Γ2, mir0, q0, ssMir, scBase, Expr.v0, Expr.v2, Expr.cost]
    at h1 h2 h3 hpost
  dsimp only [dfCorrStepC, dfSmRNoneE, ssStopped, mWin, ssMir, scBase, Expr.v0, Expr.v1, Expr.v2]
  generalize mCorrAllowedFastE (ℓ := ℓ) (Pt := Pt) _ _ _ = ec1 at h1 ⊢
  generalize mInWinE (ℓ := ℓ) (Pt := Pt) _ _ = ec2 at h2 ⊢
  generalize mNoSpkCorrE (ℓ := ℓ) (Pt := Pt) _ _ = ec3 at h3 ⊢
  generalize dfPostCorrStateE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) _ _ _ _ _ _ = epost at hpost ⊢
  simp only [dfOrE, Comp.cost, Expr.cost]
  omega

private theorem bits_25000_mul_le (n : ℕ) :
    _root_.ReductionDsl.bits (25000 * n) ≤ _root_.ReductionDsl.bits (n + 1) + 15 := by
  apply Computational.Proofs.Game.PromotedCostedReds.SimFig8State.bits_le_of_lt_pow (by omega)
  have hn : n + 1 < 2 ^ _root_.ReductionDsl.bits (n + 1) := by
    unfold _root_.ReductionDsl.bits
    simpa using Nat.lt_pow_succ_log_self (by omega : 1 < 2) (n + 1)
  have hp : 2 ^ (_root_.ReductionDsl.bits (n + 1) + 15) =
      2 ^ _root_.ReductionDsl.bits (n + 1) * 32768 := by
    rw [Nat.pow_add]
  omega

omit [SampleableType Pt] in
private theorem dfPostCorrStateE_descBits_le {Γ : List (Ty (atomicSig ℓ Pt))}
    (stE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (dfSendCorrStateT ℓ Pt))
    (qE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .bool)
    (fig8stE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ
      (fig8StT (ℓ := ℓ) (Pt := Pt))) :
    atomicExprDescBits atomicSessionOpDescBits
      (dfPostCorrStateE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB q stE qE fig8stE) ≤
      atomicExprDescBits atomicSessionOpDescBits stE +
      atomicExprDescBits atomicSessionOpDescBits qE +
      atomicExprDescBits atomicSessionOpDescBits fig8stE +
      52 * _root_.ReductionDsl.bits (q + 1) + 75000 := by
  have hbq : _root_.ReductionDsl.bits q ≤ _root_.ReductionDsl.bits (q + 1) :=
    _root_.ReductionDsl.bits_mono (Nat.le_succ q)
  have hb25k : _root_.ReductionDsl.bits (25000 * q) ≤ _root_.ReductionDsl.bits (q + 1) + 15 :=
    bits_25000_mul_le q
  let AOps := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
  let gcT := Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost.ghostChainT ℓ Pt
  let T0 := Ty.prod (dfSendCorrStateT ℓ Pt) (.prod .bool (fig8StT (ℓ := ℓ) (Pt := Pt)))
  let Tc := Ty.prod (.list gcT) (.list gcT)
  let Γ0 := T0 :: Γ
  let Γr := BV256 (ℓ := ℓ) (Pt := Pt) :: Γ0
  let Γ1 := Tc :: Γ0
  let Γ2 := GhostStT (ℓ := ℓ) (Pt := Pt) :: Γ1
  let pkE : Expr AOps Γr (_root_.ReductionDsl.PK (ℓ := ℓ) (Pt := Pt)) :=
    sOpPtEnc (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) .ptEncPk
      (sOpGrp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) .ptDh
        (.pair .v0
          (sOpGrp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
            (decT := decT) (lam := lam) .ptBase .unit)))
  have hrev := Computational.Proofs.Game.PromotedCostedReds.SimFig8State.revealSpkChainsE_descBits_le
    atomicSessionOpDescBits (.fst (ssChains (scBase (.fst (.fst (.v1 : Expr AOps Γr _)))))) pkE
  dsimp only [AOps, Γ0, Γr, pkE, ssChains, scBase, Expr.v0, Expr.v1, atomicExprDescBits,
    Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost.varIdx] at hrev
  simp only [Computational.Proofs.Game.PromotedCostedReds.SimFig8State.descBits_sOpPtEnc,
    Computational.Proofs.Game.PromotedCostedReds.SimFig8State.descBits_sOpGrp,
    atomicExprDescBits, Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost.varIdx,
    Nat.reduceAdd, hb0_bits, hb1_bits] at hrev
  let b1 : Expr AOps Γ1 (simBaseT ℓ Pt) := scBase (.fst (.fst .v1))
  let baseForGhost : Expr AOps Γ1 (simBaseT ℓ Pt) :=
    ssMk (ssMir b1) (ssPq b1) (ssPn b1) (ssUnackA b1) .nil .v0 (ssAmb b1) (ssStopped b1)
  have htg := Computational.Proofs.Game.PromotedCostedReds.SimFig8State.toGhostE_descBits_le
    (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (25000 * q) baseForGhost
    (.fst (.snd .v1)) (.snd (.snd .v1))
  have hmc := Computational.Proofs.Game.PromotedCostedReds.SimFig8State.mAfterCorrFastE_descBits_le
    atomicSessionOpDescBits q
    (ssMir (scBase (.fst (.fst (.v2 : Expr AOps Γ2 _))))) (.fst (.snd .v2))
  have hkp := Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept.keptOfStAtomicE_descBits_le
    atomicSessionOpDescBits (.snd (.snd (.v2 : Expr AOps Γ2 _)))
  dsimp only [AOps, gcT, T0, Tc, Γ0, Γ1, Γ2, b1, baseForGhost, scBase, ssMir, ssPq, ssPn,
    ssUnackA, ssAmb, ssStopped, ssMk, fig8CtT, _root_.ReductionDsl.fig8HdrT,
    _root_.ReductionDsl.lctT, _root_.ReductionDsl.wireSaltCtT, B, _root_.ReductionDsl.PB,
    _root_.ReductionDsl.U64, BV256, _root_.ReductionDsl.PtT, Expr.v0, Expr.v1, Expr.v2,
    atomicExprDescBits, Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost.atomicTyDescBits,
    Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost.atomicSortDescBits,
    Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost.varIdx] at htg hmc hkp
  simp only [Nat.reduceAdd, hb0_bits, hb1_bits, hb2_bits, hb32_pnat] at htg hmc hkp
  dsimp only [dfPostCorrStateE, dfSmRCorrSomeE, pGet, pSet, scBase, scKept, scSent, scSnaps, scMk,
    ssChains, ssMir, ssPq, ssPn, ssUnackA, ssHonest, ssAmb, ssStopped, ssMk, mEpoch, f8Gamma,
    Expr.v0, Expr.v1, Expr.v2]
  generalize revealSpkChainsE (ℓ := ℓ) (Pt := Pt) _ _ = erev at hrev ⊢
  generalize toGhostE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) _ _ _ _ _ _ = etg at htg ⊢
  generalize mAfterCorrFastE (ℓ := ℓ) (Pt := Pt) _ _ _ = emc at hmc ⊢
  generalize keptOfStAtomicE (ℓ := ℓ) (Pt := Pt) _ = ekp at hkp ⊢
  simp only [Computational.Proofs.Game.PromotedCostedReds.SimFig8State.descBits_eLet,
    smRT, _root_.ReductionDsl.recvResultT, fig8CtT, _root_.ReductionDsl.fig8HdrT,
    _root_.ReductionDsl.lctT, _root_.ReductionDsl.wireSaltCtT, B,
    _root_.ReductionDsl.U64, PlainT, BV256, _root_.ReductionDsl.PtT, GhostStT,
    atomicExprDescBits, Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost.atomicTyDescBits,
    Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost.atomicSortDescBits,
    Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost.varIdx,
    Nat.reduceAdd, hb0_bits, hb1_bits, hb2_bits, hb32_pnat]
  omega

omit [SampleableType Pt] in
private theorem fig8SendStepAtomicE_descBits_tight (B_cl : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (stE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (fig8StT (ℓ := ℓ) (Pt := Pt)))
    (mcOptE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ
      (.opt (.prod (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) PlainT) BV256))) :
    atomicExprDescBits atomicSessionOpDescBits
      (Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept.fig8SendStepAtomicE
        (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB B_cl stE mcOptE) ≤
      atomicExprDescBits atomicSessionOpDescBits stE +
      atomicExprDescBits atomicSessionOpDescBits mcOptE +
        8 * _root_.ReductionDsl.bits B_cl + 25000 := by
  have hdef := Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept.defaultMcAtomicE_descBits_le
    (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)
  let t0 := Ty.prod (fig8StT (ℓ := ℓ) (Pt := Pt))
    (.prod (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) PlainT) BV256)
  let Γ1 := t0 :: Γ
  let Γ2 := Ty.prod (ckaStT (ℓ := ℓ) (Pt := Pt))
    (.prod (_root_.ReductionDsl.PtT (ℓ := ℓ) (Pt := Pt))
      (_root_.ReductionDsl.PtT (ℓ := ℓ) (Pt := Pt))) :: Γ1
  let Γ3 := Ty.prod .bool
    (.prod (fig8StT (ℓ := ℓ) (Pt := Pt)) (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) PlainT)) :: Γ1
  let Γ4 := fsSendStT (ℓ := ℓ) (Pt := Pt) :: Γ3
  have hcka := Computational.Proofs.Game.PromotedCostedReds.SimFig8State.descBits_runFig8WithIds
    (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    idA idB (Γ := Γ1) (Computational.Proofs.ReductionDsl.Fig8Atomic.ckaSendExpr ℓ Pt C Dh encPt encT lam)
    (.pair (f8Gamma (.fst .v0)) (.snd (.snd .v0)))
  have hup := Computational.Proofs.Game.PromotedCostedReds.SimFig8State.descBits_runFig8WithIds
    (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    idA idB (Γ := Γ2) (Computational.Proofs.ReductionDsl.Fig8Atomic.prngUpExpr ℓ Pt C Dh encPt encT lam)
    (.pair (Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept.f8Root (.fst .v1)) (.snd (.snd .v0)))
  have hdefE := Computational.Proofs.Game.PromotedCostedReds.SimFig8State.descBits_runFig8WithIds
    (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    idA idB (Γ := Γ3) (Computational.Proofs.ReductionDsl.Fig8Atomic.defaultEExpr ℓ Pt C Dh encPt encT lam)
    .unit
  have hfs := Computational.Proofs.Game.PromotedCostedReds.SimFig8State.descBits_runFig8WithIds
    (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    idA idB (Γ := Γ4) (Computational.Proofs.ReductionDsl.Fig8Atomic.fsSendExpr ℓ Pt C Dh encPt encT lam)
    (.pair .v0 (.pair (.pair (f8Tcur (.fst (.snd .v1)))
      (Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept.f8Cur (.fst (.snd .v1))))
      (.snd (.snd .v1))))
  have hd_cka := Computational.Proofs.Game.PromotedCostedReds.SimFig8SpqrDesc.ckaSendExpr_descBits_le
    (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh) (encPt := encPt) (encT := encT) (lam := lam)
  have hd_up := Computational.Proofs.Game.PromotedCostedReds.SimFig8SpqrDesc.prngUpExpr_descBits_le
    (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh) (encPt := encPt) (encT := encT) (lam := lam)
  have hd_defE := Computational.Proofs.Game.PromotedCostedReds.SimFig8SpqrDesc.defaultEExpr_descBits_le
    (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh) (encPt := encPt) (encT := encT) (lam := lam)
  have hd_fs := Computational.Proofs.Game.PromotedCostedReds.SimFig8SpqrDesc.fsSendExpr_descBits_le
    (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh) (encPt := encPt) (encT := encT) (lam := lam)
  dsimp only [Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept.fig8SendStepAtomicE,
    Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept.f8Mk, f8Id,
    Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept.f8Root, f8VS,
    Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept.f8VR, f8Gamma,
    Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept.f8Cur, f8Tcur,
    sendsInE, Expr.v0, Expr.v1, Expr.v2] at hcka hup hdefE hfs ⊢
  generalize Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept.defaultMcAtomicE
    (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ) = e_def at hdef ⊢
  generalize Computational.Proofs.Game.PromotedCostedReds.SimFig8State.runFig8WithIds
    (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    idA idB (Γ := Γ1) _ _ = e_rcka at hcka ⊢
  generalize Computational.Proofs.Game.PromotedCostedReds.SimFig8State.runFig8WithIds
    (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    idA idB (Γ := Γ2) _ _ = e_rup at hup ⊢
  generalize Computational.Proofs.Game.PromotedCostedReds.SimFig8State.runFig8WithIds
    (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    idA idB (Γ := Γ3) _ .unit = e_rdefE at hdefE ⊢
  generalize Computational.Proofs.Game.PromotedCostedReds.SimFig8State.runFig8WithIds
    (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    idA idB (Γ := Γ4) _ _ = e_rfs at hfs ⊢
  simp only [Computational.Proofs.Game.PromotedCostedReds.SimFig8State.descBits_eLet,
    Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost.varIdx,
    atomicExprDescBits, Nat.reduceAdd, hb0_bits, hb1_bits, hb2_bits] at hcka hup hdefE hfs ⊢
  omega

omit [SampleableType Pt] in
private theorem keptSendAtomicE_descBits_tight {Γ : List (Ty (atomicSig ℓ Pt))}
    (kE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (keptT ℓ Pt)) :
    atomicExprDescBits atomicSessionOpDescBits
      (keptSendAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB kE) ≤
      atomicExprDescBits atomicSessionOpDescBits kE + 30000 := by
  let Γ1 := fig8StT (ℓ := ℓ) (Pt := Pt) :: keptT ℓ Pt :: Γ
  have hstep := fig8SendStepAtomicE_descBits_tight ℓ C K idA idB Dh encPt encT decT lam 0
    (Γ := Γ1) .v0 .none
  have ht_f8 := Computational.Proofs.Game.PromotedCostedReds.SimFig8State.atomicTyDescBits_fig8StT
    (ℓ := ℓ) (Pt := Pt)
  dsimp only [keptSendAtomicE, sendsInE, f8Id, f8Tcur,
    Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept.f8VR, Expr.v0, Expr.v1] at hstep ⊢
  generalize Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept.fig8SendStepAtomicE
    (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB 0 (Γ := Γ1) _ _ = e_s at hstep ⊢
  simp only [Computational.Proofs.Game.PromotedCostedReds.SimFig8State.descBits_eLet, BV256,
    Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost.varIdx,
    atomicExprDescBits,
    Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost.atomicTyDescBits,
    Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost.atomicSortDescBits,
    Nat.reduceAdd, hb0_bits, hb1_bits, hb2_bits, hb32_pnat] at hstep ⊢
  omega

omit [SampleableType Pt] in
private theorem dfIdxPredU32E_descBits_le {Γ : List (Ty (atomicSig ℓ Pt))}
    (idxE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .nat) :
    atomicExprDescBits atomicSessionOpDescBits
      (dfIdxPredU32E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idxE) ≤
      atomicExprDescBits atomicSessionOpDescBits idxE + 300 := by
  simp only [dfIdxPredU32E,
    Computational.Proofs.Game.PromotedCostedReds.SimFig8State.descBits_eLet,
    Computational.Proofs.Game.PromotedCostedReds.SimFig8State.descBits_sOpPure,
    Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost.atomicPureOpDescBits,
    Expr.v0, Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost.varIdx,
    atomicExprDescBits, hb0_bits, hb1_bits]
  omega

private theorem dfDrawSendCoinsC_descBits_le {Γ : List (Ty (atomicSig ℓ Pt))}
    (rE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (.opt BV512)) :
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
      (dfDrawSendCoinsC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) rE) ≤
      atomicExprDescBits atomicSessionOpDescBits rE + 200 := by
  simp only [dfDrawSendCoinsC, BV256, Expr.v0, Expr.v1,
    Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost.varIdx,
    atomicCompDescBits, atomicExprDescBits,
    Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost.atomicTyDescBits,
    Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost.atomicSortDescBits,
    Nat.reduceAdd, hb0_bits, hb1_bits]
  omega

omit [SampleableType Pt] in
private theorem dfPostSendStateE_descBits_le {Γ : List (Ty (atomicSig ℓ Pt))}
    (stE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (dfSendCorrStateT ℓ Pt))
    (s1E : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (simMirT ℓ Pt))
    (qE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .bool)
    (m0E : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ PlainT)
    (isChallE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .bool)
    (pq'E : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (B 32))
    (pnE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ U32)
    (cE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ
      (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    atomicExprDescBits atomicSessionOpDescBits
      (dfPostSendStateE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB stE s1E qE m0E isChallE pq'E pnE cE) ≤
      atomicExprDescBits atomicSessionOpDescBits stE +
      atomicExprDescBits atomicSessionOpDescBits s1E +
      atomicExprDescBits atomicSessionOpDescBits qE +
      atomicExprDescBits atomicSessionOpDescBits m0E +
      atomicExprDescBits atomicSessionOpDescBits isChallE +
      atomicExprDescBits atomicSessionOpDescBits pq'E +
      atomicExprDescBits atomicSessionOpDescBits pnE +
      atomicExprDescBits atomicSessionOpDescBits cE + 35000 := by
  let AOps := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
  let Γ1 := dfPostSendArgT ℓ Pt :: Γ
  let Γ2 := B (ℓ := ℓ) (Pt := Pt) 32 :: Γ1
  have hw := Computational.Proofs.Game.PromotedCostedReds.SimFig8WireSnap.toWireAtomicE_descBits_le
    (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    (Γ := Γ1) (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))))
  let s1' : Expr AOps Γ2 (simMirT ℓ Pt) := .fst (.snd .v1)
  let q1 : Expr AOps Γ2 .bool := .fst (.snd (.snd .v1))
  let recE : Expr AOps Γ2
      (Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost.simRecT ℓ Pt) :=
    .pair (.pair q1 (.pair (pGet (mEpoch s1') q1) (.add (pGet (mIdx s1') q1) (.nat 1))))
      (.pair (.fst (.snd (.snd (.snd .v1)))) .v0)
  have hmr := Computational.Proofs.Game.PromotedCostedReds.SimFig8State.mRecordE_descBits_le
    atomicSessionOpDescBits s1' q1 recE (.fst (.snd (.snd (.snd (.snd .v1)))))
  have hks := keptSendAtomicE_descBits_tight ℓ C K idA idB Dh encPt encT decT lam
    (Γ := Γ2) (pGet (scKept (.fst (.fst .v1))) q1)
  dsimp only [AOps, Γ1, Γ2, s1', q1, recE, dfPostSendStateE, dfSmRSendSomeE,
    pGet, pSet, sendsInE, scBase, scKept, scSent, scSnaps, scMk,
    ssMir, ssPq, ssPn, ssUnackA, ssHonest, ssChains, ssAmb, ssStopped, ssMk,
    mEpoch, mIdx, f8Id, f8VS, f8Tcur, Expr.v0, Expr.v1, Expr.v2] at hw hmr hks ⊢
  generalize toWireAtomicE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) _ = ew at hw ⊢
  generalize mRecordE (ℓ := ℓ) (Pt := Pt) _ _ _ _ = emr at hmr ⊢
  generalize keptSendAtomicE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) _ _ _ = eks at hks ⊢
  simp only [Computational.Proofs.Game.PromotedCostedReds.SimFig8State.descBits_eLet,
    smRT, _root_.ReductionDsl.recvResultT, B, PlainT, GhostStT,
    Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost.varIdx,
    atomicExprDescBits,
    Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost.atomicTyDescBits,
    Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost.atomicSortDescBits,
    Nat.reduceAdd, hb0_bits, hb1_bits, hb2_bits, hb3_bits] at hw hmr hks ⊢
  omega

theorem dfSendStepC_descBits_le (hℓ : ℓ < 10 ^ 6) {Γ : List (Ty (atomicSig ℓ Pt))}
    (stE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (dfSendCorrStateT ℓ Pt))
    (qE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .bool)
    (m0E : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ PlainT)
    (chalE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (.opt PlainT))
    (rE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (.opt BV512)) :
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
      (dfSendStepC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB qep stE qE m0E chalE rE) ≤
      8 * (atomicExprDescBits atomicSessionOpDescBits stE +
           atomicExprDescBits atomicSessionOpDescBits qE +
           atomicExprDescBits atomicSessionOpDescBits m0E +
           atomicExprDescBits atomicSessionOpDescBits chalE +
           atomicExprDescBits atomicSessionOpDescBits rE) +
        2 ^ 18 + 2 ^ 10 * _root_.ReductionDsl.bits (ratchetCostBudget q (qep + 1) + (qep + 1)) := by
  let _ := hℓ
  have hbqep : _root_.ReductionDsl.bits qep ≤
      _root_.ReductionDsl.bits (ratchetCostBudget q (qep + 1) + (qep + 1)) :=
    Nat.le_trans (_root_.ReductionDsl.bits_mono (Nat.le_succ qep))
      (Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost.bits_qep_le_ratchetCostBudget
        q (qep + 1))
  let AOps := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
  let DFIface := fig8SmIfaceDF ℓ Pt
  let inpT := dfSendInpT ℓ Pt
  let coinsT : Ty (atomicSig ℓ Pt) := .prod BV512 (.opt BV256)
  let pubPairT : Ty (atomicSig ℓ Pt) := .prod (B 32) (lpubT (ℓ := ℓ) (Pt := Pt))
  let Γ0 := inpT :: Γ
  let Γ1 := simMirT ℓ Pt :: Γ0
  let Γ2 := coinsT :: Γ1
  let Γ3 := U32 (ℓ := ℓ) (Pt := Pt) :: Γ2
  let Γ4 := Ty.opt pubPairT :: Γ3
  let Γ5 := pubPairT :: Γ4
  let Γ6 := Ty.opt (fig8CtT (ℓ := ℓ) (Pt := Pt)) :: Γ5
  let Γ7 := fig8CtT (ℓ := ℓ) (Pt := Pt) :: Γ6
  let mir0 : Expr AOps Γ0 (simMirT ℓ Pt) := ssMir (scBase (.fst (.fst .v0)))
  let q0 : Expr AOps Γ0 .bool := .fst (.snd .v0)
  have hmnb := Computational.Proofs.Game.PromotedCostedReds.SimFig8State.mNoBobEpoch0E_descBits_le
    atomicSessionOpDescBits mir0 q0
  have hmep := Computational.Proofs.Game.PromotedCostedReds.SimFig8State.mEpMgmtE_descBits_le
    atomicSessionOpDescBits qep mir0 q0 (dfIsSomeE (.snd (.snd (.snd (.snd .v0)))))
  have hmsc := Computational.Proofs.Game.PromotedCostedReds.SimFig8State.mSafeChE_descBits_le
    atomicSessionOpDescBits (Γ := Γ1) (.v0 : Expr AOps Γ1 _) (.fst (.snd .v1))
  have hdsc := dfDrawSendCoinsC_descBits_le ℓ C K Dh encPt encT decT lam
    (Γ := Γ1) (.snd (.snd (.snd (.snd .v1))))
  let pn2 : Expr AOps Γ2 U32 :=
    .ite (dfNatNeE (pGet (mEpoch .v1) (.fst (.snd .v2)))
        (pGet (mEpoch (ssMir (scBase (.fst (.fst .v2))))) (.fst (.snd .v2))))
      (dfIdxPredU32E (pGet (mIdx (ssMir (scBase (.fst (.fst .v2))))) (.fst (.snd .v2))))
      (pGet (ssPn (scBase (.fst (.fst .v2)))) (.fst (.snd .v2)))
  have hpn2 : atomicExprDescBits atomicSessionOpDescBits pn2 ≤ 1200 := by
    have hidx := dfIdxPredU32E_descBits_le ℓ C K Dh encPt encT decT lam
      (Γ := Γ2) (pGet (mIdx (ssMir (scBase (.fst (.fst .v2))))) (.fst (.snd .v2)))
    dsimp only [AOps, inpT, coinsT, Γ0, Γ1, Γ2, pn2, dfNatNeE, dfOrE, pGet, mEpoch, mIdx,
      ssPn, ssMir, scBase, Expr.v0, Expr.v1, Expr.v2] at hidx ⊢
    generalize dfIdxPredU32E (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) _ = eidx at hidx ⊢
    simp only [Computational.Proofs.Game.PromotedCostedReds.SimFig8State.descBits_eLet,
      Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost.varIdx,
      atomicExprDescBits, Nat.reduceAdd, hb0_bits, hb1_bits, hb2_bits] at hidx ⊢
    omega
  let base3 : Expr AOps Γ3 (simBaseT ℓ Pt) :=
    scBase (.fst (.fst (.var (.succ (.succ (.succ .zero))))))
  let q3 : Expr AOps Γ3 .bool := .fst (.snd (.var (.succ (.succ (.succ .zero)))))
  let addr3 : Expr AOps Γ3 (.opt (B 32)) :=
    .ite (.and (.not q3) (ssUnackA base3)) (optBytesLitE (paramsV1 C K idA idB).addrAB) .none
  have hpub : atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
      (mkPubAtomicC DFIface
        (.pair (pGet (ssPq base3) q3) (.pair (.fst .v1) (.pair .v0 addr3)))) ≤ 28000 := by
    have hm := Computational.Proofs.Game.PromotedCostedReds.SimFig8WireSnap.mkPubAtomicC_descBits_le
      (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      DFIface (fun _ => 8) (fun _ => 8) (Γ := Γ3)
      (.pair (pGet (ssPq base3) q3) (.pair (.fst .v1) (.pair .v0 addr3)))
    have hab := Computational.Proofs.Game.PromotedCostedReds.SimFig8WireSnap.optBytesLitE_descBits_le
      (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      (Γ := Γ3) (paramsV1 C K idA idB).addrAB
      (fun v hv => Nat.le_trans
        (Computational.Proofs.Game.PromotedCostedReds.SimFig8Crypto.serializedPartyAddresses_len_le_36
          .A .B v hv) (by omega))
    dsimp only [AOps, DFIface, inpT, coinsT, Γ0, Γ1, Γ2, Γ3, base3, q3, addr3,
      pGet, ssPq, ssUnackA, scBase, Expr.v0, Expr.v1] at hm hab ⊢
    generalize optBytesLitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) _ = eab at hab hm ⊢
    simp only [B, Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost.varIdx,
      atomicExprDescBits,
      Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost.atomicTyDescBits,
      Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost.atomicSortDescBits,
      Nat.reduceAdd, hb0_bits, hb1_bits, hb3_bits, hb32_pnat] at hm ⊢
    omega
  let inp7 : Expr AOps Γ7 inpT :=
    .var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))
  have hpost := dfPostSendStateE_descBits_le ℓ C K idA idB Dh encPt encT decT lam (Γ := Γ7)
    (.fst inp7) (.var (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))
    (.fst (.snd inp7)) (.fst (.snd (.snd inp7)))
    (dfIsSomeE (.fst (.snd (.snd (.snd inp7)))))
    (.fst (.var (.succ (.succ .zero)))) (.var (.succ (.succ (.succ (.succ .zero))))) .v0
  dsimp only [AOps, DFIface, inpT, coinsT, pubPairT, Γ0, Γ1, Γ2, Γ3, Γ4, Γ5, Γ6, Γ7,
    mir0, q0, pn2, base3, q3, addr3, inp7, dfSendStepC, dfOrE, dfIsSomeE, dfSmRNoneE,
    ssStopped, mWin, ssMir, scBase, Expr.v0, Expr.v1, Expr.v2]
    at hmnb hmep hmsc hdsc hpn2 hpub hpost ⊢
  generalize mNoBobEpoch0E (ℓ := ℓ) (Pt := Pt) _ _ = emnb at hmnb ⊢
  generalize mEpMgmtE (ℓ := ℓ) (Pt := Pt) _ _ _ _ = emep at hmep ⊢
  generalize mSafeChE (ℓ := ℓ) (Pt := Pt) _ _ = emsc at hmsc ⊢
  generalize dfDrawSendCoinsC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) _ = cdsc at hdsc ⊢
  generalize (Expr.ite (dfNatNeE _ _) _ _ :
    Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) _ _) = epn2 at hpn2 ⊢
  generalize mkPubAtomicC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) _ _ = cpub at hpub ⊢
  generalize dfPostSendStateE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) _ _ _ _ _ _ _ _ _ _ = epost at hpost ⊢
  simp only [smRT, _root_.ReductionDsl.recvResultT, B, PlainT, GhostStT,
    atomicCompDescBits, atomicExprDescBits,
    Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost.atomicTyDescBits,
    Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost.atomicSortDescBits,
    Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost.varIdx,
    Nat.reduceAdd, hb0_bits, hb1_bits, hb2_bits, hb3_bits, hb4_bits, hb5_bits, hb6_bits,
    hb7_bits, hb32_pnat] at hmnb hmep hmsc hdsc hpn2 hpub hpost ⊢
  omega

theorem dfCorrStepC_descBits_le (hℓ : ℓ < 10 ^ 6) {Γ : List (Ty (atomicSig ℓ Pt))}
    (stE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (dfSendCorrStateT ℓ Pt))
    (qE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .bool) :
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
      (dfCorrStepC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB q stE qE) ≤
      8 * (atomicExprDescBits atomicSessionOpDescBits stE +
           atomicExprDescBits atomicSessionOpDescBits qE) +
        2 ^ 18 + 2 ^ 10 * _root_.ReductionDsl.bits (ratchetCostBudget q (qep + 1) + (qep + 1)) := by
  let _ := hℓ
  have hbq1 : _root_.ReductionDsl.bits (q + 1) ≤
      _root_.ReductionDsl.bits (ratchetCostBudget q (qep + 1) + (qep + 1)) :=
    Nat.le_trans (_root_.ReductionDsl.bits_mono (by omega : q + 1 ≤ 2 * q + 2))
      (Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost.bits_two_mul_add_two_le_ratchetCostBudget
        q (qep + 1))
  have hbq : _root_.ReductionDsl.bits q ≤ _root_.ReductionDsl.bits (q + 1) :=
    _root_.ReductionDsl.bits_mono (Nat.le_succ q)
  let AOps := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
  let Γ0 := Ty.prod (dfSendCorrStateT ℓ Pt) .bool :: Γ
  let Γ2 := fig8StT (ℓ := ℓ) (Pt := Pt) :: Ty.opt (fig8StT (ℓ := ℓ) (Pt := Pt)) :: Γ0
  let mir0 : Expr AOps Γ0 (simMirT ℓ Pt) := ssMir (scBase (.fst (.fst .v0)))
  let q0 : Expr AOps Γ0 .bool := .snd .v0
  have h1 := Computational.Proofs.Game.PromotedCostedReds.SimFig8State.mCorrAllowedFastE_descBits_le
    atomicSessionOpDescBits q mir0 q0
  have h2 := Computational.Proofs.Game.PromotedCostedReds.SimFig8State.mInWinE_descBits_le
    atomicSessionOpDescBits mir0 q0
  have h3 := Computational.Proofs.Game.PromotedCostedReds.SimFig8State.mNoSpkCorrE_descBits_le
    atomicSessionOpDescBits mir0 q0
  have hpost := dfPostCorrStateE_descBits_le ℓ C K idA idB Dh encPt encT decT lam q
    (Γ := Γ2) (.fst .v2) (.snd .v2) .v0
  dsimp only [AOps, Γ0, Γ2, mir0, q0, ssMir, scBase, Expr.v0, Expr.v2, atomicExprDescBits,
    Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost.varIdx] at h1 h2 h3 hpost
  simp only [Nat.reduceAdd, hb0_bits, hb2_bits] at h1 h2 h3 hpost
  dsimp only [dfCorrStepC, dfOrE, dfSmRNoneE, ssStopped, mWin, ssMir, scBase,
    Expr.v0, Expr.v1, Expr.v2]
  generalize mCorrAllowedFastE (ℓ := ℓ) (Pt := Pt) _ _ _ = ec1 at h1 ⊢
  generalize mInWinE (ℓ := ℓ) (Pt := Pt) _ _ = ec2 at h2 ⊢
  generalize mNoSpkCorrE (ℓ := ℓ) (Pt := Pt) _ _ = ec3 at h3 ⊢
  generalize dfPostCorrStateE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) _ _ _ _ _ _ = epost at hpost ⊢
  simp only [smRT, _root_.ReductionDsl.recvResultT, B, PlainT, GhostStT,
    atomicCompDescBits, atomicExprDescBits,
    Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost.atomicTyDescBits,
    Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost.atomicSortDescBits,
    Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost.varIdx,
    Nat.reduceAdd, hb0_bits, hb1_bits, hb32_pnat]
  omega

end StaticBounds

end

end Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStepSendCorrCost

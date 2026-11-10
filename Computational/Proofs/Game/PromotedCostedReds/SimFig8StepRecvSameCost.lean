/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SimFig8Crypto
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8SanOracle
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8SanCoupling

/-!
# Atomic `SimFig8` Receive Programs and Static Bounds

Defines the `ReductionDsl` programs over `atomicSessionOps` and `fig8SmIface` for the `SimFig8`
existing-chain receive path and proves their static query, cost, and description-bit bounds.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvSameCost

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Ops Iface Expr Comp bits
  atomicSig atomicSessionOps fig8SmIface GhostStT smQT smRT smRrT
  recvResultT B PK PtT PlainT lpubT lctT fig8CtT SMTag)
open CryptoGames.CKA (DHFun)
open CryptoGames.SM (posTy orE boolEq isSomeE otherE senderOfE pGet pSet)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalSession (ratchetCostBudget)
open CryptoVerification.E2E (Bytes)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost
  (atomicSessionOpDescBits atomicExprDescBits atomicCompDescBits)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost
  (simFullT simBaseT simMirT simRecT ghostChainT keptT snapT sentEntryT)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8State
  (sOpPure eLet eMapOpt srecPos mSafeInjE mInTransitE mAcceptE mChallContainsE mTrivialE
   ghostAcceptC ghostRejectsE pushChainE findChainIdxE getChainDE modifyChainAcceptC
   ssMir ssPq ssPn ssUnackA ssHonest ssChains ssAmb ssStopped ssMk ssSetMirWin
   scBase scKept scSent scSnaps scMk)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8Crypto
  (kDecOutT orElseOptE knownSeedDecryptAtomicFastC lctSaltEqOfLctAtomicE injOKAtomicE
   parseOutT parseRecvAtomicC toWireAtomicE toWireAtomicE_cost toWireAtomicE_descBits_le)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept
  (eqFig8CAtomicE keptRecvAtomicE keptEvalAtomicE sentEvalAtomicE)

/-! ## Input and output types -/

abbrev recvOutT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (.opt (recvResultT (ℓ := ℓ) (Pt := Pt))) (simFullT ℓ Pt)

abbrev smRrFullT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  smRrT (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) PlainT)

/-- Input tuple `(s, (qB, (w, (isDel, (t, (i, (m, (ci?, (Tpk, pq')))))))))` for `onAcceptPure`. -/
abbrev onAcceptInpT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (simBaseT ℓ Pt)
    (.prod .bool
      (.prod (B 32)
        (.prod .bool
          (.prod .nat
            (.prod .nat
              (.prod PlainT
                (.prod (.opt .nat)
                  (.prod PK (B 32)))))))))

/-- Input tuple `(s, (qB, (w, (isDel, (ci?, (Tpk, (pq', res)))))))` for `onAnswerPure`. -/
abbrev onAnswerInpT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (simBaseT ℓ Pt)
    (.prod .bool
      (.prod (B 32)
        (.prod .bool
          (.prod (.opt .nat)
            (.prod PK
              (.prod (B 32)
                (.opt (smRrFullT ℓ Pt))))))))

/-- Input tuple `(sC, (qB, (w, (c, c'))))` for `evalCKS`. -/
abbrev evalCKInpT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (simFullT ℓ Pt)
    (.prod .bool
      (.prod (B 32)
        (.prod (fig8CtT (ℓ := ℓ) (Pt := Pt))
          (fig8CtT (ℓ := ℓ) (Pt := Pt)))))

/-- Input tuple `(sC, (qB, (w, (ci?, (Tpk, (pq', (c, r)))))))` for `semResyncHookS`. -/
abbrev resyncInpT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (simFullT ℓ Pt)
    (.prod .bool
      (.prod (B 32)
        (.prod (.opt .nat)
          (.prod PK
            (.prod (B 32)
              (.prod (fig8CtT (ℓ := ℓ) (Pt := Pt))
                (.opt (kDecOutT ℓ Pt))))))))

/-- Input tuple `(sC, (qB, (w, (isDel, (ci?, (Tpk, (pq', c')))))))` for `semFwdAnswerHookS`. -/
abbrev fwdAnsInpT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (simFullT ℓ Pt)
    (.prod .bool
      (.prod (B 32)
        (.prod .bool
          (.prod (.opt .nat)
            (.prod PK
              (.prod (B 32)
                (fig8CtT (ℓ := ℓ) (Pt := Pt))))))))

/-- Input tuple `(sC, (qB, (w, (isDel, (ci?, (Tpk, (pq', (honestC, c'))))))))` for `semFwdHookS`. -/
abbrev fwdHookInpT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (simFullT ℓ Pt)
    (.prod .bool
      (.prod (B 32)
        (.prod .bool
          (.prod (.opt .nat)
            (.prod PK
              (.prod (B 32)
                (.prod (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt)))
                  (fig8CtT (ℓ := ℓ) (Pt := Pt)))))))))

/-- Input tuple `(sC, (qB, (w, (isDel, (parsed, (honestC, ci))))))` for `semRecvSameBranch`. -/
abbrev recvSameInpT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (simFullT ℓ Pt)
    (.prod .bool
      (.prod (B 32)
        (.prod .bool
          (.prod (parseOutT ℓ Pt)
            (.prod (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))) .nat)))))

/-- Input tuple `(sC, (qB, (w, (isDel, (parsed, honestC)))))` for `semRecvNewBranch`. -/
abbrev recvNewInpT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (simFullT ℓ Pt)
    (.prod .bool
      (.prod (B 32)
        (.prod .bool
          (.prod (parseOutT ℓ Pt)
            (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt)))))))

/-! ## Atomic programs -/

section Programs

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
variable {ℓ : ℕ} {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
variable {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
local notation "FIface" => fig8SmIface ℓ Pt

def onAccBase {O' : Ops ASig} {Γ} (x : Expr O' Γ (onAcceptInpT ℓ Pt)) : Expr O' Γ (simBaseT ℓ Pt) :=
  .fst x
def onAccQ {O' : Ops ASig} {Γ} (x : Expr O' Γ (onAcceptInpT ℓ Pt)) : Expr O' Γ .bool :=
  .fst (.snd x)
def onAccW {O' : Ops ASig} {Γ} (x : Expr O' Γ (onAcceptInpT ℓ Pt)) : Expr O' Γ (B 32) :=
  .fst (.snd (.snd x))
def onAccIsDel {O' : Ops ASig} {Γ} (x : Expr O' Γ (onAcceptInpT ℓ Pt)) : Expr O' Γ .bool :=
  .fst (.snd (.snd (.snd x)))
def onAccT {O' : Ops ASig} {Γ} (x : Expr O' Γ (onAcceptInpT ℓ Pt)) : Expr O' Γ .nat :=
  .fst (.snd (.snd (.snd (.snd x))))
def onAccI {O' : Ops ASig} {Γ} (x : Expr O' Γ (onAcceptInpT ℓ Pt)) : Expr O' Γ .nat :=
  .fst (.snd (.snd (.snd (.snd (.snd x)))))
def onAccM {O' : Ops ASig} {Γ} (x : Expr O' Γ (onAcceptInpT ℓ Pt)) : Expr O' Γ PlainT :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd x))))))
def onAccCi? {O' : Ops ASig} {Γ} (x : Expr O' Γ (onAcceptInpT ℓ Pt)) : Expr O' Γ (.opt .nat) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd x)))))))
def onAccPk {O' : Ops ASig} {Γ} (x : Expr O' Γ (onAcceptInpT ℓ Pt)) : Expr O' Γ PK :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd x))))))))
def onAccPq' {O' : Ops ASig} {Γ} (x : Expr O' Γ (onAcceptInpT ℓ Pt)) : Expr O' Γ (B 32) :=
  .snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd x))))))))

def ssAcceptUpdate {O' : Ops ASig} {Γ}
    (sE : Expr O' Γ (simBaseT ℓ Pt)) (qE : Expr O' Γ .bool)
    (mirE : Expr O' Γ (simMirT ℓ Pt))
    (csE : Expr O' Γ (.list (ghostChainT ℓ Pt)))
    (pq'E : Expr O' Γ (B 32)) : Expr O' Γ (simBaseT ℓ Pt) :=
  ssMk mirE (pSet (ssPq sE) qE pq'E) (ssPn sE) (.and (ssUnackA sE) qE)
    (ssHonest sE) (pSet (ssChains sE) qE csE) (ssAmb sE) (ssStopped sE)

/-- Atomic computation implementing `onAcceptPure`. -/
def onAcceptPureAtomicC (L qep : ℕ) {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (onAcceptInpT ℓ Pt)) :
    Comp AOps FIface Γ (.prod (.opt (recvResultT (ℓ := ℓ) (Pt := Pt))) (simBaseT ℓ Pt)) :=
  .bind (.ret inpE)
    (.bind
      (.caseOpt (onAccCi? .v0)
        (.bind
          (ghostAcceptC FIface
            (.pair (.some (onAccPk .v0)) (.pair (onAccT .v0) (.pair (.nat 0) .nil)))
            (onAccI .v0))
          (.ret (pushChainE (pGet (ssChains (onAccBase .v1)) (onAccQ .v1)) .v0)))
        (modifyChainAcceptC FIface (pGet (ssChains (onAccBase .v1)) (onAccQ .v1)) .v0 (onAccI .v1)))
      (.ret
        (let cs0 : Expr AOps _ (.list (ghostChainT ℓ Pt)) := .v0
         let x0 : Expr AOps _ (onAcceptInpT ℓ Pt) := .v1
         let s0 := onAccBase x0
         let q0 := onAccQ x0
         let w0 := onAccW x0
         let isDel0 := onAccIsDel x0
         let t0 := onAccT x0
         let i0 := onAccI x0
         let m0 := onAccM x0
         let pq'0 := onAccPq' x0
         .ite isDel0
           (.caseOpt (mInTransitE L (ssMir s0) (otherE q0) w0)
             (.pair .none s0)
             (let r0 : Expr AOps _ (simRecT ℓ Pt) := .v0
              let cs1 : Expr AOps _ (.list (ghostChainT ℓ Pt)) := .v1
              let x1 : Expr AOps _ (onAcceptInpT ℓ Pt) := .v2
              let s1 := onAccBase x1
              let q1 := onAccQ x1
              let t1 := onAccT x1
              let i1 := onAccI x1
              let m1 := onAccM x1
              let pq'1 := onAccPq' x1
              let posR := srecPos r0
              .pair
                (.some (.inr (.pair t1 (.pair i1
                  (.ite (mChallContainsE L (ssMir s1) posR) .none (.some m1))))))
                (ssAcceptUpdate s1 q1 (mAcceptE L (ssMir s1) q1 posR) cs1 pq'1)))
           (.ite (.lt (.nat (qep + 1)) t0)
             (.pair (.some (.inl .unit)) s0)
             (let posInj : Expr AOps _ posTy := .pair (otherE q0) (.pair t0 i0)
              .ite (mTrivialE L (ssMir s0) posInj)
                (.pair
                  (.some (.inr (.pair t0 (.pair i0 (.some m0)))))
                  (ssAcceptUpdate s0 q0 (mAcceptE L (ssMir s0) q0 posInj) cs0 pq'0))
                (.pair (.some (.inl .unit)) (ssSetMirWin s0)))))))

def onAnsBase {O' : Ops ASig} {Γ} (x : Expr O' Γ (onAnswerInpT ℓ Pt)) : Expr O' Γ (simBaseT ℓ Pt) :=
  .fst x
def onAnsQ {O' : Ops ASig} {Γ} (x : Expr O' Γ (onAnswerInpT ℓ Pt)) : Expr O' Γ .bool :=
  .fst (.snd x)
def onAnsW {O' : Ops ASig} {Γ} (x : Expr O' Γ (onAnswerInpT ℓ Pt)) : Expr O' Γ (B 32) :=
  .fst (.snd (.snd x))
def onAnsIsDel {O' : Ops ASig} {Γ} (x : Expr O' Γ (onAnswerInpT ℓ Pt)) : Expr O' Γ .bool :=
  .fst (.snd (.snd (.snd x)))
def onAnsCi? {O' : Ops ASig} {Γ} (x : Expr O' Γ (onAnswerInpT ℓ Pt)) : Expr O' Γ (.opt .nat) :=
  .fst (.snd (.snd (.snd (.snd x))))
def onAnsPk {O' : Ops ASig} {Γ} (x : Expr O' Γ (onAnswerInpT ℓ Pt)) : Expr O' Γ PK :=
  .fst (.snd (.snd (.snd (.snd (.snd x)))))
def onAnsPq' {O' : Ops ASig} {Γ} (x : Expr O' Γ (onAnswerInpT ℓ Pt)) : Expr O' Γ (B 32) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd x))))))
def onAnsRes {O' : Ops ASig} {Γ} (x : Expr O' Γ (onAnswerInpT ℓ Pt)) :
    Expr O' Γ (.opt (smRrFullT ℓ Pt)) :=
  .snd (.snd (.snd (.snd (.snd (.snd (.snd x))))))

/-- Atomic computation implementing `onAnswerPure`. -/
def onAnswerPureAtomicC (L qep : ℕ) {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (onAnswerInpT ℓ Pt)) :
    Comp AOps FIface Γ (.prod (.opt (recvResultT (ℓ := ℓ) (Pt := Pt))) (simBaseT ℓ Pt)) :=
  .bind (.ret inpE)
    (.caseOpt (onAnsRes .v0)
      (.ret (.pair (.some (.inl .unit)) (onAnsBase .v0)))
      (.caseSum .v0
        (.ret (.pair (.some (.inl .unit)) (onAnsBase .v2)))
        (let acc0 : Expr AOps _ (.prod .nat (.prod .nat (.opt (.prod lpubT PlainT)))) := .v0
         let x2 : Expr AOps _ (onAnswerInpT ℓ Pt) := .v2
         let mDef : Expr AOps _ PlainT :=
           .caseOpt (.snd (.snd acc0)) (sOpPure .plainDefault .unit) (.snd .v0)
         onAcceptPureAtomicC L qep
           (.pair (onAnsBase x2)
             (.pair (onAnsQ x2)
               (.pair (onAnsW x2)
                 (.pair (onAnsIsDel x2)
                   (.pair (.fst acc0)
                     (.pair (.fst (.snd acc0))
                       (.pair mDef
                         (.pair (onAnsCi? x2)
                           (.pair (onAnsPk x2) (onAnsPq' x2)))))))))))))

/-- Atomic computation implementing `evalCKS`. -/
def evalCKSAtomicC (idA idB : IdentityKey) (L B_cap T Kc : ℕ) {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (evalCKInpT ℓ Pt)) :
    Comp AOps FIface Γ (.opt (.opt (kDecOutT ℓ Pt))) :=
  .bind (.ret inpE)
    (let sC0 : Expr AOps _ (simFullT ℓ Pt) := .fst .v0
     let q0 : Expr AOps _ .bool := .fst (.snd .v0)
     let w0 : Expr AOps _ (B 32) := .fst (.snd (.snd .v0))
     let c0 : Expr AOps _ (fig8CtT (ℓ := ℓ) (Pt := Pt)) := .fst (.snd (.snd (.snd .v0)))
     let c'0 : Expr AOps _ (fig8CtT (ℓ := ℓ) (Pt := Pt)) := .snd (.snd (.snd (.snd .v0)))
     let predE : Expr AOps _ (.opt (.opt (kDecOutT ℓ Pt))) :=
       orElseOptE
         (keptEvalAtomicE idA idB T B_cap (pGet (scKept sC0) q0) c'0)
         (sentEvalAtomicE idA idB L B_cap (scSent sC0) c0 c'0)
     .caseOpt predE
       (knownSeedDecryptAtomicFastC idA idB L Kc B_cap FIface
         (scSnaps sC0) q0 (.fst (.fst c0)) w0 c'0)
       (.ret (.some .v0)))

def inTransitHonestE (L : ℕ) {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt))
    (qBE : Expr AOps Γ .bool)
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) : Expr AOps Γ .bool :=
  eLet (.pair sCE (.pair qBE c'E))
    (.and
      (.anyB L (ssHonest (scBase (.fst .v0)))
        (eqFig8CAtomicE (.snd .v0) (.snd (.snd .v1))))
      (isSomeE (mInTransitE L (ssMir (scBase (.fst .v0)))
        (otherE (.fst (.snd .v0))) (toWireAtomicE (.snd (.snd .v0))))))

def honestFindE (L : ℕ) {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt))
    (qBE : Expr AOps Γ .bool)
    (wE : Expr AOps Γ (B 32)) : Expr AOps Γ (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))) :=
  eLet (.pair sCE (.pair qBE wE))
    (eMapOpt
      (.findB L (ssHonest (scBase (.fst .v0)))
        (.and
          (sOpPure (.bytesEq 32 32) (.pair (.fst .v0) (.snd (.snd .v1))))
          (boolEq (senderOfE (.fst (.fst (.snd .v0)))) (otherE (.fst (.snd .v1))))))
      (.snd .v0))

def mkCE {Γ : List (Ty ASig)}
    (honestCE : Expr AOps Γ (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))))
    (tE : Expr AOps Γ .nat)
    (T?E : Expr AOps Γ (.opt PtT))
    (lctE : Expr AOps Γ (lctT (ℓ := ℓ) (Pt := Pt))) :
    Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)) :=
  eLet (.pair honestCE (.pair (.pair tE T?E) lctE))
    (.caseOpt (.fst .v0)
      (.snd .v0)
      (.ite (lctSaltEqOfLctAtomicE .v0 (.snd (.snd .v1))) .v0 (.snd .v1)))

def recvRefuseE (L : ℕ) {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt))
    (qBE : Expr AOps Γ .bool)
    (wE : Expr AOps Γ (B 32))
    (isDelE : Expr AOps Γ .bool) : Expr AOps Γ .bool :=
  eLet (.pair sCE (.pair qBE (.pair wE isDelE)))
    (let base0 : Expr AOps _ (simBaseT ℓ Pt) := scBase (.fst .v0)
     let mir0 : Expr AOps _ (simMirT ℓ Pt) := ssMir base0
     let q0 : Expr AOps _ .bool := .fst (.snd .v0)
     let w0 : Expr AOps _ (B 32) := .fst (.snd (.snd .v0))
     let isDel0 : Expr AOps _ .bool := .snd (.snd (.snd .v0))
     let inTrSome : Expr AOps _ .bool := isSomeE (mInTransitE L mir0 (otherE q0) w0)
     orE (ssStopped base0)
       (orE (Expr.fst (.snd mir0))
         (orE (.and isDel0 (.not inTrSome))
           (.and (.not isDel0)
             (orE inTrSome
               (orE (.not (mSafeInjE mir0))
                 (.not (injOKAtomicE w0))))))))

def scUpdateKeptRecv (idA idB : IdentityKey) (T : ℕ) {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt))
    (qBE : Expr AOps Γ .bool)
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    Expr AOps Γ (.prod (keptT ℓ Pt) (keptT ℓ Pt)) :=
  pSet (scKept sCE) qBE (keptRecvAtomicE idA idB T (pGet (scKept sCE) qBE) cE)

def rsySC {O' : Ops ASig} {Γ} (x : Expr O' Γ (resyncInpT ℓ Pt)) : Expr O' Γ (simFullT ℓ Pt) :=
  .fst x
def rsyQ {O' : Ops ASig} {Γ} (x : Expr O' Γ (resyncInpT ℓ Pt)) : Expr O' Γ .bool :=
  .fst (.snd x)
def rsyW {O' : Ops ASig} {Γ} (x : Expr O' Γ (resyncInpT ℓ Pt)) : Expr O' Γ (B 32) :=
  .fst (.snd (.snd x))
def rsyCi? {O' : Ops ASig} {Γ} (x : Expr O' Γ (resyncInpT ℓ Pt)) : Expr O' Γ (.opt .nat) :=
  .fst (.snd (.snd (.snd x)))
def rsyPk {O' : Ops ASig} {Γ} (x : Expr O' Γ (resyncInpT ℓ Pt)) : Expr O' Γ PK :=
  .fst (.snd (.snd (.snd (.snd x))))
def rsyPq' {O' : Ops ASig} {Γ} (x : Expr O' Γ (resyncInpT ℓ Pt)) : Expr O' Γ (B 32) :=
  .fst (.snd (.snd (.snd (.snd (.snd x)))))
def rsyC {O' : Ops ASig} {Γ} (x : Expr O' Γ (resyncInpT ℓ Pt)) :
    Expr O' Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd x))))))
def rsyR {O' : Ops ASig} {Γ} (x : Expr O' Γ (resyncInpT ℓ Pt)) :
    Expr O' Γ (.opt (kDecOutT ℓ Pt)) :=
  .snd (.snd (.snd (.snd (.snd (.snd (.snd x))))))

/-- Atomic computation implementing `semResyncHookS` with `fig8IdSemHook none`. -/
def semResyncAtomicC (idA idB : IdentityKey) (L qep T : ℕ) {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (resyncInpT ℓ Pt)) :
    Comp AOps FIface Γ (recvOutT ℓ Pt) :=
  .bind (.ret inpE)
    (.caseOpt (rsyR .v0)
      (.ret (.pair (.some (.inl .unit)) (rsySC .v0)))
      (.bind (.query SMTag.dl (.pair (rsyQ .v1) (rsyC .v1)))
        (.caseOpt .v0
          (.ret (.pair (.some (.inl .unit)) (rsySC .v2)))
          (.caseSum .v0
            (.ret (.pair (.some (.inl .unit)) (rsySC .v4)))
            (.bind
              (onAcceptPureAtomicC L qep
                (.pair (scBase (rsySC .v4))
                  (.pair (rsyQ .v4)
                    (.pair (rsyW .v4)
                      (.pair (.bool true)
                        (.pair (.fst .v3)
                          (.pair (.fst (.snd .v3))
                            (.pair (.snd (.snd (.snd .v3)))
                              (.pair (rsyCi? .v4)
                                (.pair (rsyPk .v4) (rsyPq' .v4)))))))))))
              (.ret
                (.pair (.fst .v0)
                  (scMk (.snd .v0)
                    (scUpdateKeptRecv idA idB T (rsySC .v5) (rsyQ .v5) (rsyC .v5))
                    (scSent (rsySC .v5))
                    (scSnaps (rsySC .v5))))))))))

def fwaSC {O' : Ops ASig} {Γ} (x : Expr O' Γ (fwdAnsInpT ℓ Pt)) : Expr O' Γ (simFullT ℓ Pt) :=
  .fst x
def fwaQ {O' : Ops ASig} {Γ} (x : Expr O' Γ (fwdAnsInpT ℓ Pt)) : Expr O' Γ .bool :=
  .fst (.snd x)
def fwaW {O' : Ops ASig} {Γ} (x : Expr O' Γ (fwdAnsInpT ℓ Pt)) : Expr O' Γ (B 32) :=
  .fst (.snd (.snd x))
def fwaIsDel {O' : Ops ASig} {Γ} (x : Expr O' Γ (fwdAnsInpT ℓ Pt)) : Expr O' Γ .bool :=
  .fst (.snd (.snd (.snd x)))
def fwaCi? {O' : Ops ASig} {Γ} (x : Expr O' Γ (fwdAnsInpT ℓ Pt)) : Expr O' Γ (.opt .nat) :=
  .fst (.snd (.snd (.snd (.snd x))))
def fwaPk {O' : Ops ASig} {Γ} (x : Expr O' Γ (fwdAnsInpT ℓ Pt)) : Expr O' Γ PK :=
  .fst (.snd (.snd (.snd (.snd (.snd x)))))
def fwaPq' {O' : Ops ASig} {Γ} (x : Expr O' Γ (fwdAnsInpT ℓ Pt)) : Expr O' Γ (B 32) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd x))))))
def fwaC' {O' : Ops ASig} {Γ} (x : Expr O' Γ (fwdAnsInpT ℓ Pt)) :
    Expr O' Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)) :=
  .snd (.snd (.snd (.snd (.snd (.snd (.snd x))))))

def isResAcceptedE {O' : Ops ASig} {Γ} (resE : Expr O' Γ (.opt (smRrFullT ℓ Pt))) :
    Expr O' Γ .bool :=
  .caseOpt resE (.bool false) (.caseSum .v0 (.bool false) (.bool true))

/-- Atomic computation implementing `semFwdAnswerHookS` with `fig8IdSemHook none`. -/
def semFwdAnswerAtomicC (idA idB : IdentityKey) (L qep T : ℕ) {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (fwdAnsInpT ℓ Pt)) :
    Comp AOps FIface Γ (recvOutT ℓ Pt) :=
  .bind (.ret inpE)
    (.bind
      (Comp.ite (t := .opt (smRrFullT ℓ Pt))
        (inTransitHonestE L (fwaSC .v0) (fwaQ .v0) (fwaC' .v0))
        (Comp.query (I := FIface) SMTag.dl (.pair (fwaQ .v0) (fwaC' .v0)))
        (Comp.query (I := FIface) SMTag.ij (.pair (fwaQ .v0) (fwaC' .v0))))
      (.bind
        (onAnswerPureAtomicC L qep
          (.pair (scBase (fwaSC .v1))
            (.pair (fwaQ .v1)
              (.pair (fwaW .v1)
                (.pair (fwaIsDel .v1)
                  (.pair (fwaCi? .v1)
                    (.pair (fwaPk .v1)
                      (.pair (fwaPq' .v1) .v0))))))))
        (.ret
          (let sC2 := fwaSC .v2
           let keptNew :=
             .ite (isResAcceptedE .v1)
               (scUpdateKeptRecv idA idB T sC2 (fwaQ .v2) (fwaC' .v2))
               (scKept sC2)
           .pair (.fst .v0)
             (scMk (.snd .v0) keptNew (scSent sC2) (scSnaps sC2))))))

def fwhSC {O' : Ops ASig} {Γ} (x : Expr O' Γ (fwdHookInpT ℓ Pt)) : Expr O' Γ (simFullT ℓ Pt) :=
  .fst x
def fwhQ {O' : Ops ASig} {Γ} (x : Expr O' Γ (fwdHookInpT ℓ Pt)) : Expr O' Γ .bool :=
  .fst (.snd x)
def fwhW {O' : Ops ASig} {Γ} (x : Expr O' Γ (fwdHookInpT ℓ Pt)) : Expr O' Γ (B 32) :=
  .fst (.snd (.snd x))
def fwhIsDel {O' : Ops ASig} {Γ} (x : Expr O' Γ (fwdHookInpT ℓ Pt)) : Expr O' Γ .bool :=
  .fst (.snd (.snd (.snd x)))
def fwhCi? {O' : Ops ASig} {Γ} (x : Expr O' Γ (fwdHookInpT ℓ Pt)) : Expr O' Γ (.opt .nat) :=
  .fst (.snd (.snd (.snd (.snd x))))
def fwhPk {O' : Ops ASig} {Γ} (x : Expr O' Γ (fwdHookInpT ℓ Pt)) : Expr O' Γ PK :=
  .fst (.snd (.snd (.snd (.snd (.snd x)))))
def fwhPq' {O' : Ops ASig} {Γ} (x : Expr O' Γ (fwdHookInpT ℓ Pt)) : Expr O' Γ (B 32) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd x))))))
def fwhHonest {O' : Ops ASig} {Γ} (x : Expr O' Γ (fwdHookInpT ℓ Pt)) :
    Expr O' Γ (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd x)))))))
def fwhC' {O' : Ops ASig} {Γ} (x : Expr O' Γ (fwdHookInpT ℓ Pt)) :
    Expr O' Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)) :=
  .snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd x)))))))

def fwhToAnsInp {O' : Ops ASig} {Γ} (x : Expr O' Γ (fwdHookInpT ℓ Pt)) :
    Expr O' Γ (fwdAnsInpT ℓ Pt) :=
  .pair (fwhSC x)
    (.pair (fwhQ x)
      (.pair (fwhW x)
        (.pair (fwhIsDel x)
          (.pair (fwhCi? x)
            (.pair (fwhPk x)
              (.pair (fwhPq' x) (fwhC' x)))))))

/-- Atomic computation implementing `semFwdHookS` with `fig8IdSemHook none`. -/
def semFwdHookAtomicC (idA idB : IdentityKey) (L qep B_cap T Kc : ℕ) {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (fwdHookInpT ℓ Pt)) :
    Comp AOps FIface Γ (recvOutT ℓ Pt) :=
  .bind (.ret inpE)
    (.caseOpt (fwhHonest .v0)
      (semFwdAnswerAtomicC idA idB L qep T (fwhToAnsInp .v0))
      (.ite
        (.and (.not (eqFig8CAtomicE .v0 (fwhC' .v1)))
          (.and (fwhIsDel .v1) (.not (mSafeInjE (ssMir (scBase (fwhSC .v1)))))))
        (.bind
          (evalCKSAtomicC idA idB L B_cap T Kc
            (.pair (fwhSC .v1)
              (.pair (fwhQ .v1)
                (.pair (fwhW .v1) (.pair .v0 (fwhC' .v1))))))
          (.caseOpt .v0
            (.ret (.pair (.some (.inl .unit)) (fwhSC .v2)))
            (semResyncAtomicC idA idB L qep T
              (.pair (fwhSC .v3)
                (.pair (fwhQ .v3)
                  (.pair (fwhW .v3)
                    (.pair (fwhCi? .v3)
                      (.pair (fwhPk .v3)
                        (.pair (fwhPq' .v3)
                          (.pair .v2 .v0))))))))))
        (semFwdAnswerAtomicC idA idB L qep T (fwhToAnsInp .v1))))

def poPq' {O' : Ops ASig} {Γ} (p : Expr O' Γ (parseOutT ℓ Pt)) : Expr O' Γ (B 32) :=
  .fst p
def poI {O' : Ops ASig} {Γ} (p : Expr O' Γ (parseOutT ℓ Pt)) : Expr O' Γ .nat :=
  .fst (.snd p)
def poPk {O' : Ops ASig} {Γ} (p : Expr O' Γ (parseOutT ℓ Pt)) : Expr O' Γ PK :=
  .fst (.snd (.snd p))
def poT? {O' : Ops ASig} {Γ} (p : Expr O' Γ (parseOutT ℓ Pt)) : Expr O' Γ (.opt PtT) :=
  .fst (.snd (.snd (.snd p)))
def poLct {O' : Ops ASig} {Γ} (p : Expr O' Γ (parseOutT ℓ Pt)) :
    Expr O' Γ (lctT (ℓ := ℓ) (Pt := Pt)) :=
  .snd (.snd (.snd (.snd p)))

def rsmSC {O' : Ops ASig} {Γ} (x : Expr O' Γ (recvSameInpT ℓ Pt)) : Expr O' Γ (simFullT ℓ Pt) :=
  .fst x
def rsmQ {O' : Ops ASig} {Γ} (x : Expr O' Γ (recvSameInpT ℓ Pt)) : Expr O' Γ .bool :=
  .fst (.snd x)
def rsmW {O' : Ops ASig} {Γ} (x : Expr O' Γ (recvSameInpT ℓ Pt)) : Expr O' Γ (B 32) :=
  .fst (.snd (.snd x))
def rsmIsDel {O' : Ops ASig} {Γ} (x : Expr O' Γ (recvSameInpT ℓ Pt)) : Expr O' Γ .bool :=
  .fst (.snd (.snd (.snd x)))
def rsmParsed {O' : Ops ASig} {Γ} (x : Expr O' Γ (recvSameInpT ℓ Pt)) :
    Expr O' Γ (parseOutT ℓ Pt) :=
  .fst (.snd (.snd (.snd (.snd x))))
def rsmHonest {O' : Ops ASig} {Γ} (x : Expr O' Γ (recvSameInpT ℓ Pt)) :
    Expr O' Γ (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))) :=
  .fst (.snd (.snd (.snd (.snd (.snd x)))))
def rsmCi {O' : Ops ASig} {Γ} (x : Expr O' Γ (recvSameInpT ℓ Pt)) : Expr O' Γ .nat :=
  .snd (.snd (.snd (.snd (.snd (.snd x)))))

/-- Atomic computation implementing the existing-chain receive branch `semRecvSameBranch`. -/
def recvSameBranchAtomicC (idA idB : IdentityKey) (L qep B_cap T Kc : ℕ) {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (recvSameInpT ℓ Pt)) :
    Comp AOps FIface Γ (recvOutT ℓ Pt) :=
  .bind (.ret inpE)
    (let gE := getChainDE (pGet (ssChains (scBase (rsmSC .v0))) (rsmQ .v0)) (rsmCi .v0)
     let p0 := rsmParsed .v0
     .ite (ghostRejectsE gE (poI p0))
       (.ret (.pair (.some (.inl .unit)) (rsmSC .v0)))
       (semFwdHookAtomicC idA idB L qep B_cap T Kc
         (.pair (rsmSC .v0)
           (.pair (rsmQ .v0)
             (.pair (rsmW .v0)
               (.pair (rsmIsDel .v0)
                 (.pair (.some (rsmCi .v0))
                   (.pair (poPk p0)
                     (.pair (poPq' p0)
                       (.pair (rsmHonest .v0)
                         (mkCE (rsmHonest .v0) (.fst (.snd gE)) (poT? p0) (poLct p0))))))))))))

abbrev recvNewSiteCtx (ℓ : ℕ) (Pt : Type) (Γ : List (Ty (atomicSig ℓ Pt))) :
    List (Ty (atomicSig ℓ Pt)) :=
  recvNewInpT ℓ Pt ::
    .opt (fig8CtT (ℓ := ℓ) (Pt := Pt)) ::
      parseOutT ℓ Pt :: .opt (parseOutT ℓ Pt) :: Γ

/-- Atomic computation implementing `semRecvHookS`, parameterized by `newBranchC` for a new chain. -/
def recvHookOfNewAtomicC (idA idB : IdentityKey) (L qep B_cap T Kc : ℕ) {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt))
    (qBE : Expr AOps Γ .bool)
    (wE : Expr AOps Γ (B 32))
    (isDelE : Expr AOps Γ .bool)
    (newBranchC : Comp AOps FIface
      (recvNewSiteCtx ℓ Pt (.prod (simFullT ℓ Pt) (.prod .bool (.prod (B 32) .bool)) :: Γ))
      (recvOutT ℓ Pt)) :
    Comp AOps FIface Γ (recvOutT ℓ Pt) :=
  .bind (.ret (.pair sCE (.pair qBE (.pair wE isDelE))))
    (let sC0 : Expr AOps _ (simFullT ℓ Pt) := .fst .v0
     let qB0 : Expr AOps _ .bool := .fst (.snd .v0)
     let w0 : Expr AOps _ (B 32) := .fst (.snd (.snd .v0))
     let isDel0 : Expr AOps _ .bool := .snd (.snd (.snd .v0))
     .ite (recvRefuseE L sC0 qB0 w0 isDel0)
       (.ret (.pair .none sC0))
       (.bind
         (parseRecvAtomicC FIface idA idB (2 ^ 32) qB0 (pGet (ssPq (scBase sC0)) qB0) w0)
         (.caseOpt .v0
           (.ret (.pair (.some (.inl .unit)) (.fst .v1)))
           (.bind
             (.ret (honestFindE L (.fst .v2) (.fst (.snd .v2)) (.fst (.snd (.snd .v2)))))
             (.caseOpt (findChainIdxE (pGet (ssChains (scBase (.fst .v3))) (.fst (.snd .v3))) (poPk .v1))
               (.bind
                 (.ret
                   (.pair (.fst .v3)
                     (.pair (.fst (.snd .v3))
                       (.pair (.fst (.snd (.snd .v3)))
                         (.pair (.snd (.snd (.snd .v3))) (.pair .v1 .v0))))))
                 newBranchC)
               (recvSameBranchAtomicC idA idB L qep B_cap T Kc
                 (.pair (.fst .v4)
                   (.pair (.fst (.snd .v4))
                     (.pair (.fst (.snd (.snd .v4)))
                       (.pair (.snd (.snd (.snd .v4))) (.pair .v2 (.pair .v1 .v0))))))))))))

def wrapRecvSmOut {O' : Ops ASig} {Γ} (outE : Expr O' Γ (recvOutT ℓ Pt)) :
    Expr O' Γ (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)) :=
  .pair (.pair .none (.pair (.fst outE) .none)) (.snd outE)

end Programs

/-! ## Static cost and description bounds -/

section StaticBounds

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
variable {ℓ : ℕ} {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
variable {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

set_option linter.unusedSimpArgs false

open _root_.ReductionDsl (fsRecvStT fsSendStT fig8StT fig8HdrT ckaStT wireSaltCtT IdKey
  U32 U64 BV256 PB bits_mono AtomicPureOp AtomicSymOp)
open CryptoGames.SM (sendsInE)
open CryptoGames.LibsignalSession (maxForwardJumps)
open CryptoVerification.E2E (toU8 vecU8)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost
  (varIdx atomicTyDescBits atomicSortDescBits atomicPureOpDescBits atomicSymOpDescBits)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8State
  (bits_zero bits_eq_of_bounds bits_le_of_lt_pow atomicFig8OpDescBits runFig8WithIds
   cost_runFig8WithIds descBits_runFig8WithIds cost_eLet descBits_eLet cost_eMapOpt descBits_eMapOpt
   cost_sOpPure descBits_sOpPure cost_mSafeInjE mSafeInjE_descBits_le
   cost_mInTransitE mInTransitE_descBits_le cost_mAcceptE mAcceptE_descBits_le
   cost_mChallContainsE mChallContainsE_descBits_le cost_mTrivialE mTrivialE_descBits_le
   cost_ssSetMirWin ssSetMirWin_descBits_le ghostAcceptC_queries ghostAcceptC_cost
   ghostAcceptC_descBits_le cost_ghostRejectsE ghostRejectsE_descBits_le
   cost_pushChainE pushChainE_descBits_le cost_findChainIdxE findChainIdxE_descBits_le
   cost_getChainDE getChainDE_descBits_le modifyChainAcceptC_queries modifyChainAcceptC_cost
   modifyChainAcceptC_descBits_le atomicTyDescBits_fig8StT atomicTyDescBits_fsRecvStT
   atomicTyDescBits_simRecT atomicTyDescBits_simMirT atomicTyDescBits_simBaseT
   atomicTyDescBits_simFullT atomicTyDescBits_fig8CtT atomicTyDescBits_ghostChainT
   atomicTyDescBits_keptT atomicTyDescBits_snapT atomicTyDescBits_sentEntryT atomicTyDescBits_posTy)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SpqrDesc
  (small_bits_bounds bits_mul_le_add bits_clampB_le_budget bits_skipB_le_budget
   bits_L_le_budget bits_qep1_le_budget bits_add_le
   lPubOfExpr_descBits_le unitsPowExpr_descBits_le chainGenExpr_descBits_le
   ckaRecvExpr_descBits_le prngUpExpr_descBits_le)
open Computational.Proofs.ReductionDsl.Fig8Atomic
  (opPure opPtEncPk opSym fsRecvExpr fsRecvExpr_cost ckaRecvExpr ckaRecvExpr_cost
   prngUpExpr prngUpExpr_cost appAux aeadDecExpr pkLitExpr optBytesEqExpr)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept
  (f8Mk f8Id f8Root f8VS f8VR f8Gamma f8Cur f8Tcur fsReceiveAtomicE fig8ReceiveAtomicE
   sanRSAtomicE sanRSAtomicE_cost sanRSAtomicE_descBits_le sanGammaAtomicE sanGammaAtomicE_descBits_le
   sanAtAtomicE sanAtAtomicE_cost senderToFreshVrAtomicE senderToFreshVrAtomicE_cost
   senderToFreshVrAtomicE_descBits_le eqFig8CAtomicE_cost eqFig8CAtomicE_descBits_le)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8Crypto
  (cost_orElseOptE descBits_orElseOptE knownSeedDecryptAtomicFastC_queries knownSeedDecryptAtomicFastC_cost
   knownSeedDecryptAtomicFastC_descBits_le lctSaltEqOfLctAtomicE_cost lctSaltEqOfLctAtomicE_descBits_le
   injOKAtomicE_cost injOKAtomicE_descBits_le parseRecvAtomicC_queries parseRecvAtomicC_cost
   parseRecvAtomicC_descBits_le)

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
local notation "FIface" => fig8SmIface ℓ Pt
local notation "ADesc" => atomicSessionOpDescBits (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
  (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
local notation "FOps" => _root_.ReductionDsl.atomicFig8Ops ℓ Pt C Dh encPt encT lam
local notation "FDesc" => atomicFig8OpDescBits (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh)
  (encPt := encPt) (encT := encT) (lam := lam)

@[local simp] private theorem rb_c0 : bits 0 = 1 := bits_zero
@[local simp] private theorem rb_c1 : bits 1 = 1 := small_bits_bounds.2.1
@[local simp] private theorem rb_c2 : bits 2 = 2 := small_bits_bounds.2.2.1
@[local simp] private theorem rb_c3 : bits 3 = 2 := small_bits_bounds.2.2.2.1
@[local simp] private theorem rb_c4 : bits 4 = 3 := small_bits_bounds.2.2.2.2.1
@[local simp] private theorem rb_c5 : bits 5 = 3 := small_bits_bounds.2.2.2.2.2.1
@[local simp] private theorem rb_c6 : bits 6 = 3 := small_bits_bounds.2.2.2.2.2.2.1
@[local simp] private theorem rb_c7 : bits 7 = 3 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
@[local simp] private theorem rb_c8 : bits 8 = 4 := small_bits_bounds.2.2.2.2.2.2.2.1
@[local simp] private theorem rb_c32 : bits 32 = 6 := small_bits_bounds.2.2.2.2.2.2.2.2.2.2.1
@[local simp] private theorem rb_p8 : bits ((8 : ℕ+) : ℕ) = 4 := rb_c8
@[local simp] private theorem rb_p32 : bits ((32 : ℕ+) : ℕ) = 6 := rb_c32
@[local simp] private theorem rb_mfj : bits maxForwardJumps = 15 := small_bits_bounds.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
@[local simp] private theorem rb_232 : bits (2 ^ 32) = 33 := small_bits_bounds.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
private theorem bits_le_succ_nat (n : ℕ) : bits n ≤ n + 1 := by
  have h := bits_add_le 0 n; simpa [rb_c0, Nat.add_comm] using h

omit [SampleableType Pt] in private theorem fsRecvExpr_descBits_tight (B0 Bmax : ℕ) :
    atomicExprDescBits FDesc (fsRecvExpr ℓ Pt C Dh encPt encT lam B0 Bmax) ≤
      6 * bits B0 + 4 * bits Bmax + 5605 := by
  let inT : Ty ASig := .prod fsRecvStT (.prod fig8HdrT lctT)
  let Γ₀ : List (Ty ASig) := [inT, .prod IdKey IdKey]
  let Γ₁ : List (Ty ASig) := [lpubT, inT, .prod IdKey IdKey]
  have hlpub := lPubOfExpr_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh) (encPt := encPt) (encT := encT) (lam := lam) (Γ := Γ₀) (.snd (.snd (.snd (.var .zero))))
  have hpow := unitsPowExpr_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh) (encPt := encPt) (encT := encT) (lam := lam) 15 (Γ := Γ₁)
  have hcg1 := chainGenExpr_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh) (encPt := encPt) (encT := encT) (lam := lam) (Γ := .unit :: fsRecvStT :: Γ₁) (.fst (.var (.succ .zero)))
  have hcg2 := chainGenExpr_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh) (encPt := encPt) (encT := encT) (lam := lam) (Γ := fsRecvStT :: Γ₁) (.fst (.var .zero))
  have hdk : CryptoGames.Ratchet.LibsignalInst.dummyKey.bytes.toList.length = 32 := rfl
  dsimp only [fsRecvExpr, appAux, aeadDecExpr, pkLitExpr, optBytesEqExpr, Expr.renameM,
    _root_.ReductionDsl.liftRen, _root_.ReductionDsl.atomicFig8Ops, _root_.ReductionDsl.atomicFsOps,
    _root_.ReductionDsl.atomicGroupOps, _root_.ReductionDsl.Ops.sum,
    _root_.ReductionDsl.atomicPureOps, _root_.ReductionDsl.atomicPtEncOps,
    _root_.ReductionDsl.atomicSymOps, wireSaltCtT, U64, _root_.ReductionDsl.BV128,
    Sum.elim_inl, Sum.elim_inr, AtomicPureOp.dom, AtomicSymOp.dom, opPure, opPtEncPk, opSym]
    at hlpub hpow hcg1 hcg2 ⊢
  simp only [inT, Γ₀, Γ₁, hdk, fsRecvStT, lpubT, PlainT, _root_.ReductionDsl.B, U32, BV256, vecU8, toU8,
    atomicExprDescBits, atomicFig8OpDescBits, atomicTyDescBits, atomicSortDescBits,
    atomicSymOpDescBits, atomicPureOpDescBits, List.length_map, Vector.length_toList,
    List.length_replicate, List.length_nil, varIdx, Nat.reduceAdd,
    rb_c0, rb_c1, rb_c2, rb_c3, rb_c4, rb_c5, rb_c6, rb_c7, rb_c8, rb_c32, rb_p8, rb_p32,
    rb_mfj] at hlpub hpow hcg1 hcg2 ⊢
  omega

local notation "runIds" => runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
local notation "fsRecvE" => fsReceiveAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
local notation "f8RecvE" => fig8ReceiveAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
local notation "sanAtE" => sanAtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
local notation "sanGamE" => sanGammaAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
local notation "eqCtE" => eqFig8CAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)

omit [SampleableType Pt] in private theorem fsReceiveAtomicE_cost_tight (idA idB : IdentityKey) (B0 B : ℕ) {Γ : List (Ty ASig)}
    (vE : Expr AOps Γ (fsRecvStT (ℓ := ℓ) (Pt := Pt))) (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (fsRecvE idA idB B0 B vE cE).cost ≤ vE.cost + cE.cost + 20 * B0 + 3 * bits B + 16 * (ℓ / 32) + 2200300 := by
  have hr := cost_runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB (fsRecvExpr ℓ Pt C Dh encPt encT lam B0 B) (.pair vE cE)
  have hf := fsRecvExpr_cost ℓ Pt C Dh encPt encT lam B0 B
  simp only [fsReceiveAtomicE, Expr.cost] at hr ⊢; omega

omit [SampleableType Pt] in private theorem fsReceiveAtomicE_descBits_tight (idA idB : IdentityKey) (B0 B : ℕ) {Γ : List (Ty ASig)}
    (vE : Expr AOps Γ (fsRecvStT (ℓ := ℓ) (Pt := Pt))) (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    atomicExprDescBits ADesc (fsRecvE idA idB B0 B vE cE) ≤
      atomicExprDescBits ADesc vE + atomicExprDescBits ADesc cE + 6 * bits B0 + 4 * bits B + 6620 := by
  have hr := descBits_runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ) (fsRecvExpr ℓ Pt C Dh encPt encT lam B0 B) (.pair vE cE)
  have hf := fsRecvExpr_descBits_tight (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh) (encPt := encPt) (encT := encT) (lam := lam) B0 B
  simp only [fsReceiveAtomicE, atomicExprDescBits] at hr ⊢; omega

omit [SampleableType Pt] in private theorem fig8ReceiveAtomicE_cost_tight (idA idB : IdentityKey) (B0 B : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (f8RecvE idA idB B0 B stE cE).cost ≤ stE.cost + cE.cost + 20 * B0 + 5 * bits B + 16 * (ℓ / 32) + 2320000 := by
  let Γ1 := Ty.prod (fig8StT (ℓ := ℓ) (Pt := Pt)) (fig8CtT (ℓ := ℓ) (Pt := Pt)) :: Γ
  let Γ2 := PtT (ℓ := ℓ) (Pt := Pt) :: Γ1; let Γ3 := Ty.prod (ckaStT (ℓ := ℓ) (Pt := Pt)) PtT :: Γ2
  let Γ4 := fsRecvStT (ℓ := ℓ) (Pt := Pt) :: fig8StT (ℓ := ℓ) (Pt := Pt) :: Γ1
  have hcka := cost_runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ2) (ckaRecvExpr ℓ Pt C Dh encPt encT lam) (.pair (f8Gamma (.fst .v1)) .v0)
  have hup := cost_runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ3) (prngUpExpr ℓ Pt C Dh encPt encT lam) (.pair (f8Root (.fst .v2)) (.snd .v0))
  have hfs := fsReceiveAtomicE_cost_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB B0 B (Γ := Γ4) .v0 (.snd .v2)
  have hc_cka := ckaRecvExpr_cost ℓ Pt C Dh encPt encT lam; have hc_up := prngUpExpr_cost ℓ Pt C Dh encPt encT lam
  unfold fig8ReceiveAtomicE
  dsimp only [f8Mk, f8Id, f8Root, f8VS, f8VR, f8Gamma, f8Cur, f8Tcur, orE, sendsInE, Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hcka hup hfs ⊢
  generalize runIds idA idB (Γ := Γ2) (ckaRecvExpr ℓ Pt C Dh encPt encT lam) _ = e_rcka at hcka ⊢
  generalize runIds idA idB (Γ := Γ3) (prngUpExpr ℓ Pt C Dh encPt encT lam) _ = e_rup at hup ⊢
  generalize fsRecvE idA idB B0 B (Γ := Γ4) _ _ = e_rfs at hfs ⊢
  dsimp only [cost_eLet, Expr.cost] at hcka hup hfs ⊢; simp only [rb_c0, rb_c1, rb_c2] at hcka hup hfs ⊢; omega

omit [SampleableType Pt] in private theorem fig8ReceiveAtomicE_descBits_tight (idA idB : IdentityKey) (B0 B : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    atomicExprDescBits ADesc (f8RecvE idA idB B0 B stE cE) ≤
      atomicExprDescBits ADesc stE + atomicExprDescBits ADesc cE + 6 * bits B0 + 8 * bits B + 11500 := by
  let Γ1 := Ty.prod (fig8StT (ℓ := ℓ) (Pt := Pt)) (fig8CtT (ℓ := ℓ) (Pt := Pt)) :: Γ
  let Γ2 := PtT (ℓ := ℓ) (Pt := Pt) :: Γ1; let Γ3 := Ty.prod (ckaStT (ℓ := ℓ) (Pt := Pt)) PtT :: Γ2
  let Γ4 := fsRecvStT (ℓ := ℓ) (Pt := Pt) :: fig8StT (ℓ := ℓ) (Pt := Pt) :: Γ1
  have hcka := descBits_runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ2) (ckaRecvExpr ℓ Pt C Dh encPt encT lam) (.pair (f8Gamma (.fst .v1)) .v0)
  have hup := descBits_runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ3) (prngUpExpr ℓ Pt C Dh encPt encT lam) (.pair (f8Root (.fst .v2)) (.snd .v0))
  have hfs := fsReceiveAtomicE_descBits_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB B0 B (Γ := Γ4) .v0 (.snd .v2)
  have hd_cka := ckaRecvExpr_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh) (encPt := encPt) (encT := encT) (lam := lam)
  have hd_up := prngUpExpr_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh) (encPt := encPt) (encT := encT) (lam := lam)
  have ht_f8 := atomicTyDescBits_fig8StT (ℓ := ℓ) (Pt := Pt)
  dsimp only [fig8ReceiveAtomicE, f8Mk, f8Id, f8Root, f8VS, f8VR, f8Gamma, f8Cur, f8Tcur, orE, sendsInE, Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hcka hup hfs ⊢
  generalize runIds idA idB (Γ := Γ2) (ckaRecvExpr ℓ Pt C Dh encPt encT lam) _ = e_rcka at hcka ⊢
  generalize runIds idA idB (Γ := Γ3) (prngUpExpr ℓ Pt C Dh encPt encT lam) _ = e_rup at hup ⊢
  generalize fsRecvE idA idB B0 B (Γ := Γ4) _ _ = e_rfs at hfs ⊢
  simp only [descBits_eLet, lpubT, PlainT, _root_.ReductionDsl.B, U32, BV256, varIdx, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, Nat.reduceAdd, rb_c0, rb_c1, rb_c2, rb_c3, rb_c32, rb_p32] at hcka hup hfs ⊢
  omega

omit [SampleableType Pt] in private theorem sanAtAtomicE_descBits_tight (T : ℕ) {Γ : List (Ty ASig)}
    (tE : Expr AOps Γ .nat) (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) :
    atomicExprDescBits ADesc (sanAtE T tE stE) ≤
      atomicExprDescBits ADesc tE + atomicExprDescBits ADesc stE + 2 * bits T + 1250 := by
  let tP := Ty.prod .nat (fig8StT (ℓ := ℓ) (Pt := Pt))
  have hrs := sanRSAtomicE_descBits_le (ℓ := ℓ) (Pt := Pt) T ADesc (Γ := fsRecvStT (ℓ := ℓ) (Pt := Pt) :: tP :: Γ) .v0
  have hγ := sanGammaAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := tP :: Γ) (.snd .v0)
  have ht_fsR := atomicTyDescBits_fsRecvStT (ℓ := ℓ) (Pt := Pt)
  dsimp only [sanAtAtomicE, f8Mk, f8Id, f8Root, f8VS, f8VR, f8Cur, f8Tcur, Expr.v0] at hrs hγ ⊢
  generalize sanRSAtomicE (ℓ := ℓ) (Pt := Pt) (O' := AOps) T _ = e_rs at hrs ⊢
  generalize sanGamE _ = e_g at hγ ⊢
  simp only [descBits_eLet, varIdx, atomicExprDescBits, rb_c0] at hrs hγ ⊢; omega

omit [SampleableType Pt] in private theorem keptRecvAtomicE_cost_tight (idA idB : IdentityKey) (T : ℕ) {Γ : List (Ty ASig)}
    (kE : Expr AOps Γ (keptT ℓ Pt)) (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (keptRecvAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB T kE cE).cost ≤
      kE.cost + cE.cost + 21 * T + 16 * (ℓ / 32) + 2420000 := by
  let ΓN := fsRecvStT (ℓ := ℓ) (Pt := Pt) :: .prod (keptT ℓ Pt) (fig8CtT (ℓ := ℓ) (Pt := Pt)) :: Γ
  let ΓS := fig8StT (ℓ := ℓ) (Pt := Pt) :: .prod (keptT ℓ Pt) (fig8CtT (ℓ := ℓ) (Pt := Pt)) :: Γ
  have hrs := sanRSAtomicE_cost (ℓ := ℓ) (Pt := Pt) (O' := AOps) T (Γ := ΓN) .v0
  have hfs := fsReceiveAtomicE_cost_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB T 0 (Γ := ΓN) (sanRSAtomicE T .v0) (.snd .v1)
  have hat := sanAtAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) T (Γ := ΓS) (.fst (.fst (.snd .v1))) .v0
  have hf8 := fig8ReceiveAtomicE_cost_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB T 0 (Γ := ΓS) (sanAtE T (.fst (.fst (.snd .v1))) .v0) (.snd .v1)
  have hbT : bits T ≤ T + 1 := bits_le_succ_nat T
  dsimp only [keptRecvAtomicE, f8VR, Expr.v0, Expr.v1, Expr.v2] at hrs hfs hat hf8 ⊢
  generalize fsRecvE idA idB T 0 (Γ := ΓN) _ _ = e_fs at hfs ⊢
  generalize f8RecvE idA idB T 0 (Γ := ΓS) _ _ = e_f8 at hf8 ⊢
  generalize sanRSAtomicE (ℓ := ℓ) (Pt := Pt) (O' := AOps) T (Γ := ΓN) _ = e_rs at hrs hfs ⊢
  generalize sanAtE T (Γ := ΓS) _ _ = e_at at hat hf8 ⊢
  dsimp only [cost_eLet, Expr.cost] at hrs hfs hat hf8 ⊢; simp only [rb_c0] at hrs hfs hat hf8 ⊢; omega

omit [SampleableType Pt] in private theorem keptRecvAtomicE_descBits_tight (idA idB : IdentityKey) (T : ℕ) {Γ : List (Ty ASig)}
    (kE : Expr AOps Γ (keptT ℓ Pt)) (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    atomicExprDescBits ADesc (keptRecvAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB T kE cE) ≤
      atomicExprDescBits ADesc kE + atomicExprDescBits ADesc cE + 16 * bits T + 20350 := by
  let ΓN := fsRecvStT (ℓ := ℓ) (Pt := Pt) :: .prod (keptT ℓ Pt) (fig8CtT (ℓ := ℓ) (Pt := Pt)) :: Γ
  let ΓS := fig8StT (ℓ := ℓ) (Pt := Pt) :: .prod (keptT ℓ Pt) (fig8CtT (ℓ := ℓ) (Pt := Pt)) :: Γ
  have hrs := sanRSAtomicE_descBits_le (ℓ := ℓ) (Pt := Pt) T ADesc (Γ := ΓN) .v0
  have hfs := fsReceiveAtomicE_descBits_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB T 0 (Γ := ΓN) (sanRSAtomicE T .v0) (.snd .v1)
  have hat := sanAtAtomicE_descBits_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) T (Γ := ΓS) (.fst (.fst (.snd .v1))) .v0
  have hf8 := fig8ReceiveAtomicE_descBits_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB T 0 (Γ := ΓS) (sanAtE T (.fst (.fst (.snd .v1))) .v0) (.snd .v1)
  have ht_f8 := atomicTyDescBits_fig8StT (ℓ := ℓ) (Pt := Pt); have ht_fsR := atomicTyDescBits_fsRecvStT (ℓ := ℓ) (Pt := Pt)
  dsimp only [keptRecvAtomicE, f8VR, Expr.v0, Expr.v1, Expr.v2] at hrs hfs hat hf8 ⊢
  generalize fsRecvE idA idB T 0 (Γ := ΓN) _ _ = e_fs at hfs ⊢
  generalize f8RecvE idA idB T 0 (Γ := ΓS) _ _ = e_f8 at hf8 ⊢
  generalize sanRSAtomicE (ℓ := ℓ) (Pt := Pt) (O' := AOps) T (Γ := ΓN) _ = e_rs at hrs hfs ⊢
  generalize sanAtE T (Γ := ΓS) _ _ = e_at at hat hf8 ⊢
  simp only [descBits_eLet, varIdx, atomicExprDescBits, Nat.reduceAdd, rb_c0, rb_c1, rb_c2] at hrs hfs hat hf8 ⊢; omega

omit [SampleableType Pt] in private theorem keptEvalAtomicE_cost_tight (idA idB : IdentityKey) (T B : ℕ) {Γ : List (Ty ASig)}
    (kE : Expr AOps Γ (keptT ℓ Pt)) (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (keptEvalAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB T B kE cE).cost ≤
      kE.cost + cE.cost + 21 * T + 5 * bits B + 16 * (ℓ / 32) + 2420000 := by
  let ΓN := fsRecvStT (ℓ := ℓ) (Pt := Pt) :: .prod (keptT ℓ Pt) (fig8CtT (ℓ := ℓ) (Pt := Pt)) :: Γ
  let ΓS := fig8StT (ℓ := ℓ) (Pt := Pt) :: .prod (keptT ℓ Pt) (fig8CtT (ℓ := ℓ) (Pt := Pt)) :: Γ
  have hrs := sanRSAtomicE_cost (ℓ := ℓ) (Pt := Pt) (O' := AOps) T (Γ := ΓN) .v0
  have hfs := fsReceiveAtomicE_cost_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB T B (Γ := ΓN) (sanRSAtomicE T .v0) (.snd .v1)
  have hat := sanAtAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) T (Γ := ΓS) (.fst (.fst (.snd .v1))) .v0
  have hf8 := fig8ReceiveAtomicE_cost_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB T B (Γ := ΓS) (sanAtE T (.fst (.fst (.snd .v1))) .v0) (.snd .v1)
  have hbT : bits T ≤ T + 1 := bits_le_succ_nat T
  dsimp only [keptEvalAtomicE, Expr.v0, Expr.v1, Expr.v2] at hrs hfs hat hf8 ⊢
  generalize fsRecvE idA idB T B (Γ := ΓN) _ _ = e_fs at hfs ⊢
  generalize f8RecvE idA idB T B (Γ := ΓS) _ _ = e_f8 at hf8 ⊢
  generalize sanRSAtomicE (ℓ := ℓ) (Pt := Pt) (O' := AOps) T (Γ := ΓN) _ = e_rs at hrs hfs ⊢
  generalize sanAtE T (Γ := ΓS) _ _ = e_at at hat hf8 ⊢
  dsimp only [cost_eLet, Expr.cost] at hrs hfs hat hf8 ⊢; omega

omit [SampleableType Pt] in private theorem keptEvalAtomicE_descBits_tight (idA idB : IdentityKey) (T B : ℕ) {Γ : List (Ty ASig)}
    (kE : Expr AOps Γ (keptT ℓ Pt)) (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    atomicExprDescBits ADesc (keptEvalAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB T B kE cE) ≤
      atomicExprDescBits ADesc kE + atomicExprDescBits ADesc cE + 16 * bits T + 12 * bits B + 20350 := by
  let tKC := Ty.prod (keptT ℓ Pt) (fig8CtT (ℓ := ℓ) (Pt := Pt))
  let ΓN := fsRecvStT (ℓ := ℓ) (Pt := Pt) :: tKC :: Γ; let ΓS := fig8StT (ℓ := ℓ) (Pt := Pt) :: tKC :: Γ
  have hrs := sanRSAtomicE_descBits_le (ℓ := ℓ) (Pt := Pt) T ADesc (Γ := ΓN) .v0
  have hfs := fsReceiveAtomicE_descBits_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB T B (Γ := ΓN) (sanRSAtomicE T .v0) (.snd .v1)
  have hat := sanAtAtomicE_descBits_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) T (Γ := ΓS) (.fst (.fst (.snd .v1))) .v0
  have hf8 := fig8ReceiveAtomicE_descBits_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB T B (Γ := ΓS) (sanAtE T (.fst (.fst (.snd .v1))) .v0) (.snd .v1)
  dsimp only [keptEvalAtomicE, Expr.v0, Expr.v1, Expr.v2] at hrs hfs hat hf8 ⊢
  generalize fsRecvE idA idB T B (Γ := ΓN) _ _ = e_fs at hfs ⊢
  generalize f8RecvE idA idB T B (Γ := ΓS) _ _ = e_f8 at hf8 ⊢
  generalize sanRSAtomicE (ℓ := ℓ) (Pt := Pt) (O' := AOps) T (Γ := ΓN) _ = e_rs at hrs hfs ⊢
  generalize sanAtE T (Γ := ΓS) _ _ = e_at at hat hf8 ⊢
  simp only [descBits_eLet, lpubT, PlainT, _root_.ReductionDsl.B, U32, BV256, varIdx, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, Nat.reduceAdd, rb_c0, rb_c1, rb_c2, rb_c32, rb_p32] at hrs hfs hat hf8 ⊢
  omega

omit [SampleableType Pt] in private theorem sentEvalAtomicE_cost_tight (idA idB : IdentityKey) (L B : ℕ) {Γ : List (Ty ASig)}
    (sentE : Expr AOps Γ (.list (sentEntryT ℓ Pt))) (cE c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (sentEvalAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB L B sentE cE c'E).cost ≤
      sentE.cost + cE.cost + c'E.cost + L * (ℓ / 16 + 230) + 3 * bits B + 16 * (ℓ / 32) + 2201000 := by
  let t0 := Ty.prod (.list (sentEntryT ℓ Pt)) (.prod (fig8CtT (ℓ := ℓ) (Pt := Pt)) (fig8CtT (ℓ := ℓ) (Pt := Pt)))
  let Γ1 := sentEntryT ℓ Pt :: t0 :: Γ
  have heq := eqFig8CAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ1) (.fst .v0) (.fst (.snd .v1))
  have hvr := senderToFreshVrAtomicE_cost (ℓ := ℓ) (Pt := Pt) (O' := AOps) (Γ := Γ1) (.snd .v0)
  have hfs := fsReceiveAtomicE_cost_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB 0 B (Γ := Γ1) (senderToFreshVrAtomicE (.snd .v0)) (.snd (.snd .v1))
  dsimp only [Expr.cost, Expr.v0, Expr.v1] at heq hvr
  have hmul : L * ((eqCtE (.fst (.v0 : Expr AOps Γ1 _)) (.fst (.snd .v1))).cost + 1) ≤ L * (ℓ / 16 + 230) :=
    Nat.mul_le_mul_left L (by dsimp only [Expr.v0, Expr.v1]; omega)
  dsimp only [sentEvalAtomicE, Expr.v0, Expr.v1, Expr.v2] at heq hvr hfs hmul ⊢
  generalize eqCtE _ _ = e_eq at heq hmul ⊢; generalize fsRecvE idA idB 0 B (Γ := Γ1) _ _ = e_fs at hfs ⊢
  generalize senderToFreshVrAtomicE (ℓ := ℓ) (Pt := Pt) (O' := AOps) (Γ := Γ1) _ = e_vr at hvr hfs ⊢
  dsimp only [cost_eLet, Expr.cost] at hfs ⊢; omega

omit [SampleableType Pt] in private theorem sentEvalAtomicE_descBits_tight (idA idB : IdentityKey) (L B : ℕ) {Γ : List (Ty ASig)}
    (sentE : Expr AOps Γ (.list (sentEntryT ℓ Pt))) (cE c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    atomicExprDescBits ADesc (sentEvalAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB L B sentE cE c'E) ≤
      atomicExprDescBits ADesc sentE + atomicExprDescBits ADesc cE + atomicExprDescBits ADesc c'E + 2 * bits L + 4 * bits B + 8550 := by
  let t0 := Ty.prod (.list (sentEntryT ℓ Pt)) (.prod (fig8CtT (ℓ := ℓ) (Pt := Pt)) (fig8CtT (ℓ := ℓ) (Pt := Pt)))
  let Γ1 := sentEntryT ℓ Pt :: t0 :: Γ
  have heq := eqFig8CAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ1) (.fst .v0) (.fst (.snd .v1))
  have hvr := senderToFreshVrAtomicE_descBits_le (ℓ := ℓ) (Pt := Pt) ADesc (Γ := Γ1) (.snd .v0)
  have hfs := fsReceiveAtomicE_descBits_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB 0 B (Γ := Γ1) (senderToFreshVrAtomicE (.snd .v0)) (.snd (.snd .v1))
  dsimp only [sentEvalAtomicE, Expr.v0, Expr.v1, Expr.v2] at heq hvr hfs ⊢
  generalize eqCtE _ _ = e_eq at heq ⊢; generalize fsRecvE idA idB 0 B (Γ := Γ1) _ _ = e_fs at hfs ⊢
  generalize senderToFreshVrAtomicE (ℓ := ℓ) (Pt := Pt) (O' := AOps) (Γ := Γ1) _ = e_vr at hvr hfs ⊢
  simp only [descBits_eLet, lpubT, PlainT, _root_.ReductionDsl.B, U32, BV256, varIdx, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, Nat.reduceAdd, rb_c0, rb_c1, rb_c2, rb_c32, rb_p32] at heq hvr hfs ⊢
  omega

private theorem bits_T_le_budget (q qep : ℕ) :
    bits (50000 * q) ≤ 16 + bits (ratchetCostBudget q (qep + 1) + (qep + 1)) := by
  have h1 := bits_skipB_le_budget q qep
  have h2 := bits_mul_le_add (k := 1) (a := 2) (b := 25000 * q) (by omega) (by omega)
  exact le_trans (bits_mono (b := 2 * (25000 * q)) (by omega)) (by omega)

private theorem bits_Kc_le_budget (q qep : ℕ) :
    bits (25001 * q + 25000) ≤ 49 + bits (ratchetCostBudget q (qep + 1) + (qep + 1)) := by
  have h1 := bits_clampB_le_budget q qep
  have h2 := bits_mul_le_add (k := 15) (a := 25001) (b := 2 ^ 32 + q + 2) (by omega) (by omega)
  exact le_trans (bits_mono (b := 25001 * (2 ^ 32 + q + 2)) (by omega)) (by omega)

private theorem bits_clampB_cost (q : ℕ) : bits (2 ^ 32 + q + 2) ≤ q + 35 := by
  have h1 := bits_add_le (2 ^ 32) (q + 2)
  rw [show 2 ^ 32 + q + 2 = 2 ^ 32 + (q + 2) by omega]
  simp only [rb_232] at h1; omega

private theorem onAcceptPureAtomicC_queries (L qep : ℕ) {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (onAcceptInpT ℓ Pt)) :
    (onAcceptPureAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) L qep inpE).queries (fun _ => 1) (fun _ => 0) = 0 := by
  simp [onAcceptPureAtomicC, Comp.queries, ghostAcceptC_queries, modifyChainAcceptC_queries]

private theorem onAcceptPureAtomicC_cost (L qep : ℕ) {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (onAcceptInpT ℓ Pt)) :
    (onAcceptPureAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) L qep inpE).cost ≤
      inpE.cost + 650 * L + bits (qep + 1) + 255000 := by
  let Γ0 := onAcceptInpT ℓ Pt :: Γ; let Γg := ghostChainT ℓ Pt :: Γ0; let Γm := .nat :: Γ0
  let Γ1 := Ty.list (ghostChainT ℓ Pt) :: Γ0; let Γ2 := simRecT ℓ Pt :: Γ1
  have hb1 : 1 ≤ bits (qep + 1) := by unfold bits; omega
  have hg := ghostAcceptC_cost (O' := AOps) FIface (Γ := Γ0) (.pair (.some (onAccPk .v0)) (.pair (onAccT .v0) (.pair (.nat 0) .nil))) (onAccI .v0)
  have hp := cost_pushChainE (O' := AOps) (Γ := Γg) (pGet (ssChains (onAccBase .v1)) (onAccQ .v1)) .v0
  have hm := modifyChainAcceptC_cost (O' := AOps) FIface (Γ := Γm) (pGet (ssChains (onAccBase .v1)) (onAccQ .v1)) .v0 (onAccI .v1)
  have hit := cost_mInTransitE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ1) L (ssMir (onAccBase .v1)) (otherE (onAccQ .v1)) (onAccW .v1)
  have hch := cost_mChallContainsE (O' := AOps) (Γ := Γ2) L (ssMir (onAccBase .v2)) (srecPos .v0)
  have hac1 := cost_mAcceptE (O' := AOps) (Γ := Γ2) L (ssMir (onAccBase .v2)) (onAccQ .v2) (srecPos .v0)
  let posInj : Expr AOps Γ1 posTy := .pair (otherE (onAccQ .v1)) (.pair (onAccT .v1) (onAccI .v1))
  have htr := cost_mTrivialE (O' := AOps) (Γ := Γ1) L (ssMir (onAccBase .v1)) posInj
  have hac2 := cost_mAcceptE (O' := AOps) (Γ := Γ1) L (ssMir (onAccBase .v1)) (onAccQ .v1) posInj
  have hw := cost_ssSetMirWin (O' := AOps) (Γ := Γ1) (onAccBase .v1)
  dsimp only [onAcceptPureAtomicC, onAccBase, onAccQ, onAccW, onAccIsDel, onAccT, onAccI, onAccM,
    onAccCi?, onAccPk, onAccPq', ssAcceptUpdate, posInj, ssMk, ssMir, ssPq, ssPn, ssUnackA,
    ssHonest, ssChains, ssAmb, ssStopped, srecPos, otherE, pGet, pSet, Expr.v0, Expr.v1, Expr.v2]
    at hg hp hm hit hch hac1 htr hac2 hw ⊢
  generalize ghostAcceptC (O' := AOps) FIface (Γ := Γ0) _ _ = c_g at hg ⊢
  generalize pushChainE (O' := AOps) (Γ := Γg) _ _ = e_p at hp ⊢
  generalize modifyChainAcceptC (O' := AOps) FIface (Γ := Γm) _ _ _ = c_m at hm ⊢
  generalize mInTransitE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ1) L _ _ _ = e_it at hit ⊢
  generalize mChallContainsE (O' := AOps) (Γ := Γ2) L _ _ = e_ch at hch ⊢
  generalize mAcceptE (O' := AOps) (Γ := Γ2) L _ _ _ = e_ac1 at hac1 ⊢
  generalize mTrivialE (O' := AOps) (Γ := Γ1) L _ _ = e_tr at htr ⊢
  generalize mAcceptE (O' := AOps) (Γ := Γ1) L _ _ _ = e_ac2 at hac2 ⊢
  generalize ssSetMirWin (O' := AOps) (Γ := Γ1) _ = e_w at hw ⊢
  dsimp only [Comp.cost, cost_eLet, Expr.cost] at hg hp hm hit hch hac1 htr hac2 hw ⊢
  simp only [rb_c0] at hg ⊢; omega

private theorem onAcceptPureAtomicC_descBits_le (L qep : ℕ) {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (onAcceptInpT ℓ Pt)) :
    atomicCompDescBits ADesc (fun _ => 8) (fun _ => 8)
      (onAcceptPureAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) L qep inpE) ≤
      atomicExprDescBits ADesc inpE + 24 * bits L + 2 * bits (qep + 1) + 28500 := by
  let Γ0 := onAcceptInpT ℓ Pt :: Γ; let Γg := ghostChainT ℓ Pt :: Γ0; let Γm := .nat :: Γ0
  let Γ1 := Ty.list (ghostChainT ℓ Pt) :: Γ0; let Γ2 := simRecT ℓ Pt :: Γ1
  have hg := ghostAcceptC_descBits_le (O' := AOps) ADesc FIface (fun _ => 8) (fun _ => 8) (Γ := Γ0) (.pair (.some (onAccPk .v0)) (.pair (onAccT .v0) (.pair (.nat 0) .nil))) (onAccI .v0)
  have hp := pushChainE_descBits_le (O' := AOps) ADesc (Γ := Γg) (pGet (ssChains (onAccBase .v1)) (onAccQ .v1)) .v0
  have hm := modifyChainAcceptC_descBits_le (O' := AOps) ADesc FIface (fun _ => 8) (fun _ => 8) (Γ := Γm) (pGet (ssChains (onAccBase .v1)) (onAccQ .v1)) .v0 (onAccI .v1)
  have hit := mInTransitE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) L (Γ := Γ1) (ssMir (onAccBase .v1)) (otherE (onAccQ .v1)) (onAccW .v1)
  have hch := mChallContainsE_descBits_le (O' := AOps) ADesc L (Γ := Γ2) (ssMir (onAccBase .v2)) (srecPos .v0)
  have hac1 := mAcceptE_descBits_le (O' := AOps) ADesc L (Γ := Γ2) (ssMir (onAccBase .v2)) (onAccQ .v2) (srecPos .v0)
  let posInj : Expr AOps Γ1 posTy := .pair (otherE (onAccQ .v1)) (.pair (onAccT .v1) (onAccI .v1))
  have htr := mTrivialE_descBits_le (O' := AOps) ADesc L (Γ := Γ1) (ssMir (onAccBase .v1)) posInj
  have hac2 := mAcceptE_descBits_le (O' := AOps) ADesc L (Γ := Γ1) (ssMir (onAccBase .v1)) (onAccQ .v1) posInj
  have hw := ssSetMirWin_descBits_le (O' := AOps) ADesc (Γ := Γ1) (onAccBase .v1)
  dsimp only [onAcceptPureAtomicC, onAccBase, onAccQ, onAccW, onAccIsDel, onAccT, onAccI, onAccM,
    onAccCi?, onAccPk, onAccPq', ssAcceptUpdate, posInj, ssMk, ssMir, ssPq, ssPn, ssUnackA,
    ssHonest, ssChains, ssAmb, ssStopped, srecPos, otherE, pGet, pSet, Expr.v0, Expr.v1, Expr.v2]
    at hg hp hm hit hch hac1 htr hac2 hw ⊢
  generalize ghostAcceptC (O' := AOps) FIface (Γ := Γ0) _ _ = c_g at hg ⊢
  generalize pushChainE (O' := AOps) (Γ := Γg) _ _ = e_p at hp ⊢
  generalize modifyChainAcceptC (O' := AOps) FIface (Γ := Γm) _ _ _ = c_m at hm ⊢
  generalize mInTransitE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) L (Γ := Γ1) _ _ _ = e_it at hit ⊢
  generalize mChallContainsE (O' := AOps) L (Γ := Γ2) _ _ = e_ch at hch ⊢
  generalize mAcceptE (O' := AOps) L (Γ := Γ2) _ _ _ = e_ac1 at hac1 ⊢
  generalize mTrivialE (O' := AOps) L (Γ := Γ1) _ _ = e_tr at htr ⊢
  generalize mAcceptE (O' := AOps) L (Γ := Γ1) _ _ _ = e_ac2 at hac2 ⊢
  generalize ssSetMirWin (O' := AOps) (Γ := Γ1) _ = e_w at hw ⊢
  simp only [descBits_eLet, recvResultT, smRrT, PlainT, PB, varIdx, atomicCompDescBits,
    atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, Nat.reduceAdd, rb_c0, rb_c1, rb_c2]
    at hg hp hm hit hch hac1 htr hac2 hw ⊢
  omega

private theorem onAnswerPureAtomicC_queries (L qep : ℕ) {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (onAnswerInpT ℓ Pt)) :
    (onAnswerPureAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) L qep inpE).queries (fun _ => 1) (fun _ => 0) = 0 := by
  simp [onAnswerPureAtomicC, Comp.queries, onAcceptPureAtomicC_queries]

private theorem onAnswerPureAtomicC_cost (L qep : ℕ) (hℓ : ℓ < 10 ^ 6) {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (onAnswerInpT ℓ Pt)) :
    (onAnswerPureAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) L qep inpE).cost ≤
      inpE.cost + 650 * L + bits (qep + 1) + 382000 := by
  let pmT := Ty.prod (lpubT (ℓ := ℓ) (Pt := Pt)) PlainT
  let Γ2 := Ty.prod .nat (.prod .nat (.opt pmT)) :: smRrFullT ℓ Pt :: onAnswerInpT ℓ Pt :: Γ
  have hoa := onAcceptPureAtomicC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) L qep (Γ := Γ2)
    (.pair (onAnsBase .v2) (.pair (onAnsQ .v2) (.pair (onAnsW .v2) (.pair (onAnsIsDel .v2)
      (.pair (.fst .v0) (.pair (.fst (.snd .v0)) (.pair (.caseOpt (.snd (.snd .v0)) (sOpPure .plainDefault .unit) (.snd .v0))
        (.pair (onAnsCi? .v2) (.pair (onAnsPk .v2) (onAnsPq' .v2))))))))))
  dsimp only [onAnswerPureAtomicC, onAnsBase, onAnsQ, onAnsW, onAnsIsDel, onAnsCi?, onAnsPk,
    onAnsPq', onAnsRes, Expr.v0, Expr.v2] at hoa ⊢
  generalize onAcceptPureAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) L qep (Γ := Γ2) _ = c_oa at hoa ⊢
  dsimp only [Comp.cost, cost_sOpPure, AtomicPureOp.cost, Expr.cost] at hoa ⊢; omega

private theorem onAnswerPureAtomicC_descBits_le (L qep : ℕ) (hℓ : ℓ < 10 ^ 6) {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (onAnswerInpT ℓ Pt)) :
    atomicCompDescBits ADesc (fun _ => 8) (fun _ => 8)
      (onAnswerPureAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) L qep inpE) ≤
      atomicExprDescBits ADesc inpE + 24 * bits L + 2 * bits (qep + 1) + 29350 := by
  let pmT := Ty.prod (lpubT (ℓ := ℓ) (Pt := Pt)) PlainT
  let Γ2 := Ty.prod .nat (.prod .nat (.opt pmT)) :: smRrFullT ℓ Pt :: onAnswerInpT ℓ Pt :: Γ
  have hbℓ : bits ℓ ≤ 20 := bits_le_of_lt_pow (by omega) (by omega)
  have hoa := onAcceptPureAtomicC_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) L qep (Γ := Γ2)
    (.pair (onAnsBase .v2) (.pair (onAnsQ .v2) (.pair (onAnsW .v2) (.pair (onAnsIsDel .v2)
      (.pair (.fst .v0) (.pair (.fst (.snd .v0)) (.pair (.caseOpt (.snd (.snd .v0)) (sOpPure .plainDefault .unit) (.snd .v0))
        (.pair (onAnsCi? .v2) (.pair (onAnsPk .v2) (onAnsPq' .v2))))))))))
  dsimp only [onAnswerPureAtomicC, onAnsBase, onAnsQ, onAnsW, onAnsIsDel, onAnsCi?, onAnsPk,
    onAnsPq', onAnsRes, Expr.v0, Expr.v2] at hoa ⊢
  generalize onAcceptPureAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) L qep (Γ := Γ2) _ = c_oa at hoa ⊢
  simp only [descBits_sOpPure, atomicPureOpDescBits, recvResultT, smRrT, PlainT, PB, varIdx,
    atomicCompDescBits, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, Nat.reduceAdd,
    rb_c0, rb_c1, rb_c2] at hoa ⊢
  omega

omit [SampleableType Pt] in private theorem inTransitHonestE_cost (L : ℕ) (hℓ : ℓ < 10 ^ 6) {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (qBE : Expr AOps Γ .bool) (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (inTransitHonestE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) L sCE qBE c'E).cost ≤
      sCE.cost + qBE.cost + c'E.cost + 63100 * L + 200 := by
  let Γ1 := Ty.prod (simFullT ℓ Pt) (.prod .bool (fig8CtT (ℓ := ℓ) (Pt := Pt))) :: Γ
  let Γ2 := Ty.prod (B 32) (fig8CtT (ℓ := ℓ) (Pt := Pt)) :: Γ1
  have heq := eqFig8CAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ2) (.snd .v0) (.snd (.snd .v1))
  have htw := toWireAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ1) (.snd (.snd .v0))
  have hit := cost_mInTransitE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ1) L (ssMir (scBase (.fst .v0))) (otherE (.fst (.snd .v0))) (toWireAtomicE (.snd (.snd .v0)))
  let bodyE : Expr AOps Γ2 .bool := eqCtE (.snd .v0) (.snd (.snd .v1))
  have hbody : bodyE.cost ≤ 62800 := by
    dsimp only [bodyE, Expr.v0, Expr.v1] at heq ⊢
    generalize eqCtE _ _ = e_eq at heq ⊢
    dsimp only [Expr.cost] at heq ⊢; omega
  dsimp only [inTransitHonestE, scBase, ssHonest, ssMir, isSomeE, otherE, Expr.v0, Expr.v1] at htw hit ⊢
  change (eLet (.pair sCE (.pair qBE c'E)) (.and (.anyB L _ bodyE) _)).cost ≤ _
  generalize bodyE = eb at hbody ⊢
  generalize mInTransitE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ1) L _ _ _ = e_it at hit ⊢
  generalize toWireAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ1) _ = e_tw at htw hit
  have hmul : L * eb.cost ≤ 62800 * L := by
    calc L * eb.cost ≤ L * 62800 := Nat.mul_le_mul_left L hbody
      _ = 62800 * L := Nat.mul_comm _ _
  dsimp only [cost_eLet, Expr.cost] at htw hit ⊢; simp only [Nat.mul_add]; omega

omit [SampleableType Pt] in private theorem inTransitHonestE_descBits_le (L : ℕ) {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (qBE : Expr AOps Γ .bool) (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    atomicExprDescBits ADesc (inTransitHonestE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) L sCE qBE c'E) ≤
      atomicExprDescBits ADesc sCE + atomicExprDescBits ADesc qBE + atomicExprDescBits ADesc c'E + 4 * bits L + 1900 := by
  let Γ1 := Ty.prod (simFullT ℓ Pt) (.prod .bool (fig8CtT (ℓ := ℓ) (Pt := Pt))) :: Γ
  let Γ2 := Ty.prod (B 32) (fig8CtT (ℓ := ℓ) (Pt := Pt)) :: Γ1
  have heq := eqFig8CAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ2) (.snd .v0) (.snd (.snd .v1))
  have htw := toWireAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ1) (.snd (.snd .v0))
  have hit := mInTransitE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) L (Γ := Γ1) (ssMir (scBase (.fst .v0))) (otherE (.fst (.snd .v0))) (toWireAtomicE (.snd (.snd .v0)))
  dsimp only [inTransitHonestE, scBase, ssHonest, ssMir, isSomeE, otherE, Expr.v0, Expr.v1] at heq htw hit ⊢
  generalize eqCtE _ _ = e_eq at heq ⊢
  generalize mInTransitE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) L (Γ := Γ1) _ _ _ = e_it at hit ⊢
  generalize toWireAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ1) _ = e_tw at htw hit
  simp only [descBits_eLet, atomicExprDescBits, varIdx, Nat.reduceAdd, rb_c0, rb_c1] at heq htw hit ⊢; omega

private theorem semFwdAnswerAtomicC_descBits_tight (idA idB : IdentityKey) (q qep : ℕ) {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (fwdAnsInpT ℓ Pt)) (hℓ : ℓ < 10 ^ 6) :
    atomicCompDescBits ADesc (fun _ => 8) (fun _ => 8)
      (semFwdAnswerAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q qep (50000 * q) inpE) ≤
      atomicExprDescBits ADesc inpE + 54350 + 46 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)) := by
  let Γ0 := fwdAnsInpT ℓ Pt :: Γ; let Γ1 := Ty.opt (smRrFullT ℓ Pt) :: Γ0
  let Γ2 := Ty.prod (.opt (recvResultT (ℓ := ℓ) (Pt := Pt))) (simBaseT ℓ Pt) :: Γ1
  have hbL := bits_L_le_budget q qep; have hbQ := bits_qep1_le_budget q qep; have hbT := bits_T_le_budget q qep
  have hin := inTransitHonestE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q (Γ := Γ0) (fwaSC .v0) (fwaQ .v0) (fwaC' .v0)
  have han := onAnswerPureAtomicC_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q qep hℓ (Γ := Γ1)
    (.pair (scBase (fwaSC .v1)) (.pair (fwaQ .v1) (.pair (fwaW .v1) (.pair (fwaIsDel .v1) (.pair (fwaCi? .v1) (.pair (fwaPk .v1) (.pair (fwaPq' .v1) .v0)))))))
  have hkr := keptRecvAtomicE_descBits_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB (50000 * q) (Γ := Γ2) (pGet (scKept (fwaSC .v2)) (fwaQ .v2)) (fwaC' .v2)
  dsimp only [semFwdAnswerAtomicC, fwaSC, fwaQ, fwaW, fwaIsDel, fwaCi?, fwaPk, fwaPq', fwaC', isResAcceptedE, scUpdateKeptRecv, scBase, scKept, scSent, scSnaps, scMk, pGet, pSet, Expr.v0, Expr.v1, Expr.v2] at hin han hkr ⊢
  generalize inTransitHonestE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q (Γ := Γ0) _ _ _ = e_in at hin ⊢
  generalize onAnswerPureAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q qep (Γ := Γ1) _ = c_an at han ⊢
  generalize keptRecvAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB (50000 * q) (Γ := Γ2) _ _ = e_kr at hkr ⊢
  simp only [descBits_eLet, smRrFullT, smRrT, lpubT, PlainT, PB, varIdx, atomicCompDescBits, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, Nat.reduceAdd, rb_c0, rb_c1, rb_c2] at hin han hkr ⊢; omega

theorem semFwdAnswerAtomicC_queries (idA idB : IdentityKey) (q qep : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (inpE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (fwdAnsInpT ℓ Pt)) :
    (semFwdAnswerAtomicC (Pt := Pt) (ℓ := ℓ) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      idA idB q qep (50000 * q) inpE).queries
      (fun _ => 1) (fun _ => 0) ≤ 1 := by
  simp [semFwdAnswerAtomicC, Comp.queries, onAnswerPureAtomicC_queries]

theorem semFwdAnswerAtomicC_cost (idA idB : IdentityKey) (q qep : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (inpE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (fwdAnsInpT ℓ Pt))
    (hℓ : ℓ < 10 ^ 6) :
    (semFwdAnswerAtomicC (Pt := Pt) (ℓ := ℓ) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      idA idB q qep (50000 * q) inpE).cost ≤
      inpE.cost + 4000000 + 1200000 * q + 64 * bits (qep + 1) := by
  let Γ0 := fwdAnsInpT ℓ Pt :: Γ; let Γ1 := Ty.opt (smRrFullT ℓ Pt) :: Γ0
  let Γ2 := Ty.prod (.opt (recvResultT (ℓ := ℓ) (Pt := Pt))) (simBaseT ℓ Pt) :: Γ1
  have hin := inTransitHonestE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q hℓ (Γ := Γ0) (fwaSC .v0) (fwaQ .v0) (fwaC' .v0)
  have han := onAnswerPureAtomicC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q qep hℓ (Γ := Γ1)
    (.pair (scBase (fwaSC .v1)) (.pair (fwaQ .v1) (.pair (fwaW .v1) (.pair (fwaIsDel .v1) (.pair (fwaCi? .v1) (.pair (fwaPk .v1) (.pair (fwaPq' .v1) .v0)))))))
  have hkr := keptRecvAtomicE_cost_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB (50000 * q) (Γ := Γ2) (pGet (scKept (fwaSC .v2)) (fwaQ .v2)) (fwaC' .v2)
  dsimp only [semFwdAnswerAtomicC, fwaSC, fwaQ, fwaW, fwaIsDel, fwaCi?, fwaPk, fwaPq', fwaC', isResAcceptedE, scUpdateKeptRecv, scBase, scKept, scSent, scSnaps, scMk, pGet, pSet, Expr.v0, Expr.v1, Expr.v2] at hin han hkr ⊢
  generalize inTransitHonestE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q (Γ := Γ0) _ _ _ = e_in at hin ⊢
  generalize onAnswerPureAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q qep (Γ := Γ1) _ = c_an at han ⊢
  generalize keptRecvAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB (50000 * q) (Γ := Γ2) _ _ = e_kr at hkr ⊢
  dsimp only [Comp.cost, cost_eLet, Expr.cost, fig8SmIface] at hin han hkr ⊢; omega

theorem semFwdAnswerAtomicC_descBits_le (idA idB : IdentityKey) (q qep : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (inpE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (fwdAnsInpT ℓ Pt))
    (hℓ : ℓ < 10 ^ 6) :
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
      (semFwdAnswerAtomicC (Pt := Pt) (ℓ := ℓ) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
        idA idB q qep (50000 * q) inpE) ≤
      atomicExprDescBits atomicSessionOpDescBits inpE +
        100000 + 128 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)) := by
  have h := semFwdAnswerAtomicC_descBits_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q qep inpE hℓ
  omega

private theorem evalCKSAtomicC_cost (idA idB : IdentityKey) (q : ℕ) (hℓ : ℓ < 10 ^ 6) {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (evalCKInpT ℓ Pt)) :
    (evalCKSAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      idA idB q (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) inpE).cost ≤
      inpE.cost + 6750000 + 5000000 * q := by
  let B_cap := 2 ^ 32 + q + 2; let T := 50000 * q; let Kc := 25001 * q + 25000
  let Γ0 := evalCKInpT ℓ Pt :: Γ
  have hbB := bits_clampB_cost q
  have hbKc : bits (25001 * q + 25000) ≤ 25001 * q + 25001 := bits_le_succ_nat _
  have hmulL : q * (ℓ / 16 + 230) ≤ 62730 * q := by
    calc q * (ℓ / 16 + 230) ≤ q * 62730 := Nat.mul_le_mul_left q (by omega)
      _ = 62730 * q := Nat.mul_comm _ _
  have hke := keptEvalAtomicE_cost_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB T B_cap (Γ := Γ0) (pGet (scKept (.fst .v0)) (.fst (.snd .v0))) (.snd (.snd (.snd (.snd .v0))))
  have hse := sentEvalAtomicE_cost_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q B_cap (Γ := Γ0) (scSent (.fst .v0)) (.fst (.snd (.snd (.snd .v0)))) (.snd (.snd (.snd (.snd .v0))))
  have hor := cost_orElseOptE (O' := AOps) (Γ := Γ0)
    (keptEvalAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB T B_cap (pGet (scKept (.fst .v0)) (.fst (.snd .v0))) (.snd (.snd (.snd (.snd .v0)))))
    (sentEvalAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q B_cap (scSent (.fst .v0)) (.fst (.snd (.snd (.snd .v0)))) (.snd (.snd (.snd (.snd .v0)))))
  have hks := knownSeedDecryptAtomicFastC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q Kc B_cap FIface (Γ := Γ0) (scSnaps (.fst .v0)) (.fst (.snd .v0)) (.fst (.fst (.fst (.snd (.snd (.snd .v0)))))) (.fst (.snd (.snd .v0))) (.snd (.snd (.snd (.snd .v0))))
  dsimp only [evalCKSAtomicC, B_cap, T, Kc, scKept, scSent, scSnaps, pGet, Expr.v0] at hke hse hor hks ⊢
  generalize orElseOptE (O' := AOps) (Γ := Γ0) _ _ = e_or at hor ⊢
  generalize keptEvalAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB (50000 * q) (2 ^ 32 + q + 2) (Γ := Γ0) _ _ = e_ke at hke hor
  generalize sentEvalAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q (2 ^ 32 + q + 2) (Γ := Γ0) _ _ _ = e_se at hse hor
  generalize knownSeedDecryptAtomicFastC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q (25001 * q + 25000) (2 ^ 32 + q + 2) FIface (Γ := Γ0) _ _ _ _ _ = c_ks at hks ⊢
  dsimp only [Comp.cost, Expr.cost] at hke hse hor hks ⊢; omega

private theorem evalCKSAtomicC_descBits_le (idA idB : IdentityKey) (q qep : ℕ) {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (evalCKInpT ℓ Pt)) :
    atomicCompDescBits ADesc (fun _ => 8) (fun _ => 8)
      (evalCKSAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
        idA idB q (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) inpE) ≤
      atomicExprDescBits ADesc inpE + 47050 + 52 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)) := by
  let B_cap := 2 ^ 32 + q + 2; let T := 50000 * q; let Kc := 25001 * q + 25000
  let Γ0 := evalCKInpT ℓ Pt :: Γ
  have hbL := bits_L_le_budget q qep; have hbB := bits_clampB_le_budget q qep
  have hbT := bits_T_le_budget q qep; have hbKc := bits_Kc_le_budget q qep
  have hke := keptEvalAtomicE_descBits_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB T B_cap (Γ := Γ0) (pGet (scKept (.fst .v0)) (.fst (.snd .v0))) (.snd (.snd (.snd (.snd .v0))))
  have hse := sentEvalAtomicE_descBits_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q B_cap (Γ := Γ0) (scSent (.fst .v0)) (.fst (.snd (.snd (.snd .v0)))) (.snd (.snd (.snd (.snd .v0))))
  have hor := descBits_orElseOptE (O' := AOps) ADesc (Γ := Γ0)
    (keptEvalAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB T B_cap (pGet (scKept (.fst .v0)) (.fst (.snd .v0))) (.snd (.snd (.snd (.snd .v0)))))
    (sentEvalAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q B_cap (scSent (.fst .v0)) (.fst (.snd (.snd (.snd .v0)))) (.snd (.snd (.snd (.snd .v0)))))
  have hks := knownSeedDecryptAtomicFastC_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q Kc B_cap FIface (fun _ => 8) (fun _ => 8) (Γ := Γ0) (scSnaps (.fst .v0)) (.fst (.snd .v0)) (.fst (.fst (.fst (.snd (.snd (.snd .v0)))))) (.fst (.snd (.snd .v0))) (.snd (.snd (.snd (.snd .v0))))
  dsimp only [evalCKSAtomicC, B_cap, T, Kc, scKept, scSent, scSnaps, pGet, Expr.v0] at hke hse hor hks ⊢
  generalize orElseOptE (O' := AOps) (Γ := Γ0) _ _ = e_or at hor ⊢
  generalize keptEvalAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB (50000 * q) (2 ^ 32 + q + 2) (Γ := Γ0) _ _ = e_ke at hke hor
  generalize sentEvalAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q (2 ^ 32 + q + 2) (Γ := Γ0) _ _ _ = e_se at hse hor
  generalize knownSeedDecryptAtomicFastC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q (25001 * q + 25000) (2 ^ 32 + q + 2) FIface (Γ := Γ0) _ _ _ _ _ = c_ks at hks ⊢
  simp only [atomicCompDescBits, atomicExprDescBits, varIdx, rb_c0] at hke hse hor hks ⊢; omega

private theorem semResyncAtomicC_cost (idA idB : IdentityKey) (q qep : ℕ) (hℓ : ℓ < 10 ^ 6) {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (resyncInpT ℓ Pt)) :
    (semResyncAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      idA idB q qep (50000 * q) inpE).cost ≤
      inpE.cost + 3240000 + 1051000 * q + bits (qep + 1) := by
  let pmT := Ty.prod (lpubT (ℓ := ℓ) (Pt := Pt)) PlainT
  let Γ4 := Ty.prod .nat (.prod .nat (.opt pmT)) :: smRrFullT ℓ Pt :: .opt (smRrFullT ℓ Pt) :: kDecOutT ℓ Pt :: resyncInpT ℓ Pt :: Γ
  let Γ5 := Ty.prod (.opt (recvResultT (ℓ := ℓ) (Pt := Pt))) (simBaseT ℓ Pt) :: Γ4
  have hoa := onAcceptPureAtomicC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q qep (Γ := Γ4)
    (.pair (scBase (rsySC .v4)) (.pair (rsyQ .v4) (.pair (rsyW .v4) (.pair (.bool true) (.pair (.fst .v3) (.pair (.fst (.snd .v3)) (.pair (.snd (.snd (.snd .v3))) (.pair (rsyCi? .v4) (.pair (rsyPk .v4) (rsyPq' .v4))))))))))
  have hkr := keptRecvAtomicE_cost_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB (50000 * q) (Γ := Γ5) (pGet (scKept (rsySC .v5)) (rsyQ .v5)) (rsyC .v5)
  dsimp only [semResyncAtomicC, rsySC, rsyQ, rsyW, rsyCi?, rsyPk, rsyPq', rsyC, rsyR, scUpdateKeptRecv, scBase, scKept, scSent, scSnaps, scMk, pGet, pSet, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5] at hoa hkr ⊢
  generalize onAcceptPureAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q qep (Γ := Γ4) _ = c_oa at hoa ⊢
  generalize keptRecvAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB (50000 * q) (Γ := Γ5) _ _ = e_kr at hkr ⊢
  dsimp only [Comp.cost, cost_eLet, Expr.cost, fig8SmIface] at hoa hkr ⊢; omega

private theorem semResyncAtomicC_descBits_le (idA idB : IdentityKey) (q qep : ℕ) {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (resyncInpT ℓ Pt)) :
    atomicCompDescBits ADesc (fun _ => 8) (fun _ => 8)
      (semResyncAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
        idA idB q qep (50000 * q) inpE) ≤
      atomicExprDescBits ADesc inpE + 51150 + 42 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)) := by
  let pmT := Ty.prod (lpubT (ℓ := ℓ) (Pt := Pt)) PlainT
  let Γ4 := Ty.prod .nat (.prod .nat (.opt pmT)) :: smRrFullT ℓ Pt :: .opt (smRrFullT ℓ Pt) :: kDecOutT ℓ Pt :: resyncInpT ℓ Pt :: Γ
  let Γ5 := Ty.prod (.opt (recvResultT (ℓ := ℓ) (Pt := Pt))) (simBaseT ℓ Pt) :: Γ4
  have hbL := bits_L_le_budget q qep; have hbQ := bits_qep1_le_budget q qep; have hbT := bits_T_le_budget q qep
  have hoa := onAcceptPureAtomicC_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q qep (Γ := Γ4)
    (.pair (scBase (rsySC .v4)) (.pair (rsyQ .v4) (.pair (rsyW .v4) (.pair (.bool true) (.pair (.fst .v3) (.pair (.fst (.snd .v3)) (.pair (.snd (.snd (.snd .v3))) (.pair (rsyCi? .v4) (.pair (rsyPk .v4) (rsyPq' .v4))))))))))
  have hkr := keptRecvAtomicE_descBits_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB (50000 * q) (Γ := Γ5) (pGet (scKept (rsySC .v5)) (rsyQ .v5)) (rsyC .v5)
  dsimp only [semResyncAtomicC, rsySC, rsyQ, rsyW, rsyCi?, rsyPk, rsyPq', rsyC, rsyR, scUpdateKeptRecv, scBase, scKept, scSent, scSnaps, scMk, pGet, pSet, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5] at hoa hkr ⊢
  generalize onAcceptPureAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q qep (Γ := Γ4) _ = c_oa at hoa ⊢
  generalize keptRecvAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB (50000 * q) (Γ := Γ5) _ _ = e_kr at hkr ⊢
  simp only [descBits_eLet, recvResultT, smRrFullT, smRrT, lpubT, PlainT, PB, varIdx, atomicCompDescBits, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, Nat.reduceAdd, rb_c0, rb_c1, rb_c2, rb_c3, rb_c4, rb_c5] at hoa hkr ⊢
  omega

private theorem semFwdHookAtomicC_descBits_tight (idA idB : IdentityKey) (q qep : ℕ) {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (fwdHookInpT ℓ Pt)) (hℓ : ℓ < 10 ^ 6) :
    atomicCompDescBits ADesc (fun _ => 8) (fun _ => 8)
      (semFwdHookAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
        idA idB q qep (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) inpE) ≤
      atomicExprDescBits ADesc inpE + 211400 + 186 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)) := by
  let ctT := fig8CtT (ℓ := ℓ) (Pt := Pt)
  let Γ0 := fwdHookInpT ℓ Pt :: Γ; let Γ1 := ctT :: Γ0
  let Γ2 := Ty.opt (.opt (kDecOutT ℓ Pt)) :: Γ1; let Γ3 := Ty.opt (kDecOutT ℓ Pt) :: Γ2
  have hfa0 := semFwdAnswerAtomicC_descBits_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q qep (Γ := Γ0) (fwhToAnsInp .v0) hℓ
  have hfa1 := semFwdAnswerAtomicC_descBits_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q qep (Γ := Γ1) (fwhToAnsInp .v1) hℓ
  have heq := eqFig8CAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ1) .v0 (fwhC' .v1)
  have hsi := mSafeInjE_descBits_le (O' := AOps) ADesc (Γ := Γ1) (ssMir (scBase (fwhSC .v1)))
  have hev := evalCKSAtomicC_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q qep (Γ := Γ1) (.pair (fwhSC .v1) (.pair (fwhQ .v1) (.pair (fwhW .v1) (.pair .v0 (fwhC' .v1)))))
  have hrs := semResyncAtomicC_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q qep (Γ := Γ3) (.pair (fwhSC .v3) (.pair (fwhQ .v3) (.pair (fwhW .v3) (.pair (fwhCi? .v3) (.pair (fwhPk .v3) (.pair (fwhPq' .v3) (.pair .v2 .v0)))))))
  dsimp only [semFwdHookAtomicC, fwhToAnsInp, fwhSC, fwhQ, fwhW, fwhIsDel, fwhCi?, fwhPk, fwhPq', fwhHonest, fwhC', scBase, ssMir, Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hfa0 hfa1 heq hsi hev hrs ⊢
  generalize semFwdAnswerAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q qep (50000 * q) (Γ := Γ0) _ = c_fa0 at hfa0 ⊢
  generalize semFwdAnswerAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q qep (50000 * q) (Γ := Γ1) _ = c_fa1 at hfa1 ⊢
  generalize eqCtE _ _ = e_eq at heq ⊢
  generalize mSafeInjE (O' := AOps) (Γ := Γ1) _ = e_si at hsi ⊢
  generalize evalCKSAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (Γ := Γ1) _ = c_ev at hev ⊢
  generalize semResyncAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q qep (50000 * q) (Γ := Γ3) _ = c_rs at hrs ⊢
  simp only [recvResultT, smRrT, PlainT, PB, varIdx, atomicCompDescBits, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, Nat.reduceAdd, rb_c0, rb_c1, rb_c2, rb_c3] at hfa0 hfa1 heq hsi hev hrs ⊢; omega

theorem semFwdHookAtomicC_queries (idA idB : IdentityKey) (q qep : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (inpE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (fwdHookInpT ℓ Pt)) :
    (semFwdHookAtomicC (Pt := Pt) (ℓ := ℓ) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      idA idB q qep (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) inpE).queries
      (fun _ => 1) (fun _ => 0) ≤ 1 := by
  let Γ0 := fwdHookInpT ℓ Pt :: Γ; let Γ1 := fig8CtT (ℓ := ℓ) (Pt := Pt) :: Γ0
  have h0 := semFwdAnswerAtomicC_queries (Pt := Pt) (ℓ := ℓ) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q qep (Γ := Γ0) (fwhToAnsInp .v0)
  have h1 := semFwdAnswerAtomicC_queries (Pt := Pt) (ℓ := ℓ) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q qep (Γ := Γ1) (fwhToAnsInp .v1)
  dsimp only [semFwdHookAtomicC]
  generalize semFwdAnswerAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q qep (50000 * q) (Γ := Γ0) _ = c0 at h0 ⊢
  generalize semFwdAnswerAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q qep (50000 * q) (Γ := Γ1) _ = c1 at h1 ⊢
  dsimp only [evalCKSAtomicC, semResyncAtomicC]
  simp only [Comp.queries, onAcceptPureAtomicC_queries, knownSeedDecryptAtomicFastC_queries] at h0 h1 ⊢; omega

theorem semFwdHookAtomicC_cost (idA idB : IdentityKey) (q qep : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (inpE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (fwdHookInpT ℓ Pt))
    (hℓ : ℓ < 10 ^ 6) :
    (semFwdHookAtomicC (Pt := Pt) (ℓ := ℓ) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      idA idB q qep (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) inpE).cost ≤
      inpE.cost + 12000000 + 7000000 * q + 64 * bits (qep + 1) := by
  let ctT := fig8CtT (ℓ := ℓ) (Pt := Pt)
  let Γ0 := fwdHookInpT ℓ Pt :: Γ; let Γ1 := ctT :: Γ0
  let Γ2 := Ty.opt (.opt (kDecOutT ℓ Pt)) :: Γ1; let Γ3 := Ty.opt (kDecOutT ℓ Pt) :: Γ2
  have hfa0 := semFwdAnswerAtomicC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q qep (Γ := Γ0) (fwhToAnsInp .v0) hℓ
  have hfa1 := semFwdAnswerAtomicC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q qep (Γ := Γ1) (fwhToAnsInp .v1) hℓ
  have heq := eqFig8CAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ1) .v0 (fwhC' .v1)
  have hsi := cost_mSafeInjE (O' := AOps) (Γ := Γ1) (ssMir (scBase (fwhSC .v1)))
  have hev := evalCKSAtomicC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q hℓ (Γ := Γ1) (.pair (fwhSC .v1) (.pair (fwhQ .v1) (.pair (fwhW .v1) (.pair .v0 (fwhC' .v1)))))
  have hrs := semResyncAtomicC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q qep hℓ (Γ := Γ3) (.pair (fwhSC .v3) (.pair (fwhQ .v3) (.pair (fwhW .v3) (.pair (fwhCi? .v3) (.pair (fwhPk .v3) (.pair (fwhPq' .v3) (.pair .v2 .v0)))))))
  dsimp only [semFwdHookAtomicC, fwhToAnsInp, fwhSC, fwhQ, fwhW, fwhIsDel, fwhCi?, fwhPk, fwhPq', fwhHonest, fwhC', scBase, ssMir, Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hfa0 hfa1 heq hsi hev hrs ⊢
  generalize semFwdAnswerAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q qep (50000 * q) (Γ := Γ0) _ = c_fa0 at hfa0 ⊢
  generalize semFwdAnswerAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q qep (50000 * q) (Γ := Γ1) _ = c_fa1 at hfa1 ⊢
  generalize eqCtE _ _ = e_eq at heq ⊢
  generalize mSafeInjE (O' := AOps) (Γ := Γ1) _ = e_si at hsi ⊢
  generalize evalCKSAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (Γ := Γ1) _ = c_ev at hev ⊢
  generalize semResyncAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q qep (50000 * q) (Γ := Γ3) _ = c_rs at hrs ⊢
  dsimp only [Comp.cost, Expr.cost] at hfa0 hfa1 heq hsi hev hrs ⊢; omega

theorem semFwdHookAtomicC_descBits_le (idA idB : IdentityKey) (q qep : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (inpE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (fwdHookInpT ℓ Pt))
    (hℓ : ℓ < 10 ^ 6) :
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
      (semFwdHookAtomicC (Pt := Pt) (ℓ := ℓ) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
        idA idB q qep (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) inpE) ≤
      atomicExprDescBits atomicSessionOpDescBits inpE +
        250000 + 256 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)) := by
  have h := semFwdHookAtomicC_descBits_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q qep inpE hℓ
  omega

private theorem recvSameBranchAtomicC_descBits_tight (idA idB : IdentityKey) (q qep : ℕ) {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (recvSameInpT ℓ Pt)) (hℓ : ℓ < 10 ^ 6) :
    atomicCompDescBits ADesc (fun _ => 8) (fun _ => 8)
      (recvSameBranchAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
        idA idB q qep (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) inpE) ≤
      atomicExprDescBits ADesc inpE + 220400 + 186 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)) := by
  let ctT := fig8CtT (ℓ := ℓ) (Pt := Pt)
  let Γ0 := recvSameInpT ℓ Pt :: Γ
  let Γmk := ctT :: .prod (.opt ctT) ctT :: Γ0
  let gE := getChainDE (pGet (ssChains (scBase (rsmSC (.v0 : Expr AOps Γ0 _)))) (rsmQ .v0)) (rsmCi .v0)
  let p0 := rsmParsed (.v0 : Expr AOps Γ0 _)
  have hg := getChainDE_descBits_le (O' := AOps) ADesc (Γ := Γ0) (pGet (ssChains (scBase (rsmSC .v0))) (rsmQ .v0)) (rsmCi .v0)
  have hgr := ghostRejectsE_descBits_le (O' := AOps) ADesc (Γ := Γ0) gE (poI p0)
  have hlct := lctSaltEqOfLctAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γmk) .v0 (.snd (.snd .v1))
  have hfh := semFwdHookAtomicC_descBits_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q qep (Γ := Γ0)
    (.pair (rsmSC .v0) (.pair (rsmQ .v0) (.pair (rsmW .v0) (.pair (rsmIsDel .v0) (.pair (.some (rsmCi .v0)) (.pair (poPk p0) (.pair (poPq' p0) (.pair (rsmHonest .v0) (mkCE (rsmHonest .v0) (.fst (.snd gE)) (poT? p0) (poLct p0)))))))))) hℓ
  dsimp only [recvSameBranchAtomicC, gE, p0, mkCE, rsmSC, rsmQ, rsmW, rsmIsDel, rsmParsed, rsmHonest, rsmCi, poPq', poI, poPk, poT?, poLct, scBase, ssChains, pGet, Expr.v0, Expr.v1] at hg hgr hlct hfh ⊢
  generalize semFwdHookAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q qep (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (Γ := Γ0) _ = c_fh at hfh ⊢
  generalize lctSaltEqOfLctAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γmk) _ _ = e_lct at hlct hfh
  generalize ghostRejectsE (O' := AOps) (Γ := Γ0) _ _ = e_gr at hgr ⊢
  generalize getChainDE (O' := AOps) (Γ := Γ0) _ _ = e_gc at hg hgr hfh
  simp only [descBits_eLet, recvResultT, smRrT, PlainT, PB, varIdx, atomicCompDescBits, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, Nat.reduceAdd, rb_c0, rb_c1] at hg hgr hlct hfh ⊢
  omega

theorem recvSameBranchAtomicC_queries (idA idB : IdentityKey) (q qep : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (inpE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (recvSameInpT ℓ Pt)) :
    (recvSameBranchAtomicC (Pt := Pt) (ℓ := ℓ) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      idA idB q qep (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) inpE).queries
      (fun _ => 1) (fun _ => 0) ≤ 1 := by
  let Γ0 := recvSameInpT ℓ Pt :: Γ
  let gE := getChainDE (pGet (ssChains (scBase (rsmSC (.v0 : Expr AOps Γ0 _)))) (rsmQ .v0)) (rsmCi .v0)
  let p0 := rsmParsed (.v0 : Expr AOps Γ0 _)
  have hf := semFwdHookAtomicC_queries (Pt := Pt) (ℓ := ℓ) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q qep (Γ := Γ0)
    (.pair (rsmSC .v0) (.pair (rsmQ .v0) (.pair (rsmW .v0) (.pair (rsmIsDel .v0) (.pair (.some (rsmCi .v0)) (.pair (poPk p0) (.pair (poPq' p0) (.pair (rsmHonest .v0) (mkCE (rsmHonest .v0) (.fst (.snd gE)) (poT? p0) (poLct p0))))))))))
  dsimp only [recvSameBranchAtomicC]
  generalize semFwdHookAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q qep (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (Γ := Γ0) _ = c_fh at hf ⊢
  simp only [Comp.queries] at hf ⊢; omega

theorem recvSameBranchAtomicC_cost (idA idB : IdentityKey) (q qep : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (inpE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (recvSameInpT ℓ Pt))
    (hℓ : ℓ < 10 ^ 6) :
    (recvSameBranchAtomicC (Pt := Pt) (ℓ := ℓ) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      idA idB q qep (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) inpE).cost ≤
      inpE.cost + 13000000 + 7000000 * q + 64 * bits (qep + 1) := by
  let ctT := fig8CtT (ℓ := ℓ) (Pt := Pt)
  let Γ0 := recvSameInpT ℓ Pt :: Γ
  let Γmk := ctT :: .prod (.opt ctT) ctT :: Γ0
  let gE := getChainDE (pGet (ssChains (scBase (rsmSC (.v0 : Expr AOps Γ0 _)))) (rsmQ .v0)) (rsmCi .v0)
  let p0 := rsmParsed (.v0 : Expr AOps Γ0 _)
  have hg := cost_getChainDE (O' := AOps) (Γ := Γ0) (pGet (ssChains (scBase (rsmSC .v0))) (rsmQ .v0)) (rsmCi .v0)
  have hgr := cost_ghostRejectsE (O' := AOps) (Γ := Γ0) gE (poI p0)
  have hlct := lctSaltEqOfLctAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γmk) .v0 (.snd (.snd .v1))
  have hfh := semFwdHookAtomicC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q qep (Γ := Γ0)
    (.pair (rsmSC .v0) (.pair (rsmQ .v0) (.pair (rsmW .v0) (.pair (rsmIsDel .v0) (.pair (.some (rsmCi .v0)) (.pair (poPk p0) (.pair (poPq' p0) (.pair (rsmHonest .v0) (mkCE (rsmHonest .v0) (.fst (.snd gE)) (poT? p0) (poLct p0)))))))))) hℓ
  dsimp only [recvSameBranchAtomicC, gE, p0, mkCE, rsmSC, rsmQ, rsmW, rsmIsDel, rsmParsed, rsmHonest, rsmCi, poPq', poI, poPk, poT?, poLct, scBase, ssChains, pGet, Expr.v0, Expr.v1] at hg hgr hlct hfh ⊢
  generalize semFwdHookAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q qep (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (Γ := Γ0) _ = c_fh at hfh ⊢
  generalize lctSaltEqOfLctAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γmk) _ _ = e_lct at hlct hfh
  generalize ghostRejectsE (O' := AOps) (Γ := Γ0) _ _ = e_gr at hgr ⊢
  generalize getChainDE (O' := AOps) (Γ := Γ0) _ _ = e_gc at hg hgr hfh
  dsimp only [Comp.cost, cost_eLet, Expr.cost] at hg hgr hlct hfh ⊢; omega

theorem recvSameBranchAtomicC_descBits_le (idA idB : IdentityKey) (q qep : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (inpE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (recvSameInpT ℓ Pt))
    (hℓ : ℓ < 10 ^ 6) :
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
      (recvSameBranchAtomicC (Pt := Pt) (ℓ := ℓ) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
        idA idB q qep (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) inpE) ≤
      atomicExprDescBits atomicSessionOpDescBits inpE +
        260000 + 256 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)) := by
  have h := recvSameBranchAtomicC_descBits_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q qep inpE hℓ
  omega

theorem recvHookOfNewAtomicC_queries (idA idB : IdentityKey) (q qep : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (sCE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (simFullT ℓ Pt))
    (qBE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .bool)
    (wE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (B 32))
    (isDelE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .bool)
    (newBranchC : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      (recvNewSiteCtx ℓ Pt (.prod (simFullT ℓ Pt) (.prod .bool (.prod (B 32) .bool)) :: Γ))
      (recvOutT ℓ Pt))
    (hq_new : newBranchC.queries (fun _ => 1) (fun _ => 0) ≤ 1) :
    (recvHookOfNewAtomicC (Pt := Pt) (ℓ := ℓ) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      idA idB q qep (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000)
      sCE qBE wE isDelE newBranchC).queries (fun _ => 1) (fun _ => 0) ≤ 1 := by
  let inpT := Ty.prod (simFullT ℓ Pt) (.prod .bool (.prod (B 32) .bool))
  let Γ4 := .nat :: .opt (fig8CtT (ℓ := ℓ) (Pt := Pt)) :: parseOutT ℓ Pt :: .opt (parseOutT ℓ Pt) :: inpT :: Γ
  have hsame := recvSameBranchAtomicC_queries (Pt := Pt) (ℓ := ℓ) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q qep (Γ := Γ4)
    (.pair (.fst .v4) (.pair (.fst (.snd .v4)) (.pair (.fst (.snd (.snd .v4))) (.pair (.snd (.snd (.snd .v4))) (.pair .v2 (.pair .v1 .v0))))))
  dsimp only [recvHookOfNewAtomicC, recvNewSiteCtx] at hq_new ⊢
  generalize recvSameBranchAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q qep (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (Γ := Γ4) _ = c_same at hsame ⊢
  simp only [Comp.queries, parseRecvAtomicC_queries] at hq_new hsame ⊢; omega

omit [SampleableType Pt] in private theorem honestFindE_cost (L : ℕ) {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32)) :
    (honestFindE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) L sCE qBE wE).cost ≤
      sCE.cost + qBE.cost + wE.cost + 105 * L + 30 := by
  let Γ1 := Ty.prod (simFullT ℓ Pt) (.prod .bool (B 32)) :: Γ
  let Γ2 := Ty.prod (B 32) (fig8CtT (ℓ := ℓ) (Pt := Pt)) :: Γ1
  let bodyE : Expr AOps Γ2 .bool := .and (sOpPure (.bytesEq 32 32) (.pair (.fst .v0) (.snd (.snd .v1))))
    (boolEq (senderOfE (.fst (.fst (.snd .v0)))) (otherE (.fst (.snd .v1))))
  have hbody : bodyE.cost ≤ 100 := by
    dsimp only [bodyE, boolEq, senderOfE, otherE, cost_sOpPure, AtomicPureOp.cost, Expr.cost, Expr.v0, Expr.v1]
    simp only [PNat.val_ofNat, rb_c1, rb_c2]; omega
  change (eLet (.pair sCE (.pair qBE wE)) (eMapOpt (.findB L (ssHonest (scBase (.fst .v0))) bodyE) (.snd .v0))).cost ≤ _
  generalize bodyE = eb at hbody ⊢
  have hmul : L * eb.cost ≤ 100 * L := by
    calc L * eb.cost ≤ L * 100 := Nat.mul_le_mul_left L hbody
      _ = 100 * L := Nat.mul_comm _ _
  simp only [cost_eLet, cost_eMapOpt, scBase, ssHonest, Expr.cost, Expr.v0, Nat.mul_add]; omega

omit [SampleableType Pt] in private theorem recvRefuseE_cost (L : ℕ) (hℓ : ℓ < 10 ^ 6) {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32)) (isDelE : Expr AOps Γ .bool) :
    (recvRefuseE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) L sCE qBE wE isDelE).cost ≤
      sCE.cost + qBE.cost + wE.cost + isDelE.cost + 500 * L + 35000 := by
  let Γ0 := Ty.prod (simFullT ℓ Pt) (.prod .bool (.prod (B 32) .bool)) :: Γ
  have hit := cost_mInTransitE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ0) L (ssMir (scBase (.fst .v0))) (otherE (.fst (.snd .v0))) (.fst (.snd (.snd .v0)))
  have hsi := cost_mSafeInjE (O' := AOps) (Γ := Γ0) (ssMir (scBase (.fst .v0)))
  have hinj := injOKAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ0) (.fst (.snd (.snd .v0)))
  dsimp only [recvRefuseE, orE, isSomeE, otherE, scBase, ssMir, ssStopped, Expr.v0] at hit hsi hinj ⊢
  generalize mInTransitE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ0) L _ _ _ = e_it at hit ⊢
  generalize mSafeInjE (O' := AOps) (Γ := Γ0) _ = e_si at hsi ⊢
  generalize injOKAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ0) _ = e_inj at hinj ⊢
  dsimp only [cost_eLet, Expr.cost] at hit hsi hinj ⊢; omega

theorem recvHookOfNewAtomicC_cost (idA idB : IdentityKey) (q qep : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (sCE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (simFullT ℓ Pt))
    (qBE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .bool)
    (wE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (B 32))
    (isDelE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .bool)
    (newBranchC : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      (recvNewSiteCtx ℓ Pt (.prod (simFullT ℓ Pt) (.prod .bool (.prod (B 32) .bool)) :: Γ))
      (recvOutT ℓ Pt))
    (hℓ : ℓ < 10 ^ 6) :
    (recvHookOfNewAtomicC (Pt := Pt) (ℓ := ℓ) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      idA idB q qep (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000)
      sCE qBE wE isDelE newBranchC).cost ≤
      sCE.cost + qBE.cost + wE.cost + isDelE.cost +
        146000000 + 7100000 * q + 64 * bits (qep + 1) + newBranchC.cost := by
  let inpT := Ty.prod (simFullT ℓ Pt) (.prod .bool (.prod (B 32) .bool))
  let Γ0 := inpT :: Γ
  let Γ2 := parseOutT ℓ Pt :: .opt (parseOutT ℓ Pt) :: Γ0
  let Γ3 := Ty.opt (fig8CtT (ℓ := ℓ) (Pt := Pt)) :: Γ2
  let Γ4 := .nat :: Γ3
  have href := recvRefuseE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q hℓ (Γ := Γ0) (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))
  have hpr := parseRecvAtomicC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) FIface idA idB (2 ^ 32) (Γ := Γ0) (.fst (.snd .v0)) (pGet (ssPq (scBase (.fst .v0))) (.fst (.snd .v0))) (.fst (.snd (.snd .v0)))
  have hhf := honestFindE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q (Γ := Γ2) (.fst .v2) (.fst (.snd .v2)) (.fst (.snd (.snd .v2)))
  have hfci := cost_findChainIdxE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ3) (pGet (ssChains (scBase (.fst .v3))) (.fst (.snd .v3))) (poPk .v1)
  have hsame := recvSameBranchAtomicC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q qep (Γ := Γ4)
    (.pair (.fst .v4) (.pair (.fst (.snd .v4)) (.pair (.fst (.snd (.snd .v4))) (.pair (.snd (.snd (.snd .v4))) (.pair .v2 (.pair .v1 .v0)))))) hℓ
  dsimp only [recvHookOfNewAtomicC, poPk, scBase, ssPq, ssChains, pGet, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4] at href hpr hhf hfci hsame ⊢
  generalize recvSameBranchAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q qep (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (Γ := Γ4) _ = c_same at hsame ⊢
  generalize findChainIdxE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ3) _ _ = e_fci at hfci ⊢
  generalize honestFindE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q (Γ := Γ2) _ _ _ = e_hf at hhf ⊢
  generalize parseRecvAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) FIface idA idB (2 ^ 32) (Γ := Γ0) _ _ _ = c_pr at hpr ⊢
  generalize recvRefuseE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q (Γ := Γ0) _ _ _ _ = e_ref at href ⊢
  dsimp only [Comp.cost, Expr.cost] at href hpr hhf hfci hsame ⊢
  simp only [rb_c0, rb_c1, rb_c2, rb_232] at href hpr hhf hfci hsame ⊢
  omega

theorem recvHookOfNewAtomicC_descBits_le (idA idB : IdentityKey) (q qep : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (sCE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (simFullT ℓ Pt))
    (qBE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .bool)
    (wE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (B 32))
    (isDelE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .bool)
    (newBranchC : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      (recvNewSiteCtx ℓ Pt (.prod (simFullT ℓ Pt) (.prod .bool (.prod (B 32) .bool)) :: Γ))
      (recvOutT ℓ Pt))
    (hℓ : ℓ < 10 ^ 6) :
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
      (recvHookOfNewAtomicC (Pt := Pt) (ℓ := ℓ) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
        idA idB q qep (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000)
        sCE qBE wE isDelE newBranchC) ≤
      atomicExprDescBits atomicSessionOpDescBits sCE +
      atomicExprDescBits atomicSessionOpDescBits qBE +
      atomicExprDescBits atomicSessionOpDescBits wE +
      atomicExprDescBits atomicSessionOpDescBits isDelE +
      320000 + 256 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)) +
        atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) newBranchC := by
  let inpT := Ty.prod (simFullT ℓ Pt) (.prod .bool (.prod (B 32) .bool))
  let Γ0 := inpT :: Γ; let Γref := inpT :: Γ0
  let Γ3 := Ty.opt (fig8CtT (ℓ := ℓ) (Pt := Pt)) :: parseOutT ℓ Pt :: .opt (parseOutT ℓ Pt) :: Γ0
  let Γ4 := .nat :: Γ3
  have hbL := bits_L_le_budget q qep; have ht_ct := atomicTyDescBits_fig8CtT (ℓ := ℓ) (Pt := Pt)
  have hit := mInTransitE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q (Γ := Γref) (ssMir (scBase (.fst .v0))) (otherE (.fst (.snd .v0))) (.fst (.snd (.snd .v0)))
  have hsi := mSafeInjE_descBits_le (O' := AOps) ADesc (Γ := Γref) (ssMir (scBase (.fst .v0)))
  have hinj := injOKAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γref) (.fst (.snd (.snd .v0)))
  have hpr := parseRecvAtomicC_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) FIface idA idB (2 ^ 32) (fun _ => 8) (fun _ => 8) (Γ := Γ0) (.fst (.snd .v0)) (pGet (ssPq (scBase (.fst .v0))) (.fst (.snd .v0))) (.fst (.snd (.snd .v0)))
  have hfci := findChainIdxE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ3) (pGet (ssChains (scBase (.fst .v3))) (.fst (.snd .v3))) (poPk .v1)
  have hsame := recvSameBranchAtomicC_descBits_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q qep (Γ := Γ4)
    (.pair (.fst .v4) (.pair (.fst (.snd .v4)) (.pair (.fst (.snd (.snd .v4))) (.pair (.snd (.snd (.snd .v4))) (.pair .v2 (.pair .v1 .v0)))))) hℓ
  dsimp only [recvHookOfNewAtomicC, recvRefuseE, honestFindE, poPk, orE, isSomeE, otherE, boolEq, senderOfE, scBase, ssMir, ssPq, ssHonest, ssChains, ssStopped, pGet, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4] at hit hsi hinj hpr hfci hsame ⊢
  generalize recvSameBranchAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q qep (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (Γ := Γ4) _ = c_same at hsame ⊢
  generalize findChainIdxE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ3) _ _ = e_fci at hfci ⊢
  generalize parseRecvAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) FIface idA idB (2 ^ 32) (Γ := Γ0) _ _ _ = c_pr at hpr ⊢
  generalize mInTransitE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q (Γ := Γref) _ _ _ = e_it at hit ⊢
  generalize mSafeInjE (O' := AOps) (Γ := Γref) _ = e_si at hsi ⊢
  generalize injOKAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γref) _ = e_inj at hinj ⊢
  simp only [descBits_eLet, descBits_eMapOpt, descBits_sOpPure, atomicPureOpDescBits, recvResultT, smRrT, PlainT, PB, _root_.ReductionDsl.B, varIdx, atomicCompDescBits, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, Nat.reduceAdd, rb_c0, rb_c1, rb_c2, rb_c3, rb_c4, rb_c32, rb_p32, rb_232] at hit hsi hinj hpr hfci hsame ⊢
  omega

end StaticBounds

end Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvSameCost

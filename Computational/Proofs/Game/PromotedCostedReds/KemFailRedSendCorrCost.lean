/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.KemFailRedInit
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8Crypto
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept

/-!
# Atomic Send, Challenge, and Corrupt Programs and Cost Bounds for `KemFailRed`

Defines the `atomicSessionOps` combinators implementing `KemFailRed`'s transmit/challenge
(`kemFailSendBodyC`), corrupt (`kemFailCorrBodyC`), and braid-tracker (`stepKemFailSendAtomicC`)
branches, together with static query, cost, and `descBits` bounds.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.KemFailRedSendCorrCost

open _root_.ReductionDsl (Sig Ty Var Env Ops Iface Expr Comp UniformSamplerTag bits
  atomicSig atomicSessionOps coinOnlyIface GhostStT smQT smRT
  B U8 U32 U64 BV256 BV512 PlainT PK
  lpubT fig8CtT fig8StT fsSendStT)
open CryptoGames.CKA (DHFun)
open CryptoGames.SM (posTy posSender posIdx posEq boolEq maxN isSomeE sendsInE pGet pSet otherE)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (Bytes)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost (
  simFullT simBaseT simMirT keptT sentEntryT ghostChainT)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8State (
  sOpPure sOpPtEnc sOpGrp sOpSpqr eLet
  ssMir ssPq ssPn ssUnackA ssHonest ssChains ssAmb ssStopped ssMk
  scBase scKept scSent scSnaps scMk
  revealSpkChainsE toGhostE)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept (
  f8Id f8Tcur f8VS f8Gamma
  fig8SendStepAtomicE keptOfStAtomicE keptSendAtomicE)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8Crypto (
  mkPubAtomicC toWireAtomicE)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost (
  atomicSortDescBits atomicTyDescBits varIdx atomicPureOpDescBits
  atomicSessionOpDescBits atomicExprDescBits atomicCompDescBits)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedInit (
  fig8RecT fig8MirT fig8GsT kemCoinsT kemSentEntryT kemTrackT kemFailStateT)

section Definitions

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {C : Crypto} {K : MlKem}
  {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
  {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

/-! ## Structural accessors -/

def boolOrE {O' : Ops ASig} {Γ : List (Ty ASig)} (a b : Expr O' Γ .bool) : Expr O' Γ .bool :=
  .ite a (.bool true) b

def boolEqE {O' : Ops ASig} {Γ : List (Ty ASig)} (a b : Expr O' Γ .bool) : Expr O' Γ .bool :=
  .ite a b (.not b)

def fgSt {O' : Ops ASig} {Γ : List (Ty ASig)} (g : Expr O' Γ (fig8GsT ℓ Pt)) :
    Expr O' Γ (.prod (fig8StT (ℓ := ℓ) (Pt := Pt)) (fig8StT (ℓ := ℓ) (Pt := Pt))) :=
  .fst g

def fgMir {O' : Ops ASig} {Γ : List (Ty ASig)} (g : Expr O' Γ (fig8GsT ℓ Pt)) :
    Expr O' Γ (fig8MirT ℓ Pt) :=
  .snd g

def fgRecPos {O' : Ops ASig} {Γ : List (Ty ASig)} (r : Expr O' Γ (fig8RecT ℓ Pt)) :
    Expr O' Γ posTy := .fst r
def fgB {O' : Ops ASig} {Γ : List (Ty ASig)} (m : Expr O' Γ (fig8MirT ℓ Pt)) :
    Expr O' Γ .bool := .fst m
def fgWin {O' : Ops ASig} {Γ : List (Ty ASig)} (m : Expr O' Γ (fig8MirT ℓ Pt)) :
    Expr O' Γ .bool := .fst (.snd m)
def fgEpoch {O' : Ops ASig} {Γ : List (Ty ASig)} (m : Expr O' Γ (fig8MirT ℓ Pt)) :
    Expr O' Γ (.prod .nat .nat) := .fst (.snd (.snd m))
def fgIdx {O' : Ops ASig} {Γ : List (Ty ASig)} (m : Expr O' Γ (fig8MirT ℓ Pt)) :
    Expr O' Γ (.prod .nat .nat) := .fst (.snd (.snd (.snd m)))
def fgTL {O' : Ops ASig} {Γ : List (Ty ASig)} (m : Expr O' Γ (fig8MirT ℓ Pt)) :
    Expr O' Γ (.opt .nat) := .fst (.snd (.snd (.snd (.snd m))))
def fgTrans {O' : Ops ASig} {Γ : List (Ty ASig)} (m : Expr O' Γ (fig8MirT ℓ Pt)) :
    Expr O' Γ (.list (fig8RecT ℓ Pt)) := .fst (.snd (.snd (.snd (.snd (.snd m)))))
def fgChall {O' : Ops ASig} {Γ : List (Ty ASig)} (m : Expr O' Γ (fig8MirT ℓ Pt)) :
    Expr O' Γ (.list posTy) := .fst (.snd (.snd (.snd (.snd (.snd (.snd m))))))
def fgComp {O' : Ops ASig} {Γ : List (Ty ASig)} (m : Expr O' Γ (fig8MirT ℓ Pt)) :
    Expr O' Γ (.list posTy) := .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd m)))))))
def fgMaxAcc {O' : Ops ASig} {Γ : List (Ty ASig)} (m : Expr O' Γ (fig8MirT ℓ Pt)) :
    Expr O' Γ (.prod (.tbl .nat) (.tbl .nat)) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd m))))))))
def fgLeaks {O' : Ops ASig} {Γ : List (Ty ASig)} (m : Expr O' Γ (fig8MirT ℓ Pt)) :
    Expr O' Γ (.list .nat) := .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd m)))))))))
def fgCorrs {O' : Ops ASig} {Γ : List (Ty ASig)} (m : Expr O' Γ (fig8MirT ℓ Pt)) :
    Expr O' Γ (.list (.prod .bool .nat)) :=
  .snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd m)))))))))

def fgMirMk {O' : Ops ASig} {Γ : List (Ty ASig)}
    (b win : Expr O' Γ .bool) (epoch idx : Expr O' Γ (.prod .nat .nat))
    (tL : Expr O' Γ (.opt .nat)) (trs : Expr O' Γ (.list (fig8RecT ℓ Pt)))
    (chall comp : Expr O' Γ (.list posTy)) (maxAcc : Expr O' Γ (.prod (.tbl .nat) (.tbl .nat)))
    (leaks : Expr O' Γ (.list .nat)) (corrs : Expr O' Γ (.list (.prod .bool .nat))) :
    Expr O' Γ (fig8MirT ℓ Pt) :=
  .pair b (.pair win (.pair epoch (.pair idx (.pair tL
    (.pair trs (.pair chall (.pair comp (.pair maxAcc (.pair leaks corrs)))))))))

def fgToSimMirE {O' : Ops ASig} {Γ : List (Ty ASig)} (m : Expr O' Γ (fig8MirT ℓ Pt)) :
    Expr O' Γ (simMirT ℓ Pt) :=
  SimFig8State.mMk (fgB m) (fgWin m) (fgEpoch m) (fgIdx m) (fgTL m) .nil
    (fgChall m) (fgComp m) (fgMaxAcc m) (fgLeaks m) (fgCorrs m)

def simToFgMirKeepTransE {O' : Ops ASig} {Γ : List (Ty ASig)}
    (s : Expr O' Γ (simMirT ℓ Pt)) (trs : Expr O' Γ (.list (fig8RecT ℓ Pt))) :
    Expr O' Γ (fig8MirT ℓ Pt) :=
  fgMirMk (SimFig8State.mB s) (SimFig8State.mWin s) (SimFig8State.mEpoch s)
    (SimFig8State.mIdx s) (SimFig8State.mTL s) trs
    (SimFig8State.mChall s) (SimFig8State.mComp s) (SimFig8State.mMaxAcc s)
    (SimFig8State.mLeaks s) (SimFig8State.mCorrs s)

def fgSafeChE {O' : Ops ASig} {Γ : List (Ty ASig)}
    (m : Expr O' Γ (fig8MirT ℓ Pt)) (p : Expr O' Γ .bool) : Expr O' Γ .bool :=
  SimFig8State.mSafeChE (fgToSimMirE m) p

def fgLeakE {O' : Ops ASig} {Γ : List (Ty ASig)}
    (m : Expr O' Γ (fig8MirT ℓ Pt)) (l : Expr O' Γ .nat) : Expr O' Γ (fig8MirT ℓ Pt) :=
  eLet (.pair m l)
    (simToFgMirKeepTransE
      (SimFig8State.mLeakE (fgToSimMirE (.fst .v0)) (.snd .v0))
      (fgTrans (.fst .v0)))

def fgEpMgmtE {O' : Ops ASig} {Γ : List (Ty ASig)} (qepFig : ℕ)
    (m : Expr O' Γ (fig8MirT ℓ Pt)) (p bad : Expr O' Γ .bool) :
    Expr O' Γ (.opt (fig8MirT ℓ Pt)) :=
  eLet (.pair m (.pair p bad))
    (.caseOpt
      (SimFig8State.mEpMgmtE qepFig (fgToSimMirE (.fst .v0)) (.fst (.snd .v0)) (.snd (.snd .v0)))
      .none
      (.some (simToFgMirKeepTransE .v0 (fgTrans (.fst .v1)))))

def fgRecordE {O' : Ops ASig} {Γ : List (Ty ASig)}
    (m : Expr O' Γ (fig8MirT ℓ Pt)) (p : Expr O' Γ .bool)
    (r : Expr O' Γ (fig8RecT ℓ Pt)) (isChall : Expr O' Γ .bool) : Expr O' Γ (fig8MirT ℓ Pt) :=
  eLet (.pair m (.pair p (.pair r isChall)))
    (let m0 : Expr O' _ (fig8MirT ℓ Pt) := .fst .v0
     let p0 : Expr O' _ .bool := .fst (.snd .v0)
     let r0 : Expr O' _ (fig8RecT ℓ Pt) := .fst (.snd (.snd .v0))
     let ch0 : Expr O' _ .bool := .snd (.snd (.snd .v0))
     fgMirMk (fgB m0) (fgWin m0) (fgEpoch m0)
       (pSet (fgIdx m0) p0 (posIdx (fgRecPos r0)))
       (fgTL m0) (.cons r0 (fgTrans m0))
       (.ite ch0 (.cons (fgRecPos r0) (fgChall m0)) (fgChall m0))
       (.ite (fgSafeChE m0 p0) (fgComp m0) (.cons (fgRecPos r0) (fgComp m0)))
       (fgMaxAcc m0) (fgLeaks m0) (fgCorrs m0))

def fgCompContainsE {O' : Ops ASig} {Γ : List (Ty ASig)} (Lq : ℕ)
    (m : Expr O' Γ (fig8MirT ℓ Pt)) (pos : Expr O' Γ posTy) : Expr O' Γ .bool :=
  eLet (.pair m pos) (.anyB Lq (fgComp (.fst .v0)) (posEq .v0 (.snd .v1)))

def fgCorrAllowedE {O' : Ops ASig} {Γ : List (Ty ASig)} (Lq : ℕ)
    (m : Expr O' Γ (fig8MirT ℓ Pt)) (p : Expr O' Γ .bool) : Expr O' Γ .bool :=
  eLet (.pair m p)
    (let m0 : Expr O' _ (fig8MirT ℓ Pt) := .fst .v0
     .and
       (.not (.anyB Lq (fgChall m0) (boolEq (posSender .v0) (otherE (.snd .v1)))))
       (.not (.anyB Lq (fgTrans m0)
         (.and (boolEq (posSender (fgRecPos .v0)) (otherE (.snd .v1)))
           (.not (fgCompContainsE Lq (.fst .v1) (fgRecPos .v0)))))))

def fgAfterCorrE {O' : Ops ASig} {Γ : List (Ty ASig)} (Lq : ℕ)
    (m : Expr O' Γ (fig8MirT ℓ Pt)) (p : Expr O' Γ .bool) : Expr O' Γ (fig8MirT ℓ Pt) :=
  eLet (.pair m p)
    (let m0 : Expr O' _ (fig8MirT ℓ Pt) := .fst .v0
     let p0 : Expr O' _ .bool := .snd .v0
     let comp' := Expr.foldrB Lq (fgTrans m0) (fgComp m0)
       (.ite
         (.and (boolEq (posSender (fgRecPos .v0)) (otherE (.snd .v2)))
           (.not (.anyB Lq .v1 (posEq .v0 (fgRecPos .v1)))))
         (.cons (fgRecPos .v0) .v1)
         .v1)
     let m1 := fgMirMk (fgB m0) (fgWin m0) (fgEpoch m0) (fgIdx m0) (fgTL m0)
       (fgTrans m0) (fgChall m0) comp' (fgMaxAcc m0) (fgLeaks m0) (fgCorrs m0)
     let m2 := fgLeakE m1 (maxN (.fst (fgEpoch m0)) (.snd (fgEpoch m0)))
     fgMirMk (fgB m2) (fgWin m2) (fgEpoch m2) (fgIdx m2) (fgTL m2)
       (fgTrans m2) (fgChall m2) (fgComp m2) (fgMaxAcc m2) (fgLeaks m2)
       (.cons (.pair p0 (pGet (fgEpoch m0) p0)) (fgCorrs m2)))

def trE_e {O' : Ops ASig} {Γ : List (Ty ASig)} (tr : Expr O' Γ (kemTrackT ℓ Pt)) :
    Expr O' Γ U64 := .fst tr

def trE_c {O' : Ops ASig} {Γ : List (Ty ASig)} (tr : Expr O' Γ (kemTrackT ℓ Pt)) :
    Expr O' Γ (kemCoinsT ℓ Pt) := .fst (.snd tr)

def trE_st {O' : Ops ASig} {Γ : List (Ty ASig)} (tr : Expr O' Γ (kemTrackT ℓ Pt)) :
    Expr O' Γ (.prod (B 32) (B 32)) := .fst (.snd (.snd tr))

def trE_sentB {O' : Ops ASig} {Γ : List (Ty ASig)} (tr : Expr O' Γ (kemTrackT ℓ Pt)) :
    Expr O' Γ (.list (kemSentEntryT ℓ Pt)) := .fst (.snd (.snd (.snd tr)))

def trE_sendCtr {O' : Ops ASig} {Γ : List (Ty ASig)} (tr : Expr O' Γ (kemTrackT ℓ Pt)) :
    Expr O' Γ (.prod (.tbl .nat) (.tbl .nat)) := .fst (.snd (.snd (.snd (.snd tr))))

def trE_cand {O' : Ops ASig} {Γ : List (Ty ASig)} (tr : Expr O' Γ (kemTrackT ℓ Pt)) :
    Expr O' Γ (.opt (.prod BV512 BV256)) := .snd (.snd (.snd (.snd (.snd tr))))

def trMk {O' : Ops ASig} {Γ : List (Ty ASig)}
    (e : Expr O' Γ U64) (c : Expr O' Γ (kemCoinsT ℓ Pt))
    (st : Expr O' Γ (.prod (B 32) (B 32)))
    (sentB : Expr O' Γ (.list (kemSentEntryT ℓ Pt)))
    (sendCtr : Expr O' Γ (.prod (.tbl .nat) (.tbl .nat)))
    (cand : Expr O' Γ (.opt (.prod BV512 BV256))) : Expr O' Γ (kemTrackT ℓ Pt) :=
  .pair e (.pair c (.pair st (.pair sentB (.pair sendCtr cand))))

def kfSimC {O' : Ops ASig} {Γ : List (Ty ASig)} (s : Expr O' Γ (kemFailStateT ℓ Pt)) :
    Expr O' Γ (simFullT ℓ Pt) := .fst s

def kfFig8 {O' : Ops ASig} {Γ : List (Ty ASig)} (s : Expr O' Γ (kemFailStateT ℓ Pt)) :
    Expr O' Γ (fig8GsT ℓ Pt) := .fst (.snd s)

def kfTrack {O' : Ops ASig} {Γ : List (Ty ASig)} (s : Expr O' Γ (kemFailStateT ℓ Pt)) :
    Expr O' Γ (kemTrackT ℓ Pt) := .snd (.snd s)

def kfMk {O' : Ops ASig} {Γ : List (Ty ASig)}
    (sC : Expr O' Γ (simFullT ℓ Pt)) (g : Expr O' Γ (fig8GsT ℓ Pt))
    (tr : Expr O' Γ (kemTrackT ℓ Pt)) : Expr O' Γ (kemFailStateT ℓ Pt) :=
  .pair sC (.pair g tr)

def sendReplyE {O' : Ops ASig} {Γ : List (Ty ASig)} (optW : Expr O' Γ (.opt (B 32))) :
    Expr O' Γ (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) :=
  .pair optW (.pair .none .none)

def corrReplyE {O' : Ops ASig} {Γ : List (Ty ASig)} (optG : Expr O' Γ (.opt GhostStT)) :
    Expr O' Γ (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) :=
  .pair .none (.pair .none optG)

/-! ## Issue-1275 fixup and `honestExchangeFailsAtomicC` -/

def bytes2EqLitE {Γ : List (Ty ASig)} (x : Expr AOps Γ (B 2)) (b0 b1 : BitVec 8) :
    Expr AOps Γ .bool :=
  sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (.bytesEq 2 2)
    (.pair x
      (sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) (.bytesLit 2 [b0, b1]) .unit))

def issue1275ScanStepE {Γ : List (Ty ASig)} :
    Expr AOps (.prod (B 512) (.opt .bool) :: Γ) (.prod (B 512) (.opt .bool)) :=
  let rem : Expr AOps (.prod (B 512) (.opt .bool) :: Γ) (B 512) := .fst .v0
  .caseOpt (.snd .v0)
    (.ite
      (.lt (.nat 1)
        (sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) (.bytesLen 512) rem))
      (eLet
        (sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) (.bytesTakeK 512 2) rem)
        (let p2 : Expr AOps (B 2 :: .prod (B 512) (.opt .bool) :: Γ) (B 2) := .v0
         let rem1 : Expr AOps (B 2 :: .prod (B 512) (.opt .bool) :: Γ) (B 512) := .fst .v1
         let isCont :=
           boolOrE
             (bytes2EqLitE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
               (decT := decT) (lam := lam) p2 0x00#8 0x00#8)
             (bytes2EqLitE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
               (decT := decT) (lam := lam) p2 0xff#8 0xff#8)
         let isFlip :=
           boolOrE
             (bytes2EqLitE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
               (decT := decT) (lam := lam) p2 0x00#8 0x01#8)
             (boolOrE
               (bytes2EqLitE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
                 (decT := decT) (lam := lam) p2 0x00#8 0x02#8)
               (bytes2EqLitE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
                 (decT := decT) (lam := lam) p2 0xff#8 0xfe#8))
         .ite isCont
           (.pair
             (sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
               (decT := decT) (lam := lam) (.bytesDrop 512) (.pair (.nat 2) rem1))
             .none)
           (.pair rem1 (.some isFlip))))
      (.pair rem (.some (.bool false))))
    .v1

def swapPairsStepE {Γ : List (Ty ASig)} :
    Expr AOps (.prod (B 2048) (B 2048) :: Γ) (.prod (B 2048) (B 2048)) :=
  let rem : Expr AOps (.prod (B 2048) (B 2048) :: Γ) (B 2048) := .fst .v0
  let acc : Expr AOps (.prod (B 2048) (B 2048) :: Γ) (B 2048) := .snd .v0
  .ite
    (.lt (.nat 1)
      (sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) (.bytesLen 2048) rem))
    (let b0 := sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
       (decT := decT) (lam := lam) (.bytesTakeK 2048 1) rem
     let b1 := sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
       (decT := decT) (lam := lam) (.bytesTakeK 2048 1)
       (sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
         (decT := decT) (lam := lam) (.bytesDrop 2048) (.pair (.nat 1) rem))
     let swapped2 : Expr AOps (.prod (B 2048) (B 2048) :: Γ) (B 2) :=
       sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
         (decT := decT) (lam := lam) (.bytesCat 1 1) (.pair b1 b0)
     let rem' := sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
       (decT := decT) (lam := lam) (.bytesDrop 2048) (.pair (.nat 2) rem)
     let acc' := sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
       (decT := decT) (lam := lam) (.bytesTakeK 2050 2048)
       (sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
         (decT := decT) (lam := lam) (.bytesCat 2048 2) (.pair acc swapped2))
     .pair rem' acc')
    .v0

/-- Atomic `Comp` computing `(potentiallyFixStateIncorrectlyEncodedByLibcruxIssue1275Bytes es).getD es`
for `es` of length `2080`. -/
def issue1275FixEsC {Γ : List (Ty ASig)} (esE : Expr AOps Γ (B 2080)) :
    Comp AOps (coinOnlyIface ℓ Pt) Γ (B 2080) :=
  .bind (.ret esE)
    (let errSlice : Expr AOps (B 2080 :: Γ) (B 512) :=
       sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
         (decT := decT) (lam := lam) (.bytesTakeK 2080 512)
         (sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
           (decT := decT) (lam := lam) (.bytesDrop 2080) (.pair (.nat 1536) .v0))
     .bind
       (.iter 256 (.pair errSlice .none)
         (.ret (issue1275ScanStepE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
           (encT := encT) (decT := decT) (lam := lam))))
       (let needsFlip : Expr AOps (.prod (B 512) (.opt .bool) :: B 2080 :: Γ) .bool :=
          .caseOpt (.snd .v0) (.bool false) .v0
        .ite needsFlip
          (let initSwap : Expr AOps (.prod (B 512) (.opt .bool) :: B 2080 :: Γ)
              (.prod (B 2048) (B 2048)) :=
             .pair
               (sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
                 (decT := decT) (lam := lam) (.bytesTakeK 2080 2048) .v1)
               (sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
                 (decT := decT) (lam := lam) (.bytesLit 2048 []) .unit)
           .bind
             (.iter 1024 initSwap
               (.ret (swapPairsStepE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                 (encT := encT) (decT := decT) (lam := lam))))
             (let tail32 :=
                sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
                  (decT := decT) (lam := lam) (.bytesTakeK 2080 32)
                  (sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
                    (decT := decT) (lam := lam) (.bytesDrop 2080) (.pair (.nat 2048) .v2))
              .ret
                (sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
                  (decT := decT) (lam := lam) (.bytesCat 2048 32) (.pair (.snd .v0) tail32))))
          (.ret .v1)))

/-- Atomic `Comp` computing `K.honestExchangeFails ⟨coinBytes seed, _⟩ (keyToBytesVec32 rand)`. -/
def honestExchangeFailsAtomicC {Γ : List (Ty ASig)}
    (seedE : Expr AOps Γ BV512) (randE : Expr AOps Γ BV256) :
    Comp AOps (coinOnlyIface ℓ Pt) Γ .bool :=
  .bind
    (.ret
      (.pair
        (sOpSpqr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) .kem768FromSeed seedE)
        randE))
    (let hdr1 := Expr.fst (.fst .v0)
     let rand1 := Expr.snd .v0
     .caseOpt
       (sOpSpqr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
         (decT := decT) (lam := lam) .kem768Encaps1 (.pair hdr1 rand1))
       (.ret (.bool true))
       (let hdr2 := Expr.fst (.fst .v1)
        let ek2 := Expr.fst (.snd (.fst .v1))
        let es2 := Expr.fst (.snd .v0)
        .ite
          (.not
            (sOpSpqr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
              (decT := decT) (lam := lam) .kem768ValidPk (.pair hdr2 ek2)))
          (.ret (.bool true))
          (.bind
            (issue1275FixEsC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
              (decT := decT) (lam := lam) es2)
            (let ek3 := Expr.fst (.snd (.fst .v2))
             .ret
               (Expr.caseOpt
                 (sOpSpqr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
                   (decT := decT) (lam := lam) .kem768Encaps2 (.pair .v0 ek3))
                 (.bool true)
                 (Expr.caseOpt
                   (sOpSpqr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
                     (decT := decT) (lam := lam) .kem768Decaps
                     (.pair (.snd (.snd (.fst .v3))) (.pair (.fst .v2) .v0)))
                   (.bool true)
                   (.not
                     (sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
                       (decT := decT) (lam := lam) .bv256Eq
                       (.pair .v0 (.snd (.snd .v3)))))))))))

/-! ## Braid-tracker send step -/

def encRandBvAtomicE {Γ : List (Ty ASig)} (rqE : Expr AOps Γ BV512) : Expr AOps Γ BV256 :=
  sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) .bytesToBv256
    (sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (.bytesTakeK 64 32)
      (sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) .bv512ToBytes64 rqE))

/-- Test whether `V1State.encodeRaw st.into_pb` encodes `.keysUnsampled _` (protobuf field `1#32`,
wire tag byte `0x0a#8`). -/
def isKeysUnsampledV1E {Γ : List (Ty ASig)} (v1E : Expr AOps Γ (B 32)) : Expr AOps Γ .bool :=
  sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (.bytesEq 1 1)
    (.pair
      (sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) (.bytesTakeK 32 1) v1E)
      (sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) (.bytesLit 1 [0x0a#8]) .unit))

/-- Test whether `V1State.encodeRaw st.into_pb` encodes `.headerReceived _` (protobuf field `7#32`,
wire tag byte `0x3a#8`). -/
def isHeaderReceivedV1E {Γ : List (Ty ASig)} (v1E : Expr AOps Γ (B 32)) : Expr AOps Γ .bool :=
  sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (.bytesEq 1 1)
    (.pair
      (sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) (.bytesTakeK 32 1) v1E)
      (sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) (.bytesLit 1 [0x3a#8]) .unit))

def ekSideIsAE {Γ : List (Ty ASig)} (eE : Expr AOps Γ U64) : Expr AOps Γ .bool :=
  .eqN
    (.modK 2
      (sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) .u64ToNat eE))
    (.nat 1)

def nextKemCoinsAtomicE {Γ : List (Ty ASig)}
    (cE : Expr AOps Γ (kemCoinsT ℓ Pt)) (v1QE : Expr AOps Γ (B 32))
    (rqE : Expr AOps Γ BV512) : Expr AOps Γ (kemCoinsT ℓ Pt) :=
  eLet (.pair cE (.pair v1QE rqE))
    (let c0 : Expr AOps _ (kemCoinsT ℓ Pt) := .fst .v0
     .caseSum c0
       (.ite
         (isKeysUnsampledV1E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
           (decT := decT) (lam := lam) (.fst (.snd .v1)))
         (.inr (.inl (.snd (.snd .v1))))
         (.inl .unit))
       (.caseSum .v0
         (.ite
           (isHeaderReceivedV1E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
             (decT := decT) (lam := lam) (.fst (.snd .v2)))
           (.inr (.inr
             (.pair .v0
               (encRandBvAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
                 (decT := decT) (lam := lam) (.snd (.snd .v2))))))
           (.inr (.inl .v0)))
         (.inr (.inr .v0))))

def nextKemCandAtomicC {Γ : List (Ty ASig)}
    (trE : Expr AOps Γ (kemTrackT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (rqE : Expr AOps Γ BV512) :
    Comp AOps (coinOnlyIface ℓ Pt) Γ (.opt (.prod BV512 BV256)) :=
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
                 (honestExchangeFailsAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
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

def stepPostKemSendE (q : ℕ) {Γ : List (Ty ASig)}
    (trE : Expr AOps Γ (kemTrackT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (rqE : Expr AOps Γ BV512) (candE : Expr AOps Γ (.opt (.prod BV512 BV256))) :
    Expr AOps Γ (.prod (kemTrackT ℓ Pt) (kemTrackT ℓ Pt)) :=
  eLet (.pair trE (.pair qBE (.pair rqE candE)))
    (let tr0 : Expr AOps _ (kemTrackT ℓ Pt) := .fst .v0
     let q0 : Expr AOps _ .bool := .fst (.snd .v0)
     let rq0 : Expr AOps _ BV512 := .fst (.snd (.snd .v0))
     let cand0 : Expr AOps _ (.opt (.prod BV512 BV256)) := .snd (.snd (.snd .v0))
     let v1Q := pGet (trE_st tr0) q0
     let trCandOnly := trMk (trE_e tr0) (trE_c tr0) (trE_st tr0)
       (trE_sentB tr0) (trE_sendCtr tr0) cand0
     .caseOpt
       (.snd
         (sOpSpqr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
           (decT := decT) (lam := lam) .spqrBraidSend (.pair v1Q rq0)))
       (.pair trCandOnly trCandOnly)
       (let tr1 : Expr AOps _ (kemTrackT ℓ Pt) := .fst .v1
        let q1 : Expr AOps _ .bool := .fst (.snd .v1)
        let rq1 : Expr AOps _ BV512 := .fst (.snd (.snd .v1))
        let cand1 : Expr AOps _ (.opt (.prod BV512 BV256)) := .snd (.snd (.snd .v1))
        let newV1 := Expr.fst .v0
        let msgEpoch := Expr.fst (.snd .v0)
        let payloadSuffix := Expr.snd (.snd (.snd .v0))
        let epIdx :=
          Expr.sub
            (sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
              (decT := decT) (lam := lam) .u64ToNat msgEpoch)
            (.nat 1)
        let ctrTblQ := pGet (trE_sendCtr tr1) q1
        let n1 := Expr.add (.tget ctrTblQ epIdx) (.nat 1)
        let ctrBv := sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) .u32OfNat n1
        let newEntry : Expr AOps _ (kemSentEntryT ℓ Pt) :=
          .pair (.pair msgEpoch payloadSuffix) ctrBv
        let sentB' := Expr.appendL (q + 1) (trE_sentB tr1) (.cons newEntry .nil)
        let sendCtr' := pSet (trE_sendCtr tr1) q1 (.tset ctrTblQ epIdx n1)
        let st' := pSet (trE_st tr1) q1 newV1
        let c' := nextKemCoinsAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam) (trE_c tr1) (pGet (trE_st tr1) q1) rq1
        let trFull := trMk (trE_e tr1) c' st' sentB' sendCtr' cand1
        let trCandOnly1 := trMk (trE_e tr1) (trE_c tr1) (trE_st tr1)
          (trE_sentB tr1) (trE_sendCtr tr1) cand1
        .pair trFull trCandOnly1))

/-- Atomic `Comp` computing `(stepKemFailSend tr Q rq, { tr with cand := (stepKemFailSend tr Q rq).cand })`. -/
def stepKemFailSendAtomicC (q : ℕ) {Γ : List (Ty ASig)}
    (trE : Expr AOps Γ (kemTrackT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (rqE : Expr AOps Γ BV512) :
    Comp AOps (coinOnlyIface ℓ Pt) Γ (.prod (kemTrackT ℓ Pt) (kemTrackT ℓ Pt)) :=
  .bind (.ret (.pair trE (.pair qBE rqE)))
    (.bind
      (nextKemCandAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) (.fst .v0) (.fst (.snd .v0)) (.snd (.snd .v0)))
      (.ret
        (stepPostKemSendE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) q (.fst .v1) (.fst (.snd .v1)) (.snd (.snd .v1)) .v0)))

/-! ## Local Fig. 8 send and simulator post-send -/

def samIfNecFig8AtomicC {Γ : List (Ty ASig)} (rcE : Expr AOps Γ (.opt BV256)) :
    Comp AOps (coinOnlyIface ℓ Pt) Γ (.prod BV256 .bool) :=
  .caseOpt rcE
    (.bind (Comp.sample (I := coinOnlyIface ℓ Pt) (UniformSamplerTag.base .bv256) .unit)
      (.ret (.pair .v0 (.bool false))))
    (.ret (.pair .v0 (.bool true)))

def fig8SendOrChalPostE (idA idB : IdentityKey) (qep B : ℕ) {Γ : List (Ty ASig)}
    (argE : Expr AOps Γ
      (.prod (fig8GsT ℓ Pt)
        (.prod .bool (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) (.prod PlainT (.opt PlainT))))))
    (coinsE : Expr AOps Γ BV256) (badE : Expr AOps Γ .bool) :
    Expr AOps Γ (.prod (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))) (fig8GsT ℓ Pt)) :=
  eLet (.pair argE (.pair coinsE badE))
    (let arg0 := Expr.fst .v0
     let g0 : Expr AOps _ (fig8GsT ℓ Pt) := .fst arg0
     let q0 : Expr AOps _ .bool := .fst (.snd arg0)
     let bad0 : Expr AOps _ .bool := .snd (.snd .v0)
     .caseOpt (fgEpMgmtE (qep + 1) (fgMir g0) q0 bad0)
       (.pair .none g0)
       (let mir2 : Expr AOps _ (fig8MirT ℓ Pt) := .v0
        let arg1 := Expr.fst .v1
        let g1 : Expr AOps _ (fig8GsT ℓ Pt) := .fst arg1
        let q1 : Expr AOps _ .bool := .fst (.snd arg1)
        let pub1 : Expr AOps _ (lpubT (ℓ := ℓ) (Pt := Pt)) := .fst (.snd (.snd arg1))
        let m0_1 : Expr AOps _ PlainT := .fst (.snd (.snd (.snd arg1)))
        let chal1 : Expr AOps _ (.opt PlainT) := .snd (.snd (.snd (.snd arg1)))
        let coins1 : Expr AOps _ BV256 := .fst (.snd .v1)
        .ite (.and (isSomeE chal1) (.not (fgSafeChE mir2 q1)))
          (.pair .none g1)
          (let mPlain : Expr AOps _ PlainT :=
             .caseOpt chal1 m0_1
               (.ite (fgB .v1)
                 .v0
                 (.fst (.snd (.snd (.snd (.fst .v2))))))
           let mFull := Expr.pair pub1 mPlain
           eLet
             (fig8SendStepAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
               (decT := decT) (lam := lam) idA idB B
               (pGet (fgSt g1) q1) (.some (.pair mFull coins1)))
             (let out2 := Expr.v0
              let mir3 : Expr AOps _ (fig8MirT ℓ Pt) := .v1
              let arg3 := Expr.fst .v2
              let g3 : Expr AOps _ (fig8GsT ℓ Pt) := .fst arg3
              let q3 : Expr AOps _ .bool := .fst (.snd arg3)
              let pub3 : Expr AOps _ (lpubT (ℓ := ℓ) (Pt := Pt)) := .fst (.snd (.snd arg3))
              let m0_3 : Expr AOps _ PlainT := .fst (.snd (.snd (.snd arg3)))
              let chal3 : Expr AOps _ (.opt PlainT) := .snd (.snd (.snd (.snd arg3)))
              let mPlain3 : Expr AOps _ PlainT :=
                .caseOpt chal3 m0_3
                  (.ite (fgB .v2)
                    .v0
                    (.fst (.snd (.snd (.snd (.fst .v3))))))
              let st' := Expr.fst (.snd out2)
              let c := Expr.snd (.snd out2)
              let recE : Expr AOps _ (fig8RecT ℓ Pt) :=
                .pair
                  (.pair q3
                    (.pair (pGet (fgEpoch mir3) q3)
                      (.add (pGet (fgIdx mir3) q3) (.nat 1))))
                  (.pair (.pair pub3 mPlain3) c)
              let g' : Expr AOps _ (fig8GsT ℓ Pt) :=
                .pair (pSet (fgSt g3) q3 st')
                  (fgRecordE mir3 q3 recE (isSomeE chal3))
              .pair (.some c) g'))))

/-- Unified local Fig. 8 `transmitImpl` (`chal = none`) and `challImpl` (`chal = some m₁`) `Comp`. -/
def fig8SendOrChalAtomicC (idA idB : IdentityKey) (qep B : ℕ) {Γ : List (Ty ASig)}
    (gE : Expr AOps Γ (fig8GsT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (pubE : Expr AOps Γ (lpubT (ℓ := ℓ) (Pt := Pt)))
    (m0E : Expr AOps Γ PlainT) (chalE : Expr AOps Γ (.opt PlainT))
    (rcE : Expr AOps Γ (.opt BV256)) :
    Comp AOps (coinOnlyIface ℓ Pt) Γ
      (.prod (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))) (fig8GsT ℓ Pt)) :=
  .bind (.ret (.pair (.pair gE (.pair qBE (.pair pubE (.pair m0E chalE)))) rcE))
    (.ite (fgWin (fgMir (.fst (.fst .v0))))
      (.ret (.pair .none (.fst (.fst .v0))))
      (.bind
        (samIfNecFig8AtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) (.snd .v0))
        (.ret
          (fig8SendOrChalPostE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
            (decT := decT) (lam := lam) idA idB qep B
            (.fst .v1) (.fst .v0) (.snd .v0)))))

def scPostSendAtomicE (idA idB : IdentityKey) {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (s1E : Expr AOps Γ (simMirT ℓ Pt))
    (qBE : Expr AOps Γ .bool) (m0E : Expr AOps Γ PlainT)
    (isChallE : Expr AOps Γ .bool) (pq'E : Expr AOps Γ (B 32))
    (pnE : Expr AOps Γ U32) (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    Expr AOps Γ (.prod (B 32) (simFullT ℓ Pt)) :=
  eLet (.pair sCE (.pair s1E (.pair qBE (.pair m0E (.pair isChallE (.pair pq'E (.pair pnE cE)))))))
    (let sC0 : Expr AOps _ (simFullT ℓ Pt) := .fst .v0
     let s0 : Expr AOps _ (simBaseT ℓ Pt) := scBase sC0
     let s1_0 : Expr AOps _ (simMirT ℓ Pt) := .fst (.snd .v0)
     let q0 : Expr AOps _ .bool := .fst (.snd (.snd .v0))
     let m0 : Expr AOps _ PlainT := .fst (.snd (.snd (.snd .v0)))
     let ch0 : Expr AOps _ .bool := .fst (.snd (.snd (.snd (.snd .v0))))
     let pq0 : Expr AOps _ (B 32) := .fst (.snd (.snd (.snd (.snd (.snd .v0)))))
     let pn0 : Expr AOps _ U32 := .fst (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))
     let c0 : Expr AOps _ (fig8CtT (ℓ := ℓ) (Pt := Pt)) :=
       .snd (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))
     let w0 := toWireAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
       (decT := decT) (lam := lam) c0
     let rec' := Expr.pair
       (.pair q0
         (.pair (pGet (SimFig8State.mEpoch s1_0) q0)
           (.add (pGet (SimFig8State.mIdx s1_0) q0) (.nat 1))))
       (.pair m0 w0)
     let mir' := SimFig8State.mRecordE s1_0 q0 rec' ch0
     let base' := ssMk mir' (pSet (ssPq s0) q0 pq0) (pSet (ssPn s0) q0 pn0) (ssUnackA s0)
       (.cons (.pair w0 c0) (ssHonest s0)) (ssChains s0) (ssAmb s0) (ssStopped s0)
     let kQ := pGet (scKept sC0) q0
     let sent' : Expr AOps _ (.list (sentEntryT ℓ Pt)) :=
       .caseOpt (.fst kQ)
         (scSent sC0)
         (.ite (sendsInE (f8Id .v0) (.add (f8Tcur .v0) (.nat 1)))
           (scSent (.fst .v1))
           (.caseOpt (f8VS .v0)
             (scSent (.fst .v1))
             (.cons
               (.pair (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v2))))))) .v0)
               (scSent (.fst .v2)))))
     let kept' := pSet (scKept sC0) q0
       (keptSendAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
         (decT := decT) (lam := lam) idA idB kQ)
     .pair w0 (scMk base' kept' sent' (scSnaps sC0)))

/-! ## Send, challenge, and corrupt branch programs -/

def drawSendCoinsAtomicC {Γ : List (Ty ASig)} (rE : Expr AOps Γ (.opt BV512)) :
    Comp AOps (coinOnlyIface ℓ Pt) Γ (.prod BV512 (.opt BV256)) :=
  .caseOpt rE
    (.bind (Comp.sample (I := coinOnlyIface ℓ Pt) (UniformSamplerTag.base .bv512) .unit)
      (.ret (.pair .v0 .none)))
    (.bind (Comp.sample (I := coinOnlyIface ℓ Pt) (UniformSamplerTag.base .bv256) .unit)
      (.ret (.pair .v1 (.some .v0))))

def sendPnE {Γ : List (Ty ASig)}
    (s0 : Expr AOps Γ (simBaseT ℓ Pt)) (s1 : Expr AOps Γ (simMirT ℓ Pt))
    (q0 : Expr AOps Γ .bool) : Expr AOps Γ U32 :=
  .ite (.not (.eqN (pGet (SimFig8State.mEpoch s1) q0) (pGet (SimFig8State.mEpoch (ssMir s0)) q0)))
    (sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) .u32OfNat
      (.sub (pGet (SimFig8State.mIdx (ssMir s0)) q0) (.nat 1)))
    (pGet (ssPn s0) q0)

/-- Context-polymorphic atomic `Comp` implementing the `.transmit` (`chal = none`) and
`.challenge` (`chal = some m₁`) branches of `KemFailRed`. -/
def kemFailSendBodyC (idA idB : IdentityKey) (qep B q : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (kemFailStateT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (m0E : Expr AOps Γ PlainT) (chalE : Expr AOps Γ (.opt PlainT))
    (rE : Expr AOps Γ (.opt BV512)) :
    Comp AOps (coinOnlyIface ℓ Pt) Γ
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (kemFailStateT ℓ Pt)) :=
  .bind (.ret (.pair stE (.pair qBE (.pair m0E (.pair chalE rE)))))
    (let st0 : Expr AOps _ (kemFailStateT ℓ Pt) := .fst .v0
     let sC0 := kfSimC st0
     let s0 := scBase sC0
     let q0 : Expr AOps _ .bool := .fst (.snd .v0)
     let r0 : Expr AOps _ (.opt BV512) := .snd (.snd (.snd (.snd .v0)))
     let refuse :=
       boolOrE (ssStopped s0)
         (boolOrE (SimFig8State.mWin (ssMir s0))
           (.not (SimFig8State.mNoBobEpoch0E (ssMir s0) q0)))
     .ite refuse
       (.ret (.pair (sendReplyE .none) st0))
       (.caseOpt (SimFig8State.mEpMgmtE qep (ssMir s0) q0 (isSomeE r0))
         (.ret (.pair (sendReplyE .none) st0))
         (let s1 : Expr AOps _ (simMirT ℓ Pt) := .v0
          let st1 : Expr AOps _ (kemFailStateT ℓ Pt) := .fst .v1
          let q1 : Expr AOps _ .bool := .fst (.snd .v1)
          let chal1 : Expr AOps _ (.opt PlainT) := .fst (.snd (.snd (.snd .v1)))
          let r1 : Expr AOps _ (.opt BV512) := .snd (.snd (.snd (.snd .v1)))
          .ite (.and (isSomeE chal1) (.not (SimFig8State.mSafeChE s1 q1)))
            (.ret (.pair (sendReplyE .none) st1))
            (.bind
              (drawSendCoinsAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                (encT := encT) (decT := decT) (lam := lam) r1)
              (let rq2 : Expr AOps _ BV512 := .fst .v0
               let st2 : Expr AOps _ (kemFailStateT ℓ Pt) := .fst .v2
               let q2 : Expr AOps _ .bool := .fst (.snd .v2)
               .bind
                 (stepKemFailSendAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                   (encT := encT) (decT := decT) (lam := lam) q (kfTrack st2) q2 rq2)
                 (let rq3 : Expr AOps _ BV512 := .fst .v1
                  let s1_3 : Expr AOps _ (simMirT ℓ Pt) := .v2
                  let st3 : Expr AOps _ (kemFailStateT ℓ Pt) := .fst .v3
                  let sC3 := kfSimC st3
                  let s3 := scBase sC3
                  let q3 : Expr AOps _ .bool := .fst (.snd .v3)
                  let pn3 := sendPnE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                    (encT := encT) (decT := decT) (lam := lam) s3 s1_3 q3
                  .bind
                    (mkPubAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                      (encT := encT) (decT := decT) (lam := lam)
                      (coinOnlyIface ℓ Pt) idA idB s3 q3 rq3 pn3)
                    (.caseOpt .v0
                      (let trFail4 : Expr AOps _ (kemTrackT ℓ Pt) := .snd .v1
                       let st4 : Expr AOps _ (kemFailStateT ℓ Pt) := .fst .v4
                       .ret (.pair (sendReplyE .none) (kfMk (kfSimC st4) (kfFig8 st4) trFail4)))
                      (let pub5 : Expr AOps _ (lpubT (ℓ := ℓ) (Pt := Pt)) := .snd .v0
                       let rc5 : Expr AOps _ (.opt BV256) := .snd .v3
                       let st5 : Expr AOps _ (kemFailStateT ℓ Pt) := .fst .v5
                       let q5 : Expr AOps _ .bool := .fst (.snd .v5)
                       let m0_5 : Expr AOps _ PlainT := .fst (.snd (.snd .v5))
                       let chal5 : Expr AOps _ (.opt PlainT) := .fst (.snd (.snd (.snd .v5)))
                       .bind
                         (fig8SendOrChalAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                           (encT := encT) (decT := decT) (lam := lam) idA idB qep B
                           (kfFig8 st5) q5 pub5 m0_5 chal5 rc5)
                         (.caseOpt (.fst .v0)
                           (let gFail6 : Expr AOps _ (fig8GsT ℓ Pt) := .snd .v0
                            let trFail6 : Expr AOps _ (kemTrackT ℓ Pt) := .snd .v3
                            let st6 : Expr AOps _ (kemFailStateT ℓ Pt) := .fst .v6
                            .ret (.pair (sendReplyE .none) (kfMk (kfSimC st6) gFail6 trFail6)))
                           (let c7 : Expr AOps _ (fig8CtT (ℓ := ℓ) (Pt := Pt)) := .v0
                            let pq'7 : Expr AOps _ (_root_.ReductionDsl.B 32) := .fst .v2
                            let s1_7 : Expr AOps _ (simMirT ℓ Pt) := .v6
                            let st7 : Expr AOps _ (kemFailStateT ℓ Pt) := .fst .v7
                            let sC7 := kfSimC st7
                            let s7 := scBase sC7
                            let q7 : Expr AOps _ .bool := .fst (.snd .v7)
                            let m0_7 : Expr AOps _ PlainT := .fst (.snd (.snd .v7))
                            let chal7 : Expr AOps _ (.opt PlainT) := .fst (.snd (.snd (.snd .v7)))
                            let pn7 := sendPnE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                              (encT := encT) (decT := decT) (lam := lam) s7 s1_7 q7
                            .ret
                              (eLet
                                (scPostSendAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                                  (encT := encT) (decT := decT) (lam := lam) idA idB
                                  sC7 s1_7 q7 m0_7 (isSomeE chal7) pq'7 pn7 c7)
                                (.pair
                                  (sendReplyE (.some (.fst .v0)))
                                  (kfMk (.snd .v0) (.snd .v2) (.fst .v5))))))))))))))

def kemCorrBlockedE (L : ℕ) {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (qBE : Expr AOps Γ .bool) : Expr AOps Γ .bool :=
  eLet (.pair sCE qBE)
    (let base0 := scBase (.fst .v0)
     let mir0 := ssMir base0
     let q0 : Expr AOps _ .bool := .snd .v0
     boolOrE (ssStopped base0)
       (boolOrE (SimFig8State.mWin mir0)
         (boolOrE (.not (SimFig8State.mCorrAllowedE L mir0 q0))
           (boolOrE (SimFig8State.mInWinE mir0 q0)
             (.not (SimFig8State.mNoSpkCorrE mir0 q0))))))

def kemCorrChainsUpdE {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (stQE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) :
    Expr AOps Γ (.prod (.list (ghostChainT ℓ Pt)) (.list (ghostChainT ℓ Pt))) :=
  eLet (.pair sCE (.pair qBE stQE))
    (let base0 := scBase (.fst .v0)
     let mir0 := ssMir base0
     let q0 : Expr AOps _ .bool := .fst (.snd .v0)
     let st0 : Expr AOps _ (fig8StT (ℓ := ℓ) (Pt := Pt)) := .snd (.snd .v0)
     let isBobEp0 := Expr.and q0 (.eqN (.snd (SimFig8State.mEpoch mir0)) (.nat 0))
     .ite isBobEp0
       (.caseSum (f8Gamma st0)
         (ssChains (scBase (.fst .v1)))
         (let pkE := sOpPtEnc (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
            (decT := decT) (lam := lam) .ptEncPk
            (sOpGrp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
              (decT := decT) (lam := lam) .ptDh
              (.pair .v0
                (sOpGrp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
                  (decT := decT) (lam := lam) .ptBase .unit)))
          let cs0 := ssChains (scBase (.fst .v1))
          .pair (revealSpkChainsE (.fst cs0) pkE) (.snd cs0)))
       (ssChains base0))

def kemFailCorrOutE (idA idB : IdentityKey) (L B_skip : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (kemFailStateT ℓ Pt)) (qBE : Expr AOps Γ .bool) :
    Expr AOps Γ (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (kemFailStateT ℓ Pt)) :=
  eLet (.pair stE qBE)
    (let st0 : Expr AOps _ (kemFailStateT ℓ Pt) := .fst .v0
     let sC0 := kfSimC st0
     let g0 := kfFig8 st0
     let q0 : Expr AOps _ .bool := .snd .v0
     .ite
       (boolOrE
         (kemCorrBlockedE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
           (decT := decT) (lam := lam) L sC0 q0)
         (boolOrE (fgWin (fgMir g0))
           (.not (fgCorrAllowedE L (fgMir g0) q0))))
       (.pair (corrReplyE .none) st0)
       (let stQ := pGet (fgSt g0) q0
        eLet
          (kemCorrChainsUpdE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
            (decT := decT) (lam := lam) sC0 q0 stQ)
          (let st1 : Expr AOps _ (kemFailStateT ℓ Pt) := .fst .v1
           let q1 : Expr AOps _ .bool := .snd .v1
           let sC1 := kfSimC st1
           let g1 := kfFig8 st1
           let b1 := scBase sC1
           let stQ1 := pGet (fgSt g1) q1
           let baseForGhost := ssMk (ssMir b1) (ssPq b1) (ssPn b1) (ssUnackA b1)
             (ssHonest b1) .v0 (ssAmb b1) (ssStopped b1)
           eLet
             (toGhostE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
               (decT := decT) (lam := lam) idA idB B_skip baseForGhost q1 stQ1)
             (let st2 : Expr AOps _ (kemFailStateT ℓ Pt) := .fst .v2
              let q2 : Expr AOps _ .bool := .snd .v2
              let sC2 := kfSimC st2
              let g2 := kfFig8 st2
              let tr2 := kfTrack st2
              let b2 := scBase sC2
              let mir2 := ssMir b2
              let stQ2 := pGet (fgSt g2) q2
              let base' := ssMk (SimFig8State.mAfterCorrE L mir2 q2) (ssPq b2) (ssPn b2)
                (ssUnackA b2) (ssHonest b2) .v1 (ssAmb b2) (ssStopped b2)
              let kept' := pSet (scKept sC2) q2 (keptOfStAtomicE stQ2)
              let epQ := pGet (SimFig8State.mEpoch mir2) q2
              let snapEntry := Expr.pair q2 (.pair epQ .v0)
              let sC' := scMk base' kept' (scSent sC2) (.cons snapEntry (scSnaps sC2))
              let g' := Expr.pair (fgSt g2) (fgAfterCorrE L (fgMir g2) q2)
              .pair (corrReplyE (.some .v0)) (kfMk sC' g' tr2)))))

/-- Context-polymorphic atomic `Comp` implementing the `.corrupt` branch of `KemFailRed`. -/
def kemFailCorrBodyC (idA idB : IdentityKey) (L B_skip : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (kemFailStateT ℓ Pt)) (qBE : Expr AOps Γ .bool) :
    Comp AOps (coinOnlyIface ℓ Pt) Γ
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (kemFailStateT ℓ Pt)) :=
  .ret (kemFailCorrOutE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB L B_skip stE qBE)

end Definitions

/-! ## Query, cost, and description-bit bounds -/

section CostAndDescBounds

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {C : Crypto} {K : MlKem}
  {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
  {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

@[simp] theorem issue1275FixEsC_queries_zero {Γ : List (Ty ASig)}
    (esE : Expr AOps Γ (B 2080)) (w : Empty → ℕ) :
    (issue1275FixEsC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) esE).queries w (fun _ => 0) = 0 := by
  simp [issue1275FixEsC, Comp.queries]

@[simp] theorem honestExchangeFailsAtomicC_queries_zero {Γ : List (Ty ASig)}
    (seedE : Expr AOps Γ BV512) (randE : Expr AOps Γ BV256) (w : Empty → ℕ) :
    (honestExchangeFailsAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) seedE randE).queries w (fun _ => 0) = 0 := by
  simp [honestExchangeFailsAtomicC, Comp.queries]

@[simp] theorem stepKemFailSendAtomicC_queries_zero (q : ℕ) {Γ : List (Ty ASig)}
    (trE : Expr AOps Γ (kemTrackT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (rqE : Expr AOps Γ BV512) (w : Empty → ℕ) :
    (stepKemFailSendAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) q trE qBE rqE).queries w (fun _ => 0) = 0 := by
  simp [stepKemFailSendAtomicC, nextKemCandAtomicC, Comp.queries]

@[simp] theorem kemFailSendBodyC_queries_zero (idA idB : IdentityKey) (qep B q : ℕ)
    {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (kemFailStateT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (m0E : Expr AOps Γ PlainT) (chalE : Expr AOps Γ (.opt PlainT))
    (rE : Expr AOps Γ (.opt BV512)) (w : Empty → ℕ) :
    (kemFailSendBodyC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB qep B q stE qBE m0E chalE rE).queries w (fun _ => 0) = 0 := by
  simp [kemFailSendBodyC, drawSendCoinsAtomicC, fig8SendOrChalAtomicC, samIfNecFig8AtomicC,
    SimFig8Crypto.mkPubAtomicC_queries, Comp.queries]

@[simp] theorem kemFailCorrBodyC_queries_zero (idA idB : IdentityKey) (L B_skip : ℕ)
    {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (kemFailStateT ℓ Pt)) (qBE : Expr AOps Γ .bool) (w : Empty → ℕ) :
    (kemFailCorrBodyC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB L B_skip stE qBE).queries w (fun _ => 0) = 0 := by
  simp [kemFailCorrBodyC, Comp.queries]

private theorem hb0_bits : bits 0 = 1 :=
  SimFig8State.bits_zero

private theorem hb1_bits : bits 1 = 1 :=
  SimFig8State.bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)

private theorem hb2_bits : bits 2 = 2 :=
  SimFig8State.bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)

private theorem hb3_bits : bits 3 = 2 :=
  SimFig8State.bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)

private theorem hb4_bits : bits 4 = 3 := SimFig8State.bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem hb5_bits : bits 5 = 3 := SimFig8State.bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem hb6_bits : bits 6 = 3 := SimFig8State.bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem hb7_bits : bits 7 = 3 := SimFig8State.bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem hb32_bits : bits 32 = 6 := SimFig8State.bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem hb64_bits : bits 64 = 7 := SimFig8State.bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem hb256_bits : bits 256 = 9 := SimFig8State.bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem hb512_bits : bits 512 = 10 := SimFig8State.bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem hb1024_bits : bits 1024 = 11 := SimFig8State.bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem hb1536_bits : bits 1536 = 11 := SimFig8State.bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem hb2048_bits : bits 2048 = 12 := SimFig8State.bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem hb2050_bits : bits 2050 = 12 := SimFig8State.bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem hb2080_bits : bits 2080 = 12 := SimFig8State.bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem hp1_bits : bits ((1 : ℕ+) : ℕ) = 1 := hb1_bits
private theorem hp2_bits : bits ((2 : ℕ+) : ℕ) = 2 := hb2_bits
private theorem hp32_bits : bits ((32 : ℕ+) : ℕ) = 6 := hb32_bits
private theorem hp64_bits : bits ((64 : ℕ+) : ℕ) = 7 := hb64_bits
private theorem hp512_bits : bits ((512 : ℕ+) : ℕ) = 10 := hb512_bits
private theorem hp2048_bits : bits ((2048 : ℕ+) : ℕ) = 12 := hb2048_bits
private theorem hp2050_bits : bits ((2050 : ℕ+) : ℕ) = 12 := hb2050_bits
private theorem hp2080_bits : bits ((2080 : ℕ+) : ℕ) = 12 := hb2080_bits

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem bits_mono_le {a b : ℕ} (h : a ≤ b) : bits a ≤ bits b := by
  unfold _root_.ReductionDsl.bits
  exact Nat.add_le_add_right (Nat.log_mono_right h) 1

omit [SampleableType Pt] in
private theorem swapPairsStepE_cost {Γ : List (Ty ASig)} :
    (swapPairsStepE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (Γ := Γ)).cost = 14380 := by
  have hp1 : ((1 : ℕ+) : ℕ) = 1 := rfl
  have hp2 : ((2 : ℕ+) : ℕ) = 2 := rfl
  have hp2048 : ((2048 : ℕ+) : ℕ) = 2048 := rfl
  have hp2050 : ((2050 : ℕ+) : ℕ) = 2050 := rfl
  simp only [swapPairsStepE, SimFig8State.sOpPure, AtomicSessionBridge.sessPureOp,
    _root_.ReductionDsl.atomicSessionOps, _root_.ReductionDsl.atomicFig8Ops,
    _root_.ReductionDsl.atomicFsOps, _root_.ReductionDsl.Ops.sum,
    _root_.ReductionDsl.atomicPureOps, Sum.elim,
    Expr.cost, _root_.ReductionDsl.AtomicPureOp.cost, Expr.v0,
    hp1, hp2, hp2048, hp2050]
  simp only [hb1_bits, hb2_bits, hb2048_bits]
  omega

omit [SampleableType Pt] in
private theorem issue1275ScanStepE_cost {Γ : List (Ty ASig)} :
    (issue1275ScanStepE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (Γ := Γ)).cost = 1080 := by
  have hp2 : ((2 : ℕ+) : ℕ) = 2 := rfl
  have hp512 : ((512 : ℕ+) : ℕ) = 512 := rfl
  simp only [issue1275ScanStepE, bytes2EqLitE, boolOrE, SimFig8State.eLet,
    SimFig8State.sOpPure, AtomicSessionBridge.sessPureOp,
    _root_.ReductionDsl.atomicSessionOps, _root_.ReductionDsl.atomicFig8Ops,
    _root_.ReductionDsl.atomicFsOps, _root_.ReductionDsl.Ops.sum,
    _root_.ReductionDsl.atomicPureOps, Sum.elim,
    Expr.cost, _root_.ReductionDsl.AtomicPureOp.cost,
    Expr.v0, Expr.v1, List.length_cons, List.length_nil,
    hb1_bits, hb2_bits, hp2, hp512]
  rw [hb512_bits]
  decide

private theorem issue1275FixEsC_cost {Γ : List (Ty ASig)} (esE : Expr AOps Γ (B 2080)) :
    (issue1275FixEsC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) esE).cost ≤ esE.cost + 15022000 := by
  have hp32 : ((32 : ℕ+) : ℕ) = 32 := rfl
  have hp512 : ((512 : ℕ+) : ℕ) = 512 := rfl
  have hp2048 : ((2048 : ℕ+) : ℕ) = 2048 := rfl
  have hp2080 : ((2080 : ℕ+) : ℕ) = 2080 := rfl
  have hscan := issue1275ScanStepE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := B 2080 :: Γ)
  have hswap := swapPairsStepE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (Γ := .prod (B 512) (.opt .bool) :: B 2080 :: Γ)
  dsimp only [issue1275FixEsC]
  generalize issue1275ScanStepE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := B 2080 :: Γ) = eScan at hscan ⊢
  generalize swapPairsStepE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (Γ := .prod (B 512) (.opt .bool) :: B 2080 :: Γ) = eSwap at hswap ⊢
  simp only [Comp.cost, Expr.cost, SimFig8State.sOpPure, AtomicSessionBridge.sessPureOp,
    _root_.ReductionDsl.atomicSessionOps, _root_.ReductionDsl.atomicFig8Ops,
    _root_.ReductionDsl.atomicFsOps, _root_.ReductionDsl.Ops.sum,
    _root_.ReductionDsl.atomicPureOps, Sum.elim,
    _root_.ReductionDsl.AtomicPureOp.cost,
    Expr.v0, Expr.v1, Expr.v2, List.length_nil,
    hp32, hp512, hp2048, hp2080] at hscan hswap ⊢
  simp only [hb1536_bits, hb2048_bits, hscan, hswap]
  omega

theorem honestExchangeFailsAtomicC_cost {Γ : List (Ty ASig)}
    (seedE : Expr AOps Γ BV512) (randE : Expr AOps Γ BV256) :
    (honestExchangeFailsAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) seedE randE).cost ≤
      seedE.cost + randE.cost + 15085000 := by
  let Γ1 := Ty.prod (_root_.ReductionDsl.AtomicSpqrKemOp.kem768FromSeed.cod ℓ Pt) BV256 :: Γ
  let Γ2 := Ty.prod (B 960) (.prod (B 2080) BV256) :: Γ1
  have hfix := issue1275FixEsC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ2) (.fst (.snd .v0))
  dsimp only [honestExchangeFailsAtomicC]
  generalize issue1275FixEsC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ2) (.fst (.snd .v0)) = cFix at hfix ⊢
  simp only [SimFig8State.cost_sOpSpqr, SimFig8State.cost_sOpPure,
    _root_.ReductionDsl.AtomicSpqrKemOp.cost, _root_.ReductionDsl.AtomicPureOp.cost,
    Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hfix ⊢
  omega

theorem stepKemFailSendAtomicC_cost (q : ℕ) {Γ : List (Ty ASig)}
    (trE : Expr AOps Γ (kemTrackT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (rqE : Expr AOps Γ BV512) :
    (stepKemFailSendAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) q trE qBE rqE).cost ≤
      trE.cost + qBE.cost + rqE.cost + 4 * q + 15100000 := by
  let Γ0 := Ty.prod (kemTrackT ℓ Pt) (.prod .bool BV512) :: Γ
  let Γ1 := Γ0
  let Γc := BV512 :: Ty.sum BV512 (.prod BV512 BV256) ::
    Ty.prod (kemTrackT ℓ Pt) (.prod .bool BV512) :: Γ0
  have hhon := honestExchangeFailsAtomicC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γc) .v0
    (encRandBvAtomicE (.snd (.snd .v2)))
  dsimp only [stepKemFailSendAtomicC, nextKemCandAtomicC, stepPostKemSendE, nextKemCoinsAtomicE,
    encRandBvAtomicE, isKeysUnsampledV1E, isHeaderReceivedV1E, ekSideIsAE, boolEqE,
    trE_e, trE_c, trE_st, trE_sentB, trE_sendCtr, trE_cand, trMk, pGet, pSet] at hhon ⊢
  generalize honestExchangeFailsAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) .v0 _ = cHon at hhon ⊢
  have hp1 : ((1 : ℕ+) : ℕ) = 1 := rfl
  have hp32 : ((32 : ℕ+) : ℕ) = 32 := rfl
  have hp64 : ((64 : ℕ+) : ℕ) = 64 := rfl
  simp only [SimFig8State.cost_eLet, SimFig8State.cost_sOpSpqr, SimFig8State.cost_sOpPure,
    _root_.ReductionDsl.AtomicSpqrKemOp.cost, _root_.ReductionDsl.AtomicPureOp.cost,
    Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, List.length_singleton,
    hb1_bits, hb2_bits, hp1, hp32, hp64] at hhon ⊢
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem fgEpMgmtE_cost {O' : Ops ASig} {Γ : List (Ty ASig)} (qepFig : ℕ)
    (m : Expr O' Γ (fig8MirT ℓ Pt)) (p bad : Expr O' Γ .bool) :
    (fgEpMgmtE qepFig m p bad).cost ≤ m.cost + p.cost + bad.cost + 2 * bits qepFig + 1100 := by
  simp only [fgEpMgmtE, fgToSimMirE, simToFgMirKeepTransE, SimFig8State.mEpMgmtE,
    SimFig8State.cost_eLet, SimFig8State.mSafeChE, SimFig8State.mLeakE, SimFig8State.mMk,
    CryptoGames.SM.maxOptE, maxN, CryptoGames.SM.healedByE, CryptoGames.SM.leN, sendsInE,
    pGet, pSet, SimFig8State.mB, SimFig8State.mWin, SimFig8State.mEpoch, SimFig8State.mIdx,
    SimFig8State.mTL, SimFig8State.mTrans, SimFig8State.mChall, SimFig8State.mComp,
    SimFig8State.mMaxAcc, SimFig8State.mLeaks, SimFig8State.mCorrs,
    fgMirMk, fgB, fgWin, fgEpoch, fgIdx, fgTL, fgTrans, fgChall, fgComp, fgMaxAcc,
    fgLeaks, fgCorrs, Expr.cost, Expr.v0, Expr.v1, hb0_bits, hb1_bits, hb2_bits, hb3_bits]
  omega

private theorem fig8SendOrChalAtomicC_cost (idA idB : IdentityKey) (qep B : ℕ)
    {Γ : List (Ty ASig)} (gE : Expr AOps Γ (fig8GsT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (pubE : Expr AOps Γ (lpubT (ℓ := ℓ) (Pt := Pt)))
    (m0E : Expr AOps Γ PlainT) (chalE : Expr AOps Γ (.opt PlainT))
    (rcE : Expr AOps Γ (.opt BV256)) :
    (fig8SendOrChalAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB qep B gE qBE pubE m0E chalE rcE).cost ≤
      gE.cost + qBE.cost + pubE.cost + m0E.cost + chalE.cost + rcE.cost +
        2 * bits (qep + 1) + 3 * bits B + 13 * (ℓ / 32) + 235000 := by
  let fgArgT : Ty ASig := .prod (fig8GsT ℓ Pt)
    (.prod .bool (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) (.prod PlainT (.opt PlainT))))
  let Γb := Ty.prod BV256 .bool :: Ty.prod fgArgT (.opt BV256) :: Γ
  let Γ1 := Ty.prod fgArgT (.prod BV256 .bool) :: Γb
  let Γ2 := fig8MirT ℓ Pt :: Γ1
  have hep := fgEpMgmtE_cost (O' := AOps) (Γ := Γ1) (qep + 1)
    (fgMir (.fst (.fst .v0))) (.fst (.snd (.fst .v0))) (.snd (.snd .v0))
  have hfs := SimFig8Kept.fig8SendStepAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB B (Γ := Γ2)
    (pGet (fgSt (.fst (.fst .v1))) (.fst (.snd (.fst .v1))))
    (.some (.pair (.pair (.fst (.snd (.snd (.fst .v1))))
      (.caseOpt (.snd (.snd (.snd (.snd (.fst .v1))))) (.fst (.snd (.snd (.snd (.fst .v1)))))
        (.ite (fgB .v1) .v0 (.fst (.snd (.snd (.snd (.fst .v2)))))))) (.fst (.snd .v1))))
  dsimp only [fgArgT, Γb, Γ1, Γ2, fig8SendOrChalAtomicC, samIfNecFig8AtomicC,
    fig8SendOrChalPostE] at hep hfs ⊢
  generalize fgEpMgmtE (O' := AOps) (qep + 1) _ _ _ = eep at hep ⊢
  generalize fig8SendStepAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB B _ _ = efs at hfs ⊢
  simp only [SimFig8State.cost_eLet, fgRecordE, fgSafeChE, fgToSimMirE,
    SimFig8State.mSafeChE, CryptoGames.SM.healedByE, CryptoGames.SM.leN,
    SimFig8State.mMk, SimFig8State.mEpoch, SimFig8State.mTL,
    fgMirMk, fgSt, fgMir, fgRecPos, fgB, fgWin, fgEpoch, fgIdx,
    fgTL, fgTrans, fgChall, fgComp, fgMaxAcc, fgLeaks, fgCorrs, pGet, pSet, posIdx,
    isSomeE, Comp.cost, Expr.cost,
    _root_.ReductionDsl.AtomicUnifBase.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, hb1_bits, hb3_bits] at hep hfs ⊢
  omega

omit [SampleableType Pt] in
private theorem scPostSendAtomicE_cost (idA idB : IdentityKey) {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (s1E : Expr AOps Γ (simMirT ℓ Pt))
    (qBE : Expr AOps Γ .bool) (m0E : Expr AOps Γ PlainT) (isChallE : Expr AOps Γ .bool)
    (pq'E : Expr AOps Γ (B 32)) (pnE : Expr AOps Γ U32)
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (scPostSendAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB sCE s1E qBE m0E isChallE pq'E pnE cE).cost ≤
      sCE.cost + s1E.cost + qBE.cost + m0E.cost + isChallE.cost + pq'E.cost + pnE.cost +
        cE.cost + 13 * (ℓ / 32) + 241000 := by
  let tupT : Ty ASig := .prod (simFullT ℓ Pt) (.prod (simMirT ℓ Pt)
    (.prod .bool (.prod PlainT (.prod .bool (.prod (B 32) (.prod U32 (fig8CtT (ℓ := ℓ) (Pt := Pt))))))))
  let Γ1 := tupT :: Γ
  have hw := SimFig8Crypto.toWireAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ1)
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))))
  have hks := SimFig8Kept.keptSendAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ1)
    (pGet (scKept (.fst .v0)) (.fst (.snd (.snd .v0))))
  dsimp only [tupT, Γ1, scPostSendAtomicE] at hw hks ⊢
  generalize toWireAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) _ = ew at hw ⊢
  generalize keptSendAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB _ = eks at hks ⊢
  simp only [SimFig8State.cost_eLet, SimFig8State.mRecordE, SimFig8State.mSafeChE,
    CryptoGames.SM.healedByE, CryptoGames.SM.leN, SimFig8State.mMk, SimFig8State.srecPos,
    SimFig8State.mB, SimFig8State.mWin, SimFig8State.mEpoch, SimFig8State.mIdx,
    SimFig8State.mTL, SimFig8State.mTrans, SimFig8State.mChall, SimFig8State.mComp,
    SimFig8State.mMaxAcc, SimFig8State.mLeaks, SimFig8State.mCorrs,
    pGet, pSet, posIdx, sendsInE, scMk, ssMk, scBase, scKept, scSent, scSnaps,
    ssPq, ssPn, ssUnackA, ssHonest, ssChains, ssAmb, ssStopped, f8Id, f8Tcur, f8VS,
    Expr.v0, Expr.v1, Expr.v2, Expr.cost, hb0_bits, hb1_bits, hb2_bits, hb3_bits] at hw hks ⊢
  omega

theorem kemFailSendBodyC_cost (idA idB : IdentityKey) (qep B q : ℕ) (hℓ : ℓ < 10 ^ 6)
    {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (kemFailStateT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (m0E : Expr AOps Γ PlainT) (chalE : Expr AOps Γ (.opt PlainT))
    (rE : Expr AOps Γ (.opt BV512)) :
    (kemFailSendBodyC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB qep B q stE qBE m0E chalE rE).cost ≤
      stE.cost + qBE.cost + m0E.cost + chalE.cost + rE.cost +
        25000000 + 32 * q + 32 * bits B + 32 * bits (qep + 1) := by
  have hbqep : bits qep ≤ bits (qep + 1) := bits_mono_le (Nat.le_succ qep)
  let inpT : Ty ASig := .prod (kemFailStateT ℓ Pt)
    (.prod .bool (.prod PlainT (.prod (.opt PlainT) (.opt BV512))))
  let Γ1 := inpT :: Γ
  let Γ2 := simMirT ℓ Pt :: Γ1
  let Γ3 := Ty.prod BV512 (.opt BV256) :: Γ2
  let Γ4 := Ty.prod (kemTrackT ℓ Pt) (kemTrackT ℓ Pt) :: Γ3
  let Γ5 := Ty.opt (.prod (_root_.ReductionDsl.B 32) (lpubT (ℓ := ℓ) (Pt := Pt))) :: Γ4
  let Γ6 := Ty.prod (_root_.ReductionDsl.B 32) (lpubT (ℓ := ℓ) (Pt := Pt)) :: Γ5
  let Γ7 := Ty.prod (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))) (fig8GsT ℓ Pt) :: Γ6
  let Γ8 := fig8CtT (ℓ := ℓ) (Pt := Pt) :: Γ7
  have hnb := SimFig8State.cost_mNoBobEpoch0E (ℓ := ℓ) (Pt := Pt) (O' := AOps) (Γ := Γ1)
    (ssMir (scBase (kfSimC (.fst .v0)))) (.fst (.snd .v0))
  have hep := SimFig8State.cost_mEpMgmtE (ℓ := ℓ) (Pt := Pt) (O' := AOps) (Γ := Γ1) qep
    (ssMir (scBase (kfSimC (.fst .v0)))) (.fst (.snd .v0)) (isSomeE (.snd (.snd (.snd (.snd .v0)))))
  have hsf := SimFig8State.cost_mSafeChE (ℓ := ℓ) (Pt := Pt) (O' := AOps) (Γ := Γ2)
    .v0 (.fst (.snd .v1))
  have hst := stepKemFailSendAtomicC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) q (Γ := Γ3)
    (kfTrack (.fst .v2)) (.fst (.snd .v2)) (.fst .v0)
  have hmk := SimFig8Crypto.mkPubAtomicC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (coinOnlyIface ℓ Pt) idA idB (Γ := Γ4)
    (scBase (kfSimC (.fst .v3))) (.fst (.snd .v3)) (.fst .v1)
    (sendPnE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (scBase (kfSimC (.fst .v3))) .v2 (.fst (.snd .v3)))
  have hfg := fig8SendOrChalAtomicC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB qep B (Γ := Γ6)
    (kfFig8 (.fst .v5)) (.fst (.snd .v5)) (.snd .v0)
    (.fst (.snd (.snd .v5))) (.fst (.snd (.snd (.snd .v5)))) (.snd .v3)
  have hps := scPostSendAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ8)
    (kfSimC (.fst .v7)) .v6 (.fst (.snd .v7)) (.fst (.snd (.snd .v7)))
    (isSomeE (.fst (.snd (.snd (.snd .v7))))) (.fst .v2)
    (sendPnE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (scBase (kfSimC (.fst .v7))) .v6 (.fst (.snd .v7))) .v0
  dsimp only [inpT, Γ1, Γ2, Γ3, Γ4, Γ5, Γ6, Γ7, Γ8,
    kemFailSendBodyC, drawSendCoinsAtomicC] at hnb hep hsf hst hmk hfg hps ⊢
  generalize SimFig8State.mNoBobEpoch0E (ℓ := ℓ) (Pt := Pt) (O' := AOps) _ _ = enb at hnb ⊢
  generalize SimFig8State.mEpMgmtE (ℓ := ℓ) (Pt := Pt) (O' := AOps) qep _ _ _ = eep at hep ⊢
  generalize SimFig8State.mSafeChE (ℓ := ℓ) (Pt := Pt) (O' := AOps) _ _ = esf at hsf ⊢
  generalize stepKemFailSendAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) q _ _ _ = cst at hst ⊢
  generalize mkPubAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (coinOnlyIface ℓ Pt) idA idB _ _ _ _ = cmk at hmk ⊢
  generalize fig8SendOrChalAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB qep B _ _ _ _ _ _ = cfg at hfg ⊢
  generalize scPostSendAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB _ _ _ _ _ _ _ _ = eps at hps ⊢
  simp only [SimFig8State.cost_eLet, sendPnE, SimFig8State.cost_sOpPure,
    _root_.ReductionDsl.AtomicPureOp.cost, boolOrE, sendReplyE, kfSimC, kfFig8, kfTrack, kfMk,
    scBase, ssMir, ssPn, ssStopped, SimFig8State.mWin, SimFig8State.mEpoch, SimFig8State.mIdx,
    pGet, isSomeE, Comp.cost, Expr.cost, coinOnlyIface, _root_.ReductionDsl.atomicSamplers,
    _root_.ReductionDsl.unifSamplers, _root_.ReductionDsl.AtomicUnifBase.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6, Expr.v7,
    hb1_bits] at hnb hep hsf hst hmk hfg hps ⊢
  omega

omit [SampleableType Pt] in
private theorem kemCorrBlockedE_cost {Γ : List (Ty ASig)} (L : ℕ)
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (qBE : Expr AOps Γ .bool) :
    (kemCorrBlockedE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) L sCE qBE).cost ≤
      sCE.cost + qBE.cost + 300 * L + 150 * (L * L) + 500 := by
  let Γ0 := Ty.prod (simFullT ℓ Pt) .bool :: Γ
  let mir0 : Expr AOps Γ0 (simMirT ℓ Pt) := ssMir (scBase (.fst .v0))
  let q0 : Expr AOps Γ0 .bool := .snd .v0
  have h1 := SimFig8State.cost_mCorrAllowedE L mir0 q0
  have h2 := SimFig8State.cost_mInWinE mir0 q0
  have h3 := SimFig8State.cost_mNoSpkCorrE mir0 q0
  dsimp only [Γ0, mir0, q0, ssMir, scBase, Expr.v0, Expr.cost] at h1 h2 h3
  simp only [kemCorrBlockedE, SimFig8State.cost_eLet, boolOrE, ssStopped, SimFig8State.mWin,
    ssMir, scBase, Expr.v0, Expr.cost]
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem fgCorrAllowedE_cost {O' : Ops ASig} {Γ : List (Ty ASig)} (Lq : ℕ)
    (m : Expr O' Γ (fig8MirT ℓ Pt)) (p : Expr O' Γ .bool) :
    (fgCorrAllowedE Lq m p).cost ≤ m.cost + p.cost + 300 * Lq + 150 * (Lq * Lq) + 300 := by
  simp only [fgCorrAllowedE, fgCompContainsE, SimFig8State.cost_eLet, boolEq, otherE, posEq,
    posSender, CryptoGames.SM.posEpoch, posIdx, fgRecPos, fgChall, fgTrans, fgComp,
    Expr.cost, Expr.v0, Expr.v1, Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd, Nat.mul_add]
  nlinarith

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem fgAfterCorrE_cost {O' : Ops ASig} {Γ : List (Ty ASig)} (Lq : ℕ)
    (m : Expr O' Γ (fig8MirT ℓ Pt)) (p : Expr O' Γ .bool) :
    (fgAfterCorrE Lq m p).cost ≤ m.cost + p.cost + 1500 * Lq + 1000 * (Lq * Lq) + 30000 := by
  simp only [fgAfterCorrE, fgLeakE, fgToSimMirE, simToFgMirKeepTransE, SimFig8State.mLeakE,
    SimFig8State.cost_eLet, SimFig8State.mMk, CryptoGames.SM.maxOptE, maxN, CryptoGames.SM.leN,
    boolEq, otherE, posEq, posSender, CryptoGames.SM.posEpoch, posIdx, fgRecPos, pGet,
    SimFig8State.mB, SimFig8State.mWin, SimFig8State.mEpoch, SimFig8State.mIdx, SimFig8State.mTL,
    SimFig8State.mTrans, SimFig8State.mChall, SimFig8State.mComp, SimFig8State.mMaxAcc,
    SimFig8State.mLeaks, SimFig8State.mCorrs, fgMirMk, fgB, fgWin, fgEpoch, fgIdx, fgTL,
    fgTrans, fgChall, fgComp, fgMaxAcc, fgLeaks, fgCorrs, Expr.cost, Expr.v0, Expr.v1, Expr.v2,
    Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd, Nat.mul_add]
  nlinarith

omit [SampleableType Pt] in
private theorem kemCorrChainsUpdE_cost {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (stQE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) :
    (kemCorrChainsUpdE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) sCE qBE stQE).cost ≤
      sCE.cost + qBE.cost + stQE.cost + 300 := by
  let Γ0 := Ty.prod (simFullT ℓ Pt) (.prod .bool (fig8StT (ℓ := ℓ) (Pt := Pt))) :: Γ
  let Γr := BV256 (ℓ := ℓ) (Pt := Pt) :: Γ0
  let pkE : Expr AOps Γr PK := sOpPtEnc (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) .ptEncPk
    (sOpGrp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) .ptDh (.pair .v0
        (sOpGrp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) .ptBase .unit)))
  have hrev := SimFig8State.cost_revealSpkChainsE (.fst (ssChains (scBase (.fst (.v1 : Expr AOps Γr _))))) pkE
  dsimp only [Γ0, Γr, pkE, ssChains, scBase, Expr.v0, Expr.v1] at hrev
  simp only [SimFig8State.cost_sOpPtEnc, SimFig8State.cost_sOpGrp,
    _root_.ReductionDsl.AtomicGroupOp.cost, Expr.cost] at hrev
  simp only [kemCorrChainsUpdE, SimFig8State.cost_eLet, ssChains, ssMir, scBase,
    SimFig8State.mEpoch, f8Gamma, Expr.v0, Expr.v1, Expr.cost, hb0_bits]
  omega

theorem kemFailCorrBodyC_cost (idA idB : IdentityKey) (L B_skip : ℕ)
    {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (kemFailStateT ℓ Pt)) (qBE : Expr AOps Γ .bool) :
    (kemFailCorrBodyC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB L B_skip stE qBE).cost ≤
      stE.cost + qBE.cost + 1000 * B_skip + 4000 * L + 2500 * (L * L) + 2000000 := by
  let Γ0 := Ty.prod (kemFailStateT ℓ Pt) .bool :: Γ
  let Γ1 := Ty.prod (.list (ghostChainT ℓ Pt)) (.list (ghostChainT ℓ Pt)) :: Γ0
  let Γ2 := GhostStT (ℓ := ℓ) (Pt := Pt) :: Γ1
  have hbl := kemCorrBlockedE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) L (kfSimC (.fst (.v0 : Expr AOps Γ0 _))) (.snd .v0)
  have hca := fgCorrAllowedE_cost (O' := AOps) L (fgMir (kfFig8 (.fst (.v0 : Expr AOps Γ0 _)))) (.snd .v0)
  have hch := kemCorrChainsUpdE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (kfSimC (.fst (.v0 : Expr AOps Γ0 _))) (.snd .v0)
    (pGet (fgSt (kfFig8 (.fst .v0))) (.snd .v0))
  let b1 : Expr AOps Γ1 (simBaseT ℓ Pt) := scBase (kfSimC (.fst .v1))
  let baseForGhost : Expr AOps Γ1 (simBaseT ℓ Pt) :=
    ssMk (ssMir b1) (ssPq b1) (ssPn b1) (ssUnackA b1) (ssHonest b1) .v0 (ssAmb b1) (ssStopped b1)
  have htg := SimFig8State.cost_toGhostE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB B_skip baseForGhost
    (.snd .v1) (pGet (fgSt (kfFig8 (.fst .v1))) (.snd .v1))
  have hmc := SimFig8State.cost_mAfterCorrE L
    (ssMir (scBase (kfSimC (.fst (.v2 : Expr AOps Γ2 _))))) (.snd .v2)
  have hfc := fgAfterCorrE_cost (O' := AOps) L
    (fgMir (kfFig8 (.fst (.v2 : Expr AOps Γ2 _)))) (.snd .v2)
  have hkp := SimFig8Kept.keptOfStAtomicE_cost (pGet (fgSt (kfFig8 (.fst (.v2 : Expr AOps Γ2 _)))) (.snd .v2))
  dsimp only [Γ0, Γ1, Γ2, b1, baseForGhost, kemFailCorrBodyC, kemFailCorrOutE] at hbl hca hch htg hmc hfc hkp ⊢
  generalize kemCorrBlockedE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) L _ _ = ebl at hbl ⊢
  generalize fgCorrAllowedE (O' := AOps) L _ _ = eca at hca ⊢
  generalize kemCorrChainsUpdE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) _ _ _ = ech at hch ⊢
  generalize toGhostE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB B_skip _ _ _ = etg at htg ⊢
  generalize SimFig8State.mAfterCorrE (ℓ := ℓ) (Pt := Pt) (O' := AOps) L _ _ = emc at hmc ⊢
  generalize fgAfterCorrE (O' := AOps) L _ _ = efc at hfc ⊢
  generalize keptOfStAtomicE (ℓ := ℓ) (Pt := Pt) (O' := AOps) _ = ekp at hkp ⊢
  simp only [SimFig8State.cost_eLet, boolOrE, corrReplyE,
    kfSimC, kfFig8, kfTrack, kfMk, fgSt, fgMir, fgWin, SimFig8State.mEpoch,
    pGet, pSet, scBase, scKept, scSent, scSnaps, scMk,
    ssMir, ssPq, ssPn, ssUnackA, ssHonest, ssAmb, ssStopped, ssMk,
    Comp.cost, Expr.v0, Expr.v1, Expr.v2, Expr.cost] at hbl hca hch htg hmc hfc hkp ⊢
  omega

omit [SampleableType Pt] in
private theorem swapPairsStepE_descBits_le {Γ : List (Ty ASig)} :
    atomicExprDescBits atomicSessionOpDescBits
      (swapPairsStepE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) (Γ := Γ)) ≤ 600 := by
  dsimp only [swapPairsStepE, SimFig8State.sOpPure, AtomicSessionBridge.sessPureOp,
    atomicExprDescBits, atomicSessionOpDescBits, atomicPureOpDescBits, Expr.v0, varIdx]
  simp only [hb0_bits, hb1_bits, hb2_bits, hp1_bits, hp2_bits, hp2048_bits, hp2050_bits]
  omega

omit [SampleableType Pt] in
private theorem issue1275ScanStepE_descBits_le {Γ : List (Ty ASig)} :
    atomicExprDescBits atomicSessionOpDescBits
      (issue1275ScanStepE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) (Γ := Γ)) ≤ 1200 := by
  dsimp only [issue1275ScanStepE, bytes2EqLitE, boolOrE, SimFig8State.eLet,
    SimFig8State.sOpPure, AtomicSessionBridge.sessPureOp,
    atomicExprDescBits, atomicTyDescBits, atomicSessionOpDescBits, atomicPureOpDescBits,
    Expr.v0, Expr.v1, varIdx, List.length_cons, List.length_nil]
  simp only [Nat.reduceAdd, hb0_bits, hb1_bits, hb2_bits, hp2_bits, hp512_bits]
  omega

private theorem issue1275FixEsC_descBits_le {Γ : List (Ty ASig)} (esE : Expr AOps Γ (B 2080)) :
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) Empty.elim
      (issue1275FixEsC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) esE) ≤
      atomicExprDescBits atomicSessionOpDescBits esE + 3500 := by
  have hscan := issue1275ScanStepE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := B 2080 :: Γ)
  have hswap := swapPairsStepE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (Γ := .prod (B 512) (.opt .bool) :: B 2080 :: Γ)
  dsimp only [issue1275FixEsC]
  generalize issue1275ScanStepE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := B 2080 :: Γ) = eScan at hscan ⊢
  generalize swapPairsStepE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (Γ := .prod (B 512) (.opt .bool) :: B 2080 :: Γ) = eSwap at hswap ⊢
  dsimp only [SimFig8State.sOpPure, AtomicSessionBridge.sessPureOp,
    atomicCompDescBits, atomicExprDescBits, atomicTyDescBits,
    atomicSessionOpDescBits, atomicPureOpDescBits,
    Expr.v0, Expr.v1, Expr.v2, varIdx, List.length_nil]
  simp only [Nat.reduceAdd, hb0_bits, hb1_bits, hb2_bits, hb256_bits, hb1024_bits, hb1536_bits,
    hb2048_bits, hp32_bits, hp512_bits, hp2048_bits, hp2080_bits]
  omega

private theorem honestExchangeFailsAtomicC_descBits_le {Γ : List (Ty ASig)}
    (seedE : Expr AOps Γ BV512) (randE : Expr AOps Γ BV256) :
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) Empty.elim
      (honestExchangeFailsAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) seedE randE) ≤
      atomicExprDescBits atomicSessionOpDescBits seedE +
      atomicExprDescBits atomicSessionOpDescBits randE + 4500 := by
  let Γ1 := Ty.prod (_root_.ReductionDsl.AtomicSpqrKemOp.kem768FromSeed.cod ℓ Pt) BV256 :: Γ
  let Γ2 := Ty.prod (B 960) (.prod (B 2080) BV256) :: Γ1
  have hfix := issue1275FixEsC_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ2) (.fst (.snd .v0))
  dsimp only [honestExchangeFailsAtomicC]
  generalize issue1275FixEsC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ2) (.fst (.snd .v0)) = cFix at hfix ⊢
  simp only [SimFig8State.descBits_sOpSpqr, SimFig8State.descBits_sOpPure, atomicPureOpDescBits,
    atomicCompDescBits, atomicExprDescBits, Expr.v0, Expr.v1, Expr.v2, Expr.v3, varIdx,
    Nat.reduceAdd, hb0_bits, hb1_bits, hb2_bits, hb3_bits] at hfix ⊢
  omega

private theorem stepKemFailSendAtomicC_descBits_le (q : ℕ) {Γ : List (Ty ASig)}
    (trE : Expr AOps Γ (kemTrackT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (rqE : Expr AOps Γ BV512) :
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) Empty.elim
      (stepKemFailSendAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) q trE qBE rqE) ≤
      atomicExprDescBits atomicSessionOpDescBits trE +
      atomicExprDescBits atomicSessionOpDescBits qBE +
      atomicExprDescBits atomicSessionOpDescBits rqE + 2 * bits (q + 1) + 12000 := by
  let Γ0 := Ty.prod (kemTrackT ℓ Pt) (.prod .bool BV512) :: Γ
  let Γc := BV512 :: Ty.sum BV512 (.prod BV512 BV256) ::
    Ty.prod (kemTrackT ℓ Pt) (.prod .bool BV512) :: Γ0
  have hhon := honestExchangeFailsAtomicC_descBits_le (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γc) .v0
    (encRandBvAtomicE (.snd (.snd .v2)))
  dsimp only [Γ0, Γc, stepKemFailSendAtomicC, nextKemCandAtomicC, stepPostKemSendE, nextKemCoinsAtomicE,
    encRandBvAtomicE, isKeysUnsampledV1E, isHeaderReceivedV1E, ekSideIsAE, boolEqE,
    trE_e, trE_c, trE_st, trE_sentB, trE_sendCtr, trE_cand, trMk, pGet, pSet, SimFig8State.eLet] at hhon ⊢
  generalize honestExchangeFailsAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) .v0 _ = cHon at hhon ⊢
  dsimp only [SimFig8State.sOpPure, AtomicSessionBridge.sessPureOp,
    kemCoinsT, kemSentEntryT, U64, U32, B, BV512, BV256,
    atomicCompDescBits, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits,
    atomicSessionOpDescBits, atomicPureOpDescBits,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, varIdx, List.length_singleton] at hhon ⊢
  simp only [SimFig8State.descBits_sOpSpqr] at hhon ⊢
  dsimp only [atomicExprDescBits, varIdx] at hhon ⊢
  simp only [Nat.reduceAdd, hb0_bits, hb1_bits, hb2_bits, hb3_bits, hp1_bits, hp32_bits, hp64_bits] at hhon ⊢
  omega

omit [SampleableType Pt] in
private theorem fig8SendStepAtomicE_descBits_tight (idA idB : IdentityKey) (B_cl : ℕ)
    {Γ : List (Ty ASig)} (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt)))
    (mcOptE : Expr AOps Γ (.opt (.prod (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) PlainT) BV256))) :
    atomicExprDescBits atomicSessionOpDescBits
      (fig8SendStepAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB B_cl stE mcOptE) ≤
      atomicExprDescBits atomicSessionOpDescBits stE +
      atomicExprDescBits atomicSessionOpDescBits mcOptE + 8 * bits B_cl + 25000 := by
  have hdef := SimFig8Kept.defaultMcAtomicE_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
    (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)
  let t0 := Ty.prod (fig8StT (ℓ := ℓ) (Pt := Pt))
    (.prod (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) PlainT) BV256)
  let Γ1 := t0 :: Γ
  let Γ2 := Ty.prod (_root_.ReductionDsl.ckaStT (ℓ := ℓ) (Pt := Pt))
    (.prod (_root_.ReductionDsl.PtT (ℓ := ℓ) (Pt := Pt))
      (_root_.ReductionDsl.PtT (ℓ := ℓ) (Pt := Pt))) :: Γ1
  let Γ3 := Ty.prod .bool
    (.prod (fig8StT (ℓ := ℓ) (Pt := Pt)) (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) PlainT)) :: Γ1
  let Γ4 := fsSendStT (ℓ := ℓ) (Pt := Pt) :: Γ3
  have hcka := SimFig8State.descBits_runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ1)
    (Computational.Proofs.ReductionDsl.Fig8Atomic.ckaSendExpr ℓ Pt C Dh encPt encT lam)
    (.pair (f8Gamma (.fst .v0)) (.snd (.snd .v0)))
  have hup := SimFig8State.descBits_runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ2)
    (Computational.Proofs.ReductionDsl.Fig8Atomic.prngUpExpr ℓ Pt C Dh encPt encT lam)
    (.pair (SimFig8Kept.f8Root (.fst .v1)) (.snd (.snd .v0)))
  have hdefE := SimFig8State.descBits_runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ3)
    (Computational.Proofs.ReductionDsl.Fig8Atomic.defaultEExpr ℓ Pt C Dh encPt encT lam) .unit
  have hfs := SimFig8State.descBits_runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ4)
    (Computational.Proofs.ReductionDsl.Fig8Atomic.fsSendExpr ℓ Pt C Dh encPt encT lam)
    (.pair .v0 (.pair (.pair (f8Tcur (.fst (.snd .v1))) (SimFig8Kept.f8Cur (.fst (.snd .v1))))
      (.snd (.snd .v1))))
  have hd_cka := Computational.Proofs.Game.PromotedCostedReds.SimFig8SpqrDesc.ckaSendExpr_descBits_le
    (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh) (encPt := encPt) (encT := encT) (lam := lam)
  have hd_up := Computational.Proofs.Game.PromotedCostedReds.SimFig8SpqrDesc.prngUpExpr_descBits_le
    (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh) (encPt := encPt) (encT := encT) (lam := lam)
  have hd_defE := Computational.Proofs.Game.PromotedCostedReds.SimFig8SpqrDesc.defaultEExpr_descBits_le
    (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh) (encPt := encPt) (encT := encT) (lam := lam)
  have hd_fs := Computational.Proofs.Game.PromotedCostedReds.SimFig8SpqrDesc.fsSendExpr_descBits_le
    (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh) (encPt := encPt) (encT := encT) (lam := lam)
  dsimp only [fig8SendStepAtomicE, SimFig8Kept.f8Mk, f8Id, SimFig8Kept.f8Root, f8VS,
    SimFig8Kept.f8VR, f8Gamma, SimFig8Kept.f8Cur, f8Tcur, sendsInE,
    Expr.v0, Expr.v1, Expr.v2] at hcka hup hdefE hfs ⊢
  generalize SimFig8Kept.defaultMcAtomicE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ) = e_def at hdef ⊢
  generalize SimFig8State.runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ1) _ _ = e_rcka at hcka ⊢
  generalize SimFig8State.runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ2) _ _ = e_rup at hup ⊢
  generalize SimFig8State.runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ3) _ .unit = e_rdefE at hdefE ⊢
  generalize SimFig8State.runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ4) _ _ = e_rfs at hfs ⊢
  simp only [SimFig8State.descBits_eLet, varIdx, atomicExprDescBits, Nat.reduceAdd,
    hb0_bits, hb1_bits, hb2_bits] at hcka hup hdefE hfs ⊢
  omega

omit [SampleableType Pt] in
private theorem keptSendAtomicE_descBits_tight (idA idB : IdentityKey) {Γ : List (Ty ASig)}
    (kE : Expr AOps Γ (keptT ℓ Pt)) :
    atomicExprDescBits atomicSessionOpDescBits
      (keptSendAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB kE) ≤
      atomicExprDescBits atomicSessionOpDescBits kE + 30000 := by
  let Γ1 := fig8StT (ℓ := ℓ) (Pt := Pt) :: keptT ℓ Pt :: Γ
  have hstep := fig8SendStepAtomicE_descBits_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB 0 (Γ := Γ1) .v0 .none
  have ht_f8 := SimFig8State.atomicTyDescBits_fig8StT (ℓ := ℓ) (Pt := Pt)
  dsimp only [keptSendAtomicE, sendsInE, f8Id, f8Tcur, SimFig8Kept.f8VR, Expr.v0, Expr.v1] at hstep ⊢
  generalize fig8SendStepAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB 0 (Γ := Γ1) _ _ = e_s at hstep ⊢
  simp only [SimFig8State.descBits_eLet, BV256, varIdx,
    atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, Nat.reduceAdd,
    hb0_bits, hb1_bits, hb2_bits, hp32_bits] at hstep ⊢
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem fgEpMgmtE_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ) (qepFig : ℕ)
    {Γ : List (Ty ASig)} (m : Expr O' Γ (fig8MirT ℓ Pt)) (p bad : Expr O' Γ .bool) :
    atomicExprDescBits opB (fgEpMgmtE qepFig m p bad) ≤
      atomicExprDescBits opB m + atomicExprDescBits opB p + atomicExprDescBits opB bad +
        4 * bits qepFig + 6000 := by
  dsimp only [fgEpMgmtE, fgToSimMirE, simToFgMirKeepTransE, SimFig8State.mEpMgmtE, eLet,
    SimFig8State.mSafeChE, SimFig8State.mLeakE, SimFig8State.mMk, CryptoGames.SM.maxOptE,
    maxN, CryptoGames.SM.healedByE, CryptoGames.SM.leN, sendsInE, pGet, pSet,
    SimFig8State.mB, SimFig8State.mWin, SimFig8State.mEpoch, SimFig8State.mIdx,
    SimFig8State.mTL, SimFig8State.mTrans, SimFig8State.mChall, SimFig8State.mComp,
    SimFig8State.mMaxAcc, SimFig8State.mLeaks, SimFig8State.mCorrs,
    fgMirMk, fgB, fgWin, fgEpoch, fgIdx, fgTL, fgTrans, fgChall, fgComp, fgMaxAcc,
    fgLeaks, fgCorrs, fig8MirT, fig8RecT, simMirT, SimFig8LoopAndCost.simRecT, posTy, lpubT,
    PlainT, fig8CtT, _root_.ReductionDsl.fig8HdrT, _root_.ReductionDsl.lctT,
    _root_.ReductionDsl.wireSaltCtT, _root_.ReductionDsl.B, _root_.ReductionDsl.PB, U32, U64,
    BV256, _root_.ReductionDsl.PtT, Expr.v0, Expr.v1,
    atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, varIdx]
  simp only [Nat.reduceAdd, hb0_bits, hb1_bits, hb2_bits, hb3_bits, hp32_bits]
  omega

private theorem fig8SendOrChalAtomicC_descBits_le (idA idB : IdentityKey) (qep B : ℕ)
    {Γ : List (Ty ASig)} (gE : Expr AOps Γ (fig8GsT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (pubE : Expr AOps Γ (lpubT (ℓ := ℓ) (Pt := Pt)))
    (m0E : Expr AOps Γ PlainT) (chalE : Expr AOps Γ (.opt PlainT))
    (rcE : Expr AOps Γ (.opt BV256)) :
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) Empty.elim
      (fig8SendOrChalAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB qep B gE qBE pubE m0E chalE rcE) ≤
      atomicExprDescBits atomicSessionOpDescBits gE +
      atomicExprDescBits atomicSessionOpDescBits qBE +
      atomicExprDescBits atomicSessionOpDescBits pubE +
      atomicExprDescBits atomicSessionOpDescBits m0E +
      atomicExprDescBits atomicSessionOpDescBits chalE +
      atomicExprDescBits atomicSessionOpDescBits rcE +
      4 * bits (qep + 1) + 8 * bits B + 38000 := by
  let fgArgT : Ty ASig := .prod (fig8GsT ℓ Pt)
    (.prod .bool (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) (.prod PlainT (.opt PlainT))))
  let Γb := Ty.prod BV256 .bool :: Ty.prod fgArgT (.opt BV256) :: Γ
  let Γ1 := Ty.prod fgArgT (.prod BV256 .bool) :: Γb
  let Γ2 := fig8MirT ℓ Pt :: Γ1
  have hep := fgEpMgmtE_descBits_le (O' := AOps) atomicSessionOpDescBits (qep + 1) (Γ := Γ1)
    (fgMir (.fst (.fst .v0))) (.fst (.snd (.fst .v0))) (.snd (.snd .v0))
  have hfs := fig8SendStepAtomicE_descBits_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB B (Γ := Γ2)
    (pGet (fgSt (.fst (.fst .v1))) (.fst (.snd (.fst .v1))))
    (.some (.pair (.pair (.fst (.snd (.snd (.fst .v1))))
      (.caseOpt (.snd (.snd (.snd (.snd (.fst .v1))))) (.fst (.snd (.snd (.snd (.fst .v1)))))
        (.ite (fgB .v1) .v0 (.fst (.snd (.snd (.snd (.fst .v2)))))))) (.fst (.snd .v1))))
  dsimp only [fgArgT, Γb, Γ1, Γ2, fig8SendOrChalAtomicC, samIfNecFig8AtomicC,
    fig8SendOrChalPostE] at hep hfs ⊢
  generalize fgEpMgmtE (O' := AOps) (qep + 1) _ _ _ = eep at hep ⊢
  generalize fig8SendStepAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB B _ _ = efs at hfs ⊢
  simp only [SimFig8State.descBits_eLet, fgRecordE, fgSafeChE, fgToSimMirE,
    SimFig8State.mSafeChE, CryptoGames.SM.healedByE, CryptoGames.SM.leN,
    SimFig8State.mMk, SimFig8State.mEpoch, SimFig8State.mTL,
    fgMirMk, fgSt, fgMir, fgRecPos, fgB, fgWin, fgEpoch, fgIdx,
    fgTL, fgTrans, fgChall, fgComp, fgMaxAcc, fgLeaks, fgCorrs, pGet, pSet, posIdx,
    isSomeE, SimFig8LoopAndCost.simRecT, posTy, PlainT, fig8CtT, _root_.ReductionDsl.fig8HdrT,
    _root_.ReductionDsl.lctT, _root_.ReductionDsl.wireSaltCtT, _root_.ReductionDsl.B,
    U64, BV256, _root_.ReductionDsl.PtT,
    atomicCompDescBits, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, varIdx, Nat.reduceAdd,
    hb0_bits, hb1_bits, hb2_bits, hb3_bits, hp32_bits] at hep hfs ⊢
  omega

omit [SampleableType Pt] in
private theorem scPostSendAtomicE_descBits_le (idA idB : IdentityKey) {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (s1E : Expr AOps Γ (simMirT ℓ Pt))
    (qBE : Expr AOps Γ .bool) (m0E : Expr AOps Γ PlainT) (isChallE : Expr AOps Γ .bool)
    (pq'E : Expr AOps Γ (B 32)) (pnE : Expr AOps Γ U32)
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    atomicExprDescBits atomicSessionOpDescBits
      (scPostSendAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB sCE s1E qBE m0E isChallE pq'E pnE cE) ≤
      atomicExprDescBits atomicSessionOpDescBits sCE +
      atomicExprDescBits atomicSessionOpDescBits s1E +
      atomicExprDescBits atomicSessionOpDescBits qBE +
      atomicExprDescBits atomicSessionOpDescBits m0E +
      atomicExprDescBits atomicSessionOpDescBits isChallE +
      atomicExprDescBits atomicSessionOpDescBits pq'E +
      atomicExprDescBits atomicSessionOpDescBits pnE +
      atomicExprDescBits atomicSessionOpDescBits cE + 38000 := by
  let tupT : Ty ASig := .prod (simFullT ℓ Pt) (.prod (simMirT ℓ Pt)
    (.prod .bool (.prod PlainT (.prod .bool (.prod (B 32) (.prod U32 (fig8CtT (ℓ := ℓ) (Pt := Pt))))))))
  let Γ1 := tupT :: Γ
  have hw := SimFig8Crypto.toWireAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ1)
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))))
  have hks := keptSendAtomicE_descBits_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ1)
    (pGet (scKept (.fst .v0)) (.fst (.snd (.snd .v0))))
  dsimp only [tupT, Γ1, scPostSendAtomicE] at hw hks ⊢
  generalize toWireAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) _ = ew at hw ⊢
  generalize keptSendAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB _ = eks at hks ⊢
  simp only [SimFig8State.descBits_eLet, SimFig8State.mRecordE, SimFig8State.mSafeChE,
    CryptoGames.SM.healedByE, CryptoGames.SM.leN, SimFig8State.mMk, SimFig8State.srecPos,
    SimFig8State.mB, SimFig8State.mWin, SimFig8State.mEpoch, SimFig8State.mIdx,
    SimFig8State.mTL, SimFig8State.mTrans, SimFig8State.mChall, SimFig8State.mComp,
    SimFig8State.mMaxAcc, SimFig8State.mLeaks, SimFig8State.mCorrs,
    pGet, pSet, posIdx, sendsInE, scMk, ssMk, scBase, scKept, scSent, scSnaps,
    ssPq, ssPn, ssUnackA, ssHonest, ssChains, ssAmb, ssStopped, f8Id, f8Tcur, f8VS,
    atomicExprDescBits, Expr.v0, Expr.v1, Expr.v2, varIdx, Nat.reduceAdd,
    hb0_bits, hb1_bits, hb2_bits, hb3_bits] at hw hks ⊢
  omega

theorem kemFailSendBodyC_descBits_le (idA idB : IdentityKey) (qep B q : ℕ)
    {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (kemFailStateT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (m0E : Expr AOps Γ PlainT) (chalE : Expr AOps Γ (.opt PlainT))
    (rE : Expr AOps Γ (.opt BV512)) :
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) Empty.elim
      (kemFailSendBodyC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB qep B q stE qBE m0E chalE rE) ≤
      atomicExprDescBits atomicSessionOpDescBits stE +
      atomicExprDescBits atomicSessionOpDescBits qBE +
      atomicExprDescBits atomicSessionOpDescBits m0E +
      atomicExprDescBits atomicSessionOpDescBits chalE +
      atomicExprDescBits atomicSessionOpDescBits rE +
      32 * bits (q + 1) + 32 * bits (qep + 1) + 32 * bits B + 300000 := by
  have hbqep : bits qep ≤ bits (qep + 1) := bits_mono_le (Nat.le_succ qep)
  let inpT : Ty ASig := .prod (kemFailStateT ℓ Pt)
    (.prod .bool (.prod PlainT (.prod (.opt PlainT) (.opt BV512))))
  let Γ1 := inpT :: Γ
  let Γ2 := simMirT ℓ Pt :: Γ1
  let Γ3 := Ty.prod BV512 (.opt BV256) :: Γ2
  let Γ4 := Ty.prod (kemTrackT ℓ Pt) (kemTrackT ℓ Pt) :: Γ3
  let Γ5 := Ty.opt (.prod (_root_.ReductionDsl.B 32) (lpubT (ℓ := ℓ) (Pt := Pt))) :: Γ4
  let Γ6 := Ty.prod (_root_.ReductionDsl.B 32) (lpubT (ℓ := ℓ) (Pt := Pt)) :: Γ5
  let Γ7 := Ty.prod (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))) (fig8GsT ℓ Pt) :: Γ6
  let Γ8 := fig8CtT (ℓ := ℓ) (Pt := Pt) :: Γ7
  have hnb := SimFig8State.mNoBobEpoch0E_descBits_le (ℓ := ℓ) (Pt := Pt) (O' := AOps)
    atomicSessionOpDescBits (Γ := Γ1) (ssMir (scBase (kfSimC (.fst .v0)))) (.fst (.snd .v0))
  have hep := SimFig8State.mEpMgmtE_descBits_le (ℓ := ℓ) (Pt := Pt) (O' := AOps)
    atomicSessionOpDescBits qep (Γ := Γ1) (ssMir (scBase (kfSimC (.fst .v0)))) (.fst (.snd .v0))
    (isSomeE (.snd (.snd (.snd (.snd .v0)))))
  have hsf := SimFig8State.mSafeChE_descBits_le (ℓ := ℓ) (Pt := Pt) (O' := AOps)
    atomicSessionOpDescBits (Γ := Γ2) .v0 (.fst (.snd .v1))
  have hst := stepKemFailSendAtomicC_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) q (Γ := Γ3)
    (kfTrack (.fst .v2)) (.fst (.snd .v2)) (.fst .v0)
  have hmk := SimFig8Crypto.mkPubAtomicC_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (coinOnlyIface ℓ Pt) idA idB
    (fun _ => 8) Empty.elim (Γ := Γ4)
    (scBase (kfSimC (.fst .v3))) (.fst (.snd .v3)) (.fst .v1)
    (sendPnE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (scBase (kfSimC (.fst .v3))) .v2 (.fst (.snd .v3)))
  have hfg := fig8SendOrChalAtomicC_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB qep B (Γ := Γ6)
    (kfFig8 (.fst .v5)) (.fst (.snd .v5)) (.snd .v0)
    (.fst (.snd (.snd .v5))) (.fst (.snd (.snd (.snd .v5)))) (.snd .v3)
  have hps := scPostSendAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ8)
    (kfSimC (.fst .v7)) .v6 (.fst (.snd .v7)) (.fst (.snd (.snd .v7)))
    (isSomeE (.fst (.snd (.snd (.snd .v7))))) (.fst .v2)
    (sendPnE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (scBase (kfSimC (.fst .v7))) .v6 (.fst (.snd .v7))) .v0
  dsimp only [inpT, Γ1, Γ2, Γ3, Γ4, Γ5, Γ6, Γ7, Γ8,
    kemFailSendBodyC, drawSendCoinsAtomicC] at hnb hep hsf hst hmk hfg hps ⊢
  generalize SimFig8State.mNoBobEpoch0E (ℓ := ℓ) (Pt := Pt) (O' := AOps) _ _ = enb at hnb ⊢
  generalize SimFig8State.mEpMgmtE (ℓ := ℓ) (Pt := Pt) (O' := AOps) qep _ _ _ = eep at hep ⊢
  generalize SimFig8State.mSafeChE (ℓ := ℓ) (Pt := Pt) (O' := AOps) _ _ = esf at hsf ⊢
  generalize stepKemFailSendAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) q _ _ _ = cst at hst ⊢
  generalize mkPubAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (coinOnlyIface ℓ Pt) idA idB _ _ _ _ = cmk at hmk ⊢
  generalize fig8SendOrChalAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB qep B _ _ _ _ _ _ = cfg at hfg ⊢
  generalize scPostSendAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB _ _ _ _ _ _ _ _ = eps at hps ⊢
  simp only [SimFig8State.descBits_eLet, sendPnE, SimFig8State.descBits_sOpPure,
    atomicPureOpDescBits, boolOrE, sendReplyE, kfSimC, kfFig8, kfTrack, kfMk,
    scBase, ssMir, ssPn, ssStopped, SimFig8State.mWin, SimFig8State.mEpoch, SimFig8State.mIdx,
    pGet, isSomeE, smRT, _root_.ReductionDsl.recvResultT, _root_.ReductionDsl.B,
    PlainT, BV256, GhostStT, atomicCompDescBits, atomicExprDescBits,
    atomicTyDescBits, atomicSortDescBits,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6, Expr.v7,
    varIdx, Nat.reduceAdd,
    hb0_bits, hb1_bits, hb2_bits, hb3_bits, hb4_bits, hb5_bits, hb6_bits, hb7_bits,
    hp32_bits] at hnb hep hsf hst hmk hfg hps ⊢
  omega

omit [SampleableType Pt] in
private theorem kemCorrBlockedE_descBits_le {Γ : List (Ty ASig)} (L : ℕ)
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (qBE : Expr AOps Γ .bool) :
    atomicExprDescBits atomicSessionOpDescBits
      (kemCorrBlockedE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) L sCE qBE) ≤
      atomicExprDescBits atomicSessionOpDescBits sCE +
      atomicExprDescBits atomicSessionOpDescBits qBE + 6 * bits L + 2000 := by
  let Γ0 := Ty.prod (simFullT ℓ Pt) .bool :: Γ
  let mir0 : Expr AOps Γ0 (simMirT ℓ Pt) := ssMir (scBase (.fst .v0))
  let q0 : Expr AOps Γ0 .bool := .snd .v0
  have h1 := SimFig8State.mCorrAllowedE_descBits_le atomicSessionOpDescBits L mir0 q0
  have h2 := SimFig8State.mInWinE_descBits_le atomicSessionOpDescBits mir0 q0
  have h3 := SimFig8State.mNoSpkCorrE_descBits_le atomicSessionOpDescBits mir0 q0
  dsimp only [Γ0, mir0, q0, ssMir, scBase, Expr.v0, atomicExprDescBits, varIdx] at h1 h2 h3
  simp only [hb0_bits] at h1 h2 h3
  dsimp only [kemCorrBlockedE, eLet, boolOrE, ssStopped, SimFig8State.mWin, ssMir, scBase,
    Expr.v0, atomicExprDescBits, varIdx]
  simp only [hb0_bits]
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem fgCorrAllowedE_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ) (Lq : ℕ)
    {Γ : List (Ty ASig)} (m : Expr O' Γ (fig8MirT ℓ Pt)) (p : Expr O' Γ .bool) :
    atomicExprDescBits opB (fgCorrAllowedE Lq m p) ≤
      atomicExprDescBits opB m + atomicExprDescBits opB p + 6 * bits Lq + 800 := by
  dsimp only [fgCorrAllowedE, fgCompContainsE, eLet, boolEq, otherE, posEq, posSender,
    CryptoGames.SM.posEpoch, posIdx, fgRecPos, fgChall, fgTrans, fgComp, Expr.v0, Expr.v1,
    atomicExprDescBits, varIdx]
  simp only [Nat.reduceAdd, hb0_bits, hb1_bits]
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem mAfterCorrE_descBits_tight {O' : Ops ASig} (opB : O'.Op → ℕ) (Lq : ℕ)
    {Γ : List (Ty ASig)} (s : Expr O' Γ (simMirT ℓ Pt)) (p : Expr O' Γ .bool) :
    atomicExprDescBits opB (SimFig8State.mAfterCorrE Lq s p) ≤
      atomicExprDescBits opB s + atomicExprDescBits opB p + 44 * bits Lq + 25000 := by
  dsimp only [SimFig8State.mAfterCorrE, SimFig8State.mLeakE, eLet, SimFig8State.mMk,
    CryptoGames.SM.maxOptE, maxN, CryptoGames.SM.leN, boolEq, otherE, posEq, posSender,
    CryptoGames.SM.posEpoch, posIdx, SimFig8State.srecPos, pGet,
    SimFig8State.mB, SimFig8State.mWin, SimFig8State.mEpoch, SimFig8State.mIdx, SimFig8State.mTL,
    SimFig8State.mTrans, SimFig8State.mChall, SimFig8State.mComp, SimFig8State.mMaxAcc,
    SimFig8State.mLeaks, SimFig8State.mCorrs,
    Expr.v0, Expr.v1, Expr.v2, atomicExprDescBits, varIdx]
  simp only [Nat.reduceAdd, hb0_bits, hb1_bits, hb2_bits]
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem fgAfterCorrE_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ) (Lq : ℕ)
    {Γ : List (Ty ASig)} (m : Expr O' Γ (fig8MirT ℓ Pt)) (p : Expr O' Γ .bool) :
    atomicExprDescBits opB (fgAfterCorrE Lq m p) ≤
      atomicExprDescBits opB m + atomicExprDescBits opB p + 44 * bits Lq + 178500 := by
  dsimp only [fgAfterCorrE, fgLeakE, fgToSimMirE, simToFgMirKeepTransE, SimFig8State.mLeakE,
    eLet, SimFig8State.mMk, CryptoGames.SM.maxOptE, maxN, CryptoGames.SM.leN, boolEq, otherE,
    posEq, posSender, CryptoGames.SM.posEpoch, posIdx, fgRecPos, pGet,
    SimFig8State.mB, SimFig8State.mWin, SimFig8State.mEpoch, SimFig8State.mIdx, SimFig8State.mTL,
    SimFig8State.mTrans, SimFig8State.mChall, SimFig8State.mComp, SimFig8State.mMaxAcc,
    SimFig8State.mLeaks, SimFig8State.mCorrs, fgMirMk, fgB, fgWin, fgEpoch, fgIdx, fgTL,
    fgTrans, fgChall, fgComp, fgMaxAcc, fgLeaks, fgCorrs,
    SimFig8LoopAndCost.simRecT, posTy, _root_.ReductionDsl.B, _root_.ReductionDsl.PB, PlainT,
    Expr.v0, Expr.v1, Expr.v2, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, varIdx]
  simp only [Nat.reduceAdd, hb0_bits, hb1_bits, hb2_bits, hp32_bits]
  omega

omit [SampleableType Pt] in
private theorem kemCorrChainsUpdE_descBits_le {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (stQE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) :
    atomicExprDescBits atomicSessionOpDescBits
      (kemCorrChainsUpdE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) sCE qBE stQE) ≤
      atomicExprDescBits atomicSessionOpDescBits sCE +
      atomicExprDescBits atomicSessionOpDescBits qBE +
      atomicExprDescBits atomicSessionOpDescBits stQE + 1000 := by
  let Γ0 := Ty.prod (simFullT ℓ Pt) (.prod .bool (fig8StT (ℓ := ℓ) (Pt := Pt))) :: Γ
  let Γr := BV256 (ℓ := ℓ) (Pt := Pt) :: Γ0
  let pkE : Expr AOps Γr PK := sOpPtEnc (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) .ptEncPk
    (sOpGrp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) .ptDh (.pair .v0
        (sOpGrp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) .ptBase .unit)))
  have hrev := SimFig8State.revealSpkChainsE_descBits_le (O' := AOps) atomicSessionOpDescBits
    (.fst (ssChains (scBase (.fst (.v1 : Expr AOps Γr _))))) pkE
  dsimp only [Γ0, Γr, pkE, ssChains, scBase, Expr.v0, Expr.v1, atomicExprDescBits, varIdx] at hrev
  simp only [SimFig8State.descBits_sOpPtEnc, SimFig8State.descBits_sOpGrp,
    atomicExprDescBits, varIdx, Nat.reduceAdd, hb0_bits, hb1_bits] at hrev
  dsimp only [kemCorrChainsUpdE, eLet, ssChains, ssMir, scBase, SimFig8State.mEpoch, f8Gamma,
    Expr.v0, Expr.v1, atomicExprDescBits, varIdx]
  simp only [Nat.reduceAdd, hb0_bits, hb1_bits]
  omega

theorem kemFailCorrBodyC_descBits_le (idA idB : IdentityKey) (L B_skip : ℕ)
    {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (kemFailStateT ℓ Pt)) (qBE : Expr AOps Γ .bool) :
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) Empty.elim
      (kemFailCorrBodyC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB L B_skip stE qBE) ≤
      atomicExprDescBits atomicSessionOpDescBits stE +
      atomicExprDescBits atomicSessionOpDescBits qBE +
      128 * bits L + 16 * bits B_skip + 250000 := by
  let Γ0 := Ty.prod (kemFailStateT ℓ Pt) .bool :: Γ
  let Γ1 := Ty.prod (.list (ghostChainT ℓ Pt)) (.list (ghostChainT ℓ Pt)) :: Γ0
  let Γ2 := GhostStT (ℓ := ℓ) (Pt := Pt) :: Γ1
  have hbl := kemCorrBlockedE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) L (kfSimC (.fst (.v0 : Expr AOps Γ0 _))) (.snd .v0)
  have hca := fgCorrAllowedE_descBits_le (O' := AOps) atomicSessionOpDescBits L
    (fgMir (kfFig8 (.fst (.v0 : Expr AOps Γ0 _)))) (.snd .v0)
  have hch := kemCorrChainsUpdE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (kfSimC (.fst (.v0 : Expr AOps Γ0 _))) (.snd .v0)
    (pGet (fgSt (kfFig8 (.fst .v0))) (.snd .v0))
  let b1 : Expr AOps Γ1 (simBaseT ℓ Pt) := scBase (kfSimC (.fst .v1))
  let baseForGhost : Expr AOps Γ1 (simBaseT ℓ Pt) :=
    ssMk (ssMir b1) (ssPq b1) (ssPn b1) (ssUnackA b1) (ssHonest b1) .v0 (ssAmb b1) (ssStopped b1)
  have htg := SimFig8State.toGhostE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB B_skip baseForGhost
    (.snd .v1) (pGet (fgSt (kfFig8 (.fst .v1))) (.snd .v1))
  have hmc := mAfterCorrE_descBits_tight (O' := AOps) atomicSessionOpDescBits L
    (ssMir (scBase (kfSimC (.fst (.v2 : Expr AOps Γ2 _))))) (.snd .v2)
  have hfc := fgAfterCorrE_descBits_le (O' := AOps) atomicSessionOpDescBits L
    (fgMir (kfFig8 (.fst (.v2 : Expr AOps Γ2 _)))) (.snd .v2)
  have hkp := SimFig8Kept.keptOfStAtomicE_descBits_le (O' := AOps) atomicSessionOpDescBits
    (pGet (fgSt (kfFig8 (.fst (.v2 : Expr AOps Γ2 _)))) (.snd .v2))
  dsimp only [Γ0, Γ1, Γ2, b1, baseForGhost, kemFailCorrBodyC, kemFailCorrOutE] at hbl hca hch htg hmc hfc hkp ⊢
  generalize kemCorrBlockedE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) L _ _ = ebl at hbl ⊢
  generalize fgCorrAllowedE (O' := AOps) L _ _ = eca at hca ⊢
  generalize kemCorrChainsUpdE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) _ _ _ = ech at hch ⊢
  generalize toGhostE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB B_skip _ _ _ = etg at htg ⊢
  generalize SimFig8State.mAfterCorrE (ℓ := ℓ) (Pt := Pt) (O' := AOps) L _ _ = emc at hmc ⊢
  generalize fgAfterCorrE (O' := AOps) L _ _ = efc at hfc ⊢
  generalize keptOfStAtomicE (ℓ := ℓ) (Pt := Pt) (O' := AOps) _ = ekp at hkp ⊢
  simp only [SimFig8State.descBits_eLet, boolOrE, corrReplyE,
    kfSimC, kfFig8, kfTrack, kfMk, fgSt, fgMir, fgWin, SimFig8State.mEpoch,
    pGet, pSet, scBase, scKept, scSent, scSnaps, scMk,
    ssMir, ssPq, ssPn, ssUnackA, ssHonest, ssAmb, ssStopped, ssMk,
    smRT, _root_.ReductionDsl.recvResultT, _root_.ReductionDsl.B, PlainT, GhostStT,
    Expr.v0, Expr.v1, Expr.v2, atomicCompDescBits, atomicExprDescBits,
    atomicTyDescBits, atomicSortDescBits, varIdx, Nat.reduceAdd,
    hb0_bits, hb1_bits, hb2_bits, hp32_bits] at hbl hca hch htg hmc hfc hkp ⊢
  omega

end CostAndDescBounds

end Computational.Proofs.Game.PromotedCostedReds.KemFailRedSendCorrCost

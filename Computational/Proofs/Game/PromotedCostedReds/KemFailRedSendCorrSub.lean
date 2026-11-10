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
public import LibsignalBinary.Proofs.SpqrV1Sync.TopInSync
import Computational.Proofs.E2E.Dsl.ClampsLossless
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidCodec

/-!
# Atomic Send-Step Helpers for `KemFailRed`

Defines `fig8MirT` mirror helpers, the libcrux issue-1275 endianness fixup and
`honestExchangeFailsAtomicC`, and the braid tracker step `stepKemFailSendAtomicC`,
along with their `.eval` characterizations.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.KemFailRedSendCorrSub

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Ops Iface Expr Comp
  partyToBool
  atomicSig atomicSessionOps coinOnlyIface
  B U8 U32 U64 BV256 BV512
  fig8StT)
open CryptoGames (Party)
open CryptoGames.CKA (DHFun)
open CryptoGames.SM (posTy posSender posIdx posEq boolEq maxN pGet pSet otherE)
open CryptoGames.LibsignalSession (Crypto PublicKey)
open CryptoGames.LibsignalSM.Proofs.Refinement (KemFailTrackState stepKemFailSend)
open CryptoGames.Ratchet (keyToBytesVec32)
open CryptoGames.Ratchet.LibsignalSim (SimBraidSt SimKemFailTrack
  simStepKemFailSend kemTrackEnc)
open CryptoVerification.LibsignalSpqrV1 (MlKem V1State coinBytes coinBytes_length
  potentiallyFixStateIncorrectlyEncodedByLibcruxIssue1275Bytes)
open CryptoVerification.SpqrV1Sync.SendTotal (BOkTight)
open CryptoVerification.E2E (Bytes)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost (
  simFullT simMirT)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8State (
  sOpPure sOpSpqr eLet)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedInit (
  fig8RecT fig8MirT fig8GsT kemCoinsT kemSentEntryT kemTrackT kemFailStateT
  kemTrackAtomicEnc)

section Definitions

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {C : Crypto} {K : MlKem}
  {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
  {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
local notation "sPure" => sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt)
  (encT := encT) (decT := decT) (lam := lam)
local notation "sSpqr" => sOpSpqr (C := C) (K := K) (Dh := Dh) (encPt := encPt)
  (encT := encT) (decT := decT) (lam := lam)

/-! ## Mirror projections -/

def boolOrE {O' : Ops ASig} {Γ : List (Ty ASig)} (a b : Expr O' Γ .bool) : Expr O' Γ .bool :=
  .ite a (.bool true) b
def boolEqE {O' : Ops ASig} {Γ : List (Ty ASig)} (a b : Expr O' Γ .bool) : Expr O' Γ .bool :=
  .ite a b (.not b)
def fgSt {O' : Ops ASig} {Γ : List (Ty ASig)} (g : Expr O' Γ (fig8GsT ℓ Pt)) :
    Expr O' Γ (.prod (fig8StT (ℓ := ℓ) (Pt := Pt)) (fig8StT (ℓ := ℓ) (Pt := Pt))) := .fst g
def fgMir {O' : Ops ASig} {Γ : List (Ty ASig)} (g : Expr O' Γ (fig8GsT ℓ Pt)) :
    Expr O' Γ (fig8MirT ℓ Pt) := .snd g
def fgRecPos {O' : Ops ASig} {Γ : List (Ty ASig)} (r : Expr O' Γ (fig8RecT ℓ Pt)) :
    Expr O' Γ posTy := .fst r
def fgB {O' : Ops ASig} {Γ : List (Ty ASig)} (m : Expr O' Γ (fig8MirT ℓ Pt)) : Expr O' Γ .bool := .fst m
def fgWin {O' : Ops ASig} {Γ : List (Ty ASig)} (m : Expr O' Γ (fig8MirT ℓ Pt)) : Expr O' Γ .bool :=
  .fst (.snd m)
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
    (simToFgMirKeepTransE (SimFig8State.mLeakE (fgToSimMirE (.fst .v0)) (.snd .v0)) (fgTrans (.fst .v0)))
def fgEpMgmtE {O' : Ops ASig} {Γ : List (Ty ASig)} (qepFig : ℕ)
    (m : Expr O' Γ (fig8MirT ℓ Pt)) (p bad : Expr O' Γ .bool) :
    Expr O' Γ (.opt (fig8MirT ℓ Pt)) :=
  eLet (.pair m (.pair p bad))
    (.caseOpt (SimFig8State.mEpMgmtE qepFig (fgToSimMirE (.fst .v0)) (.fst (.snd .v0)) (.snd (.snd .v0)))
      .none (.some (simToFgMirKeepTransE .v0 (fgTrans (.fst .v1)))))
def fgRecordE {O' : Ops ASig} {Γ : List (Ty ASig)}
    (m : Expr O' Γ (fig8MirT ℓ Pt)) (p : Expr O' Γ .bool)
    (r : Expr O' Γ (fig8RecT ℓ Pt)) (isChall : Expr O' Γ .bool) : Expr O' Γ (fig8MirT ℓ Pt) :=
  eLet (.pair m (.pair p (.pair r isChall)))
    (let m0 : Expr O' _ (fig8MirT ℓ Pt) := .fst .v0
     let p0 : Expr O' _ .bool := .fst (.snd .v0)
     let r0 : Expr O' _ (fig8RecT ℓ Pt) := .fst (.snd (.snd .v0))
     fgMirMk (fgB m0) (fgWin m0) (fgEpoch m0) (pSet (fgIdx m0) p0 (posIdx (fgRecPos r0))) (fgTL m0)
       (.cons r0 (fgTrans m0))
       (.ite (.snd (.snd (.snd .v0))) (.cons (fgRecPos r0) (fgChall m0)) (fgChall m0))
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
       (.ite (.and (boolEq (posSender (fgRecPos .v0)) (otherE (.snd .v2)))
           (.not (.anyB Lq .v1 (posEq .v0 (fgRecPos .v1)))))
         (.cons (fgRecPos .v0) .v1) .v1)
     let m1 := fgMirMk (fgB m0) (fgWin m0) (fgEpoch m0) (fgIdx m0) (fgTL m0)
       (fgTrans m0) (fgChall m0) comp' (fgMaxAcc m0) (fgLeaks m0) (fgCorrs m0)
     let m2 := fgLeakE m1 (maxN (.fst (fgEpoch m0)) (.snd (fgEpoch m0)))
     fgMirMk (fgB m2) (fgWin m2) (fgEpoch m2) (fgIdx m2) (fgTL m2)
       (fgTrans m2) (fgChall m2) (fgComp m2) (fgMaxAcc m2) (fgLeaks m2)
       (.cons (.pair p0 (pGet (fgEpoch m0) p0)) (fgCorrs m2)))
def trE_e {O' : Ops ASig} {Γ : List (Ty ASig)} (tr : Expr O' Γ (kemTrackT ℓ Pt)) : Expr O' Γ U64 := .fst tr
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
def trMk {O' : Ops ASig} {Γ : List (Ty ASig)} (e : Expr O' Γ U64) (c : Expr O' Γ (kemCoinsT ℓ Pt))
    (st : Expr O' Γ (.prod (B 32) (B 32))) (sentB : Expr O' Γ (.list (kemSentEntryT ℓ Pt)))
    (sendCtr : Expr O' Γ (.prod (.tbl .nat) (.tbl .nat)))
    (cand : Expr O' Γ (.opt (.prod BV512 BV256))) : Expr O' Γ (kemTrackT ℓ Pt) :=
  .pair e (.pair c (.pair st (.pair sentB (.pair sendCtr cand))))
def kfSimC {O' : Ops ASig} {Γ : List (Ty ASig)} (s : Expr O' Γ (kemFailStateT ℓ Pt)) :
    Expr O' Γ (simFullT ℓ Pt) := .fst s
def kfFig8 {O' : Ops ASig} {Γ : List (Ty ASig)} (s : Expr O' Γ (kemFailStateT ℓ Pt)) :
    Expr O' Γ (fig8GsT ℓ Pt) := .fst (.snd s)
def kfTrack {O' : Ops ASig} {Γ : List (Ty ASig)} (s : Expr O' Γ (kemFailStateT ℓ Pt)) :
    Expr O' Γ (kemTrackT ℓ Pt) := .snd (.snd s)
def kfMk {O' : Ops ASig} {Γ : List (Ty ASig)} (sC : Expr O' Γ (simFullT ℓ Pt))
    (g : Expr O' Γ (fig8GsT ℓ Pt)) (tr : Expr O' Γ (kemTrackT ℓ Pt)) :
    Expr O' Γ (kemFailStateT ℓ Pt) := .pair sC (.pair g tr)

/-! ## Issue-1275 fixup and `honestExchangeFailsAtomicC` -/

def bytes2EqLitE {Γ : List (Ty ASig)} (x : Expr AOps Γ (B 2)) (b0 b1 : BitVec 8) :
    Expr AOps Γ .bool :=
  sPure (.bytesEq 2 2) (.pair x (sPure (.bytesLit 2 [b0, b1]) .unit))

def issue1275ScanStepE {Γ : List (Ty ASig)} :
    Expr AOps (.prod (B 512) (.opt .bool) :: Γ) (.prod (B 512) (.opt .bool)) :=
  let rem : Expr AOps (.prod (B 512) (.opt .bool) :: Γ) (B 512) := .fst .v0
  .caseOpt (.snd .v0)
    (.ite (.lt (.nat 1) (sPure (.bytesLen 512) rem))
      (eLet (sPure (.bytesTakeK 512 2) rem)
        (let p2 : Expr AOps (B 2 :: .prod (B 512) (.opt .bool) :: Γ) (B 2) := .v0
         let rem1 : Expr AOps (B 2 :: .prod (B 512) (.opt .bool) :: Γ) (B 512) := .fst .v1
         let b2eq := bytes2EqLitE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
           (encT := encT) (decT := decT) (lam := lam) p2
         let isCont := boolOrE (b2eq 0x00#8 0x00#8) (b2eq 0xff#8 0xff#8)
         let isFlip := boolOrE (b2eq 0x00#8 0x01#8)
           (boolOrE (b2eq 0x00#8 0x02#8) (b2eq 0xff#8 0xfe#8))
         .ite isCont
           (.pair (sPure (.bytesDrop 512) (.pair (.nat 2) rem1)) .none)
           (.pair rem1 (.some isFlip))))
      (.pair rem (.some (.bool false))))
    .v1

def swapPairsStepE {Γ : List (Ty ASig)} :
    Expr AOps (.prod (B 2048) (B 2048) :: Γ) (.prod (B 2048) (B 2048)) :=
  let rem : Expr AOps (.prod (B 2048) (B 2048) :: Γ) (B 2048) := .fst .v0
  let acc : Expr AOps (.prod (B 2048) (B 2048) :: Γ) (B 2048) := .snd .v0
  .ite (.lt (.nat 1) (sPure (.bytesLen 2048) rem))
    (let b0 := sPure (.bytesTakeK 2048 1) rem
     let b1 := sPure (.bytesTakeK 2048 1) (sPure (.bytesDrop 2048) (.pair (.nat 1) rem))
     let swapped2 : Expr AOps _ (B 2) := sPure (.bytesCat 1 1) (.pair b1 b0)
     let rem' := sPure (.bytesDrop 2048) (.pair (.nat 2) rem)
     let acc' := sPure (.bytesTakeK 2050 2048) (sPure (.bytesCat 2048 2) (.pair acc swapped2))
     .pair rem' acc')
    .v0

/-- Atomic computation for `(potentiallyFixStateIncorrectlyEncodedByLibcruxIssue1275Bytes es).getD es`. -/
def issue1275FixEsC {Γ : List (Ty ASig)} (esE : Expr AOps Γ (B 2080)) :
    Comp AOps (coinOnlyIface ℓ Pt) Γ (B 2080) :=
  .bind (.ret esE)
    (let errSlice : Expr AOps (B 2080 :: Γ) (B 512) :=
       sPure (.bytesTakeK 2080 512) (sPure (.bytesDrop 2080) (.pair (.nat 1536) .v0))
     .bind
       (.iter 256 (.pair errSlice .none)
         (.ret (issue1275ScanStepE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
           (encT := encT) (decT := decT) (lam := lam))))
       (let needsFlip : Expr AOps (.prod (B 512) (.opt .bool) :: B 2080 :: Γ) .bool :=
          .caseOpt (.snd .v0) (.bool false) .v0
        .ite needsFlip
          (let initSwap : Expr AOps _ (.prod (B 2048) (B 2048)) :=
             .pair (sPure (.bytesTakeK 2080 2048) .v1) (sPure (.bytesLit 2048 []) .unit)
           .bind
             (.iter 1024 initSwap
               (.ret (swapPairsStepE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                 (encT := encT) (decT := decT) (lam := lam))))
             (let tail32 := sPure (.bytesTakeK 2080 32)
                (sPure (.bytesDrop 2080) (.pair (.nat 2048) .v2))
              .ret (sPure (.bytesCat 2048 32) (.pair (.snd .v0) tail32))))
          (.ret .v1)))

/-- Atomic computation for `K.honestExchangeFails` on `seedE` and `randE`. -/
def honestExchangeFailsAtomicC {Γ : List (Ty ASig)}
    (seedE : Expr AOps Γ BV512) (randE : Expr AOps Γ BV256) :
    Comp AOps (coinOnlyIface ℓ Pt) Γ .bool :=
  .bind (.ret (.pair (sSpqr .kem768FromSeed seedE) randE))
    (let hdr1 := Expr.fst (.fst .v0)
     let rand1 := Expr.snd .v0
     .caseOpt (sSpqr .kem768Encaps1 (.pair hdr1 rand1))
       (.ret (.bool true))
       (let hdr2 := Expr.fst (.fst .v1)
        let ek2 := Expr.fst (.snd (.fst .v1))
        let es2 := Expr.fst (.snd .v0)
        .ite (.not (sSpqr .kem768ValidPk (.pair hdr2 ek2)))
          (.ret (.bool true))
          (.bind
            (issue1275FixEsC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
              (decT := decT) (lam := lam) es2)
            (let ek3 := Expr.fst (.snd (.fst .v2))
             .ret
               (Expr.caseOpt (sSpqr .kem768Encaps2 (.pair .v0 ek3))
                 (.bool true)
                 (Expr.caseOpt
                   (sSpqr .kem768Decaps (.pair (.snd (.snd (.fst .v3))) (.pair (.fst .v2) .v0)))
                   (.bool true)
                   (.not (sPure .bv256Eq (.pair .v0 (.snd (.snd .v3)))))))))))

/-! ## Braid tracker send step -/

def encRandBvAtomicE {Γ : List (Ty ASig)} (rqE : Expr AOps Γ BV512) : Expr AOps Γ BV256 :=
  sPure .bytesToBv256 (sPure (.bytesTakeK 64 32) (sPure .bv512ToBytes64 rqE))

def isKeysUnsampledV1E {Γ : List (Ty ASig)} (v1E : Expr AOps Γ (B 32)) : Expr AOps Γ .bool :=
  sPure (.bytesEq 1 1) (.pair (sPure (.bytesTakeK 32 1) v1E) (sPure (.bytesLit 1 [0x0a#8]) .unit))

def isHeaderReceivedV1E {Γ : List (Ty ASig)} (v1E : Expr AOps Γ (B 32)) : Expr AOps Γ .bool :=
  sPure (.bytesEq 1 1) (.pair (sPure (.bytesTakeK 32 1) v1E) (sPure (.bytesLit 1 [0x3a#8]) .unit))

def ekSideIsAE {Γ : List (Ty ASig)} (eE : Expr AOps Γ U64) : Expr AOps Γ .bool :=
  .eqN (.modK 2 (sPure .u64ToNat eE)) (.nat 1)

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
     .caseOpt (.snd (sSpqr .spqrBraidSend (.pair v1Q rq0)))
       (.pair trCandOnly trCandOnly)
       (let tr1 : Expr AOps _ (kemTrackT ℓ Pt) := .fst .v1
        let q1 : Expr AOps _ .bool := .fst (.snd .v1)
        let rq1 : Expr AOps _ BV512 := .fst (.snd (.snd .v1))
        let cand1 : Expr AOps _ (.opt (.prod BV512 BV256)) := .snd (.snd (.snd .v1))
        let newV1 := Expr.fst .v0
        let msgEpoch := Expr.fst (.snd .v0)
        let payloadSuffix := Expr.snd (.snd (.snd .v0))
        let epIdx := Expr.sub (sPure .u64ToNat msgEpoch) (.nat 1)
        let ctrTblQ := pGet (trE_sendCtr tr1) q1
        let n1 := Expr.add (.tget ctrTblQ epIdx) (.nat 1)
        let ctrBv := sPure .u32OfNat n1
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

/-- Atomic computation returning `(stepKemFailSend tr Q rq, { tr with cand := (stepKemFailSend tr Q rq).cand })`. -/
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

end Definitions

/-! ## Evaluation lemmas -/

section EvalProofs

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {C : Crypto} {K : MlKem}
  {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
  {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

private def pack16 (b0 b1 : BitVec 8) : BitVec 16 :=
  (b1.zeroExtend 16 <<< 8) ||| b0.zeroExtend 16

private theorem pack16_extract0 (b0 b1 : BitVec 8) :
    (pack16 b0 b1).extractLsb' 0 8 = b0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [pack16, hi]; omega

private theorem pack16_extract8 (b0 b1 : BitVec 8) :
    (pack16 b0 b1).extractLsb' 8 8 = b1 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have h16 : 8 + i < 16 := by omega
  have h8 : ¬ (8 + i < 8) := by omega
  simp [pack16, hi, h16, h8]
private theorem pack16_inj {a0 a1 b0 b1 : BitVec 8} :
    pack16 a0 a1 = pack16 b0 b1 ↔ a0 = b0 ∧ a1 = b1 := by
  refine ⟨fun h => ⟨by simpa [pack16_extract0] using congrArg (·.extractLsb' 0 8) h,
    by simpa [pack16_extract8] using congrArg (·.extractLsb' 8 8) h⟩, ?_⟩
  rintro ⟨rfl, rfl⟩; rfl
private theorem pack16_beq (a0 a1 b0 b1 : BitVec 8) :
    (pack16 a0 a1 == pack16 b0 b1) = ([a0, a1] == [b0, b1]) := by
  rw [Bool.eq_iff_iff]; simp [pack16_inj]
private def issue1275ScanStepFn : Bytes × Option Bool → Bytes × Option Bool
  | (rem, some b) => (rem, some b)
  | (rem, none) =>
    if 1 < rem.length then
      let p2 := rem.take 2
      let isCont := (p2 == [0x00#8, 0x00#8]) || (p2 == [0xff#8, 0xff#8])
      let isFlip := (p2 == [0x00#8, 0x01#8]) || ((p2 == [0x00#8, 0x02#8]) || (p2 == [0xff#8, 0xfe#8]))
      if isCont then (rem.drop 2, none) else (rem, some isFlip)
    else (rem, some false)
omit [SampleableType Pt] in
private theorem issue1275ScanStepE_eval {Γ : List (Ty ASig)} (ρ : Env Γ)
    (st : (Ty.prod (B (ℓ := ℓ) (Pt := Pt) 512) (Ty.opt .bool)).denote) :
    (issue1275ScanStepE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam)).eval (.cons st ρ) = issue1275ScanStepFn st := by
  have hOr (a b : Bool) : (if a = true then true else b) = (a || b) := by cases a <;> rfl
  rcases st with ⟨rem, _ | b⟩
  · by_cases hlen : 1 < rem.length
    · simp only [issue1275ScanStepE, issue1275ScanStepFn, bytes2EqLitE, boolOrE, Expr.eval,
        Expr.v0, Expr.v1, Env.get, SimFig8State.eval_eLet, SimFig8State.eval_sOpPure,
        _root_.ReductionDsl.AtomicPureOp.eval, hlen, decide_true, ↓reduceIte, hOr]; rfl
    · simp only [issue1275ScanStepE, issue1275ScanStepFn, Expr.eval, Expr.v0, Env.get,
        SimFig8State.eval_sOpPure, _root_.ReductionDsl.AtomicPureOp.eval, hlen, decide_false,
        Bool.false_eq_true, ↓reduceIte]
  · rfl
private theorem issue1275ScanStepFn_iter_some (n : ℕ) (rem : Bytes) (b : Bool) :
    issue1275ScanStepFn^[n] (rem, some b) = (rem, some b) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, issue1275ScanStepFn, ih]

private theorem issue1275_two_byte_step (b0 b1 : BitVec 8) (rest : Bytes) :
    let p2 := [b0, b1]
    let isCont := (p2 == [0x00#8, 0x00#8]) || (p2 == [0xff#8, 0xff#8])
    let isFlip := (p2 == [0x00#8, 0x01#8]) ||
      ((p2 == [0x00#8, 0x02#8]) || (p2 == [0xff#8, 0xfe#8]))
    CryptoVerification.LibsignalSpqrV1.issue1275NeedsFlip (b0 :: b1 :: rest) =
      if isCont then CryptoVerification.LibsignalSpqrV1.issue1275NeedsFlip rest else isFlip := by
  dsimp only
  rw [CryptoVerification.LibsignalSpqrV1.issue1275NeedsFlip]
  change (let w := pack16 b0 b1
    if (w == pack16 0x00#8 0x00#8 || w == pack16 0xff#8 0xff#8) = true then _
    else if (w == pack16 0x01#8 0x00#8 || w == pack16 0x02#8 0x00#8 ||
      w == pack16 0xfe#8 0xff#8) = true then false
    else if (w == pack16 0x00#8 0x01#8 || w == pack16 0x00#8 0x02#8 ||
      w == pack16 0xff#8 0xfe#8) = true then true
    else false) = _
  simp only [pack16_beq]
  cases hc : ([b0, b1] == [0x00#8, 0x00#8] || [b0, b1] == [0xff#8, 0xff#8])
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hf : ([b0, b1] == [0x00#8, 0x01#8] ||
        ([b0, b1] == [0x00#8, 0x02#8] || [b0, b1] == [0xff#8, 0xfe#8])) = true
    · simp only [Bool.or_eq_true, beq_iff_eq, List.cons.injEq, and_true] at hf
      clear hc
      rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    · have hf' : ([b0, b1] == [0x00#8, 0x01#8] || [b0, b1] == [0x00#8, 0x02#8] ||
          [b0, b1] == [0xff#8, 0xfe#8]) = false := by
        revert hf; cases ([b0, b1] == [0x00#8, 0x01#8]) <;>
          cases ([b0, b1] == [0x00#8, 0x02#8]) <;>
          cases ([b0, b1] == [0xff#8, 0xfe#8]) <;> decide
      have hf'' : ([b0, b1] == [0x00#8, 0x01#8] ||
          ([b0, b1] == [0x00#8, 0x02#8] || [b0, b1] == [0xff#8, 0xfe#8])) = false := by
        simpa [Bool.or_assoc] using hf'
      rw [hf', hf'']
      cases ([b0, b1] == [0x01#8, 0x00#8] || [b0, b1] == [0x02#8, 0x00#8] ||
        [b0, b1] == [0xfe#8, 0xff#8]) <;> rfl
  · rfl

private theorem issue1275ScanStepFn_iter_none (n : ℕ) :
    ∀ (rem : Bytes), rem.length ≤ 2 * n →
      ((issue1275ScanStepFn^[n] (rem, none)).2).getD false =
        CryptoVerification.LibsignalSpqrV1.issue1275NeedsFlip rem := by
  induction n with
  | zero =>
    intro rem hlen
    cases rem with
    | nil => rfl
    | cons _ _ => simp at hlen
  | succ n ih =>
    intro rem hlen
    rw [Function.iterate_succ_apply]
    rcases rem with _ | ⟨b0, _ | ⟨b1, rest⟩⟩
    · simp [issue1275ScanStepFn, issue1275ScanStepFn_iter_some,
        CryptoVerification.LibsignalSpqrV1.issue1275NeedsFlip]
    · simp [issue1275ScanStepFn, issue1275ScanStepFn_iter_some,
        CryptoVerification.LibsignalSpqrV1.issue1275NeedsFlip]
    · have hgt : 1 < (b0 :: b1 :: rest).length := by simp
      have hrest : rest.length ≤ 2 * n := by simp at hlen; omega
      rw [issue1275_two_byte_step b0 b1 rest]
      simp only [issue1275ScanStepFn, hgt, ↓reduceIte, List.take_succ_cons, List.take_zero,
        List.drop_succ_cons, List.drop_zero]
      split
      · exact ih rest hrest
      · rw [issue1275ScanStepFn_iter_some]; rfl

private def swapPairsStepFn : Bytes × Bytes → Bytes × Bytes
  | (rem, acc) =>
    if 1 < rem.length then
      (rem.drop 2, (acc ++ ((rem.drop 1).take 1 ++ rem.take 1)).take 2048)
    else (rem, acc)

omit [SampleableType Pt] in
private theorem swapPairsStepE_eval {Γ : List (Ty ASig)} (ρ : Env Γ)
    (st : (Ty.prod (B (ℓ := ℓ) (Pt := Pt) 2048) (B (ℓ := ℓ) (Pt := Pt) 2048)).denote) :
    (swapPairsStepE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam)).eval (.cons st ρ) = swapPairsStepFn st := by
  rcases st with ⟨rem, acc⟩
  by_cases hlen : 1 < rem.length
  · simp only [swapPairsStepE, swapPairsStepFn, Expr.eval, Expr.v0, Env.get,
      SimFig8State.eval_sOpPure, _root_.ReductionDsl.AtomicPureOp.eval, hlen, decide_true, ↓reduceIte]
    rfl
  · simp only [swapPairsStepE, swapPairsStepFn, Expr.eval, Expr.v0, Env.get,
      SimFig8State.eval_sOpPure, _root_.ReductionDsl.AtomicPureOp.eval, hlen, decide_false,
      Bool.false_eq_true, ↓reduceIte]

private theorem swapAdjacentPairs_length :
    ∀ xs : Bytes, (CryptoVerification.LibsignalSpqrV1.swapAdjacentPairs xs).length = xs.length
  | [] | [_] => rfl
  | _ :: _ :: rest => by
    simp [CryptoVerification.LibsignalSpqrV1.swapAdjacentPairs, swapAdjacentPairs_length rest]
private theorem swapPairsStepFn_iter (n : ℕ) :
    ∀ (rem acc : Bytes), rem.length = 2 * n → acc.length + 2 * n ≤ 2048 →
      swapPairsStepFn^[n] (rem, acc) =
        ([], acc ++ CryptoVerification.LibsignalSpqrV1.swapAdjacentPairs rem) := by
  induction n with
  | zero =>
    rintro (_ | _) acc hlen _
    · simp [CryptoVerification.LibsignalSpqrV1.swapAdjacentPairs]
    · simp at hlen
  | succ n ih =>
    rintro (_ | ⟨b0, _ | ⟨b1, rest⟩⟩) acc hlen hacc
    · simp at hlen
    · simp at hlen; omega
    · have hgt : 1 < (b0 :: b1 :: rest).length := by simp
      have hrest : rest.length = 2 * n := by simp at hlen; omega
      have htk : (acc ++ [b1, b0]).take 2048 = acc ++ [b1, b0] := List.take_of_length_le (by simp; omega)
      rw [Function.iterate_succ_apply]
      simp only [swapPairsStepFn, hgt, ↓reduceIte, List.drop_succ_cons, List.drop_zero,
        List.take_succ_cons, List.take_zero]
      change swapPairsStepFn^[n] (rest, (acc ++ [b1, b0]).take 2048) = _
      rw [htk, ih rest (acc ++ [b1, b0]) hrest (by simp; omega)]
      simp [CryptoVerification.LibsignalSpqrV1.swapAdjacentPairs, List.append_assoc]

theorem issue1275FixEsC_eval {Γ : List (Ty ASig)}
    (esE : Expr AOps Γ (B 2080)) (ρ : Env Γ) (es : Bytes)
    (hes : esE.eval ρ = es) (hlen : es.length = 2080) :
    (issue1275FixEsC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) esE).eval ρ =
      pure ((potentiallyFixStateIncorrectlyEncodedByLibcruxIssue1275Bytes es).getD es) := by
  let esD : (B (ℓ := ℓ) (Pt := Pt) 2080).denote := es
  have hes' : esE.eval ρ = esD := hes
  have h512 : ((512 : ℕ+) : ℕ) = 512 := rfl
  have h2048 : ((2048 : ℕ+) : ℕ) = 2048 := rfl
  simp only [issue1275FixEsC, Comp.eval, Expr.eval, Expr.v0, Expr.v1, Env.get, hes',
    SimFig8State.eval_sOpPure, _root_.ReductionDsl.AtomicPureOp.eval, h512, h2048, pure_bind]
  have hIter1 :
      _root_.ReductionDsl.iterM (m := OracleComp unifSpec)
        (fun a => pure ((issue1275ScanStepE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)).eval (.cons a (.cons esD ρ))))
        256 ((esD.drop 1536).take 512, none) =
      pure (issue1275ScanStepFn^[256] ((esD.drop 1536).take 512, none)) := by
    simp only [issue1275ScanStepE_eval]
    exact SimFig8Crypto.iterM_pure_eq issue1275ScanStepFn 256 _
  rw [hIter1, pure_bind]
  have hScan := issue1275ScanStepFn_iter_none 256 ((esD.drop 1536).take 512)
    (le_trans (List.length_take_le 512 _) (by omega))
  generalize issue1275ScanStepFn^[256] ((esD.drop 1536).take 512, none) = stScan at hScan ⊢
  rcases stScan with ⟨remS, _ | b⟩
  · dsimp only at hScan
    change pure esD = _
    simp [potentiallyFixStateIncorrectlyEncodedByLibcruxIssue1275Bytes,
      show 2080 - 32 - 1536 = 512 by decide, ← hScan, esD]
  · cases b
    · dsimp only at hScan
      change pure esD = _
      simp [potentiallyFixStateIncorrectlyEncodedByLibcruxIssue1275Bytes,
        show 2080 - 32 - 1536 = 512 by decide, ← hScan, esD]
    · dsimp only at hScan ⊢
      have hIter2 :
          _root_.ReductionDsl.iterM (m := OracleComp unifSpec)
            (fun a => pure ((swapPairsStepE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
              (encT := encT) (decT := decT) (lam := lam)).eval
              (.cons a (Env.cons (t := .prod (B (ℓ := ℓ) (Pt := Pt) 512) (.opt .bool))
                (remS, some true) (.cons esD ρ)))))
            1024 (esD.take 2048, []) =
          pure (swapPairsStepFn^[1024] (esD.take 2048, [])) := by
        simp only [swapPairsStepE_eval]
        exact SimFig8Crypto.iterM_pure_eq swapPairsStepFn 1024 _
      rw [hIter2, pure_bind]
      refine congrArg pure (Eq.trans (SimFig8State.eval_sOpPure _ _ _) ?_)
      simp [_root_.ReductionDsl.AtomicPureOp.eval, SimFig8State.eval_sOpPure,
        Expr.eval, Expr.v2,
        swapPairsStepFn_iter 1024 (esD.take 2048) [] (by simp [esD, hlen]) (by simp),
        potentiallyFixStateIncorrectlyEncodedByLibcruxIssue1275Bytes,
        CryptoVerification.LibsignalSpqrV1.flipEndiannessOfEncapsulationStateBytes,
        show 2080 - 32 - 1536 = 512 by decide, show 2080 - 32 = 2048 by decide,
        ← hScan, esD, hlen,
        show (es.drop 2048).take 32 = es.drop 2048 from List.take_of_length_le (by simp [hlen])]

private theorem flipEndianness_length (es : Bytes) (hlen : es.length = 2080) :
    (CryptoVerification.LibsignalSpqrV1.flipEndiannessOfEncapsulationStateBytes es).length = 2080 := by
  simp [CryptoVerification.LibsignalSpqrV1.flipEndiannessOfEncapsulationStateBytes,
    swapAdjacentPairs_length, hlen]

private theorem issue1275_except_eq (es : Bytes) (hlen : es.length = 2080) :
    CryptoVerification.LibsignalSpqrV1.potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275 es =
      .ok (potentiallyFixStateIncorrectlyEncodedByLibcruxIssue1275Bytes es) ∧
    ((potentiallyFixStateIncorrectlyEncodedByLibcruxIssue1275Bytes es).getD es).length = 2080 := by
  unfold CryptoVerification.LibsignalSpqrV1.potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275
    potentiallyFixStateIncorrectlyEncodedByLibcruxIssue1275Bytes
    CryptoVerification.LibsignalSpqrV1.flip_endianness_of_encapsulation_state
  have hNe : (es.length != CryptoVerification.LibsignalSpqrV1.ENCAPSULATION_STATE_SIZE) = false := by
    simp [CryptoVerification.LibsignalSpqrV1.ENCAPSULATION_STATE_SIZE, hlen]
  have hBad : (es.length % 2 != 0 || !(es.length > 32)) = false := by simp [hlen]
  simp only [hNe, Bool.false_eq_true, ↓reduceIte]
  cases CryptoVerification.LibsignalSpqrV1.issue1275NeedsFlip
      ((es.drop 1536).take (2080 - 32 - 1536))
  · exact ⟨rfl, hlen⟩
  · simp only [↓reduceIte, hBad, Bool.false_eq_true, Option.getD_some,
      flipEndianness_length es hlen]
    exact ⟨rfl, trivial⟩

private theorem bytesToKey32_beq_iff {a b : Bytes} (ha : a.length = 32) (hb : b.length = 32) :
    (!(CryptoGames.HKDF.bytesToKey32 a == CryptoGames.HKDF.bytesToKey32 b)) = decide (a ≠ b) := by
  suffices h : (CryptoGames.HKDF.bytesToKey32 a = CryptoGames.HKDF.bytesToKey32 b) ↔ a = b by
    by_cases hab : a = b <;> simp [hab, h]
  constructor
  · intro heq
    calc a = CryptoGames.HMAC.keyToBytes32 (CryptoGames.HKDF.bytesToKey32 a) :=
            (SimFig8LoopAndCost.keyToBytes32_bytesToKey32 a ha).symm
      _ = CryptoGames.HMAC.keyToBytes32 (CryptoGames.HKDF.bytesToKey32 b) := by rw [heq]
      _ = b := SimFig8LoopAndCost.keyToBytes32_bytesToKey32 b hb
  · intro rfl; rfl

theorem honestExchangeFailsAtomicC_eval {Γ : List (Ty ASig)}
    (seedE : Expr AOps Γ BV512) (randE : Expr AOps Γ BV256) (ρ : Env Γ)
    (seed : BitVec 512) (rand : BitVec 256)
    (hs : seedE.eval ρ = seed) (hr : randE.eval ρ = rand) :
    (honestExchangeFailsAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) seedE randE).eval ρ =
      pure (K.honestExchangeFails ⟨coinBytes seed, coinBytes_length seed⟩ (keyToBytesVec32 rand)) := by
  set seedVec : List.Vector (BitVec 8) 64 := ⟨coinBytes seed, coinBytes_length seed⟩
  set mVec : List.Vector (BitVec 8) 32 := keyToBytesVec32 rand
  have hGen : CryptoVerification.LibsignalSpqrV1.generate K seedVec.toList =
      let (hdr, ek, dk) := K.fromSeed seedVec
      .ok ({ ek := ek.toList, dk := dk.toList, hdr := hdr.toList }, []) := by
    unfold CryptoVerification.LibsignalSpqrV1.generate
    have htk : seedVec.toList.take CryptoVerification.LibsignalSpqrV1.KEY_GENERATION_SEED_SIZE =
        coinBytes seed :=
      List.take_of_length_le (by simp [seedVec, coinBytes_length,
        CryptoVerification.LibsignalSpqrV1.KEY_GENERATION_SEED_SIZE])
    have hdrp : seedVec.toList.drop CryptoVerification.LibsignalSpqrV1.KEY_GENERATION_SEED_SIZE = [] :=
      List.drop_eq_nil_of_le (by simp [seedVec, coinBytes_length,
        CryptoVerification.LibsignalSpqrV1.KEY_GENERATION_SEED_SIZE])
    rw [htk, hdrp]
    simp [CryptoVerification.LibsignalSpqrV1.bytesToVector?,
      CryptoVerification.LibsignalSpqrV1.KEY_GENERATION_SEED_SIZE, coinBytes_length, seedVec]
  simp only [honestExchangeFailsAtomicC, Comp.eval, Expr.eval,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Env.get,
    hs, hr, SimFig8State.eval_sOpSpqr, SimFig8State.eval_sOpPure,
    _root_.ReductionDsl.AtomicSpqrKemOp.eval, _root_.ReductionDsl.AtomicPureOp.eval, pure_bind]
  unfold MlKem.honestExchangeFails
  rw [hGen]
  rcases hFrom : K.fromSeed seedVec with ⟨hdr, ek, dk⟩
  dsimp only
  have hEnc1Rhs : CryptoVerification.LibsignalSpqrV1.encaps1 K hdr.toList mVec.toList =
      match K.encaps1 hdr.toList mVec with
      | none => .error .encaps1Failed
      | some (ct1, es, ss) => .ok ((ct1.toList, es.toList, ss.toList), []) := by
    unfold CryptoVerification.LibsignalSpqrV1.encaps1
    have htk : mVec.toList.take CryptoVerification.LibsignalSpqrV1.SHARED_SECRET_SIZE = mVec.toList :=
      List.take_of_length_le (by simp [CryptoVerification.LibsignalSpqrV1.SHARED_SECRET_SIZE])
    have hdrp : mVec.toList.drop CryptoVerification.LibsignalSpqrV1.SHARED_SECRET_SIZE = [] :=
      List.drop_eq_nil_of_le (by simp [CryptoVerification.LibsignalSpqrV1.SHARED_SECRET_SIZE])
    rw [htk, hdrp]
    simp only [CryptoVerification.LibsignalSpqrV1.bytesToVector?,
      CryptoVerification.LibsignalSpqrV1.SHARED_SECRET_SIZE, List.Vector.toList_length, ↓reduceDIte]
    generalize_proofs pf
    have hV : ⟨mVec.toList, pf⟩ = mVec := Subtype.ext rfl
    rw [hV]
    rcases K.encaps1 hdr.toList mVec with _ | ⟨ct1, es, ss⟩ <;> rfl
  rw [hEnc1Rhs]
  rcases hE1 : K.encaps1 hdr.toList mVec with _ | ⟨ct1, es, ssB⟩
  · rfl
  · simp only [Option.map_some, CryptoVerification.LibsignalSpqrV1.ek_matches_header]
    have hIteF {α : Type} {P : Prop} [Decidable P] (h : ¬ P) (a b : α) :
        (if P then a else b) = b := by split <;> [exact absurd ‹_› h; rfl]
    have hIteT {α : Type} {P : Prop} [Decidable P] (h : P) (a b : α) :
        (if P then a else b) = a := by split <;> [rfl; exact absurd h ‹_›]
    by_cases hPk : K.validPkBytes hdr.toList ek.toList = true
    · refine Eq.trans (hIteF (by simp [hPk]) _ _)
        (Eq.trans ?_ (congrArg pure (hIteF (by simp [hPk]) _ _).symm))
      refine Eq.trans (congrArg (· >>= _) (issue1275FixEsC_eval _ _ es.toList rfl es.2)) ?_
      rw [pure_bind]
      obtain ⟨hFixOk, hEs'Len⟩ := issue1275_except_eq es.toList es.2
      set es' := (potentiallyFixStateIncorrectlyEncodedByLibcruxIssue1275Bytes es.toList).getD es.toList
      have hVecEq {n : ℕ} (v : List.Vector (BitVec 8) n) (h : v.toList.length = n) :
          (⟨v.toList, h⟩ : List.Vector (BitVec 8) n) = v := Subtype.ext rfl
      have hEnc2Rhs : CryptoVerification.LibsignalSpqrV1.encaps2 K ek.toList es.toList =
          .ok (K.encaps2 ⟨es', hEs'Len⟩ ek).toList := by
        unfold CryptoVerification.LibsignalSpqrV1.encaps2
          CryptoVerification.LibsignalSpqrV1.bytesToVector?
        rw [hFixOk]
        dsimp only [Bind.bind, Except.bind]
        rw [show (potentiallyFixStateIncorrectlyEncodedByLibcruxIssue1275Bytes es.toList).getD es.toList =
          es' from rfl]
        simp only [CryptoVerification.LibsignalSpqrV1.ENCAPSULATION_STATE_SIZE,
          CryptoVerification.LibsignalSpqrV1.ENCAPSULATION_KEY_SIZE, hEs'Len,
          List.Vector.toList_length, ↓reduceDIte]
        rfl
      rw [hEnc2Rhs]; dsimp only
      set ct2 := K.encaps2 ⟨es', hEs'Len⟩ ek
      have hDecRhs : CryptoVerification.LibsignalSpqrV1.decaps K dk.toList ct1.toList ct2.toList =
          .ok (K.decaps dk ct1 ct2).toList := by
        unfold CryptoVerification.LibsignalSpqrV1.decaps
          CryptoVerification.LibsignalSpqrV1.bytesToVector?
        simp only [CryptoVerification.LibsignalSpqrV1.CIPHERTEXT1_SIZE,
          CryptoVerification.LibsignalSpqrV1.CIPHERTEXT2_SIZE,
          CryptoVerification.LibsignalSpqrV1.DECAPSULATION_KEY_SIZE,
          List.Vector.toList_length, ↓reduceDIte]
        rfl
      rw [hDecRhs]; dsimp only
      simp only [hEs'Len, List.Vector.toList_length, ↓reduceDIte, hVecEq]
      exact congrArg pure (bytesToKey32_beq_iff (K.decaps dk ct1 ct2).2 ssB.2)
    · exact Eq.trans (hIteT (by simp [hPk]) _ _)
        (congrArg pure (hIteT (by simp [hPk]) _ _).symm)

omit [SampleableType Pt] in
theorem isKeysUnsampledV1E_eval {Γ : List (Ty ASig)}
    (v1E : Expr AOps Γ (B 32)) (ρ : Env Γ) (st : SimBraidSt C.F)
    (hv1 : v1E.eval ρ = V1State.encodeRaw st.into_pb) :
    (isKeysUnsampledV1E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) v1E).eval ρ =
      (match st with | .keysUnsampled _ => true | _ => false) := by
  simp only [isKeysUnsampledV1E, Expr.eval, hv1, SimFig8State.eval_sOpPure,
    _root_.ReductionDsl.AtomicPureOp.eval]
  cases st <;>
    (simp [CryptoVerification.LibsignalSpqrV1.States.into_pb, V1State.encodeRaw,
      V1State.InnerState.encode, CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage,
      CryptoVerification.LibsignalSpqrV1.Proto.encodeKey,
      CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint,
      CryptoVerification.LibsignalSpqrV1.Proto.encodeVarintAux,
      CryptoVerification.LibsignalSpqrV1.Proto.WireType.toU32];
     try (rintro h; injection h with h1; exact absurd h1 (by decide)))

omit [SampleableType Pt] in
theorem isHeaderReceivedV1E_eval {Γ : List (Ty ASig)}
    (v1E : Expr AOps Γ (B 32)) (ρ : Env Γ) (st : SimBraidSt C.F)
    (hv1 : v1E.eval ρ = V1State.encodeRaw st.into_pb) :
    (isHeaderReceivedV1E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) v1E).eval ρ =
      (match st with | .headerReceived _ => true | _ => false) := by
  simp only [isHeaderReceivedV1E, Expr.eval, hv1, SimFig8State.eval_sOpPure,
    _root_.ReductionDsl.AtomicPureOp.eval]
  cases st <;>
    (simp [CryptoVerification.LibsignalSpqrV1.States.into_pb, V1State.encodeRaw,
      V1State.InnerState.encode, CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage,
      CryptoVerification.LibsignalSpqrV1.Proto.encodeKey,
      CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint,
      CryptoVerification.LibsignalSpqrV1.Proto.encodeVarintAux,
      CryptoVerification.LibsignalSpqrV1.Proto.WireType.toU32];
     try (rintro h; injection h with h1; exact absurd h1 (by decide)))

private theorem bytesToWordLE256_eq_bytesToKey32 (bs : Bytes) (h : bs.length = 32) :
    _root_.ReductionDsl.bytesToWordLE 256 bs = CryptoGames.HKDF.bytesToKey32 bs := by
  calc _root_.ReductionDsl.bytesToWordLE 256 bs
      = _root_.ReductionDsl.bytesToWordLE 256
          (CryptoGames.HMAC.keyToBytes32 (CryptoGames.HKDF.bytesToKey32 bs)) := by
        rw [SimFig8LoopAndCost.keyToBytes32_bytesToKey32 bs h]
    _ = CryptoGames.HKDF.bytesToKey32 bs :=
        KemFailRedLoopAndCost.bytesToWordLE256_keyToBytes32 _

omit [SampleableType Pt] in
private theorem encRandBvAtomicE_eval {Γ : List (Ty ASig)}
    (rqE : Expr AOps Γ BV512) (ρ : Env Γ) (rq : BitVec 512) (hrq : rqE.eval ρ = rq) :
    (encRandBvAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) rqE).eval ρ =
      _root_.ReductionDsl.bytesToWordLE 256
        (CryptoGames.Ratchet.LibsignalSim.simEncRandOf rq).toList := by
  have hlen : ((coinBytes rq).take 32).length = 32 := by simp [coinBytes_length]
  simp only [encRandBvAtomicE, hrq, SimFig8State.eval_sOpPure,
    _root_.ReductionDsl.AtomicPureOp.eval, CryptoGames.Ratchet.LibsignalSim.simEncRandOf]
  exact (bytesToWordLE256_eq_bytesToKey32 ((coinBytes rq).take 32) hlen).symm

private theorem keyToBytesVec32_simEncRandOf (rq : BitVec 512) :
    keyToBytesVec32
      (_root_.ReductionDsl.bytesToWordLE 256
        (CryptoGames.Ratchet.LibsignalSim.simEncRandOf rq).toList) =
      CryptoGames.Ratchet.LibsignalSim.simEncRandOf rq :=
  Subtype.ext (KemFailRedLoopAndCost.keyToBytes32_bytesToWordLE256 _
    (CryptoGames.Ratchet.LibsignalSim.simEncRandOf rq).2)

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem spqrBraidSendEval_of_bOkTight (st : SimBraidSt C.F)
    (hbok : BOkTight st) (coins : BitVec 512) :
    _root_.ReductionDsl.spqrBraidSendEval (ℓ := ℓ) (Pt := Pt) C.F K
      (V1State.encodeRaw st.into_pb) coins =
      match st.send K (coinBytes coins) with
      | .error (.panic _) => (true, none)
      | .error (.err _) => (false, none)
      | .ok (sOut, _) =>
        (false, some (V1State.encodeRaw sOut.state.into_pb,
          (sOut.msg.epoch,
           (sOut.key.map (fun es => (es.epoch, CryptoGames.HKDF.bytesToKey32 es.secret)),
            _root_.ReductionDsl.spqrMsgPayloadSuffix sOut.msg)))) := by
  have hraw := Computational.Proofs.E2E.Dsl.ClampsLossless.v1State_encodeRaw_take64000_of_bOkTight
    C.F K st hbok
  have hlen : (V1State.encodeRaw st.into_pb).length < 2 ^ 64 := by
    have hle : ((V1State.encodeRaw st.into_pb).take 64000).length ≤ 64000 :=
      List.length_take_le 64000 _
    rw [hraw] at hle; omega
  unfold _root_.ReductionDsl.spqrBraidSendEval
  rw [CryptoVerification.SpqrV1Sync.Codec.decode_v1State st.into_pb hlen]
  dsimp only
  rw [CryptoVerification.SpqrV1Sync.SendTotal.st_bCodec C.F st hbok.1]
  dsimp only
  rcases hsend : st.send K (coinBytes coins) with ⟨e⟩ | ⟨⟨m, key, st'⟩, tape'⟩
  · cases e <;> rfl
  · dsimp only
    rw [Computational.Proofs.E2E.Dsl.ClampsLossless.bSendClosed_encodeRaw_take64000 C.F K hbok hsend]

omit [SampleableType Pt] in
private theorem eval_pGet_party {Γ : List (Ty ASig)} {t : Ty ASig}
    (pE : Expr AOps Γ (.prod t t)) (qE : Expr AOps Γ .bool) (ρ : Env Γ)
    (f : Party → t.denote) (Q : Party)
    (hp : pE.eval ρ = (f .A, f .B)) (hq : qE.eval ρ = partyToBool Q) :
    (pGet pE qE).eval ρ = f Q := by
  cases Q <;> simp [pGet, Expr.eval, Expr.v0, hp, hq, partyToBool]

omit [SampleableType Pt] in
private theorem eval_pSet_party {Γ : List (Ty ASig)} {t : Ty ASig}
    (pE : Expr AOps Γ (.prod t t)) (qE : Expr AOps Γ .bool) (vE : Expr AOps Γ t) (ρ : Env Γ)
    (f : Party → t.denote) (Q : Party) (v : t.denote)
    (hp : pE.eval ρ = (f .A, f .B)) (hq : qE.eval ρ = partyToBool Q) (hv : vE.eval ρ = v) :
    (pSet pE qE vE).eval ρ = (Function.update f Q v .A, Function.update f Q v .B) := by
  cases Q <;> simp [pSet, Expr.eval, Expr.v0, hp, hq, hv, partyToBool, Function.update]

omit [SampleableType Pt] in
private theorem nextKemCoinsAtomicE_eval {Γ : List (Ty ASig)}
    (cE : Expr AOps Γ (kemCoinsT ℓ Pt)) (v1QE : Expr AOps Γ (B 32))
    (rqE : Expr AOps Γ BV512) (ρ : Env Γ)
    (c : CryptoGames.Ratchet.LibsignalSim.SimKemCoins) (stQ : SimBraidSt C.F) (rq : BitVec 512)
    (hc : cE.eval ρ = KemFailRedInit.kemCoinsAtomicEnc c)
    (hv1 : v1QE.eval ρ = V1State.encodeRaw stQ.into_pb)
    (hrq : rqE.eval ρ = rq) :
    (nextKemCoinsAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) cE v1QE rqE).eval ρ =
      KemFailRedInit.kemCoinsAtomicEnc
        (CryptoGames.Ratchet.LibsignalSim.simNextKemCoins C.F c stQ (coinBytes rq)) := by
  simp only [nextKemCoinsAtomicE, SimFig8State.eval_eLet, Expr.eval, hc, hv1, hrq]
  rcases c with _ | ⟨s⟩ | ⟨s, r⟩
  · simp only [KemFailRedInit.kemCoinsAtomicEnc, Expr.eval, Expr.v0, Expr.v1, Env.get]
    rw [isKeysUnsampledV1E_eval _ _ stQ (by simp [Expr.eval])]
    cases stQ <;>
      simp [CryptoGames.Ratchet.LibsignalSim.simNextKemCoins,
        coinBytes_length, List.take_of_length_le, KemFailRedLoopAndCost.bytesToWordLE512_coinBytes]
  · simp only [KemFailRedInit.kemCoinsAtomicEnc, Expr.eval, Expr.v0, Expr.v2, Env.get]
    rw [isHeaderReceivedV1E_eval _ _ stQ (by simp [Expr.eval])]
    cases stQ <;>
      simp [CryptoGames.Ratchet.LibsignalSim.simNextKemCoins,
        coinBytes_length]
    refine encRandBvAtomicE_eval (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) _ _ rq ?_
    simp [Expr.eval]
  · simp only [KemFailRedInit.kemCoinsAtomicEnc, Expr.eval, Expr.v0, Env.get]
    cases stQ <;> simp [CryptoGames.Ratchet.LibsignalSim.simNextKemCoins]

private def simNextKemCand (tr : SimKemFailTrack C.F) (Q : Party) (r : BitVec 512) :
    Option (CryptoGames.Ratchet.LibsignalSim.SimKemSeed ×
      CryptoGames.Ratchet.LibsignalSim.SimKemEncRand) :=
  match tr.cand with
  | some p => some p
  | none =>
    if CryptoGames.Ratchet.LibsignalSim.simEkSideIsA tr.e != (Q == .A) then
      match tr.c, tr.st Q with
      | .seed s, .headerReceived _ =>
        if K.honestExchangeFails s (CryptoGames.Ratchet.LibsignalSim.simEncRandOf r) then
          some (s, CryptoGames.Ratchet.LibsignalSim.simEncRandOf r)
        else none
      | _, _ => none
    else none

private theorem nextKemCandAtomicC_eval {Γ : List (Ty ASig)}
    (trE : Expr AOps Γ (kemTrackT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (rqE : Expr AOps Γ BV512) (ρ : Env Γ)
    (tr : SimKemFailTrack C.F) (Q : Party) (rq : BitVec 512)
    (htr : trE.eval ρ = kemTrackAtomicEnc tr) (hqB : qBE.eval ρ = partyToBool Q)
    (hrq : rqE.eval ρ = rq) :
    (nextKemCandAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) trE qBE rqE).eval ρ =
      pure ((simNextKemCand (C := C) (K := K) tr Q rq).map
        KemFailRedLoopAndCost.kemCandVecToBv) := by
  simp only [nextKemCandAtomicC, Comp.eval, Expr.eval, htr, hqB, hrq, pure_bind]
  set p0 : (Ty.prod (kemTrackT ℓ Pt) (Ty.prod .bool BV512)).denote :=
    (kemTrackAtomicEnc tr, (partyToBool Q, rq))
  rcases hCand : tr.cand with _ | candVal
  · have hCandE : (trE_cand (O' := AOps) (.fst .v0)).eval (.cons p0 ρ) = none := by
      simp [trE_cand, p0, kemTrackAtomicEnc, hCand, Expr.eval, Expr.v0]
    simp only [hCandE, simNextKemCand, hCand]
    have hv1Q : (pGet (trE_st (O' := AOps) (.fst .v0)) (.fst (.snd .v0))).eval (.cons p0 ρ) =
        V1State.encodeRaw (tr.st Q).into_pb := by
      refine eval_pGet_party (t := B 32) _ _ _ (fun P => V1State.encodeRaw (tr.st P).into_pb) Q ?_ ?_
      · simp [trE_st, p0, kemTrackAtomicEnc, Expr.eval, Expr.v0]
      · simp [p0, Expr.eval, Expr.v0]
    have hEkEq : (boolEqE
        (ekSideIsAE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) (trE_e (.fst .v0)))
        (.fst (.snd .v0))).eval (.cons p0 ρ) =
        (CryptoGames.Ratchet.LibsignalSim.simEkSideIsA tr.e != (Q == .A)) := by
      simp only [boolEqE, ekSideIsAE, trE_e, p0, kemTrackAtomicEnc, Expr.eval, Expr.v0, Env.get,
        SimFig8State.eval_sOpPure, _root_.ReductionDsl.AtomicPureOp.eval,
        CryptoGames.Ratchet.LibsignalSim.simEkSideIsA]
      cases Q <;> cases decide (tr.e.toNat % 2 = 1) <;> rfl
    simp only [hEkEq, isHeaderReceivedV1E_eval _ _ (tr.st Q) hv1Q]
    cases hSide : (CryptoGames.Ratchet.LibsignalSim.simEkSideIsA tr.e != (Q == .A))
    · simp
    · simp only [Bool.true_and, ↓reduceIte]
      generalize tr.st Q = stQ at hv1Q ⊢
      rcases stQ with _ | _ | _ | _ | _ | _ | _ | hdrSt | _ | _ | _ | _ <;>
        try (rcases tr.c with _ | _ | _ <;> (simp; done))
      rcases hC : tr.c with _ | ⟨s⟩ | ⟨s, r0⟩
      · simp [trE_c, p0, kemTrackAtomicEnc, hC, KemFailRedInit.kemCoinsAtomicEnc,
          Expr.eval, Expr.v0]
      · set sBv : (BV512 (ℓ := ℓ) (Pt := Pt)).denote :=
          _root_.ReductionDsl.bytesToWordLE 512 s.toList
        set sInl : (Ty.sum (S := ASig) BV512 (.prod BV512 BV256)).denote := Sum.inl sBv
        have hTrC : (trE_c (O' := AOps) (.fst .v0)).eval (.cons p0 ρ) = Sum.inr sInl := by
          simp [trE_c, p0, kemTrackAtomicEnc, hC, KemFailRedInit.kemCoinsAtomicEnc, sInl, sBv,
            Expr.eval, Expr.v0]
        have hV0Inl : (Expr.v0 : Expr AOps _ _).eval (.cons sInl (.cons p0 ρ)) = Sum.inl sBv := by
          simp [sInl, Expr.eval, Expr.v0]
        simp only [hTrC, hV0Inl]
        have hHef : (honestExchangeFailsAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam) .v0
            (encRandBvAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
              (decT := decT) (lam := lam) (.snd (.snd .v2)))).eval
            (.cons sBv (.cons sInl (.cons p0 ρ))) =
            pure (K.honestExchangeFails s (CryptoGames.Ratchet.LibsignalSim.simEncRandOf rq)) := by
          rw [honestExchangeFailsAtomicC_eval _ _ _ sBv
            (_root_.ReductionDsl.bytesToWordLE 256
              (CryptoGames.Ratchet.LibsignalSim.simEncRandOf rq).toList)
            (by simp [Expr.eval, Expr.v0])
            (encRandBvAtomicE_eval _ _ rq (by simp [p0, Expr.eval, Expr.v2]))]
          have hsVec : (⟨coinBytes sBv, coinBytes_length _⟩ : List.Vector (BitVec 8) 64) = s :=
            Subtype.ext (KemFailRedLoopAndCost.coinBytes_bytesToWordLE512 s.toList s.2)
          rw [hsVec, keyToBytesVec32_simEncRandOf rq]
        rw [hHef, pure_bind]
        have hRand3 (b : Ty.bool.denote) :
            (encRandBvAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
              (decT := decT) (lam := lam) (.snd (.snd .v3))).eval
              (.cons b (.cons sBv (.cons sInl (.cons p0 ρ)))) =
            _root_.ReductionDsl.bytesToWordLE 256
              (CryptoGames.Ratchet.LibsignalSim.simEncRandOf rq).toList :=
          encRandBvAtomicE_eval _ _ rq (by simp [p0, Expr.eval, Expr.v3])
        cases K.honestExchangeFails s (CryptoGames.Ratchet.LibsignalSim.simEncRandOf rq) <;>
          simp [sBv, Expr.eval, Expr.v0, Expr.v1, hRand3,
            KemFailRedLoopAndCost.kemCandVecToBv]
      · simp [trE_c, p0, kemTrackAtomicEnc, hC, KemFailRedInit.kemCoinsAtomicEnc,
          Expr.eval, Expr.v0]
  · simp [trE_cand, p0, kemTrackAtomicEnc, hCand, simNextKemCand,
      Expr.eval, Expr.v0]

private theorem simStepKemFailSend_eq (tr : SimKemFailTrack C.F) (Q : Party) (r : BitVec 512) :
    simStepKemFailSend C.F K tr Q r =
      let cand' := simNextKemCand (C := C) (K := K) tr Q r
      let tape := coinBytes r
      match (tr.st Q).send K tape with
      | .ok (out, _) =>
        let E := out.msg.epoch.toNat - 1
        let n := tr.sendCtr Q E
        { tr with
          c := CryptoGames.Ratchet.LibsignalSim.simNextKemCoins C.F tr.c (tr.st Q) tape
          st := Function.update tr.st Q out.state
          sentB := tr.sentB ++ [(out.msg, BitVec.ofNat 32 (n + 1))]
          sendCtr := Function.update tr.sendCtr Q (Function.update (tr.sendCtr Q) E (n + 1))
          cand := cand' }
      | .error _ => { tr with cand := cand' } := by
  simp only [simStepKemFailSend, simNextKemCand]
  rcases (tr.st Q).send K (coinBytes r) with _ | ⟨out, _⟩ <;> (
    dsimp only; congr 1
    rcases tr.cand with _ | _
    · by_cases hS : (CryptoGames.Ratchet.LibsignalSim.simEkSideIsA tr.e != (Q == .A)) = true
      · simp only [hS, ↓reduceIte]; rcases tr.c with _ | _ | _ <;> rcases tr.st Q <;> rfl
      · simp [hS]
    · rfl)

theorem stepKemFailSendAtomicC_eval_sim (q : ℕ) {Γ : List (Ty ASig)}
    (trE : Expr AOps Γ (kemTrackT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (rqE : Expr AOps Γ BV512) (ρ : Env Γ)
    (tr : SimKemFailTrack C.F) (Q : Party) (rq : BitVec 512)
    (htr : trE.eval ρ = kemTrackAtomicEnc tr) (hqB : qBE.eval ρ = partyToBool Q)
    (hrq : rqE.eval ρ = rq)
    (hBOk : BOkTight (tr.st Q)) (hSentLen : tr.sentB.length ≤ q) :
    (stepKemFailSendAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) q trE qBE rqE).eval ρ =
      let tr' := simStepKemFailSend C.F K tr Q rq
      pure (kemTrackAtomicEnc tr', kemTrackAtomicEnc { tr with cand := tr'.cand }) := by
  simp only [stepKemFailSendAtomicC, Comp.eval, Expr.eval, htr, hqB, hrq, pure_bind]
  set p0 : (Ty.prod (kemTrackT ℓ Pt) (Ty.prod .bool BV512)).denote :=
    (kemTrackAtomicEnc tr, (partyToBool Q, rq))
  rw [nextKemCandAtomicC_eval _ _ _ (.cons p0 ρ) tr Q rq
    (by simp [p0, Expr.eval, Expr.v0])
    (by simp [p0, Expr.eval, Expr.v0])
    (by simp [p0, Expr.eval, Expr.v0]), pure_bind]
  set cand' := simNextKemCand (C := C) (K := K) tr Q rq
  set candBvD : (Ty.opt (Ty.prod (S := ASig) BV512 BV256)).denote :=
    cand'.map KemFailRedLoopAndCost.kemCandVecToBv
  set ρ0 := Env.cons candBvD (.cons p0 ρ)
  set pPost : (Ty.prod (kemTrackT ℓ Pt)
      (Ty.prod .bool (Ty.prod BV512 (.opt (.prod BV512 BV256))))).denote :=
    (kemTrackAtomicEnc tr, (partyToBool Q, (rq, candBvD)))
  have hTup : (Expr.pair (O := AOps) (.fst .v1)
      (.pair (.fst (.snd .v1)) (.pair (.snd (.snd .v1)) .v0))).eval ρ0 = pPost := by
    simp [ρ0, p0, pPost, Expr.eval, Expr.v0, Expr.v1]
  simp only [stepPostKemSendE, SimFig8State.eval_eLet]
  rw [hTup]
  have hv1Q : (pGet (trE_st (O' := AOps) (.fst .v0)) (.fst (.snd .v0))).eval (.cons pPost ρ0) =
      V1State.encodeRaw (tr.st Q).into_pb := by
    refine eval_pGet_party (t := B 32) _ _ _ (fun P => V1State.encodeRaw (tr.st P).into_pb) Q ?_ ?_
    · simp [trE_st, pPost, kemTrackAtomicEnc, Expr.eval, Expr.v0]
    · simp [pPost, Expr.eval, Expr.v0]
  have hOptEval : (Expr.snd (sOpSpqr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) .spqrBraidSend
      (.pair (pGet (trE_st (.fst .v0)) (.fst (.snd .v0))) (.fst (.snd (.snd .v0)))))).eval
      (.cons pPost ρ0) =
      (_root_.ReductionDsl.spqrBraidSendEval (ℓ := ℓ) (Pt := Pt) C.F K
        (V1State.encodeRaw (tr.st Q).into_pb) rq).2 := by
    simp only [Expr.eval, SimFig8State.eval_sOpSpqr, _root_.ReductionDsl.AtomicSpqrKemOp.eval]
    rw [hv1Q]; simp [pPost, Expr.eval, Expr.v0]
  have hCaseOpt {Γ' : List (Ty ASig)} {α β : Ty ASig} (e : Expr AOps Γ' (.opt α))
      (nB : Expr AOps Γ' β) (sB : Expr AOps (α :: Γ') β) (ρ' : Env Γ') :
      (Expr.caseOpt e nB sB).eval ρ' =
        match e.eval ρ' with | none => nB.eval ρ' | some x => sB.eval (.cons x ρ') := by
    simp only [Expr.eval]; cases e.eval ρ' <;> rfl
  rw [hCaseOpt, hOptEval, spqrBraidSendEval_of_bOkTight (tr.st Q) hBOk rq,
    simStepKemFailSend_eq (C := C) (K := K) tr Q rq]
  dsimp only
  rcases hSend : (tr.st Q).send K (coinBytes rq) with ⟨err⟩ | ⟨out, tape'⟩
  · cases err <;>
      simp [trMk, trE_e, trE_c, trE_st, trE_sentB, trE_sendCtr, pPost, candBvD, cand',
        kemTrackAtomicEnc, Expr.eval, Expr.v0]
  · dsimp only
    set sOutD : (Ty.prod (B (ℓ := ℓ) (Pt := Pt) 32)
        (Ty.prod U64 (Ty.prod (.opt (.prod U64 BV256)) (B (ℓ := ℓ) (Pt := Pt) 64)))).denote :=
      (V1State.encodeRaw out.state.into_pb, (out.msg.epoch,
        (out.key.map (fun es => (es.epoch, CryptoGames.HKDF.bytesToKey32 es.secret)),
          _root_.ReductionDsl.spqrMsgPayloadSuffix out.msg)))
    set ρS := Env.cons sOutD (.cons pPost ρ0)
    have hv1Q1 : (pGet (trE_st (O' := AOps) (.fst .v1)) (.fst (.snd .v1))).eval ρS =
        V1State.encodeRaw (tr.st Q).into_pb := by
      refine eval_pGet_party (t := B 32) _ _ _ (fun P => V1State.encodeRaw (tr.st P).into_pb) Q ?_ ?_
      · simp [trE_st, ρS, pPost, kemTrackAtomicEnc, Expr.eval, Expr.v1]
      · simp [ρS, pPost, Expr.eval, Expr.v1]
    have hCtrQ : (pGet (trE_sendCtr (O' := AOps) (.fst .v1)) (.fst (.snd .v1))).eval ρS =
        tr.sendCtr Q := by
      refine eval_pGet_party (trE_sendCtr (O' := AOps) (.fst .v1)) _ _ tr.sendCtr Q ?_ ?_
      · simp [trE_sendCtr, ρS, pPost, kemTrackAtomicEnc, Expr.eval, Expr.v1]
      · simp [ρS, pPost, Expr.eval, Expr.v1]
    have hC' : (nextKemCoinsAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) (trE_c (.fst .v1))
        (pGet (trE_st (.fst .v1)) (.fst (.snd .v1))) (.fst (.snd (.snd .v1)))).eval ρS =
        KemFailRedInit.kemCoinsAtomicEnc
          (CryptoGames.Ratchet.LibsignalSim.simNextKemCoins C.F tr.c (tr.st Q) (coinBytes rq)) := by
      refine nextKemCoinsAtomicE_eval _ _ _ ρS tr.c (tr.st Q) rq ?_ hv1Q1 ?_
      · simp [trE_c, ρS, pPost, kemTrackAtomicEnc, Expr.eval, Expr.v1]
      · simp [ρS, pPost, Expr.eval, Expr.v1]
    have hSt' : (pSet (trE_st (O' := AOps) (.fst .v1)) (.fst (.snd .v1)) (.fst .v0)).eval ρS =
        (V1State.encodeRaw (Function.update tr.st Q out.state .A).into_pb,
         V1State.encodeRaw (Function.update tr.st Q out.state .B).into_pb) := by
      have hSet0 : (pSet (trE_st (O' := AOps) (.fst .v1)) (.fst (.snd .v1)) (.fst .v0)).eval ρS =
          (Function.update (fun P => V1State.encodeRaw (tr.st P).into_pb) Q
             (V1State.encodeRaw out.state.into_pb) .A,
           Function.update (fun P => V1State.encodeRaw (tr.st P).into_pb) Q
             (V1State.encodeRaw out.state.into_pb) .B) := by
        refine eval_pSet_party (t := B 32) _ _ _ ρS (fun P => V1State.encodeRaw (tr.st P).into_pb) Q
          (V1State.encodeRaw out.state.into_pb) ?_ ?_ ?_
        · simp [trE_st, ρS, pPost, kemTrackAtomicEnc, Expr.eval, Expr.v1]
        · simp [ρS, pPost, Expr.eval, Expr.v1]
        · simp [ρS, sOutD, Expr.eval, Expr.v0]
      rw [hSet0]; cases Q <;> simp [Function.update]
    simp only [trMk, Expr.eval, hC', hSt', hCtrQ, SimFig8State.eval_sOpPure,
      _root_.ReductionDsl.AtomicPureOp.eval]
    simp only [pSet, Expr.eval, hCtrQ, SimFig8State.eval_sOpPure,
      _root_.ReductionDsl.AtomicPureOp.eval]
    have hTake : (List.map (fun x => ((x.1.epoch, _root_.ReductionDsl.spqrMsgPayloadSuffix x.1), x.2))
        tr.sentB ++ [((out.msg.epoch, _root_.ReductionDsl.spqrMsgPayloadSuffix out.msg),
          BitVec.ofNat 32 (tr.sendCtr Q (out.msg.epoch.toNat - 1) + 1))]).take (q + 1) =
        List.map (fun x => ((x.1.epoch, _root_.ReductionDsl.spqrMsgPayloadSuffix x.1), x.2))
          (tr.sentB ++ [(out.msg, BitVec.ofNat 32 (tr.sendCtr Q (out.msg.epoch.toNat - 1) + 1))]) := by
      rw [List.take_of_length_le (by simp; omega), List.map_append]; rfl
    cases Q <;> (
      simp [ρS, sOutD, pPost, candBvD, cand', trE_e, trE_c, trE_st, trE_sentB, trE_sendCtr,
        partyToBool, kemTrackAtomicEnc, Expr.eval, Expr.v0, Expr.v1, hTake, Function.update]
      ext j; by_cases hj : j = out.msg.epoch.toNat - 1 <;> simp [hj, Function.update])

theorem stepKemFailSendAtomicC_eval (q : ℕ) {Γ : List (Ty ASig)}
    (trE : Expr AOps Γ (kemTrackT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (rqE : Expr AOps Γ BV512) (ρ : Env Γ)
    (tr : KemFailTrackState C.F) (Q : Party) (rq : BitVec 512)
    (htr : trE.eval ρ = kemTrackAtomicEnc (kemTrackEnc tr)) (hqB : qBE.eval ρ = partyToBool Q)
    (hrq : rqE.eval ρ = rq)
    (hBOk : BOkTight (tr.st Q)) (hSentLen : tr.sentB.length ≤ q) :
    (stepKemFailSendAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) q trE qBE rqE).eval ρ =
      let tr' := stepKemFailSend C.F K tr Q rq
      pure (kemTrackAtomicEnc (kemTrackEnc tr'),
            kemTrackAtomicEnc (kemTrackEnc { tr with cand := tr'.cand })) := by
  have hBOk' : BOkTight ((kemTrackEnc tr).st Q) := by simpa [kemTrackEnc] using hBOk
  have hSentLen' : (kemTrackEnc tr).sentB.length ≤ q := by simpa [kemTrackEnc] using hSentLen
  rw [stepKemFailSendAtomicC_eval_sim q trE qBE rqE ρ (kemTrackEnc tr) Q rq htr hqB hrq hBOk' hSentLen']
  simp only [CryptoGames.Ratchet.LibsignalSim.simStepKemFailSend_kemTrackEnc]
  rfl

end EvalProofs

end Computational.Proofs.Game.PromotedCostedReds.KemFailRedSendCorrSub

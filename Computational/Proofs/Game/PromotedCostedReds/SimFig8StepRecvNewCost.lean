/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SimFig8State
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8Crypto
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8SanOracle
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8SanCoupling

/-!
# Concrete `Comp` Programs and Cost Bounds for `simFig8` New-Epoch Receive

Defines the atomic `ReductionDsl` programs for the new-chain receive branch (`recvNewOfFwdC`),
outer `semRecvHookS` dispatcher (`recvHookOfBranchesC`), and deliver/inject arm wrappers
(`recvArmC`), together with static query, cost, and description-bit bounds.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvNewCost

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Ops Expr Comp Iface GameCodec CostedReduction bits
  unifSamplers liftRen
  AtomicSort AtomicPureOp atomicSig atomicSessionOps fig8SmIface
  PB B PK PtT PlainT U32 U64 BV256 BV512 GhostStT
  fig8StT fig8StV fig8CtT fig8CtV fig8CtOfV lpubT lpubV lctT lctV
  partyToBool boolToParty recvResultT recvResultEnc recvResultDec
  smQT smRT smQenc smRdec e2eSessionCodec)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey GhostState)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (Bytes paramsV1)
open CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32
  ratchetKeyAdmissible)
open CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C SimState SimCStateBounded simParseRecvC
  inReceiveOnlyEpoch)
open CryptoGames.Ratchet.LibsignalSimC (LibsignalToModularSchemeSimState)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoGames.SM (RecvResult partyEnc orE boolEq isSomeE otherE senderOfE pGet)
open Computational.Proofs.Game.PromotedCostedReds.SanOracleCore
  (semFwdEvictHookS semFwdHookS semRecvHookS)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8State
  (eLet cost_eLet eMapOpt cost_eMapOpt descBits_eMapOpt sOpPure cost_sOpPure descBits_sOpPure
   scBase scSetBase cost_scSetBase scSetBase_descBits_le
   ssMir ssPq ssHonest ssChains ssAmb ssStopped ssSetAmb cost_ssSetAmb ssSetAmb_descBits_le
   mWin mEpoch mSafeInjE cost_mSafeInjE mSafeInjE_descBits_le
   mInTransitE cost_mInTransitE mInTransitE_descBits_le
   mInWinE cost_mInWinE mInWinE_descBits_le
   findChainIdxE cost_findChainIdxE findChainIdxE_descBits_le
   anyChainKeyNoneE cost_anyChainKeyNoneE anyChainKeyNoneE_descBits_le
   atomicTyDescBits_fig8CtT rename_descBits_eq bits_zero bits_eq_of_bounds)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8Crypto
  (parseOutT parseOutV parseRecvAtomicC parseRecvAtomicC_cost parseRecvAtomicC_descBits_le
   lctSaltEqOfLctAtomicE lctSaltEqOfLctAtomicE_cost lctSaltEqOfLctAtomicE_descBits_le
   injOKAtomicE injOKAtomicE_cost injOKAtomicE_descBits_le
   isZeroPtOptAtomicE isZeroPtOptAtomicE_cost isZeroPtOptAtomicE_descBits_le)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanCoupling (SanSnapExtra)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost
  (simMirT simBaseT simFullT simFullEnc simFullDec fig8IdSemHook)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost
  (varIdx atomicSortDescBits atomicTyDescBits atomicPureOpDescBits
   atomicSessionOpDescBits atomicExprDescBits atomicCompDescBits)

section Defs

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (K : MlKem)
  (Dh : DHFun (BitVec 256) Pt)
  (encPt : Pt → List (BitVec 8))
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (lam : Pt)

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

/-! ## Input and output types -/

/-- Encoded `(Option (RecvResult (Plain ℓ)) × LibsignalToModularSchemeSimState Bytes Pt ℓ)`. -/
@[reducible] def recvOutT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (.opt (recvResultT (ℓ := ℓ) (Pt := Pt))) (simFullT ℓ Pt)

/-- Input tuple `(sC, (qB, (w, (isDel, (ci?, (pk, (pq', (honestC, c'))))))))` to `semFwdHookS`. -/
@[reducible] def fwdHookInpT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (simFullT ℓ Pt) (.prod .bool (.prod (B 32) (.prod .bool (.prod (.opt .nat)
    (.prod PK (.prod (B 32) (.prod (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt)))
      (fig8CtT (ℓ := ℓ) (Pt := Pt)))))))))

/-- Input tuple `(sC, (qB, (w, (isDel, (parsed, (honestC, ci))))))` to same-chain branch. -/
@[reducible] def recvSameInpT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (simFullT ℓ Pt) (.prod .bool (.prod (B 32) (.prod .bool
    (.prod (parseOutT ℓ Pt) (.prod (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))) .nat)))))

/-- Input tuple `(sC, (qB, (w, (isDel, (parsed, honestC)))))` to new-chain branch. -/
@[reducible] def recvNewInpT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (simFullT ℓ Pt) (.prod .bool (.prod (B 32) (.prod .bool
    (.prod (parseOutT ℓ Pt) (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt)))))))

/-- Input tuple `(sC, (qB, (w, isDel)))` to `semRecvHookS`. -/
@[reducible] def recvHookInpT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (simFullT ℓ Pt) (.prod .bool (.prod (B 32) .bool))

/-- Deliver / Inject query payload `(qB, w)`. -/
@[reducible] def smRecvArgT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod .bool (B 32)

/-! ## Pure helper expressions -/

@[reducible] def wkTop1Comp {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {a t : Ty S} (c : Comp O I [a] t) : Comp O I (a :: Γ) t :=
  Comp.renameM
    (fun ⦃_⦄ v => match v with
      | .zero => .zero
      | .succ w => nomatch w) c

def callSub1C {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {a t : Ty S}
    (c : Comp O I [a] t) (argE : Expr O Γ a) : Comp O I Γ t :=
  .bind (.ret argE) (wkTop1Comp c)

def rejOutE {O' : Ops ASig} {Γ : List (Ty ASig)}
    (sCE : Expr O' Γ (simFullT ℓ Pt)) : Expr O' Γ (recvOutT ℓ Pt) :=
  .pair (.some (.inl .unit)) sCE

def noneOutE {O' : Ops ASig} {Γ : List (Ty ASig)}
    (sCE : Expr O' Γ (simFullT ℓ Pt)) : Expr O' Γ (recvOutT ℓ Pt) :=
  .pair .none sCE

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem rejOutE_fst_eq {O' : Ops ASig} {Γ : List (Ty ASig)}
    (sCE : Expr O' Γ (simFullT ℓ Pt)) (ρ : Env Γ) :
    ((rejOutE sCE).eval ρ).1 =
      (some (.rejected : RecvResult (Plain ℓ))).map recvResultEnc := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem fig8Ct_pair_eval {O' : Ops ASig} {Γ : List (Ty ASig)}
    (tE : Expr O' Γ .nat) (tOptE : Expr O' Γ (.opt PtT))
    (lctE : Expr O' Γ (lctT (ℓ := ℓ) (Pt := Pt))) (ρ : Env Γ)
    (t : ℕ) (T? : Option Pt) (lct : ℕ × LibsignalCiphertextWithSalt32)
    (ht : tE.eval ρ = t) (hT : tOptE.eval ρ = T?) (hl : lctE.eval ρ = lctV lct) :
    (Expr.pair (Expr.pair tE tOptE) lctE).eval ρ = fig8CtV ((t, T?), lct) := by
  rw [Expr.eval, Expr.eval, ht, hT, hl]
  rfl

def mkCAtomicE {Γ : List (Ty ASig)}
    (honestCE : Expr AOps Γ (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))))
    (tE : Expr AOps Γ .nat)
    (tOptE : Expr AOps Γ (.opt PtT))
    (lctE : Expr AOps Γ (lctT (ℓ := ℓ) (Pt := Pt))) :
    Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)) :=
  eLet (.pair honestCE (.pair (.pair tE tOptE) lctE))
    (.caseOpt (.fst .v0)
      (.snd .v0)
      (.ite
        (lctSaltEqOfLctAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam) .v0 (.snd (.snd .v1)))
        .v0
        (.snd .v1)))

def recvNewEvictedE {O' : Ops ASig} {Γ : List (Ty ASig)}
    (honestCE : Expr O' Γ (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))))
    (ep1E : Expr O' Γ .nat) : Expr O' Γ .bool :=
  eLet (.pair honestCE ep1E)
    (.caseOpt (.fst .v0)
      (.bool false)
      (.not (.eqN (.fst (.fst .v0)) (.snd .v1))))

def recvNewSaltEqE {Γ : List (Ty ASig)}
    (honestCE : Expr AOps Γ (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))))
    (lctE : Expr AOps Γ (lctT (ℓ := ℓ) (Pt := Pt))) : Expr AOps Γ .bool :=
  eLet (.pair honestCE lctE)
    (.caseOpt (.fst .v0)
      (.bool false)
      (lctSaltEqOfLctAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) .v0 (.snd .v1)))

def recvNewSCAmbE {O' : Ops ASig} {Γ : List (Ty ASig)}
    (sCE : Expr O' Γ (simFullT ℓ Pt)) (qBE : Expr O' Γ .bool) :
    Expr O' Γ (simFullT ℓ Pt) :=
  eLet (.pair sCE qBE)
    (let s0 : Expr O' _ (simFullT ℓ Pt) := .fst .v0
     let q0 : Expr O' _ .bool := .snd .v0
     let b0 : Expr O' _ (simBaseT ℓ Pt) := scBase s0
     let ambE : Expr O' _ .bool :=
       orE (mInWinE (ssMir b0) q0)
         (.and (.not q0) (anyChainKeyNoneE (pGet (ssChains b0) q0)))
     .ite ambE
       (scSetBase s0 (ssSetAmb b0 (.add (ssAmb b0) (.nat 1))))
       s0)

def recvNewRangeBadE {O' : Ops ASig} {Γ : List (Ty ASig)}
    (sCE : Expr O' Γ (simFullT ℓ Pt)) (qBE : Expr O' Γ .bool)
    (iE : Expr O' Γ .nat) : Expr O' Γ .bool :=
  orE (orE (mInWinE (ssMir (scBase sCE)) qBE) (.lt (.nat 25000) (.sub iE (.nat 1))))
    (.not (.lt iE (.nat (2 ^ 32))))

def recvRefuseE (Lq : ℕ) {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (wE : Expr AOps Γ (B (ℓ := ℓ) (Pt := Pt) 32)) (isDelE : Expr AOps Γ .bool) :
    Expr AOps Γ .bool :=
  eLet (.pair sCE (.pair qBE (.pair wE isDelE)))
    (let v0_outer : Expr AOps (recvHookInpT ℓ Pt :: Γ) (recvHookInpT ℓ Pt) := .v0
     let s0 := Expr.fst v0_outer
     let q0 := Expr.fst (.snd v0_outer)
     let w0 := Expr.fst (.snd (.snd v0_outer))
     let b0 := scBase s0
     let m0 := ssMir b0
     eLet (isSomeE (mInTransitE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
       (encT := encT) (decT := decT) (lam := lam) Lq m0 (otherE q0) w0))
       (let inTr : Expr AOps (.bool :: recvHookInpT ℓ Pt :: Γ) .bool := .v0
        let v1_outer : Expr AOps (.bool :: recvHookInpT ℓ Pt :: Γ) (recvHookInpT ℓ Pt) := .v1
        let s1 := Expr.fst v1_outer
        let w1 := Expr.fst (.snd (.snd v1_outer))
        let d1 := Expr.snd (.snd (.snd v1_outer))
        let b1 := scBase s1
        let m1 := ssMir b1
        orE
          (orE
            (orE (ssStopped b1) (mWin m1))
            (.and d1 (.not inTr)))
          (.and (.not d1)
            (orE
              (orE inTr (.not (mSafeInjE m1)))
              (.not (injOKAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                (encT := encT) (decT := decT) (lam := lam) w1))))))

def honestLookupE (Lq : ℕ) {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (wE : Expr AOps Γ (B (ℓ := ℓ) (Pt := Pt) 32)) :
    Expr AOps Γ (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))) :=
  eLet (.pair sCE (.pair qBE wE))
    (eMapOpt
      (.findB Lq (ssHonest (scBase (.fst .v0)))
        (.and
          (sOpPure (.bytesEq 32 32) (.pair (.fst .v0) (.snd (.snd .v1))))
          (boolEq (senderOfE (.fst (.fst (.snd .v0)))) (otherE (.fst (.snd .v1))))))
      (.snd .v0))

/-! ## Concrete `Comp` programs -/

/-- New-chain (`findIdx? = none`) receive branch in `Comp`, calling `fwdHookC` at most once. -/
def recvNewOfFwdC
    (fwdHookC : Comp AOps (fig8SmIface ℓ Pt) [fwdHookInpT ℓ Pt] (recvOutT ℓ Pt)) :
    Comp AOps (fig8SmIface ℓ Pt) [recvNewInpT ℓ Pt] (recvOutT ℓ Pt) :=
  let inp0 : Expr AOps [recvNewInpT ℓ Pt] (recvNewInpT ℓ Pt) := .v0
  let sC0 := Expr.fst inp0
  let qB0 := Expr.fst (.snd inp0)
  let parsed0 := Expr.fst (.snd (.snd (.snd (.snd inp0))))
  let honestC0 := Expr.snd (.snd (.snd (.snd (.snd inp0))))
  let tOpt0 := Expr.fst (.snd (.snd (.snd parsed0)))
  let lct0 := Expr.snd (.snd (.snd (.snd parsed0)))
  let ep1_0 := Expr.add (pGet (mEpoch (ssMir (scBase sC0))) qB0) (.nat 1)
  let earlyRej0 :=
    orE
      (.and (recvNewEvictedE honestC0 ep1_0)
        (recvNewSaltEqE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam) honestC0 lct0))
      (isZeroPtOptAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) tOpt0)
  .ite earlyRej0
    (.ret (rejOutE sC0))
    (.bind (.ret (recvNewSCAmbE sC0 qB0))
      (let sCAmb1 : Expr AOps [simFullT ℓ Pt, recvNewInpT ℓ Pt] (simFullT ℓ Pt) := .v0
       let inp1 : Expr AOps [simFullT ℓ Pt, recvNewInpT ℓ Pt] (recvNewInpT ℓ Pt) := .v1
       let sC1 := Expr.fst inp1
       let qB1 := Expr.fst (.snd inp1)
       let parsed1 := Expr.fst (.snd (.snd (.snd (.snd inp1))))
       let i1 := Expr.fst (.snd parsed1)
       let tOpt1 := Expr.fst (.snd (.snd (.snd parsed1)))
       .ite (recvNewRangeBadE sC1 qB1 i1)
         (.ret (rejOutE sCAmb1))
         (.caseOpt tOpt1
           (.ret (rejOutE sCAmb1))
           (let t0_2 : Expr AOps [PtT, simFullT ℓ Pt, recvNewInpT ℓ Pt] PtT := .v0
            let sCAmb2 : Expr AOps [PtT, simFullT ℓ Pt, recvNewInpT ℓ Pt] (simFullT ℓ Pt) := .v1
            let inp2 : Expr AOps [PtT, simFullT ℓ Pt, recvNewInpT ℓ Pt] (recvNewInpT ℓ Pt) := .v2
            let sC2 := Expr.fst inp2
            let qB2 := Expr.fst (.snd inp2)
            let w2 := Expr.fst (.snd (.snd inp2))
            let isDel2 := Expr.fst (.snd (.snd (.snd inp2)))
            let parsed2 := Expr.fst (.snd (.snd (.snd (.snd inp2))))
            let honestC2 := Expr.snd (.snd (.snd (.snd (.snd inp2))))
            let pq'2 := Expr.fst parsed2
            let pk2 := Expr.fst (.snd (.snd parsed2))
            let lct2 := Expr.snd (.snd (.snd (.snd parsed2)))
            let ep1_2 := Expr.add (pGet (mEpoch (ssMir (scBase sC2))) qB2) (.nat 1)
            let evicted2 := recvNewEvictedE honestC2 ep1_2
            let evictProbeRej2 :=
              Expr.and evicted2 (.and isDel2 (.not (mSafeInjE (ssMir (scBase sCAmb2)))))
            let honestArg2 : Expr AOps _ (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))) :=
              .ite evicted2 .none honestC2
            let c'Arg2 : Expr AOps _ (fig8CtT (ℓ := ℓ) (Pt := Pt)) :=
              .ite evicted2
                (.pair (.pair ep1_2 (.some t0_2)) lct2)
                (mkCAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                  (encT := encT) (decT := decT) (lam := lam)
                  honestC2 ep1_2 (.some t0_2) lct2)
            let fwdInp2 : Expr AOps _ (fwdHookInpT ℓ Pt) :=
              .pair sCAmb2 (.pair qB2 (.pair w2 (.pair isDel2 (.pair .none
                (.pair pk2 (.pair pq'2 (.pair honestArg2 c'Arg2)))))))
            .ite evictProbeRej2
              (.ret (rejOutE sCAmb2))
              (callSub1C fwdHookC fwdInp2)))))

/-- Full `semRecvHookS` in `Comp`, parameterized by `sameBranchC` and `newBranchC`. -/
def recvHookOfBranchesC (idA idB : IdentityKey) (Lq : ℕ)
    (sameBranchC : Comp AOps (fig8SmIface ℓ Pt) [recvSameInpT ℓ Pt] (recvOutT ℓ Pt))
    (newBranchC : Comp AOps (fig8SmIface ℓ Pt) [recvNewInpT ℓ Pt] (recvOutT ℓ Pt)) :
    Comp AOps (fig8SmIface ℓ Pt) [recvHookInpT ℓ Pt] (recvOutT ℓ Pt) :=
  let inp0 : Expr AOps [recvHookInpT ℓ Pt] (recvHookInpT ℓ Pt) := .v0
  let sC0 := Expr.fst inp0
  let qB0 := Expr.fst (.snd inp0)
  let w0 := Expr.fst (.snd (.snd inp0))
  let isDel0 := Expr.snd (.snd (.snd inp0))
  .ite
    (recvRefuseE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) Lq sC0 qB0 w0 isDel0)
    (.ret (noneOutE sC0))
    (.bind
      (parseRecvAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam)
        (fig8SmIface ℓ Pt) idA idB (2 ^ 32) qB0 (pGet (ssPq (scBase sC0)) qB0) w0)
      (.caseOpt .v0
        (.ret (rejOutE (.fst .v1)))
        (let inp1 : Expr AOps
              [parseOutT ℓ Pt, .opt (parseOutT ℓ Pt), recvHookInpT ℓ Pt]
              (recvHookInpT ℓ Pt) := .v2
         let sC1 := Expr.fst inp1
         let qB1 := Expr.fst (.snd inp1)
         let w1 := Expr.fst (.snd (.snd inp1))
         .bind
           (.ret (honestLookupE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
             (encT := encT) (decT := decT) (lam := lam) Lq sC1 qB1 w1))
           (let honest2 : Expr AOps
                [.opt (fig8CtT (ℓ := ℓ) (Pt := Pt)), parseOutT ℓ Pt,
                 .opt (parseOutT ℓ Pt), recvHookInpT ℓ Pt]
                (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))) := .v0
            let parsed2 : Expr AOps
                [.opt (fig8CtT (ℓ := ℓ) (Pt := Pt)), parseOutT ℓ Pt,
                 .opt (parseOutT ℓ Pt), recvHookInpT ℓ Pt]
                (parseOutT ℓ Pt) := .v1
            let inp2 : Expr AOps
                [.opt (fig8CtT (ℓ := ℓ) (Pt := Pt)), parseOutT ℓ Pt,
                 .opt (parseOutT ℓ Pt), recvHookInpT ℓ Pt]
                (recvHookInpT ℓ Pt) := .v3
            let sC2 := Expr.fst inp2
            let qB2 := Expr.fst (.snd inp2)
            let w2 := Expr.fst (.snd (.snd inp2))
            let isDel2 := Expr.snd (.snd (.snd inp2))
            let pk2 := Expr.fst (.snd (.snd parsed2))
            .caseOpt
              (findChainIdxE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                (encT := encT) (decT := decT) (lam := lam)
                (pGet (ssChains (scBase sC2)) qB2) pk2)
              (callSub1C newBranchC
                (.pair sC2 (.pair qB2 (.pair w2 (.pair isDel2 (.pair parsed2 honest2))))))
              (let ci3 : Expr AOps
                    [.nat, .opt (fig8CtT (ℓ := ℓ) (Pt := Pt)), parseOutT ℓ Pt,
                     .opt (parseOutT ℓ Pt), recvHookInpT ℓ Pt]
                    .nat := .v0
               let honest3 : Expr AOps
                    [.nat, .opt (fig8CtT (ℓ := ℓ) (Pt := Pt)), parseOutT ℓ Pt,
                     .opt (parseOutT ℓ Pt), recvHookInpT ℓ Pt]
                    (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))) := .v1
               let parsed3 : Expr AOps
                    [.nat, .opt (fig8CtT (ℓ := ℓ) (Pt := Pt)), parseOutT ℓ Pt,
                     .opt (parseOutT ℓ Pt), recvHookInpT ℓ Pt]
                    (parseOutT ℓ Pt) := .v2
               let inp3 : Expr AOps
                    [.nat, .opt (fig8CtT (ℓ := ℓ) (Pt := Pt)), parseOutT ℓ Pt,
                     .opt (parseOutT ℓ Pt), recvHookInpT ℓ Pt]
                    (recvHookInpT ℓ Pt) := .v4
               let sC3 := Expr.fst inp3
               let qB3 := Expr.fst (.snd inp3)
               let w3 := Expr.fst (.snd (.snd inp3))
               let isDel3 := Expr.snd (.snd (.snd inp3))
               callSub1C sameBranchC
                 (.pair sC3 (.pair qB3 (.pair w3 (.pair isDel3
                   (.pair parsed3 (.pair honest3 ci3)))))))))))

/-- Two-variable arm `[simFullT ℓ Pt, smRecvArgT ℓ Pt] → recvOutT ℓ Pt` for Deliver (`isDel = true`)
or Inject (`isDel = false`). -/
def recvArmC (isDel : Bool)
    (recvHookC : Comp AOps (fig8SmIface ℓ Pt) [recvHookInpT ℓ Pt] (recvOutT ℓ Pt)) :
    Comp AOps (fig8SmIface ℓ Pt) [simFullT ℓ Pt, smRecvArgT ℓ Pt] (recvOutT ℓ Pt) :=
  callSub1C recvHookC
    (.pair .v0 (.pair (.fst .v1) (.pair (.snd .v1) (.bool isDel))))

/-- Semantic new-epoch (`findIdx? = none`) sub-branch of `semRecvHookS` with `fig8IdSemHook none`
(projecting away the `Unit` extra state). -/
def semRecvNewBranch
    (idA idB : IdentityKey) (qep B T Kc : ℕ)
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ)
    (Q : Party) (w : Bytes) (isDel : Bool)
    (pq' : Bytes) (i : ℕ) (pk : PublicKey) (T? : Option Pt)
    (lct : ℕ × LibsignalCiphertextWithSalt32)
    (honestC : Option (Fig8C Pt)) :
    OracleComp
      (unifSpec + CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
        (BitVec 256) (Fig8C Pt))
      (Option (RecvResult (Plain ℓ)) × LibsignalToModularSchemeSimState Bytes Pt ℓ) :=
  let P := paramsV1 C K idA idB
  let sh := fig8IdSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ) none
  let mkC (t : ℕ) (To : Option Pt) : Fig8C Pt :=
    match honestC with
    | some c => if c.2.2.2 = lct.2.2 then c else ((t, To), lct)
    | none => ((t, To), lct)
  let evicted := (honestC.map fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true
  let saltEq := (honestC.map fun c => decide (c.2.2.2 = lct.2.2)) == some true
  let amb := inReceiveOnlyEpoch sC.base.mir Q ||
    (Q == Party.A && (sC.base.chains Q).any (·.key.isNone))
  let sCAmb : LibsignalToModularSchemeSimState Bytes Pt ℓ :=
    { sC with base := if amb then { sC.base with amb := sC.base.amb + 1 } else sC.base }
  Prod.map id Prod.fst <$>
    (if evicted && saltEq then
      pure (some .rejected, (sC, ()))
    else if T? == some 0 then
      pure (some .rejected, (sC, ()))
    else if inReceiveOnlyEpoch sC.base.mir Q || decide (25000 < i - 1) || decide (2 ^ 32 ≤ i) then
      pure (some .rejected, (sCAmb, ()))
    else
      match T? with
      | none => pure (some .rejected, (sCAmb, ()))
      | some T₀ =>
        if evicted then
          semFwdEvictHookS P Dh encPt encT lam T sh qep sCAmb () Q w isDel pk pq'
            ((sC.base.mir.epoch Q + 1, some T₀), lct)
        else
          semFwdHookS P Dh encPt encT lam T Kc sh qep B sCAmb () Q w isDel none pk pq'
            honestC (mkC (sC.base.mir.epoch Q + 1) (some T₀)))

/-! ## Query, cost, and `descBits` bounds -/

@[local simp] private theorem nb_c0 : bits 0 = 1 := bits_zero
@[local simp] private theorem nb_c1 : bits 1 = 1 :=
  bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
@[local simp] private theorem nb_c2 : bits 2 = 2 :=
  bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
@[local simp] private theorem nb_c3 : bits 3 = 2 :=
  bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
@[local simp] private theorem nb_c4 : bits 4 = 3 :=
  bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
@[local simp] private theorem nb_c32 : bits 32 = 6 :=
  bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
@[local simp] private theorem nb_p32 : bits ((32 : ℕ+) : ℕ) = 6 := nb_c32
@[local simp] private theorem nb_c25000 : bits 25000 = 15 :=
  bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
@[local simp] private theorem nb_c2pow32 : bits (2 ^ 32) = 33 :=
  bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)

private theorem liftRen_varIdx {S : Sig} {Γ₁ Γ₂ : List (Ty S)} {a : Ty S}
    {ξ : ∀ ⦃u⦄, Var Γ₁ u → Var Γ₂ u}
    (hξ : ∀ u (v : Var Γ₁ u), varIdx (ξ v) = varIdx v) :
    ∀ u (v : Var (a :: Γ₁) u), varIdx (liftRen ξ v) = varIdx v
  | _, .zero => rfl
  | _, .succ w => by simp [liftRen, varIdx, hξ _ w]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem comp_renameM_descBits_eq {O' : Ops ASig}
    {ι : Type} {T : OracleSpec ι} {I' : Iface ASig T}
    (opB : O'.Op → ℕ) (sB : I'.smp.Samp → ℕ) (qB : I'.Tag → ℕ)
    {Γ₁ : List (Ty ASig)} {t : Ty ASig} (c : Comp O' I' Γ₁ t) :
    ∀ {Γ₂ : List (Ty ASig)} (ξ : ∀ ⦃u⦄, Var Γ₁ u → Var Γ₂ u),
      (∀ u (v : Var Γ₁ u), varIdx (ξ v) = varIdx v) →
      atomicCompDescBits opB sB qB (Comp.renameM ξ c) =
        atomicCompDescBits opB sB qB c := by
  induction c with
  | ret e =>
    intro Γ₂ ξ hξ
    simp only [Comp.renameM, atomicCompDescBits, rename_descBits_eq opB _ _ hξ]
  | bind c k ihc ihk =>
    intro Γ₂ ξ hξ
    simp only [Comp.renameM, atomicCompDescBits, ihc ξ hξ, ihk (liftRen ξ) (liftRen_varIdx hξ)]
  | ite b c d ihc ihd =>
    intro Γ₂ ξ hξ
    simp only [Comp.renameM, atomicCompDescBits, rename_descBits_eq opB _ _ hξ, ihc ξ hξ, ihd ξ hξ]
  | caseOpt e n s ihn ihs =>
    intro Γ₂ ξ hξ
    simp only [Comp.renameM, atomicCompDescBits, rename_descBits_eq opB _ _ hξ,
      ihn ξ hξ, ihs (liftRen ξ) (liftRen_varIdx hξ)]
  | caseSum e l r ihl ihr =>
    intro Γ₂ ξ hξ
    simp only [Comp.renameM, atomicCompDescBits, rename_descBits_eq opB _ _ hξ,
      ihl (liftRen ξ) (liftRen_varIdx hξ), ihr (liftRen ξ) (liftRen_varIdx hξ)]
  | sample s e =>
    intro Γ₂ ξ hξ
    simp only [Comp.renameM, atomicCompDescBits, rename_descBits_eq opB _ _ hξ]
  | query g e =>
    intro Γ₂ ξ hξ
    simp only [Comp.renameM, atomicCompDescBits, rename_descBits_eq opB _ _ hξ]
  | iter n e body ihb =>
    intro Γ₂ ξ hξ
    simp only [Comp.renameM, atomicCompDescBits, rename_descBits_eq opB _ _ hξ,
      ihb (liftRen ξ) (liftRen_varIdx hξ)]
  | findM K l p ihp | anyM K l p ihp | mapM K l p ihp =>
    intro Γ₂ ξ hξ
    simp only [Comp.renameM, atomicCompDescBits, rename_descBits_eq opB _ _ hξ,
      ihp (liftRen ξ) (liftRen_varIdx hξ)]
  | consumeFirstM K l p mk ihp =>
    intro Γ₂ ξ hξ
    simp only [Comp.renameM, atomicCompDescBits, rename_descBits_eq opB _ _ hξ,
      rename_descBits_eq opB _ _ (liftRen_varIdx hξ), ihp (liftRen ξ) (liftRen_varIdx hξ)]
  | foldM K l z f ihf =>
    intro Γ₂ ξ hξ
    simp only [Comp.renameM, atomicCompDescBits, rename_descBits_eq opB _ _ hξ,
      ihf (liftRen (liftRen ξ)) (liftRen_varIdx (liftRen_varIdx hξ))]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem wkTop1Comp_descBits_eq {O' : Ops ASig}
    {ι : Type} {T : OracleSpec ι} {I' : Iface ASig T}
    (opB : O'.Op → ℕ) (sB : I'.smp.Samp → ℕ) (qB : I'.Tag → ℕ)
    {Γ : List (Ty ASig)} {a t : Ty ASig} (c : Comp O' I' [a] t) :
    atomicCompDescBits opB sB qB (wkTop1Comp (Γ := Γ) c) =
      atomicCompDescBits opB sB qB c :=
  comp_renameM_descBits_eq opB sB qB c _ fun _ v => by
    cases v with
    | zero => rfl
    | succ w => nomatch w

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem callSub1C_descBits_eq {O' : Ops ASig}
    {ι : Type} {T : OracleSpec ι} {I' : Iface ASig T}
    (opB : O'.Op → ℕ) (sB : I'.smp.Samp → ℕ) (qB : I'.Tag → ℕ)
    {Γ : List (Ty ASig)} {a t : Ty ASig}
    (c : Comp O' I' [a] t) (argE : Expr O' Γ a) :
    atomicCompDescBits opB sB qB (callSub1C c argE) =
      (atomicExprDescBits opB argE + 6) + atomicCompDescBits opB sB qB c + 6 := by
  simp only [callSub1C, atomicCompDescBits, wkTop1Comp_descBits_eq]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem rejOutE_cost {O' : Ops ASig} {Γ : List (Ty ASig)}
    (sCE : Expr O' Γ (simFullT ℓ Pt)) :
    (rejOutE sCE).cost ≤ sCE.cost + 5 := by
  simp only [rejOutE, Expr.cost]
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem rejOutE_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ) {Γ : List (Ty ASig)}
    (sCE : Expr O' Γ (simFullT ℓ Pt)) :
    atomicExprDescBits opB (rejOutE sCE) ≤ atomicExprDescBits opB sCE + 60 := by
  dsimp only [rejOutE, recvOutT, recvResultT, B, PlainT,
    atomicExprDescBits, atomicTyDescBits, atomicSortDescBits]
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem noneOutE_cost {O' : Ops ASig} {Γ : List (Ty ASig)}
    (sCE : Expr O' Γ (simFullT ℓ Pt)) :
    (noneOutE sCE).cost ≤ sCE.cost + 5 := by
  simp only [noneOutE, Expr.cost]
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem noneOutE_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ) {Γ : List (Ty ASig)}
    (sCE : Expr O' Γ (simFullT ℓ Pt)) :
    atomicExprDescBits opB (noneOutE sCE) ≤ atomicExprDescBits opB sCE + 60 := by
  dsimp only [noneOutE, recvOutT, recvResultT, B, PlainT,
    atomicExprDescBits, atomicTyDescBits, atomicSortDescBits]
  omega

omit [SampleableType Pt] in
private theorem mkCAtomicE_cost {Γ : List (Ty ASig)}
    (honestCE : Expr AOps Γ (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))))
    (tE : Expr AOps Γ .nat) (tOptE : Expr AOps Γ (.opt PtT))
    (lctE : Expr AOps Γ (lctT (ℓ := ℓ) (Pt := Pt))) :
    (mkCAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) honestCE tE tOptE lctE).cost ≤
      honestCE.cost + tE.cost + tOptE.cost + lctE.cost + 40 := by
  let Γ0 := Ty.prod (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))) (fig8CtT (ℓ := ℓ) (Pt := Pt)) :: Γ
  let Γ1 := fig8CtT (ℓ := ℓ) (Pt := Pt) :: Γ0
  have hs := lctSaltEqOfLctAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (.v0 : Expr AOps Γ1 _) (.snd (.snd (.v1 : Expr AOps Γ1 _)))
  dsimp only [Γ0, Γ1, Expr.v0, Expr.v1, Expr.cost] at hs
  simp only [mkCAtomicE, cost_eLet, Expr.v0, Expr.v1, Expr.cost]
  omega

omit [SampleableType Pt] in
private theorem mkCAtomicE_descBits_le {Γ : List (Ty ASig)}
    (honestCE : Expr AOps Γ (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))))
    (tE : Expr AOps Γ .nat) (tOptE : Expr AOps Γ (.opt PtT))
    (lctE : Expr AOps Γ (lctT (ℓ := ℓ) (Pt := Pt))) :
    atomicExprDescBits atomicSessionOpDescBits
      (mkCAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) honestCE tE tOptE lctE) ≤
      atomicExprDescBits atomicSessionOpDescBits honestCE +
      atomicExprDescBits atomicSessionOpDescBits tE +
      atomicExprDescBits atomicSessionOpDescBits tOptE +
      atomicExprDescBits atomicSessionOpDescBits lctE + 200 := by
  let Γ0 := Ty.prod (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))) (fig8CtT (ℓ := ℓ) (Pt := Pt)) :: Γ
  let Γ1 := fig8CtT (ℓ := ℓ) (Pt := Pt) :: Γ0
  have hs := lctSaltEqOfLctAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (.v0 : Expr AOps Γ1 _) (.snd (.snd (.v1 : Expr AOps Γ1 _)))
  dsimp only [Γ0, Γ1, Expr.v0, Expr.v1, atomicExprDescBits, varIdx] at hs
  dsimp only [mkCAtomicE, eLet, Expr.v0, Expr.v1, atomicExprDescBits, varIdx]
  simp only [Nat.reduceAdd, nb_c0, nb_c1] at hs ⊢
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem recvNewEvictedE_cost {O' : Ops ASig} {Γ : List (Ty ASig)}
    (honestCE : Expr O' Γ (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt)))) (ep1E : Expr O' Γ .nat) :
    (recvNewEvictedE honestCE ep1E).cost ≤ honestCE.cost + ep1E.cost + 20 := by
  simp only [recvNewEvictedE, cost_eLet, Expr.v0, Expr.v1, Expr.cost]
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem recvNewEvictedE_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ) {Γ : List (Ty ASig)}
    (honestCE : Expr O' Γ (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt)))) (ep1E : Expr O' Γ .nat) :
    atomicExprDescBits opB (recvNewEvictedE honestCE ep1E) ≤
      atomicExprDescBits opB honestCE + atomicExprDescBits opB ep1E + 100 := by
  dsimp only [recvNewEvictedE, eLet, Expr.v0, Expr.v1, atomicExprDescBits, varIdx]
  simp only [Nat.reduceAdd, nb_c0, nb_c1]
  omega

omit [SampleableType Pt] in
private theorem recvNewSaltEqE_cost {Γ : List (Ty ASig)}
    (honestCE : Expr AOps Γ (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))))
    (lctE : Expr AOps Γ (lctT (ℓ := ℓ) (Pt := Pt))) :
    (recvNewSaltEqE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) honestCE lctE).cost ≤
      honestCE.cost + lctE.cost + 30 := by
  let Γ0 := Ty.prod (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))) (lctT (ℓ := ℓ) (Pt := Pt)) :: Γ
  let Γ1 := fig8CtT (ℓ := ℓ) (Pt := Pt) :: Γ0
  have hs := lctSaltEqOfLctAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (.v0 : Expr AOps Γ1 _) (.snd (.v1 : Expr AOps Γ1 _))
  dsimp only [Γ0, Γ1, Expr.v0, Expr.v1, Expr.cost] at hs
  simp only [recvNewSaltEqE, cost_eLet, Expr.v0, Expr.v1, Expr.cost]
  omega

omit [SampleableType Pt] in
private theorem recvNewSaltEqE_descBits_le {Γ : List (Ty ASig)}
    (honestCE : Expr AOps Γ (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))))
    (lctE : Expr AOps Γ (lctT (ℓ := ℓ) (Pt := Pt))) :
    atomicExprDescBits atomicSessionOpDescBits
      (recvNewSaltEqE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) honestCE lctE) ≤
      atomicExprDescBits atomicSessionOpDescBits honestCE +
      atomicExprDescBits atomicSessionOpDescBits lctE + 150 := by
  let Γ0 := Ty.prod (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))) (lctT (ℓ := ℓ) (Pt := Pt)) :: Γ
  let Γ1 := fig8CtT (ℓ := ℓ) (Pt := Pt) :: Γ0
  have hs := lctSaltEqOfLctAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (.v0 : Expr AOps Γ1 _) (.snd (.v1 : Expr AOps Γ1 _))
  dsimp only [Γ0, Γ1, Expr.v0, Expr.v1, atomicExprDescBits, varIdx] at hs
  dsimp only [recvNewSaltEqE, eLet, Expr.v0, Expr.v1, atomicExprDescBits, varIdx]
  simp only [Nat.reduceAdd, nb_c0, nb_c1] at hs ⊢
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem recvNewSCAmbE_cost {O' : Ops ASig} {Γ : List (Ty ASig)}
    (sCE : Expr O' Γ (simFullT ℓ Pt)) (qBE : Expr O' Γ .bool) :
    (recvNewSCAmbE sCE qBE).cost ≤ sCE.cost + qBE.cost + 300 := by
  let Γ0 := Ty.prod (simFullT ℓ Pt) .bool :: Γ
  let s0 : Expr O' Γ0 (simFullT ℓ Pt) := .fst .v0
  let q0 : Expr O' Γ0 .bool := .snd .v0
  let b0 : Expr O' Γ0 (simBaseT ℓ Pt) := scBase s0
  have hw := cost_mInWinE (ssMir b0) q0
  have hc := cost_anyChainKeyNoneE (pGet (ssChains b0) q0)
  have ha := cost_ssSetAmb b0 (.add (ssAmb b0) (.nat 1))
  have hb := cost_scSetBase s0 (ssSetAmb b0 (.add (ssAmb b0) (.nat 1)))
  dsimp only [Γ0, s0, q0, b0, scBase, ssMir, ssChains, ssAmb, pGet, Expr.v0, Expr.cost]
    at hw hc ha hb
  simp only [recvNewSCAmbE, cost_eLet, scBase, ssMir, ssChains, ssAmb, pGet, orE,
    Expr.v0, Expr.cost, nb_c1] at hw hc ha hb ⊢
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem recvNewSCAmbE_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ) {Γ : List (Ty ASig)}
    (sCE : Expr O' Γ (simFullT ℓ Pt)) (qBE : Expr O' Γ .bool) :
    atomicExprDescBits opB (recvNewSCAmbE sCE qBE) ≤
      atomicExprDescBits opB sCE + atomicExprDescBits opB qBE + 1800 := by
  let Γ0 := Ty.prod (simFullT ℓ Pt) .bool :: Γ
  let s0 : Expr O' Γ0 (simFullT ℓ Pt) := .fst .v0
  let q0 : Expr O' Γ0 .bool := .snd .v0
  let b0 : Expr O' Γ0 (simBaseT ℓ Pt) := scBase s0
  have hw := mInWinE_descBits_le opB (ssMir b0) q0
  have hc := anyChainKeyNoneE_descBits_le opB (pGet (ssChains b0) q0)
  have ha := ssSetAmb_descBits_le opB b0 (.add (ssAmb b0) (.nat 1))
  have hb := scSetBase_descBits_le opB s0 (ssSetAmb b0 (.add (ssAmb b0) (.nat 1)))
  dsimp only [Γ0, s0, q0, b0, scBase, ssMir, ssChains, ssAmb, pGet, Expr.v0,
    atomicExprDescBits, varIdx] at hw hc ha hb
  dsimp only [recvNewSCAmbE, eLet, scBase, ssMir, ssChains, ssAmb, pGet, orE,
    Expr.v0, atomicExprDescBits, varIdx]
  simp only [nb_c0, nb_c1] at hw hc ha hb ⊢
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem recvNewRangeBadE_cost {O' : Ops ASig} {Γ : List (Ty ASig)}
    (sCE : Expr O' Γ (simFullT ℓ Pt)) (qBE : Expr O' Γ .bool) (iE : Expr O' Γ .nat) :
    (recvNewRangeBadE sCE qBE iE).cost ≤ sCE.cost + qBE.cost + 2 * iE.cost + 150 := by
  have hw := cost_mInWinE (ssMir (scBase sCE)) qBE
  simp only [recvNewRangeBadE, orE, ssMir, scBase, Expr.cost, nb_c1, nb_c25000, nb_c2pow32]
    at hw ⊢
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem recvNewRangeBadE_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ) {Γ : List (Ty ASig)}
    (sCE : Expr O' Γ (simFullT ℓ Pt)) (qBE : Expr O' Γ .bool) (iE : Expr O' Γ .nat) :
    atomicExprDescBits opB (recvNewRangeBadE sCE qBE iE) ≤
      atomicExprDescBits opB sCE + atomicExprDescBits opB qBE +
      2 * atomicExprDescBits opB iE + 800 := by
  have hw := mInWinE_descBits_le opB (ssMir (scBase sCE)) qBE
  dsimp only [recvNewRangeBadE, orE, ssMir, scBase, atomicExprDescBits] at hw ⊢
  simp only [nb_c1, nb_c25000, nb_c2pow32] at hw ⊢
  omega

theorem recvNewOfFwdC_queries
    (fwdHookC : Comp AOps (fig8SmIface ℓ Pt) [fwdHookInpT ℓ Pt] (recvOutT ℓ Pt))
    (w : (fig8SmIface ℓ Pt).Tag → ℕ)
    (ws : (fig8SmIface ℓ Pt).smp.Samp → ℕ) :
    (recvNewOfFwdC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) fwdHookC).queries w ws =
      fwdHookC.queries w ws := by
  simp [recvNewOfFwdC, callSub1C, wkTop1Comp, Comp.queries]

theorem recvNewOfFwdC_cost
    (fwdHookC : Comp AOps (fig8SmIface ℓ Pt) [fwdHookInpT ℓ Pt] (recvOutT ℓ Pt)) :
    (recvNewOfFwdC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) fwdHookC).cost ≤
      fwdHookC.cost + 10000 := by
  let inp0 : Expr AOps [recvNewInpT ℓ Pt] (recvNewInpT ℓ Pt) := .v0
  let sC0 := Expr.fst inp0; let qB0 := Expr.fst (.snd inp0)
  let parsed0 := Expr.fst (.snd (.snd (.snd (.snd inp0))))
  let honestC0 := Expr.snd (.snd (.snd (.snd (.snd inp0))))
  let tOpt0 := Expr.fst (.snd (.snd (.snd parsed0))); let lct0 := Expr.snd (.snd (.snd (.snd parsed0)))
  let ep1_0 := Expr.add (pGet (mEpoch (ssMir (scBase sC0))) qB0) (.nat 1)
  let sCAmb1 : Expr AOps [simFullT ℓ Pt, recvNewInpT ℓ Pt] (simFullT ℓ Pt) := .v0
  let inp1 : Expr AOps [simFullT ℓ Pt, recvNewInpT ℓ Pt] (recvNewInpT ℓ Pt) := .v1
  let sC1 := Expr.fst inp1; let qB1 := Expr.fst (.snd inp1)
  let parsed1 := Expr.fst (.snd (.snd (.snd (.snd inp1)))); let i1 := Expr.fst (.snd parsed1)
  let t0_2 : Expr AOps [PtT, simFullT ℓ Pt, recvNewInpT ℓ Pt] PtT := .v0
  let sCAmb2 : Expr AOps [PtT, simFullT ℓ Pt, recvNewInpT ℓ Pt] (simFullT ℓ Pt) := .v1
  let inp2 : Expr AOps [PtT, simFullT ℓ Pt, recvNewInpT ℓ Pt] (recvNewInpT ℓ Pt) := .v2
  let sC2 := Expr.fst inp2; let qB2 := Expr.fst (.snd inp2)
  let parsed2 := Expr.fst (.snd (.snd (.snd (.snd inp2))))
  let honestC2 := Expr.snd (.snd (.snd (.snd (.snd inp2))))
  let lct2 := Expr.snd (.snd (.snd (.snd parsed2)))
  let ep1_2 := Expr.add (pGet (mEpoch (ssMir (scBase sC2))) qB2) (.nat 1)
  have h1 := recvNewEvictedE_cost honestC0 ep1_0
  have h2 := recvNewSaltEqE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) honestC0 lct0
  have h3 := isZeroPtOptAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) tOpt0
  have h4 := rejOutE_cost sC0
  have h5 := recvNewSCAmbE_cost sC0 qB0
  have h6 := recvNewRangeBadE_cost sC1 qB1 i1
  have h7 := rejOutE_cost sCAmb1
  have h8 := recvNewEvictedE_cost honestC2 ep1_2
  have h9 := cost_mSafeInjE (ssMir (scBase sCAmb2))
  have h10 := mkCAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) honestC2 ep1_2 (.some t0_2) lct2
  have h11 := rejOutE_cost sCAmb2
  dsimp only [inp0, sC0, qB0, parsed0, honestC0, tOpt0, lct0, ep1_0,
    sCAmb1, inp1, sC1, qB1, parsed1, i1, t0_2, sCAmb2, inp2, sC2, qB2, parsed2, honestC2,
    lct2, ep1_2, recvNewOfFwdC, callSub1C, wkTop1Comp] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 ⊢
  simp only [Comp.cost, Comp.renameM_cost, orE, pGet, mEpoch, ssMir, scBase,
    Expr.v0, Expr.v1, Expr.v2, Expr.cost, nb_c1] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 ⊢
  omega

theorem recvNewOfFwdC_descBits_le
    (fwdHookC : Comp AOps (fig8SmIface ℓ Pt) [fwdHookInpT ℓ Pt] (recvOutT ℓ Pt))
    (sB : (fig8SmIface ℓ Pt).smp.Samp → ℕ)
    (qB : (fig8SmIface ℓ Pt).Tag → ℕ) :
    atomicCompDescBits atomicSessionOpDescBits sB qB
      (recvNewOfFwdC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) fwdHookC) ≤
      atomicCompDescBits atomicSessionOpDescBits sB qB fwdHookC + 25000 := by
  let inp0 : Expr AOps [recvNewInpT ℓ Pt] (recvNewInpT ℓ Pt) := .v0
  let sC0 := Expr.fst inp0; let qB0 := Expr.fst (.snd inp0)
  let parsed0 := Expr.fst (.snd (.snd (.snd (.snd inp0))))
  let honestC0 := Expr.snd (.snd (.snd (.snd (.snd inp0))))
  let tOpt0 := Expr.fst (.snd (.snd (.snd parsed0))); let lct0 := Expr.snd (.snd (.snd (.snd parsed0)))
  let ep1_0 := Expr.add (pGet (mEpoch (ssMir (scBase sC0))) qB0) (.nat 1)
  let sCAmb1 : Expr AOps [simFullT ℓ Pt, recvNewInpT ℓ Pt] (simFullT ℓ Pt) := .v0
  let inp1 : Expr AOps [simFullT ℓ Pt, recvNewInpT ℓ Pt] (recvNewInpT ℓ Pt) := .v1
  let sC1 := Expr.fst inp1; let qB1 := Expr.fst (.snd inp1)
  let parsed1 := Expr.fst (.snd (.snd (.snd (.snd inp1)))); let i1 := Expr.fst (.snd parsed1)
  let t0_2 : Expr AOps [PtT, simFullT ℓ Pt, recvNewInpT ℓ Pt] PtT := .v0
  let sCAmb2 : Expr AOps [PtT, simFullT ℓ Pt, recvNewInpT ℓ Pt] (simFullT ℓ Pt) := .v1
  let inp2 : Expr AOps [PtT, simFullT ℓ Pt, recvNewInpT ℓ Pt] (recvNewInpT ℓ Pt) := .v2
  let sC2 := Expr.fst inp2; let qB2 := Expr.fst (.snd inp2)
  let parsed2 := Expr.fst (.snd (.snd (.snd (.snd inp2))))
  let honestC2 := Expr.snd (.snd (.snd (.snd (.snd inp2))))
  let lct2 := Expr.snd (.snd (.snd (.snd parsed2)))
  let ep1_2 := Expr.add (pGet (mEpoch (ssMir (scBase sC2))) qB2) (.nat 1)
  have h1 := recvNewEvictedE_descBits_le atomicSessionOpDescBits honestC0 ep1_0
  have h2 := recvNewSaltEqE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) honestC0 lct0
  have h3 := isZeroPtOptAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) tOpt0
  have h4 := rejOutE_descBits_le atomicSessionOpDescBits sC0
  have h5 := recvNewSCAmbE_descBits_le atomicSessionOpDescBits sC0 qB0
  have h6 := recvNewRangeBadE_descBits_le atomicSessionOpDescBits sC1 qB1 i1
  have h7 := rejOutE_descBits_le atomicSessionOpDescBits sCAmb1
  have h8 := recvNewEvictedE_descBits_le atomicSessionOpDescBits honestC2 ep1_2
  have h9 := mSafeInjE_descBits_le atomicSessionOpDescBits (ssMir (scBase sCAmb2))
  have h10 := mkCAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) honestC2 ep1_2 (.some t0_2) lct2
  have h11 := rejOutE_descBits_le atomicSessionOpDescBits sCAmb2
  dsimp only [inp0, sC0, qB0, parsed0, honestC0, tOpt0, lct0, ep1_0,
    sCAmb1, inp1, sC1, qB1, parsed1, i1, t0_2, sCAmb2, inp2, sC2, qB2, parsed2, honestC2,
    lct2, ep1_2, recvNewOfFwdC] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 ⊢
  simp only [atomicCompDescBits, callSub1C_descBits_eq]
  dsimp only [orE, pGet, mEpoch, ssMir, scBase, Expr.v0, Expr.v1, Expr.v2,
    atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, varIdx]
    at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 ⊢
  simp only [Nat.reduceAdd, nb_c0, nb_c1, nb_c2, nb_p32] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 ⊢
  omega

omit [SampleableType Pt] in
private theorem recvRefuseE_cost (Lq : ℕ) {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (wE : Expr AOps Γ (B (ℓ := ℓ) (Pt := Pt) 32)) (isDelE : Expr AOps Γ .bool) :
    (recvRefuseE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) Lq sCE qBE wE isDelE).cost ≤
      sCE.cost + qBE.cost + wE.cost + isDelE.cost + ℓ / 32 + 200 * Lq + 300 := by
  let Γ0 := recvHookInpT ℓ Pt :: Γ
  let Γ1 := Ty.bool :: Γ0
  let v0_outer : Expr AOps Γ0 (recvHookInpT ℓ Pt) := .v0
  let v1_outer : Expr AOps Γ1 (recvHookInpT ℓ Pt) := .v1
  have htr := cost_mInTransitE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) Lq
    (ssMir (scBase (.fst v0_outer))) (otherE (.fst (.snd v0_outer)))
    (.fst (.snd (.snd v0_outer)))
  have hsi := cost_mSafeInjE (ssMir (scBase (.fst v1_outer)))
  have hio := injOKAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (.fst (.snd (.snd v1_outer)))
  dsimp only [Γ0, Γ1, v0_outer, v1_outer, recvRefuseE] at htr hsi hio ⊢
  simp only [cost_eLet, isSomeE, otherE, orE, ssStopped, mWin, ssMir, scBase,
    Expr.v0, Expr.v1, Expr.cost] at htr hsi hio ⊢
  omega

omit [SampleableType Pt] in
private theorem recvRefuseE_descBits_le (Lq : ℕ) {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (wE : Expr AOps Γ (B (ℓ := ℓ) (Pt := Pt) 32)) (isDelE : Expr AOps Γ .bool) :
    atomicExprDescBits atomicSessionOpDescBits
      (recvRefuseE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) Lq sCE qBE wE isDelE) ≤
      atomicExprDescBits atomicSessionOpDescBits sCE +
      atomicExprDescBits atomicSessionOpDescBits qBE +
      atomicExprDescBits atomicSessionOpDescBits wE +
      atomicExprDescBits atomicSessionOpDescBits isDelE +
      2 * bits Lq + 1500 := by
  let Γ0 := recvHookInpT ℓ Pt :: Γ
  let Γ1 := Ty.bool :: Γ0
  let v0_outer : Expr AOps Γ0 (recvHookInpT ℓ Pt) := .v0
  let v1_outer : Expr AOps Γ1 (recvHookInpT ℓ Pt) := .v1
  have htr := mInTransitE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) Lq
    (ssMir (scBase (.fst v0_outer))) (otherE (.fst (.snd v0_outer)))
    (.fst (.snd (.snd v0_outer)))
  have hsi := mSafeInjE_descBits_le atomicSessionOpDescBits (ssMir (scBase (.fst v1_outer)))
  have hio := injOKAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (.fst (.snd (.snd v1_outer)))
  dsimp only [Γ0, Γ1, v0_outer, v1_outer, recvRefuseE, eLet, isSomeE, otherE, orE,
    ssStopped, mWin, ssMir, scBase, Expr.v0, Expr.v1, atomicExprDescBits, varIdx]
    at htr hsi hio ⊢
  simp only [Nat.reduceAdd, nb_c0, nb_c1] at htr hsi hio ⊢
  omega

omit [SampleableType Pt] in
private theorem honestLookupE_cost (Lq : ℕ) {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (wE : Expr AOps Γ (B (ℓ := ℓ) (Pt := Pt) 32)) :
    (honestLookupE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) Lq sCE qBE wE).cost ≤
      sCE.cost + qBE.cost + wE.cost + 150 * Lq + 50 := by
  have h32 : ((32 : ℕ+) : ℕ) = 32 := rfl
  have hmax : max 4 5 = 5 := by omega
  simp only [honestLookupE, cost_eLet, cost_eMapOpt, ssHonest, scBase, boolEq, senderOfE, otherE,
    cost_sOpPure, AtomicPureOp.cost, Expr.v0, Expr.v1, Expr.cost, h32, nb_c1, nb_c2,
    Nat.reduceAdd, hmax]
  omega

omit [SampleableType Pt] in
private theorem honestLookupE_descBits_le (Lq : ℕ) {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (wE : Expr AOps Γ (B (ℓ := ℓ) (Pt := Pt) 32)) :
    atomicExprDescBits atomicSessionOpDescBits
      (honestLookupE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) Lq sCE qBE wE) ≤
      atomicExprDescBits atomicSessionOpDescBits sCE +
      atomicExprDescBits atomicSessionOpDescBits qBE +
      atomicExprDescBits atomicSessionOpDescBits wE +
      2 * bits Lq + 700 := by
  have hct : atomicTyDescBits (fig8CtT (ℓ := ℓ) (Pt := Pt)) ≤ 110 := atomicTyDescBits_fig8CtT
  dsimp only [honestLookupE, eLet, ssHonest, scBase, boolEq, senderOfE, otherE,
    Expr.v0, Expr.v1, atomicExprDescBits]
  simp only [descBits_eMapOpt, descBits_sOpPure, atomicPureOpDescBits, atomicExprDescBits,
    varIdx, Nat.reduceAdd, nb_c0, nb_c1, nb_c2, nb_p32]
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem recvHookShape_cost_le {O' : Ops ASig}
    {ι : Type} {T : OracleSpec ι} {I' : Iface ASig T}
    (refuseE : Expr O' [recvHookInpT ℓ Pt] .bool)
    (noneE : Expr O' [recvHookInpT ℓ Pt] (recvOutT ℓ Pt))
    (parseC : Comp O' I' [recvHookInpT ℓ Pt] (.opt (parseOutT ℓ Pt)))
    (rejE : Expr O' [.opt (parseOutT ℓ Pt), recvHookInpT ℓ Pt] (recvOutT ℓ Pt))
    (honestE : Expr O' [parseOutT ℓ Pt, .opt (parseOutT ℓ Pt), recvHookInpT ℓ Pt]
      (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))))
    (findE : Expr O'
      [.opt (fig8CtT (ℓ := ℓ) (Pt := Pt)), parseOutT ℓ Pt,
       .opt (parseOutT ℓ Pt), recvHookInpT ℓ Pt] (.opt .nat))
    (newBranchC : Comp O' I' [recvNewInpT ℓ Pt] (recvOutT ℓ Pt))
    (argNE : Expr O'
      [.opt (fig8CtT (ℓ := ℓ) (Pt := Pt)), parseOutT ℓ Pt,
       .opt (parseOutT ℓ Pt), recvHookInpT ℓ Pt] (recvNewInpT ℓ Pt))
    (sameBranchC : Comp O' I' [recvSameInpT ℓ Pt] (recvOutT ℓ Pt))
    (argSE : Expr O'
      [.nat, .opt (fig8CtT (ℓ := ℓ) (Pt := Pt)), parseOutT ℓ Pt,
       .opt (parseOutT ℓ Pt), recvHookInpT ℓ Pt] (recvSameInpT ℓ Pt)) :
    (Comp.ite refuseE (.ret noneE)
      (.bind parseC (.caseOpt .v0 (.ret rejE)
        (.bind (.ret honestE)
          (.caseOpt findE (callSub1C newBranchC argNE) (callSub1C sameBranchC argSE)))))).cost ≤
      refuseE.cost + noneE.cost + parseC.cost + rejE.cost + honestE.cost + findE.cost +
      argNE.cost + argSE.cost + max newBranchC.cost sameBranchC.cost + 20 := by
  simp only [callSub1C, wkTop1Comp, Comp.cost, Comp.renameM_cost, Expr.v0, Expr.cost]
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem recvHookShape_descBits_le {O' : Ops ASig}
    {ι : Type} {T : OracleSpec ι} {I' : Iface ASig T}
    (opB : O'.Op → ℕ) (sB : I'.smp.Samp → ℕ) (qB : I'.Tag → ℕ)
    (refuseE : Expr O' [recvHookInpT ℓ Pt] .bool)
    (noneE : Expr O' [recvHookInpT ℓ Pt] (recvOutT ℓ Pt))
    (parseC : Comp O' I' [recvHookInpT ℓ Pt] (.opt (parseOutT ℓ Pt)))
    (rejE : Expr O' [.opt (parseOutT ℓ Pt), recvHookInpT ℓ Pt] (recvOutT ℓ Pt))
    (honestE : Expr O' [parseOutT ℓ Pt, .opt (parseOutT ℓ Pt), recvHookInpT ℓ Pt]
      (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))))
    (findE : Expr O'
      [.opt (fig8CtT (ℓ := ℓ) (Pt := Pt)), parseOutT ℓ Pt,
       .opt (parseOutT ℓ Pt), recvHookInpT ℓ Pt] (.opt .nat))
    (newBranchC : Comp O' I' [recvNewInpT ℓ Pt] (recvOutT ℓ Pt))
    (argNE : Expr O'
      [.opt (fig8CtT (ℓ := ℓ) (Pt := Pt)), parseOutT ℓ Pt,
       .opt (parseOutT ℓ Pt), recvHookInpT ℓ Pt] (recvNewInpT ℓ Pt))
    (sameBranchC : Comp O' I' [recvSameInpT ℓ Pt] (recvOutT ℓ Pt))
    (argSE : Expr O'
      [.nat, .opt (fig8CtT (ℓ := ℓ) (Pt := Pt)), parseOutT ℓ Pt,
       .opt (parseOutT ℓ Pt), recvHookInpT ℓ Pt] (recvSameInpT ℓ Pt)) :
    atomicCompDescBits opB sB qB
      (Comp.ite refuseE (.ret noneE)
        (.bind parseC (.caseOpt .v0 (.ret rejE)
          (.bind (.ret honestE)
            (.caseOpt findE (callSub1C newBranchC argNE) (callSub1C sameBranchC argSE)))))) ≤
      atomicExprDescBits opB refuseE + atomicExprDescBits opB noneE +
      atomicCompDescBits opB sB qB parseC + atomicExprDescBits opB rejE +
      atomicExprDescBits opB honestE + atomicExprDescBits opB findE +
      atomicExprDescBits opB argNE + atomicExprDescBits opB argSE +
      atomicCompDescBits opB sB qB newBranchC +
      atomicCompDescBits opB sB qB sameBranchC + 100 := by
  simp only [atomicCompDescBits, callSub1C_descBits_eq]
  dsimp only [Expr.v0, atomicExprDescBits, varIdx]
  simp only [nb_c0]
  omega

theorem recvHookOfBranchesC_queries (idA idB : IdentityKey) (Lq : ℕ)
    (sameBranchC : Comp AOps (fig8SmIface ℓ Pt) [recvSameInpT ℓ Pt] (recvOutT ℓ Pt))
    (newBranchC : Comp AOps (fig8SmIface ℓ Pt) [recvNewInpT ℓ Pt] (recvOutT ℓ Pt))
    (w : (fig8SmIface ℓ Pt).Tag → ℕ)
    (ws : (fig8SmIface ℓ Pt).smp.Samp → ℕ) :
    (recvHookOfBranchesC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam)
      idA idB Lq sameBranchC newBranchC).queries w ws =
      max (newBranchC.queries w ws) (sameBranchC.queries w ws) := by
  simp [recvHookOfBranchesC, callSub1C, wkTop1Comp, Comp.queries]

theorem recvHookOfBranchesC_cost (idA idB : IdentityKey) (Lq : ℕ)
    (sameBranchC : Comp AOps (fig8SmIface ℓ Pt) [recvSameInpT ℓ Pt] (recvOutT ℓ Pt))
    (newBranchC : Comp AOps (fig8SmIface ℓ Pt) [recvNewInpT ℓ Pt] (recvOutT ℓ Pt)) :
    (recvHookOfBranchesC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam)
      idA idB Lq sameBranchC newBranchC).cost ≤
      max newBranchC.cost sameBranchC.cost + 2 * (ℓ / 32) + 500 * Lq + 131220000 := by
  let inp0 : Expr AOps [recvHookInpT ℓ Pt] (recvHookInpT ℓ Pt) := .v0
  let sC0 := Expr.fst inp0; let qB0 := Expr.fst (.snd inp0)
  let w0 := Expr.fst (.snd (.snd inp0)); let isDel0 := Expr.snd (.snd (.snd inp0))
  let pq0 := pGet (ssPq (scBase sC0)) qB0
  let Γ_opt := [.opt (parseOutT ℓ Pt), recvHookInpT ℓ Pt]
  let sC_opt := Expr.fst (.v1 : Expr AOps Γ_opt (recvHookInpT ℓ Pt))
  let inp1 : Expr AOps [parseOutT ℓ Pt, .opt (parseOutT ℓ Pt), recvHookInpT ℓ Pt]
      (recvHookInpT ℓ Pt) := .v2
  let sC1 := Expr.fst inp1; let qB1 := Expr.fst (.snd inp1); let w1 := Expr.fst (.snd (.snd inp1))
  let Γ2 := [.opt (fig8CtT (ℓ := ℓ) (Pt := Pt)), parseOutT ℓ Pt,
    .opt (parseOutT ℓ Pt), recvHookInpT ℓ Pt]
  let honest2 : Expr AOps Γ2 (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))) := .v0
  let parsed2 : Expr AOps Γ2 (parseOutT ℓ Pt) := .v1
  let inp2 : Expr AOps Γ2 (recvHookInpT ℓ Pt) := .v3
  let sC2 := Expr.fst inp2; let qB2 := Expr.fst (.snd inp2)
  let w2 := Expr.fst (.snd (.snd inp2)); let isDel2 := Expr.snd (.snd (.snd inp2))
  let pk2 := Expr.fst (.snd (.snd parsed2)); let ch2 := pGet (ssChains (scBase sC2)) qB2
  let argNE : Expr AOps Γ2 (recvNewInpT ℓ Pt) :=
    .pair sC2 (.pair qB2 (.pair w2 (.pair isDel2 (.pair parsed2 honest2))))
  let Γ3 := .nat :: Γ2; let ci3 : Expr AOps Γ3 .nat := .v0
  let honest3 : Expr AOps Γ3 (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))) := .v1
  let parsed3 : Expr AOps Γ3 (parseOutT ℓ Pt) := .v2
  let inp3 : Expr AOps Γ3 (recvHookInpT ℓ Pt) := .v4
  let argSE : Expr AOps Γ3 (recvSameInpT ℓ Pt) :=
    .pair (.fst inp3) (.pair (.fst (.snd inp3)) (.pair (.fst (.snd (.snd inp3)))
      (.pair (.snd (.snd (.snd inp3))) (.pair parsed3 (.pair honest3 ci3)))))
  have hsh := recvHookShape_cost_le
    (recvRefuseE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) Lq sC0 qB0 w0 isDel0)
    (noneOutE sC0)
    (parseRecvAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam)
      (fig8SmIface ℓ Pt) idA idB (2 ^ 32) qB0 pq0 w0)
    (rejOutE sC_opt)
    (honestLookupE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) Lq sC1 qB1 w1)
    (findChainIdxE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) ch2 pk2)
    newBranchC argNE sameBranchC argSE
  have h1 := recvRefuseE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) Lq sC0 qB0 w0 isDel0
  have h2 := noneOutE_cost sC0
  have h3 := parseRecvAtomicC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (fig8SmIface ℓ Pt) idA idB (2 ^ 32) qB0 pq0 w0
  rw [nb_c2pow32] at h3
  have h4 := rejOutE_cost sC_opt
  have h5 := honestLookupE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) Lq sC1 qB1 w1
  have h6 := cost_findChainIdxE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) ch2 pk2
  have hleaf : sC0.cost + qB0.cost + w0.cost + isDel0.cost + pq0.cost + sC_opt.cost +
      sC1.cost + qB1.cost + w1.cost + ch2.cost + pk2.cost + argNE.cost + argSE.cost ≤ 300 := by
    dsimp only [Γ_opt, Γ2, Γ3, sC0, qB0, w0, isDel0, pq0, sC_opt, sC1, qB1, w1,
      sC2, qB2, w2, isDel2, ch2, pk2, argNE, argSE,
      inp0, inp1, honest2, parsed2, inp2, ci3, honest3, parsed3, inp3]
    simp only [pGet, ssPq, ssChains, scBase,
      Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.cost]
    omega
  exact le_trans hsh (by omega)

theorem recvHookOfBranchesC_descBits_le (idA idB : IdentityKey) (Lq : ℕ)
    (sameBranchC : Comp AOps (fig8SmIface ℓ Pt) [recvSameInpT ℓ Pt] (recvOutT ℓ Pt))
    (newBranchC : Comp AOps (fig8SmIface ℓ Pt) [recvNewInpT ℓ Pt] (recvOutT ℓ Pt))
    (sB : (fig8SmIface ℓ Pt).smp.Samp → ℕ)
    (qB : (fig8SmIface ℓ Pt).Tag → ℕ) :
    atomicCompDescBits atomicSessionOpDescBits sB qB
      (recvHookOfBranchesC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam)
        idA idB Lq sameBranchC newBranchC) ≤
      atomicCompDescBits atomicSessionOpDescBits sB qB newBranchC +
      atomicCompDescBits atomicSessionOpDescBits sB qB sameBranchC +
      8 * bits Lq + 130000 := by
  let inp0 : Expr AOps [recvHookInpT ℓ Pt] (recvHookInpT ℓ Pt) := .v0
  let sC0 := Expr.fst inp0; let qB0 := Expr.fst (.snd inp0)
  let w0 := Expr.fst (.snd (.snd inp0)); let isDel0 := Expr.snd (.snd (.snd inp0))
  let pq0 := pGet (ssPq (scBase sC0)) qB0
  let Γ_opt := [.opt (parseOutT ℓ Pt), recvHookInpT ℓ Pt]
  let sC_opt := Expr.fst (.v1 : Expr AOps Γ_opt (recvHookInpT ℓ Pt))
  let inp1 : Expr AOps [parseOutT ℓ Pt, .opt (parseOutT ℓ Pt), recvHookInpT ℓ Pt]
      (recvHookInpT ℓ Pt) := .v2
  let sC1 := Expr.fst inp1; let qB1 := Expr.fst (.snd inp1); let w1 := Expr.fst (.snd (.snd inp1))
  let Γ2 := [.opt (fig8CtT (ℓ := ℓ) (Pt := Pt)), parseOutT ℓ Pt,
    .opt (parseOutT ℓ Pt), recvHookInpT ℓ Pt]
  let honest2 : Expr AOps Γ2 (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))) := .v0
  let parsed2 : Expr AOps Γ2 (parseOutT ℓ Pt) := .v1
  let inp2 : Expr AOps Γ2 (recvHookInpT ℓ Pt) := .v3
  let sC2 := Expr.fst inp2; let qB2 := Expr.fst (.snd inp2)
  let w2 := Expr.fst (.snd (.snd inp2)); let isDel2 := Expr.snd (.snd (.snd inp2))
  let pk2 := Expr.fst (.snd (.snd parsed2)); let ch2 := pGet (ssChains (scBase sC2)) qB2
  let argNE : Expr AOps Γ2 (recvNewInpT ℓ Pt) :=
    .pair sC2 (.pair qB2 (.pair w2 (.pair isDel2 (.pair parsed2 honest2))))
  let Γ3 := .nat :: Γ2; let ci3 : Expr AOps Γ3 .nat := .v0
  let honest3 : Expr AOps Γ3 (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))) := .v1
  let parsed3 : Expr AOps Γ3 (parseOutT ℓ Pt) := .v2
  let inp3 : Expr AOps Γ3 (recvHookInpT ℓ Pt) := .v4
  let argSE : Expr AOps Γ3 (recvSameInpT ℓ Pt) :=
    .pair (.fst inp3) (.pair (.fst (.snd inp3)) (.pair (.fst (.snd (.snd inp3)))
      (.pair (.snd (.snd (.snd inp3))) (.pair parsed3 (.pair honest3 ci3)))))
  have hsh := recvHookShape_descBits_le atomicSessionOpDescBits sB qB
    (recvRefuseE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) Lq sC0 qB0 w0 isDel0)
    (noneOutE sC0)
    (parseRecvAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam)
      (fig8SmIface ℓ Pt) idA idB (2 ^ 32) qB0 pq0 w0)
    (rejOutE sC_opt)
    (honestLookupE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) Lq sC1 qB1 w1)
    (findChainIdxE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) ch2 pk2)
    newBranchC argNE sameBranchC argSE
  have h1 := recvRefuseE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) Lq sC0 qB0 w0 isDel0
  have h2 := noneOutE_descBits_le atomicSessionOpDescBits sC0
  have h3 := parseRecvAtomicC_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (fig8SmIface ℓ Pt) idA idB (2 ^ 32) sB qB qB0 pq0 w0
  rw [nb_c2pow32] at h3
  have h4 := rejOutE_descBits_le atomicSessionOpDescBits sC_opt
  have h5 := honestLookupE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) Lq sC1 qB1 w1
  have h6 := findChainIdxE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) ch2 pk2
  have hleaf :
      atomicExprDescBits atomicSessionOpDescBits sC0 +
      atomicExprDescBits atomicSessionOpDescBits qB0 +
      atomicExprDescBits atomicSessionOpDescBits w0 +
      atomicExprDescBits atomicSessionOpDescBits isDel0 +
      atomicExprDescBits atomicSessionOpDescBits pq0 +
      atomicExprDescBits atomicSessionOpDescBits sC_opt +
      atomicExprDescBits atomicSessionOpDescBits sC1 +
      atomicExprDescBits atomicSessionOpDescBits qB1 +
      atomicExprDescBits atomicSessionOpDescBits w1 +
      atomicExprDescBits atomicSessionOpDescBits ch2 +
      atomicExprDescBits atomicSessionOpDescBits pk2 +
      atomicExprDescBits atomicSessionOpDescBits argNE +
      atomicExprDescBits atomicSessionOpDescBits argSE ≤ 2000 := by
    dsimp only [Γ_opt, Γ2, Γ3, sC0, qB0, w0, isDel0, pq0, sC_opt, sC1, qB1, w1,
      sC2, qB2, w2, isDel2, ch2, pk2, argNE, argSE,
      inp0, inp1, honest2, parsed2, inp2, ci3, honest3, parsed3, inp3,
      pGet, ssPq, ssChains, scBase, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4,
      atomicExprDescBits, varIdx]
    simp only [Nat.reduceAdd, nb_c0, nb_c1, nb_c2, nb_c3, nb_c4]
    omega
  exact le_trans hsh (by omega)

theorem recvArmC_queries (isDel : Bool)
    (recvHookC : Comp AOps (fig8SmIface ℓ Pt) [recvHookInpT ℓ Pt] (recvOutT ℓ Pt))
    (w : (fig8SmIface ℓ Pt).Tag → ℕ)
    (ws : (fig8SmIface ℓ Pt).smp.Samp → ℕ) :
    (recvArmC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) isDel recvHookC).queries w ws =
      recvHookC.queries w ws := by
  simp [recvArmC, callSub1C, wkTop1Comp, Comp.queries]

theorem recvArmC_cost (isDel : Bool)
    (recvHookC : Comp AOps (fig8SmIface ℓ Pt) [recvHookInpT ℓ Pt] (recvOutT ℓ Pt)) :
    (recvArmC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) isDel recvHookC).cost ≤
      recvHookC.cost + 50 := by
  simp only [recvArmC, callSub1C, wkTop1Comp, Comp.cost, Comp.renameM_cost,
    Expr.cost, Expr.v0, Expr.v1]
  omega

theorem recvArmC_descBits_le (isDel : Bool)
    (recvHookC : Comp AOps (fig8SmIface ℓ Pt) [recvHookInpT ℓ Pt] (recvOutT ℓ Pt))
    (sB : (fig8SmIface ℓ Pt).smp.Samp → ℕ)
    (qB : (fig8SmIface ℓ Pt).Tag → ℕ) :
    atomicCompDescBits atomicSessionOpDescBits sB qB
      (recvArmC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) isDel recvHookC) ≤
      atomicCompDescBits atomicSessionOpDescBits sB qB recvHookC + 300 := by
  simp only [recvArmC, callSub1C_descBits_eq, atomicExprDescBits, Expr.v0, Expr.v1,
    varIdx, Nat.reduceAdd, nb_c0, nb_c1]
  omega

end Defs

end Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvNewCost

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8SanOracle
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8SanCoupling

/-!
# Corrupt Branch of the Concrete Atomic `simFig8` Step

Defines `simFig8StepCorrBody` and `simFig8StepCorrC` over `atomicSessionOps` and `fig8SmIface`
implementing the `.corrupt` branch of `simFig8OracleSan`, with cost, description-bit, and `.eval`
proofs.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart)
open CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C Fig8Comp SimCStateBounded)
open CryptoGames.Ratchet.LibsignalSimC (LibsignalToModularSchemeSimState Kept)
open CryptoGames.SM (partyEnc orE pGet pSet orE_eval pGet_eval pSet_eval ite_eval)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey GhostState)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (Bytes paramsV1)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost
  (atomicSortDescBits atomicTyDescBits varIdx atomicSessionOpDescBits atomicExprDescBits
   atomicCompDescBits)

open Computational.Proofs.Game.PromotedCostedReds.SanOracleCore (fig8StTruncSkB semCorrHookTGB semHandleHookDedupS)
open Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon (comp_eval_bind comp_eval_bind_ret comp_eval_caseOpt comp_eval_ite comp_eval_ret)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept (f8Gamma keptOfStAtomicE keptOfStAtomicE_cost keptOfStAtomicE_descBits_le keptOfStAtomicE_eval)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost (fig8IdSemHook fig8StTruncSk ghostChainDec ghostChainDec_ghostChainEnc ghostChainEnc ghostChainT simBaseDec simBaseEnc simBaseT simFullDec simFullT simMirDec simMirDec_simMirEnc simMirEnc simMirT simRecDec simRecEnc simRecEnc_simRecDec)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanCoupling (SanSnapExtra)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanOracle (simFig8OracleSan)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8State (bits_eq_of_bounds bits_le_of_lt_pow bits_zero cost_eLet cost_mAfterCorrFastE cost_mCorrAllowedFastE cost_mInWinE cost_mNoSpkCorrE cost_revealSpkChainsE cost_sOpGrp cost_sOpPtEnc cost_toGhostE descBits_sOpGrp descBits_sOpPtEnc eLet eval_eLet eval_revealSpkChainsE eval_sOpGrp eval_sOpPtEnc eval_toGhostE mAfterCorrFastE mAfterCorrFastE_descBits_le mAfterCorrFastE_eval mCorrAllowedFastE mCorrAllowedFastE_descBits_le mCorrAllowedFastE_eval mEpoch mInWinE mInWinE_descBits_le mInWinE_eval mNoSpkCorrE mNoSpkCorrE_descBits_le mNoSpkCorrE_eval mWin revealSpkChainsE revealSpkChainsE_descBits_le sOpGrp sOpPtEnc scBase scKept scMk scSent scSnaps ssAmb ssChains ssHonest ssMir ssMk ssPn ssPq ssStopped ssUnackA toGhostE toGhostE_descBits_le)
open ReductionDsl (B BV256 Comp Env Expr GhostStT Iface Ops PK PlainT PtT Ty Var atomicSessionOps atomicSig bits bits_mono ckaStV e2eSessionCodec fig8CtT fig8SmIface fig8StT fig8StV handlerImpl recvResultT smQT smQenc smRT smRdec)

namespace Computational.Proofs.Game.PromotedCostedReds.SimFig8StepCorr

section StepCorr

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
variable {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
variable {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

def corrNoneReplyE {O' : Ops ASig} {Γ : List (Ty ASig)} :
    Expr O' Γ (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) :=
  .pair .none (.pair .none .none)

def corrBlockedE {Γ : List (Ty ASig)} (q : ℕ)
    (sE : Expr AOps Γ (simFullT ℓ Pt)) (qE : Expr AOps Γ .bool) :
    Expr AOps Γ .bool :=
  eLet (.pair sE qE)
    (let base0 := scBase (.fst .v0)
     let mir0 := ssMir base0
     let q0 : Expr AOps _ .bool := .snd .v0
     orE (ssStopped base0)
       (orE (mWin mir0)
         (orE (.not (mCorrAllowedFastE q mir0 q0))
           (orE (mInWinE mir0 q0)
             (.not (mNoSpkCorrE mir0 q0))))))

def corrChainsUpdE {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ (simFullT ℓ Pt)) (qE : Expr AOps Γ .bool)
    (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) :
    Expr AOps Γ (.prod (.list (ghostChainT ℓ Pt)) (.list (ghostChainT ℓ Pt))) :=
  eLet (.pair sE (.pair qE stE))
    (let base0 := scBase (.fst .v0)
     let mir0 := ssMir base0
     let q0 : Expr AOps _ .bool := .fst (.snd .v0)
     let st0 : Expr AOps _ (fig8StT (ℓ := ℓ) (Pt := Pt)) := .snd (.snd .v0)
     let isBobEp0 := ReductionDsl.Expr.and q0 (.eqN (.snd (mEpoch mir0)) (.nat 0))
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

def corrSomeOutE {Γ : List (Ty ASig)} (idA idB : IdentityKey) (q : ℕ)
    (sE : Expr AOps Γ (simFullT ℓ Pt)) (qE : Expr AOps Γ .bool)
    (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) :
    Expr AOps Γ (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)) :=
  eLet (.pair sE (.pair qE stE))
    (let s0 : Expr AOps _ (simFullT ℓ Pt) := .fst .v0
     let q0 : Expr AOps _ .bool := .fst (.snd .v0)
     let st0 : Expr AOps _ (fig8StT (ℓ := ℓ) (Pt := Pt)) := .snd (.snd .v0)
     eLet (corrChainsUpdE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
            (decT := decT) (lam := lam) s0 q0 st0)
       (let s1 : Expr AOps _ (simFullT ℓ Pt) := .fst .v1
        let q1 : Expr AOps _ .bool := .fst (.snd .v1)
        let st1 : Expr AOps _ (fig8StT (ℓ := ℓ) (Pt := Pt)) := .snd (.snd .v1)
        let b1 := scBase s1
        let baseForGhost := ssMk (ssMir b1) (ssPq b1) (ssPn b1) (ssUnackA b1)
          .nil .v0 (ssAmb b1) (ssStopped b1)
        eLet (toGhostE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
               (decT := decT) (lam := lam) idA idB (25000 * q) baseForGhost q1 st1)
          (let s2 : Expr AOps _ (simFullT ℓ Pt) := .fst .v2
           let q2 : Expr AOps _ .bool := .fst (.snd .v2)
           let st2 : Expr AOps _ (fig8StT (ℓ := ℓ) (Pt := Pt)) := .snd (.snd .v2)
           let b2 := scBase s2
           let mir2 := ssMir b2
           let base' := ssMk (mAfterCorrFastE q mir2 q2) (ssPq b2) (ssPn b2) (ssUnackA b2)
             (ssHonest b2) .v1 (ssAmb b2) (ssStopped b2)
           let keptSt := keptOfStAtomicE st2
           let kept' := ReductionDsl.Expr.ite q2 (.pair (.fst (scKept s2)) keptSt)
             (.pair keptSt (.snd (scKept s2)))
           let epQ := ReductionDsl.Expr.ite q2 (.snd (mEpoch mir2)) (.fst (mEpoch mir2))
           let snapEntry := ReductionDsl.Expr.pair q2 (.pair epQ .v0)
           let sC' := scMk base' kept' (scSent s2) (.cons snapEntry (scSnaps s2))
           .pair (.pair .none (.pair .none (.some .v0))) sC')))

/-- Context-polymorphic atomic `Comp` implementing the `.corrupt Q` branch of `simFig8OracleSan`
at `(L, Bsk) = (q, 25000 * q)`. -/
def simFig8StepCorrBody {Γ : List (Ty ASig)} (idA idB : IdentityKey) (q : ℕ)
    (sE : Expr AOps Γ (simFullT ℓ Pt)) (qE : Expr AOps Γ .bool) :
    Comp AOps (fig8SmIface ℓ Pt) Γ
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)) :=
  .bind (.ret (.pair sE qE))
    (.ite (corrBlockedE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
            (decT := decT) (lam := lam) q (.fst (.var .zero)) (.snd (.var .zero)))
      (.ret (.pair corrNoneReplyE (.fst (.var .zero))))
      (.bind (.query (I := fig8SmIface ℓ Pt) ReductionDsl.SMTag.cr (.snd (.var .zero)))
        (.caseOpt (.var .zero)
          (.ret (.pair corrNoneReplyE (.fst (.var (.succ .zero)))))
          (.ret (corrSomeOutE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
                  (decT := decT) (lam := lam) idA idB q
                  (.fst (.var (.succ (.succ .zero))))
                  (.snd (.var (.succ (.succ .zero))))
                  (.var .zero))))))

/-- Standalone `Comp` on `[simFullT ℓ Pt, smQT]` handling `.corrupt P` (`Sum.inr P`). -/
def simFig8StepCorrC (idA idB : IdentityKey) (q : ℕ) :
    Comp AOps (fig8SmIface ℓ Pt) [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)) :=
  let noop {Γ} (sVar : Var Γ (simFullT ℓ Pt)) :
      Comp AOps (fig8SmIface ℓ Pt) Γ
        (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)) :=
    .ret (.pair corrNoneReplyE (.var sVar))
  .caseSum (.var (.succ .zero))
    (noop (.succ .zero))
    (.caseSum (.var .zero)
      (noop (.succ (.succ .zero)))
      (.caseSum (.var .zero)
        (noop (.succ (.succ (.succ .zero))))
        (.caseSum (.var .zero)
          (noop (.succ (.succ (.succ (.succ .zero)))))
          (simFig8StepCorrBody (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
            (decT := decT) (lam := lam) idA idB q
            (.var (.succ (.succ (.succ (.succ .zero))))) (.var .zero)))))

private theorem hb0_bits : bits 0 = 1 := bits_zero
private theorem hb1_bits : bits 1 = 1 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem hb2_bits : bits 2 = 2 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem hb3_bits : bits 3 = 2 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem hb4_bits : bits 4 = 3 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem hb32_pnat : bits ((32 : ℕ+) : ℕ) = 6 := by
  change bits 32 = 6
  exact bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)

private theorem bits_25000_mul_le (q : ℕ) : bits (25000 * q) ≤ bits (q + 1) + 15 := by
  apply bits_le_of_lt_pow (by omega)
  have hq : q + 1 < 2 ^ bits (q + 1) := by
    unfold bits
    simpa using Nat.lt_pow_succ_log_self (by omega : 1 < 2) (q + 1)
  have hp : 2 ^ (bits (q + 1) + 15) = 2 ^ bits (q + 1) * 32768 := by
    rw [Nat.pow_add]
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem corrNoneReplyE_cost {O' : Ops ASig} {Γ : List (Ty ASig)} :
    (corrNoneReplyE (ℓ := ℓ) (Pt := Pt) (O' := O') (Γ := Γ)).cost ≤ 10 := by
  simp only [corrNoneReplyE, ReductionDsl.Expr.cost]
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem corrNoneReplyE_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ) {Γ : List (Ty ASig)} :
    atomicExprDescBits opB (corrNoneReplyE (ℓ := ℓ) (Pt := Pt) (O' := O') (Γ := Γ)) ≤ 120 := by
  dsimp only [corrNoneReplyE, smRT, recvResultT, B, PlainT, GhostStT,
    atomicExprDescBits, atomicTyDescBits, atomicSortDescBits]
  simp only [hb32_pnat]
  omega

omit [SampleableType Pt] in
private theorem corrBlockedE_cost {Γ : List (Ty ASig)} (q : ℕ)
    (sE : Expr AOps Γ (simFullT ℓ Pt)) (qE : Expr AOps Γ .bool) :
    (corrBlockedE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) q sE qE).cost ≤
      sE.cost + qE.cost + 600 * q + 500 := by
  let Γ0 := ReductionDsl.Ty.prod (simFullT ℓ Pt) .bool :: Γ
  let mir0 : Expr AOps Γ0 (simMirT ℓ Pt) := ssMir (scBase (.fst .v0))
  let q0 : Expr AOps Γ0 .bool := .snd .v0
  have h1 := cost_mCorrAllowedFastE q mir0 q0
  have h2 := cost_mInWinE mir0 q0
  have h3 := cost_mNoSpkCorrE mir0 q0
  dsimp only [Γ0, mir0, q0, ssMir, scBase, ReductionDsl.Expr.v0, ReductionDsl.Expr.cost] at h1 h2 h3
  simp only [corrBlockedE, cost_eLet, orE, ssStopped, mWin, ssMir, scBase, ReductionDsl.Expr.v0, ReductionDsl.Expr.cost]
  omega

omit [SampleableType Pt] in
private theorem corrBlockedE_descBits_le {Γ : List (Ty ASig)} (q : ℕ)
    (sE : Expr AOps Γ (simFullT ℓ Pt)) (qE : Expr AOps Γ .bool) :
    atomicExprDescBits atomicSessionOpDescBits
      (corrBlockedE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) q sE qE) ≤
      atomicExprDescBits atomicSessionOpDescBits sE +
      atomicExprDescBits atomicSessionOpDescBits qE + 10 * bits q + 3000 := by
  let Γ0 := ReductionDsl.Ty.prod (simFullT ℓ Pt) .bool :: Γ
  let mir0 : Expr AOps Γ0 (simMirT ℓ Pt) := ssMir (scBase (.fst .v0))
  let q0 : Expr AOps Γ0 .bool := .snd .v0
  have h1 := mCorrAllowedFastE_descBits_le atomicSessionOpDescBits q mir0 q0
  have h2 := mInWinE_descBits_le atomicSessionOpDescBits mir0 q0
  have h3 := mNoSpkCorrE_descBits_le atomicSessionOpDescBits mir0 q0
  dsimp only [Γ0, mir0, q0, ssMir, scBase, ReductionDsl.Expr.v0, atomicExprDescBits, varIdx] at h1 h2 h3
  simp only [hb0_bits] at h1 h2 h3
  dsimp only [corrBlockedE, eLet, orE, ssStopped, mWin, ssMir, scBase, ReductionDsl.Expr.v0,
    atomicExprDescBits, varIdx]
  simp only [hb0_bits]
  omega

omit [SampleableType Pt] in
private theorem corrChainsUpdE_cost {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ (simFullT ℓ Pt)) (qE : Expr AOps Γ .bool)
    (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) :
    (corrChainsUpdE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) sE qE stE).cost ≤
      sE.cost + qE.cost + stE.cost + 300 := by
  let Γ0 := ReductionDsl.Ty.prod (simFullT ℓ Pt) (.prod .bool (fig8StT (ℓ := ℓ) (Pt := Pt))) :: Γ
  let Γr := BV256 (ℓ := ℓ) (Pt := Pt) :: Γ0
  let pkE : Expr AOps Γr PK :=
    sOpPtEnc (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) .ptEncPk
      (sOpGrp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) .ptDh
        (.pair .v0
          (sOpGrp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
            (decT := decT) (lam := lam) .ptBase .unit)))
  have hrev := cost_revealSpkChainsE (.fst (ssChains (scBase (.fst (.v1 : Expr AOps Γr _))))) pkE
  dsimp only [Γ0, Γr, pkE, ssChains, scBase, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1] at hrev
  simp only [cost_sOpPtEnc, cost_sOpGrp, ReductionDsl.AtomicGroupOp.cost, ReductionDsl.Expr.cost] at hrev
  have hb0 : bits 0 = 1 := bits_zero
  simp only [corrChainsUpdE, cost_eLet, ssChains, ssMir, scBase, mEpoch, f8Gamma,
    ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Expr.cost, hb0]
  omega

omit [SampleableType Pt] in
private theorem corrChainsUpdE_descBits_le {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ (simFullT ℓ Pt)) (qE : Expr AOps Γ .bool)
    (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) :
    atomicExprDescBits atomicSessionOpDescBits
      (corrChainsUpdE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) sE qE stE) ≤
      atomicExprDescBits atomicSessionOpDescBits sE +
      atomicExprDescBits atomicSessionOpDescBits qE +
      atomicExprDescBits atomicSessionOpDescBits stE + 1000 := by
  let Γ0 := ReductionDsl.Ty.prod (simFullT ℓ Pt) (.prod .bool (fig8StT (ℓ := ℓ) (Pt := Pt))) :: Γ
  let Γr := BV256 (ℓ := ℓ) (Pt := Pt) :: Γ0
  let pkE : Expr AOps Γr PK :=
    sOpPtEnc (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) .ptEncPk
      (sOpGrp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) .ptDh
        (.pair .v0
          (sOpGrp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
            (decT := decT) (lam := lam) .ptBase .unit)))
  have hrev := revealSpkChainsE_descBits_le atomicSessionOpDescBits
    (.fst (ssChains (scBase (.fst (.v1 : Expr AOps Γr _))))) pkE
  have hv1 : bits (0 + 1) = 1 := hb1_bits
  dsimp only [Γ0, Γr, pkE, ssChains, scBase, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, atomicExprDescBits, varIdx] at hrev
  simp only [descBits_sOpPtEnc, descBits_sOpGrp, atomicExprDescBits, varIdx, hb0_bits] at hrev
  dsimp only [corrChainsUpdE, eLet, ssChains, ssMir, scBase, mEpoch, f8Gamma,
    ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, atomicExprDescBits, varIdx]
  simp only [hb0_bits]
  omega

omit [SampleableType Pt] in
private theorem corrSomeOutE_cost {Γ : List (Ty ASig)} (idA idB : IdentityKey) (q : ℕ)
    (sE : Expr AOps Γ (simFullT ℓ Pt)) (qE : Expr AOps Γ .bool)
    (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) :
    (corrSomeOutE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB q sE qE stE).cost ≤
      sE.cost + qE.cost + stE.cost + 1650000 + 25010000 * q := by
  let T0 := ReductionDsl.Ty.prod (simFullT ℓ Pt) (.prod .bool (fig8StT (ℓ := ℓ) (Pt := Pt)))
  let Tc := ReductionDsl.Ty.prod (.list (ghostChainT ℓ Pt)) (.list (ghostChainT ℓ Pt))
  let Γ0 := T0 :: Γ
  let Γ1 := Tc :: Γ0
  let Γ2 := GhostStT (ℓ := ℓ) (Pt := Pt) :: Γ1
  have hch := corrChainsUpdE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam)
    (.fst (.v0 : Expr AOps Γ0 _)) (.fst (.snd .v0)) (.snd (.snd .v0))
  let b1 : Expr AOps Γ1 (simBaseT ℓ Pt) := scBase (.fst .v1)
  let baseForGhost : Expr AOps Γ1 (simBaseT ℓ Pt) :=
    ssMk (ssMir b1) (ssPq b1) (ssPn b1) (ssUnackA b1) .nil .v0 (ssAmb b1) (ssStopped b1)
  have htg := cost_toGhostE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (25000 * q) baseForGhost
    (.fst (.snd .v1)) (.snd (.snd .v1))
  have hmc := cost_mAfterCorrFastE q (ssMir (scBase (.fst (.v2 : Expr AOps Γ2 _)))) (.fst (.snd .v2))
  have hkp := keptOfStAtomicE_cost (.snd (.snd (.v2 : Expr AOps Γ2 _)))
  dsimp only [T0, Tc, Γ0, Γ1, Γ2, b1, baseForGhost, scBase, ssMir, ssPq, ssPn, ssUnackA,
    ssAmb, ssStopped, ssMk, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Expr.cost] at hch htg hmc hkp
  dsimp only [ReductionDsl.Expr.v2, ReductionDsl.Expr.cost] at hmc hkp
  simp only [corrSomeOutE, cost_eLet, scBase, scKept, scSent, scSnaps, scMk,
    ssMir, ssPq, ssPn, ssUnackA, ssHonest, ssAmb, ssStopped, ssMk, mEpoch,
    ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Expr.v2, ReductionDsl.Expr.cost]
  omega

omit [SampleableType Pt] in
private theorem corrSomeOutE_descBits_le {Γ : List (Ty ASig)} (idA idB : IdentityKey) (q : ℕ)
    (sE : Expr AOps Γ (simFullT ℓ Pt)) (qE : Expr AOps Γ .bool)
    (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) :
    atomicExprDescBits atomicSessionOpDescBits
      (corrSomeOutE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB q sE qE stE) ≤
      atomicExprDescBits atomicSessionOpDescBits sE +
      atomicExprDescBits atomicSessionOpDescBits qE +
      atomicExprDescBits atomicSessionOpDescBits stE +
      90 * bits (q + 1) + 120000 := by
  have hbq : bits q ≤ bits (q + 1) := bits_mono (Nat.le_succ q)
  have hb25k : bits (25000 * q) ≤ bits (q + 1) + 15 := bits_25000_mul_le q
  let T0 := ReductionDsl.Ty.prod (simFullT ℓ Pt) (.prod .bool (fig8StT (ℓ := ℓ) (Pt := Pt)))
  let Tc := ReductionDsl.Ty.prod (.list (ghostChainT ℓ Pt)) (.list (ghostChainT ℓ Pt))
  let Γ0 := T0 :: Γ
  let Γ1 := Tc :: Γ0
  let Γ2 := GhostStT (ℓ := ℓ) (Pt := Pt) :: Γ1
  have hch := corrChainsUpdE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (.fst (.v0 : Expr AOps Γ0 _)) (.fst (.snd .v0)) (.snd (.snd .v0))
  let b1 : Expr AOps Γ1 (simBaseT ℓ Pt) := scBase (.fst .v1)
  let baseForGhost : Expr AOps Γ1 (simBaseT ℓ Pt) :=
    ssMk (ssMir b1) (ssPq b1) (ssPn b1) (ssUnackA b1) .nil .v0 (ssAmb b1) (ssStopped b1)
  have htg := toGhostE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (25000 * q) baseForGhost
    (.fst (.snd .v1)) (.snd (.snd .v1))
  have hmc := mAfterCorrFastE_descBits_le atomicSessionOpDescBits q
    (ssMir (scBase (.fst (.v2 : Expr AOps Γ2 _)))) (.fst (.snd .v2))
  have hkp := keptOfStAtomicE_descBits_le atomicSessionOpDescBits
    (.snd (.snd (.v2 : Expr AOps Γ2 _)))
  have hv1 : bits (0 + 1) = 1 := hb1_bits
  have hv2 : bits (0 + 1 + 1) = 2 := hb2_bits
  dsimp only [T0, Tc, Γ0, Γ1, Γ2, b1, baseForGhost, scBase, ssMir, ssPq, ssPn, ssUnackA,
    ssAmb, ssStopped, ssMk, fig8CtT, ReductionDsl.fig8HdrT, ReductionDsl.lctT,
    ReductionDsl.wireSaltCtT, B, ReductionDsl.PB, ReductionDsl.U64, BV256, PtT,
    ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Expr.v2, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits,
    varIdx] at hch htg hmc hkp
  simp only [hb0_bits, hb32_pnat] at hch htg hmc hkp
  dsimp only [corrSomeOutE, eLet, scBase, scKept, scSent, scSnaps, scMk,
    ssMir, ssPq, ssPn, ssUnackA, ssHonest, ssAmb, ssStopped, ssMk, mEpoch,
    smRT, recvResultT, fig8CtT, ReductionDsl.fig8HdrT, ReductionDsl.lctT,
    ReductionDsl.wireSaltCtT, B, ReductionDsl.PB, ReductionDsl.U64, PlainT, BV256, PtT, GhostStT,
    ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Expr.v2, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, varIdx]
  simp only [hb0_bits, hb32_pnat]
  omega

theorem simFig8StepCorrBody_queries {Γ : List (Ty ASig)} (idA idB : IdentityKey) (q : ℕ)
    (sE : Expr AOps Γ (simFullT ℓ Pt)) (qE : Expr AOps Γ .bool) :
    (simFig8StepCorrBody (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB q sE qE).queries (fun _ => 1) (fun _ => 0) ≤ 1 :=
  Nat.le_refl 1

omit [DecidableEq Pt] [Zero Pt] in
private theorem corrBodyShape_cost_le {O' : Ops ASig} {Γ : List (Ty ASig)} {σ τ : Ty ASig}
    (sE : Expr O' Γ σ) (qE : Expr O' Γ .bool)
    (blk : Expr O' (ReductionDsl.Ty.prod σ .bool :: Γ) .bool)
    (n0 : Expr O' (ReductionDsl.Ty.prod σ .bool :: Γ) τ)
    (n1 : Expr O' (ReductionDsl.Ty.opt (fig8StT (ℓ := ℓ) (Pt := Pt)) :: ReductionDsl.Ty.prod σ .bool :: Γ) τ)
    (someOut : Expr O'
      (fig8StT (ℓ := ℓ) (Pt := Pt) ::
        ReductionDsl.Ty.opt (fig8StT (ℓ := ℓ) (Pt := Pt)) :: ReductionDsl.Ty.prod σ .bool :: Γ)
      (.prod τ σ)) :
    (ReductionDsl.Comp.bind (I := fig8SmIface ℓ Pt) (.ret (.pair sE qE))
      (.ite blk
        (.ret (.pair n0 (.fst (.var .zero))))
        (.bind (.query (I := fig8SmIface ℓ Pt) ReductionDsl.SMTag.cr (.snd (.var .zero)))
          (.caseOpt (.var .zero)
            (.ret (.pair n1 (.fst (.var (.succ .zero)))))
            (.ret someOut))))).cost ≤
      sE.cost + qE.cost + blk.cost + n0.cost + n1.cost + someOut.cost + 50060 := by
  dsimp only [ReductionDsl.Comp.cost, fig8SmIface, ReductionDsl.Expr.cost]
  omega

theorem simFig8StepCorrBody_cost {Γ : List (Ty ASig)} (idA idB : IdentityKey) (q : ℕ)
    (sE : Expr AOps Γ (simFullT ℓ Pt)) (qE : Expr AOps Γ .bool) (_hℓ : ℓ < 10 ^ 6) :
    (simFig8StepCorrBody (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB q sE qE).cost ≤
      sE.cost + qE.cost + 2000000 + 25100000 * q := by
  let Γ0 := ReductionDsl.Ty.prod (simFullT ℓ Pt) .bool :: Γ
  let Γ1 := ReductionDsl.Ty.opt (fig8StT (ℓ := ℓ) (Pt := Pt)) :: Γ0
  let Γ2 := fig8StT (ℓ := ℓ) (Pt := Pt) :: Γ1
  have hshape := corrBodyShape_cost_le (O' := AOps) sE qE
    (corrBlockedE q (.fst (.var .zero)) (.snd (.var .zero)))
    (corrNoneReplyE (Γ := Γ0))
    (corrNoneReplyE (Γ := Γ1))
    (corrSomeOutE idA idB q (.fst (.var (.succ (.succ .zero))))
      (.snd (.var (.succ (.succ .zero)))) (.var .zero))
  have hblk := corrBlockedE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) q (.fst (.var (.zero : Var Γ0 _))) (.snd (.var .zero))
  have hnone0 := corrNoneReplyE_cost (ℓ := ℓ) (Pt := Pt) (O' := AOps) (Γ := Γ0)
  have hnone1 := corrNoneReplyE_cost (ℓ := ℓ) (Pt := Pt) (O' := AOps) (Γ := Γ1)
  have hsome := corrSomeOutE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB q
    (.fst (.var (.succ (.succ (.zero : Var Γ0 _)) : Var Γ2 _)))
    (.snd (.var (.succ (.succ .zero))))
    (.var .zero)
  dsimp only [Γ0, Γ1, Γ2, ReductionDsl.Expr.cost] at hblk hsome
  dsimp only [simFig8StepCorrBody]
  omega

theorem simFig8StepCorrBody_descBits_le {Γ : List (Ty ASig)} (idA idB : IdentityKey) (q : ℕ)
    (sE : Expr AOps Γ (simFullT ℓ Pt)) (qE : Expr AOps Γ .bool) (_hℓ : ℓ < 10 ^ 6) :
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
      (simFig8StepCorrBody (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB q sE qE) ≤
      atomicExprDescBits atomicSessionOpDescBits sE +
      atomicExprDescBits atomicSessionOpDescBits qE +
      131072 + 128 * bits (q + 1) := by
  have hbq : bits q ≤ bits (q + 1) := bits_mono (Nat.le_succ q)
  let Γ0 := ReductionDsl.Ty.prod (simFullT ℓ Pt) .bool :: Γ
  let Γ1 := ReductionDsl.Ty.opt (fig8StT (ℓ := ℓ) (Pt := Pt)) :: Γ0
  let Γ2 := fig8StT (ℓ := ℓ) (Pt := Pt) :: Γ1
  have hblk := corrBlockedE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) q
    (.fst (.var (.zero : Var Γ0 _))) (.snd (.var .zero))
  have hnone0 := corrNoneReplyE_descBits_le (ℓ := ℓ) (Pt := Pt) (O' := AOps)
    atomicSessionOpDescBits (Γ := Γ0)
  have hnone1 := corrNoneReplyE_descBits_le (ℓ := ℓ) (Pt := Pt) (O' := AOps)
    atomicSessionOpDescBits (Γ := Γ1)
  have hsome := corrSomeOutE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB q
    (.fst (.var (.succ (.succ (.zero : Var Γ0 _)) : Var Γ2 _)))
    (.snd (.var (.succ (.succ .zero))))
    (.var .zero)
  have hv0 : bits 0 = 1 := hb0_bits
  have hv1 : bits (0 + 1) = 1 := hb1_bits
  have hv2 : bits (0 + 1 + 1) = 2 := hb2_bits
  dsimp only [Γ0, Γ1, Γ2, atomicExprDescBits, varIdx] at hblk hsome
  dsimp only [simFig8StepCorrBody, atomicCompDescBits, atomicExprDescBits, varIdx]
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem simMirEnc_simMirDec (v : (simMirT ℓ Pt).denote) :
    simMirEnc (simMirDec (Pt := Pt) v) = v := by
  rcases v with ⟨b, win, ⟨epA, epB⟩, ⟨idxA, idxB⟩, tL, trs, chall, comp, ⟨maA, maB⟩, leaks, corrs⟩
  simp only [simMirEnc, simMirDec, List.map_map]
  have htr : (simRecEnc ∘ simRecDec (ℓ := ℓ) (Pt := Pt)) = id := by
    funext r; exact simRecEnc_simRecDec r
  have hpos : (CryptoGames.SM.posEnc ∘ CryptoGames.SM.posDec) = id := by
    funext p; exact CryptoGames.SM.posEnc_posDec p
  have hcor : ((fun pe : Party × ℕ => (partyEnc pe.1, pe.2)) ∘
      (fun pe : Bool × ℕ => (CryptoGames.SM.partyDec pe.1, pe.2))) = id := by
    funext ⟨p, e⟩; simp [CryptoGames.SM.partyEnc_partyDec]
  simp only [htr, hpos, hcor, List.map_id]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem ghostChainEnc_ghostChainDec (v : (ghostChainT ℓ Pt).denote) :
    ghostChainEnc (ℓ := ℓ) (Pt := Pt) (ghostChainDec v) = v := by
  rcases v with ⟨k, e, l, sk⟩; rfl

private theorem isBobEp0_eq (P : Party) (n : ℕ) :
    (partyEnc P && decide (n = 0)) = (P == CryptoGames.Party.B && n == 0) := by
  cases P <;> cases n <;> rfl

omit [SampleableType Pt] in
private theorem corrBlockedE_eval {Γ : List (Ty ASig)} (q : ℕ)
    (sE : Expr AOps Γ (simFullT ℓ Pt)) (qE : Expr AOps Γ .bool)
    (ρ : Env Γ) (P : Party) (hq : qE.eval ρ = partyEnc P)
    (hBound : SimCStateBounded q (simFullDec (sE.eval ρ))) :
    (corrBlockedE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) q sE qE).eval ρ =
      let sC := simFullDec (sE.eval ρ)
      (sC.base.stopped || sC.base.mir.win || !(sC.base.mir.corrAllowed P) ||
        CryptoGames.Ratchet.LibsignalSim.inReceiveOnlyEpoch sC.base.mir P ||
        !(CryptoGames.SM.noAliceCorrWhileAliceBelowEpoch10 sC.base.mir P)) := by
  set sC := simFullDec (sE.eval ρ)
  have hmir : (sE.eval ρ).1.1 = simMirEnc sC.base.mir := (simMirEnc_simMirDec _).symm
  have hst : (sE.eval ρ).1.2.2.2.2.2.2.2 = sC.base.stopped := by
    rcases hv : sE.eval ρ with ⟨⟨_, _, _, _, _, _, _, _⟩, _⟩
    simp [sC, hv, simFullDec, simBaseDec]
  have hwin : (sE.eval ρ).1.1.2.1 = sC.base.mir.win := by
    rcases hv : sE.eval ρ with ⟨⟨⟨_, _, _⟩, _⟩, _⟩
    simp [sC, hv, simFullDec, simBaseDec, simMirDec]
  dsimp only [corrBlockedE]
  rw [eval_eLet]
  simp only [orE_eval, ReductionDsl.Expr.eval, scBase, ssMir, ssStopped, mWin, ReductionDsl.Expr.v0, ReductionDsl.Env.get]
  rw [mCorrAllowedFastE_eval q _ _ _ sC.base.mir P
      hBound.base.trans_le hBound.base.chall_le hBound.base.comp_le
      (by simpa [ReductionDsl.Expr.eval, scBase, ssMir, ReductionDsl.Expr.v0, ReductionDsl.Env.get] using hmir)
      (by simpa [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get] using hq),
    mInWinE_eval _ _ _ sC.base.mir P
      (by simpa [ReductionDsl.Expr.eval, scBase, ssMir, ReductionDsl.Expr.v0, ReductionDsl.Env.get] using hmir)
      (by simpa [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get] using hq),
    mNoSpkCorrE_eval _ _ _ sC.base.mir P
      (by simpa [ReductionDsl.Expr.eval, scBase, ssMir, ReductionDsl.Expr.v0, ReductionDsl.Env.get] using hmir)
      (by simpa [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get] using hq),
    hst, hwin]
  simp only [Bool.or_assoc]

private def corrChainsAfter (encT : Pt → PublicKey) (Dh : DHFun (BitVec 256) Pt)
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ) (P : Party) (fig8st : Fig8St Pt) :
    Party → List CryptoGames.Ratchet.LibsignalSim.GhostChain :=
  if P == CryptoGames.Party.B && sC.base.mir.epoch CryptoGames.Party.B == 0 then
    match fig8st.γ with
    | .exp x => Function.update sC.base.chains CryptoGames.Party.A
        ((sC.base.chains CryptoGames.Party.A).map fun g =>
          if g.key.isNone then { g with key := some (encT (Dh.dh x Dh.base)) } else g)
    | _ => sC.base.chains
  else sC.base.chains

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem corrChainsAfter_bounds (encT : Pt → PublicKey) (Dh : DHFun (BitVec 256) Pt)
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ) (P R : Party) (fig8st : Fig8St Pt)
    (hch : ∀ Q, (sC.base.chains Q).length ≤ 5 ∧ ∀ g ∈ sC.base.chains Q, g.skipped.length ≤ 2000) :
    ((corrChainsAfter encT Dh sC P fig8st R).length ≤ 5) ∧
      (∀ g ∈ corrChainsAfter encT Dh sC P fig8st R, g.skipped.length ≤ 2000) := by
  unfold corrChainsAfter
  split_ifs with hcond
  · cases fig8st.γ with
    | pub _ => exact hch R
    | exp x =>
      cases R with
      | B => simpa [Function.update] using hch .B
      | A =>
        simp only [Function.update_self, List.length_map, List.mem_map]
        refine ⟨(hch .A).1, ?_⟩
        rintro g ⟨g0, hg0, rfl⟩
        by_cases hk : g0.key.isNone <;> simp [hk, (hch .A).2 g0 hg0]
  · exact hch R

omit [SampleableType Pt] in
private theorem corrChainsUpdE_eval {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ (simFullT ℓ Pt)) (qE : Expr AOps Γ .bool)
    (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt)))
    (ρ : Env Γ) (P : Party) (fig8st : Fig8St Pt)
    (hq : qE.eval ρ = partyEnc P) (hst : stE.eval ρ = fig8StV fig8st)
    (hchA : ((simFullDec (sE.eval ρ)).base.chains .A).length ≤ 5) :
    (corrChainsUpdE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) sE qE stE).eval ρ =
      ((corrChainsAfter encT Dh (simFullDec (sE.eval ρ)) P fig8st .A).map ghostChainEnc,
       (corrChainsAfter encT Dh (simFullDec (sE.eval ρ)) P fig8st .B).map ghostChainEnc) := by
  rcases hv : sE.eval ρ with
    ⟨⟨mirV, pqAB, pnAB, unackA, honestV, ⟨chainsAV, chainsBV⟩, amb, stopped⟩, keptAB, sentV, snapsV⟩
  have hgRound : (ghostChainEnc (ℓ := ℓ) (Pt := Pt) ∘ ghostChainDec) = id :=
    funext ghostChainEnc_ghostChainDec
  have hencA : (chainsAV.map (ghostChainDec (ℓ := ℓ) (Pt := Pt))).map ghostChainEnc = chainsAV := by
    simp only [List.map_map, hgRound, List.map_id]
  have hencB : (chainsBV.map (ghostChainDec (ℓ := ℓ) (Pt := Pt))).map ghostChainEnc = chainsBV := by
    simp only [List.map_map, hgRound, List.map_id]
  have hmirB : (simMirDec (ℓ := ℓ) (Pt := Pt) mirV).epoch .B = mirV.2.2.1.2 := by
    rcases mirV with ⟨_, _, ⟨_, _⟩, _⟩; rfl
  have hlenA : (chainsAV.map (ghostChainDec (ℓ := ℓ) (Pt := Pt))).length ≤ 5 := by
    simpa [hv, simFullDec, simBaseDec] using hchA
  dsimp only [corrChainsUpdE]
  rw [eval_eLet]
  simp only [scBase, ssMir, ssChains, mEpoch, f8Gamma,
    ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Expr.eval, ReductionDsl.Env.get, hv, hq, hst, ← hmirB, isBobEp0_eq]
  unfold corrChainsAfter
  simp only [simFullDec, simBaseDec]
  by_cases hcond : (P == CryptoGames.Party.B && (simMirDec (ℓ := ℓ) (Pt := Pt) mirV).epoch .B == 0) = true
  · simp only [hcond, ↓reduceIte]
    cases hγ : fig8st.γ with
    | pub T =>
      simp [fig8StV, hγ, ckaStV, hencA, hencB]
    | exp x =>
      simp only [fig8StV, hγ, ckaStV]
      rw [eval_revealSpkChainsE _ _ _ (chainsAV.map (ghostChainDec (ℓ := ℓ) (Pt := Pt)))
        (by simp [ReductionDsl.Expr.eval, hencA]) hlenA]
      simp [eval_sOpPtEnc, eval_sOpGrp, ReductionDsl.AtomicGroupOp.eval, ReductionDsl.Expr.eval, Function.update,
        List.map_map, hencB]
  · simp only [Bool.not_eq_true] at hcond
    simp [hcond, hencA, hencB]

omit [SampleableType Pt] in
private theorem corrSomeOutE_eval {Γ : List (Ty ASig)} (idA idB : IdentityKey) (q : ℕ)
    (sE : Expr AOps Γ (simFullT ℓ Pt)) (qE : Expr AOps Γ .bool)
    (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt)))
    (ρ : Env Γ) (P : Party) (fig8st : Fig8St Pt)
    (hq : qE.eval ρ = partyEnc P) (hst : stE.eval ρ = fig8StV fig8st)
    (hBound : SimCStateBounded q (simFullDec (sE.eval ρ)))
    (hExtra : SanSnapExtra C K (simFullDec (sE.eval ρ))) :
    Prod.map ((e2eSessionCodec ℓ Pt).rdec (.inr P)) simFullDec
      ((corrSomeOutE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB q sE qE stE).eval ρ) =
      let sC := simFullDec (sE.eval ρ)
      let chains' := corrChainsAfter encT Dh sC P fig8st
      let base' := { sC.base with
        mir := Computational.Proofs.GameHop.CompDedup.afterCorrDedup sC.base.mir P,
        chains := chains' }
      let ghostOut := CryptoGames.Ratchet.LibsignalSim.toGhost (paramsV1 C K idA idB)
        { sC.base with chains := chains' } P (fig8StTruncSkB (25000 * q) fig8st)
      (some ghostOut,
       { base := base'
         kept := Function.update sC.kept P (CryptoGames.Ratchet.LibsignalSimC.Kept.ofSt fig8st)
         sent := sC.sent
         snaps := (P, sC.base.mir.epoch P, ghostOut) :: sC.snaps }) := by
  set sC := simFullDec (sE.eval ρ)
  set chains' := corrChainsAfter encT Dh sC P fig8st
  have hchUpd :
      (corrChainsUpdE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam)
        (.fst (.v0 : Expr AOps
          (ReductionDsl.Ty.prod (simFullT ℓ Pt) (.prod .bool (fig8StT (ℓ := ℓ) (Pt := Pt))) :: Γ) _))
        (.fst (.snd .v0)) (.snd (.snd .v0))).eval
        (.cons (sE.eval ρ, (qE.eval ρ, stE.eval ρ)) ρ) =
      ((chains' .A).map ghostChainEnc, (chains' .B).map ghostChainEnc) :=
    corrChainsUpdE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) _ _ _ _ P fig8st hq hst hBound.base.chainsA_le
  have hcb := corrChainsAfter_bounds encT Dh sC P P fig8st hExtra.2.1
  have hmirEnc : (sE.eval ρ).1.1 = simMirEnc sC.base.mir := (simMirEnc_simMirDec _).symm
  have hbaseGhost :
      (let b1 := scBase (.fst (.v1 : Expr AOps
        (ReductionDsl.Ty.prod (.list (ghostChainT ℓ Pt)) (.list (ghostChainT ℓ Pt)) ::
          ReductionDsl.Ty.prod (simFullT ℓ Pt) (.prod .bool (fig8StT (ℓ := ℓ) (Pt := Pt))) :: Γ) _))
       ssMk (ssMir b1) (ssPq b1) (ssPn b1) (ssUnackA b1) .nil .v0 (ssAmb b1) (ssStopped b1)).eval
        (.cons ((chains' .A).map ghostChainEnc, (chains' .B).map ghostChainEnc)
          (.cons (sE.eval ρ, (qE.eval ρ, stE.eval ρ)) ρ)) =
      simBaseEnc { sC.base with honest := [], chains := chains' } := by
    rcases hv : sE.eval ρ with
      ⟨⟨mirV, ⟨pqA, pqB⟩, ⟨pnA, pnB⟩, unackA, honestV, ⟨chainsAV, chainsBV⟩, amb, stopped⟩,
        keptAB, sentV, snapsV⟩
    simp [sC, hv, simFullDec, simBaseDec, simBaseEnc, simMirEnc_simMirDec,
      scBase, ssMk, ssMir, ssPq, ssPn, ssUnackA, ssAmb, ssStopped, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Expr.eval]
  dsimp only [corrSomeOutE]
  rw [eval_eLet, eval_eLet]
  dsimp only [ReductionDsl.Expr.eval]
  rw [hchUpd, eval_eLet, eval_toGhostE idA idB (25000 * q) _ _ _ _
    { sC.base with honest := [], chains := chains' } P fig8st
    hbaseGhost hq hst hcb.1 hcb.2]
  let Γs2 : List (Ty ASig) :=
    GhostStT (ℓ := ℓ) (Pt := Pt) ::
      ReductionDsl.Ty.prod (.list (ghostChainT ℓ Pt)) (.list (ghostChainT ℓ Pt)) ::
      ReductionDsl.Ty.prod (simFullT ℓ Pt) (.prod .bool (fig8StT (ℓ := ℓ) (Pt := Pt))) :: Γ
  let ρs2 : Env Γs2 :=
    .cons (CryptoGames.Ratchet.LibsignalSim.toGhost (paramsV1 C K idA idB)
        { sC.base with honest := [], chains := chains' } P (fig8StTruncSk (25000 * q) fig8st))
      (.cons ((chains' .A).map ghostChainEnc, (chains' .B).map ghostChainEnc)
        (.cons (sE.eval ρ, (qE.eval ρ, stE.eval ρ)) ρ))
  have hmc := mAfterCorrFastE_eval (ℓ := ℓ) (Pt := Pt) (O' := AOps) q
    (ssMir (scBase (.fst (.v2 : Expr AOps Γs2 _)))) (.fst (.snd .v2))
    ρs2 sC.base.mir P hBound.base.trans_le hBound.base.comp_u
    (by simpa [Γs2, ρs2, ssMir, scBase, ReductionDsl.Expr.v2, ReductionDsl.Expr.eval, ReductionDsl.Env.get] using hmirEnc) hq
  have hkp := keptOfStAtomicE_eval (ℓ := ℓ) (Pt := Pt) (O' := AOps)
    (.snd (.snd (.v2 : Expr AOps Γs2 _))) ρs2 fig8st hst
  dsimp only [Γs2, ρs2, Prod.map, e2eSessionCodec, smRdec, ReductionDsl.Expr.eval, scMk, ssMk, scBase, scKept,
    scSent, scSnaps, ssMir, ssPq, ssPn, ssUnackA, ssHonest, ssAmb, ssStopped, mEpoch,
    ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Expr.v2, ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ] at hmc hkp ⊢
  rw [hmc, hkp]
  refine Prod.ext rfl ?_
  dsimp only [sC, simFullDec, simBaseDec]
  rw [simMirDec_simMirEnc]
  have hgc : (ghostChainDec (ℓ := ℓ) (Pt := Pt) ∘ ghostChainEnc) = id := by
    funext g; exact ghostChainDec_ghostChainEnc g
  congr 1
  · congr 1
    funext R; cases R <;> simp only [List.map_map, hgc, List.map_id] <;> rfl
  · funext R; cases P <;> cases R <;> simp [hq, Function.update, partyEnc]
  · cases P <;> (rw [hq]; rfl)

omit [DecidableEq Pt] [Zero Pt] in
private theorem comp_eval_query_cr {O' : Ops ASig} {Γ : List (Ty ASig)}
    (e : Expr O' Γ .bool) (ρ : Env Γ) (P : Party) (he : e.eval ρ = partyEnc P) :
    (ReductionDsl.Comp.query (I := fig8SmIface ℓ Pt) ReductionDsl.SMTag.cr e).eval ρ =
      (fun r => r.map fig8StV) <$>
        CryptoGames.SM.corrQuery (St := Fig8St Pt)
          (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt) P := by
  have hb : ReductionDsl.boolToParty (partyEnc P) = P := by cases P <;> rfl
  dsimp only [ReductionDsl.Comp.eval, fig8SmIface]
  rw [he, hb]
  rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem comp_eval_ite_eq {O' : Ops ASig} {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} {a : Ty ASig} (cond : Expr O' Γ .bool) (t e : Comp O' I Γ a)
    (ρ : Env Γ) (b : Bool) (hb : cond.eval ρ = b) :
    (ReductionDsl.Comp.ite cond t e).eval ρ = (if b then t.eval ρ else e.eval ρ) := by
  rw [comp_eval_ite, hb]

theorem simFig8StepCorrBody_eval {Γ : List (Ty ASig)} (idA idB : IdentityKey) (qep q : ℕ)
    (sE : Expr AOps Γ (simFullT ℓ Pt)) (qE : Expr AOps Γ .bool)
    (ρ : Env Γ) (P : Party) (_hℓ : ℓ < 10 ^ 6)
    (hq : qE.eval ρ = partyEnc P)
    (hBound : SimCStateBounded q (simFullDec (sE.eval ρ)))
    (hExtra : SanSnapExtra C K (simFullDec (sE.eval ρ))) :
    (Prod.map ((e2eSessionCodec ℓ Pt).rdec (.inr P)) simFullDec <$>
      (simFig8StepCorrBody (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB q sE qE).eval ρ) =
    ((simFig8OracleSan (paramsV1 C K idA idB) Dh encPt encT decT lam qep
      (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (25000 * q)
      (.inr (.inr P))).run (simFullDec (sE.eval ρ))) := by
  set sC := simFullDec (sE.eval ρ)
  let Γ0 : List (Ty ASig) := ReductionDsl.Ty.prod (simFullT ℓ Pt) .bool :: Γ
  let Γ2 : List (Ty ASig) :=
    fig8StT (ℓ := ℓ) (Pt := Pt) :: ReductionDsl.Ty.opt (fig8StT (ℓ := ℓ) (Pt := Pt)) :: Γ0
  let ρ0 : Env Γ0 := ReductionDsl.Env.cons ((ReductionDsl.Expr.pair sE qE).eval ρ) ρ
  have hblk :
      (corrBlockedE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) q
        (.fst (.var (.zero : Var Γ0 _))) (.snd (.var .zero))).eval ρ0 =
      (sC.base.stopped || sC.base.mir.win || !(sC.base.mir.corrAllowed P) ||
        CryptoGames.Ratchet.LibsignalSim.inReceiveOnlyEpoch sC.base.mir P ||
        !(CryptoGames.SM.noAliceCorrWhileAliceBelowEpoch10 sC.base.mir P)) :=
    corrBlockedE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) q _ _ ρ0 P hq hBound
  dsimp only [simFig8StepCorrBody]
  rw [comp_eval_bind_ret, comp_eval_ite_eq _ _ _ ρ0 _ hblk]
  dsimp only [simFig8OracleSan, StateT.run, StateT.mk, semHandleHookDedupS, semCorrHookTGB]
  by_cases hcond : (sC.base.stopped || sC.base.mir.win || !(sC.base.mir.corrAllowed P) ||
      CryptoGames.Ratchet.LibsignalSim.inReceiveOnlyEpoch sC.base.mir P ||
      !(CryptoGames.SM.noAliceCorrWhileAliceBelowEpoch10 sC.base.mir P)) = true
  · simp only [hcond, ↓reduceIte]
    rw [comp_eval_ret, map_pure, map_pure]
    rfl
  · simp only [Bool.not_eq_true] at hcond
    simp only [hcond, Bool.false_eq_true, ↓reduceIte]
    rw [comp_eval_bind, comp_eval_query_cr (.snd (.var (.zero : Var Γ0 _))) ρ0 P
      (by simpa [Γ0, ρ0, ReductionDsl.Expr.eval, ReductionDsl.Env.get_cons_zero] using hq)]
    dsimp only [fig8IdSemHook]
    simp only [map_eq_bind_pure_comp, bind_assoc]
    congr 1; funext res
    cases res with
    | none =>
      simp only [Function.comp_apply, Option.map, pure_bind]
      rw [comp_eval_caseOpt]
      dsimp only [ReductionDsl.Expr.eval, ReductionDsl.Env.get_cons_zero]
      rw [comp_eval_ret]
      simp only [pure_bind, Function.comp_apply]
      dsimp only [Γ0, ρ0, ReductionDsl.Expr.eval, ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ]
      rfl
    | some fig8st =>
      simp only [Function.comp_apply, Option.map, pure_bind]
      rw [comp_eval_caseOpt]
      dsimp only [ReductionDsl.Expr.eval, ReductionDsl.Env.get_cons_zero]
      rw [comp_eval_ret]
      simp only [pure_bind, Function.comp_apply]
      congr 1
      let ρ2 : Env Γ2 := .cons (fig8StV fig8st) (.cons (some (fig8StV fig8st)) ρ0)
      have hsome := corrSomeOutE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) idA idB q
        (.fst (.var (.succ (.succ (.zero : Var Γ0 _)) : Var Γ2 _)))
        (.snd (.var (.succ (.succ .zero)))) (.var .zero)
        ρ2 P fig8st
        (by simpa [Γ0, Γ2, ρ0, ρ2, ReductionDsl.Expr.eval, ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ] using hq)
        rfl
        (by simpa [Γ0, Γ2, ρ0, ρ2, ReductionDsl.Expr.eval, ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ] using hBound)
        (by simpa [Γ0, Γ2, ρ0, ρ2, ReductionDsl.Expr.eval, ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ] using hExtra)
      exact hsome.trans (by
        dsimp only [Γ0, Γ2, ρ0, ρ2, ReductionDsl.Expr.eval, ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ]
        rfl)

theorem simFig8StepCorrC_queries (idA idB : IdentityKey) (q : ℕ) :
    (simFig8StepCorrC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) idA idB q).queries
      (fun _ => 1) (fun _ => 0) ≤ 1 :=
  Nat.le_refl 1

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem caseSum4_cost_le {O' : Ops ASig} {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} {a1 a2 a3 a4 b4 τ : Ty ASig}
    (v1 : Var Γ (.sum a1 (.sum a2 (.sum a3 (.sum a4 b4)))))
    (c1 : Comp O' I (a1 :: Γ) τ)
    (c2 : Comp O' I (a2 :: .sum a2 (.sum a3 (.sum a4 b4)) :: Γ) τ)
    (c3 : Comp O' I (a3 :: .sum a3 (.sum a4 b4) :: .sum a2 (.sum a3 (.sum a4 b4)) :: Γ) τ)
    (c4 : Comp O' I (a4 :: .sum a4 b4 :: .sum a3 (.sum a4 b4) ::
      .sum a2 (.sum a3 (.sum a4 b4)) :: Γ) τ)
    (c5 : Comp O' I (b4 :: .sum a4 b4 :: .sum a3 (.sum a4 b4) ::
      .sum a2 (.sum a3 (.sum a4 b4)) :: Γ) τ) :
    (ReductionDsl.Comp.caseSum (.var v1) c1
      (.caseSum (.var .zero) c2
        (.caseSum (.var .zero) c3
          (.caseSum (.var .zero) c4 c5)))).cost ≤
      c1.cost + c2.cost + c3.cost + c4.cost + c5.cost + 8 := by
  dsimp only [ReductionDsl.Comp.cost, ReductionDsl.Expr.cost]
  omega

theorem simFig8StepCorrC_cost (idA idB : IdentityKey) (q : ℕ) (hℓ : ℓ < 10 ^ 6) :
    (simFig8StepCorrC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) idA idB q).cost ≤
      2000100 + 25100000 * q := by
  let Ttr : Ty ASig := .prod .bool (.prod PlainT (.opt ReductionDsl.BV512))
  let Tch : Ty ASig := .prod .bool (.prod PlainT (.prod PlainT (.opt ReductionDsl.BV512)))
  let Tdl : Ty ASig := .prod .bool (B 32)
  let Γbase : List (Ty ASig) := [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
  let Γr1 : List (Ty ASig) := .sum Tch (.sum Tdl (.sum Tdl .bool)) :: Γbase
  let Γr2 : List (Ty ASig) := .sum Tdl (.sum Tdl .bool) :: Γr1
  let Γr3 : List (Ty ASig) := .sum Tdl .bool :: Γr2
  let Γr4 : List (Ty ASig) := .bool :: Γr3
  have hn1 := corrNoneReplyE_cost (ℓ := ℓ) (Pt := Pt) (O' := AOps) (Γ := Ttr :: Γbase)
  have hn2 := corrNoneReplyE_cost (ℓ := ℓ) (Pt := Pt) (O' := AOps) (Γ := Tch :: Γr1)
  have hn3 := corrNoneReplyE_cost (ℓ := ℓ) (Pt := Pt) (O' := AOps) (Γ := Tdl :: Γr2)
  have hn4 := corrNoneReplyE_cost (ℓ := ℓ) (Pt := Pt) (O' := AOps) (Γ := Tdl :: Γr3)
  have hb := simFig8StepCorrBody_cost (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    (Γ := Γr4) idA idB q (.var (.succ (.succ (.succ (.succ .zero))))) (.var .zero) hℓ
  dsimp only [simFig8StepCorrC]
  refine Nat.le_trans (caseSum4_cost_le (O' := AOps) (I := fig8SmIface ℓ Pt)
    (Γ := Γbase) (.succ .zero) _ _ _ _ _) ?_
  dsimp only [Ttr, Tch, Tdl, Γbase, Γr1, Γr2, Γr3, Γr4] at hn1 hn2 hn3 hn4 hb ⊢
  dsimp only [ReductionDsl.Comp.cost, ReductionDsl.Expr.cost] at hb ⊢
  omega

theorem simFig8StepCorrC_descBits_le (idA idB : IdentityKey) (q : ℕ) (hℓ : ℓ < 10 ^ 6) :
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
      (simFig8StepCorrC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) idA idB q) ≤
      132000 + 128 * bits (q + 1) := by
  let Ttr : Ty ASig := .prod .bool (.prod PlainT (.opt ReductionDsl.BV512))
  let Tch : Ty ASig := .prod .bool (.prod PlainT (.prod PlainT (.opt ReductionDsl.BV512)))
  let Tdl : Ty ASig := .prod .bool (B 32)
  let Γbase : List (Ty ASig) := [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
  let Γr1 : List (Ty ASig) := .sum Tch (.sum Tdl (.sum Tdl .bool)) :: Γbase
  let Γr2 : List (Ty ASig) := .sum Tdl (.sum Tdl .bool) :: Γr1
  let Γr3 : List (Ty ASig) := .sum Tdl .bool :: Γr2
  let Γr4 : List (Ty ASig) := .bool :: Γr3
  have hn1 := corrNoneReplyE_descBits_le (ℓ := ℓ) (Pt := Pt) (O' := AOps)
    atomicSessionOpDescBits (Γ := Ttr :: Γbase)
  have hn2 := corrNoneReplyE_descBits_le (ℓ := ℓ) (Pt := Pt) (O' := AOps)
    atomicSessionOpDescBits (Γ := Tch :: Γr1)
  have hn3 := corrNoneReplyE_descBits_le (ℓ := ℓ) (Pt := Pt) (O' := AOps)
    atomicSessionOpDescBits (Γ := Tdl :: Γr2)
  have hn4 := corrNoneReplyE_descBits_le (ℓ := ℓ) (Pt := Pt) (O' := AOps)
    atomicSessionOpDescBits (Γ := Tdl :: Γr3)
  have hbody := simFig8StepCorrBody_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    (Γ := Γr4) idA idB q (.var (.succ (.succ (.succ (.succ .zero))))) (.var .zero) hℓ
  have hv0 : bits 0 = 1 := hb0_bits
  have hv1 : bits (0 + 1) = 1 := hb1_bits
  have hv2 : bits (0 + 1 + 1) = 2 := hb2_bits
  have hv3 : bits (0 + 1 + 1 + 1) = 2 := hb3_bits
  have hv4 : bits (0 + 1 + 1 + 1 + 1) = 3 := hb4_bits
  dsimp only [Ttr, Tch, Tdl, Γbase, Γr1, Γr2, Γr3, Γr4] at hn1 hn2 hn3 hn4 hbody
  dsimp only [atomicExprDescBits, varIdx] at hbody
  dsimp only [simFig8StepCorrC, atomicCompDescBits, atomicExprDescBits, varIdx]
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem caseSum4_inr_eval {O' : Ops ASig} {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {σ a1 a2 a3 a4 b4 τ : Ty ASig}
    (c1 : Comp O' I (a1 :: [σ, .sum a1 (.sum a2 (.sum a3 (.sum a4 b4)))]) τ)
    (c2 : Comp O' I (a2 :: .sum a2 (.sum a3 (.sum a4 b4)) ::
      [σ, .sum a1 (.sum a2 (.sum a3 (.sum a4 b4)))]) τ)
    (c3 : Comp O' I (a3 :: .sum a3 (.sum a4 b4) :: .sum a2 (.sum a3 (.sum a4 b4)) ::
      [σ, .sum a1 (.sum a2 (.sum a3 (.sum a4 b4)))]) τ)
    (c4 : Comp O' I (a4 :: .sum a4 b4 :: .sum a3 (.sum a4 b4) ::
      .sum a2 (.sum a3 (.sum a4 b4)) :: [σ, .sum a1 (.sum a2 (.sum a3 (.sum a4 b4)))]) τ)
    (c5 : Comp O' I (b4 :: .sum a4 b4 :: .sum a3 (.sum a4 b4) ::
      .sum a2 (.sum a3 (.sum a4 b4)) :: [σ, .sum a1 (.sum a2 (.sum a3 (.sum a4 b4)))]) τ)
    (s : σ.denote) (x : b4.denote) :
    (ReductionDsl.Comp.caseSum (.var (.succ .zero)) c1
      (.caseSum (.var .zero) c2
        (.caseSum (.var .zero) c3
          (.caseSum (.var .zero) c4 c5)))).eval
      (.cons s (.cons (.inr (.inr (.inr (.inr x)))) .nil)) =
    c5.eval (.cons x (.cons (.inr x) (.cons (.inr (.inr x))
      (.cons (.inr (.inr (.inr x)))
        (.cons s (.cons (.inr (.inr (.inr (.inr x)))) .nil)))))) := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem map_bind_rdec_simFullDec {ι : Type} {T : OracleSpec ι} {α β γ δ : Type}
    (m : OracleComp T (α × β)) (f : α → γ) (g : β → δ) :
    (Prod.map id g <$> (m >>= fun p => pure (f p.1, p.2))) =
      (Prod.map f g <$> m) := by
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, Prod.map, id_eq]

theorem simFig8StepCorrC_run (idA idB : IdentityKey) (qep q : ℕ) (hℓ : ℓ < 10 ^ 6)
    (P : Party) (s_raw : (simFullT ℓ Pt).denote)
    (hBound : SimCStateBounded q (simFullDec s_raw))
    (hExtra : SanSnapExtra C K (simFullDec s_raw)) :
    (Prod.map id simFullDec <$>
      ((handlerImpl (C := e2eSessionCodec ℓ Pt)
        (simFig8StepCorrC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q)
        (.inr (.inr P))).run s_raw)) =
    ((simFig8OracleSan (paramsV1 C K idA idB) Dh encPt encT decT lam qep
      (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (25000 * q)
      (.inr (.inr P))).run (simFullDec s_raw)) := by
  dsimp only [handlerImpl, StateT.run, StateT.mk, id_eq, e2eSessionCodec, smQenc, simFig8StepCorrC]
  rw [caseSum4_inr_eval, map_bind_rdec_simFullDec]
  exact simFig8StepCorrBody_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB qep q
    (.var (.succ (.succ (.succ (.succ .zero))))) (.var .zero) _ P hℓ
    (by cases P <;> rfl) hBound hExtra

end StepCorr

end Computational.Proofs.Game.PromotedCostedReds.SimFig8StepCorr

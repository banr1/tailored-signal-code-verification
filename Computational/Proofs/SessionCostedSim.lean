/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.Ratchet.LibsignalSim
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalBound
import Computational.Proofs.SessionCostedBase
import Computational.Proofs.ReductionDsl.Bridge
import Computational.Proofs.ReductionDsl.Notation
import Computational.Proofs.ReductionDsl.Size
import Computational.Proofs.ReductionDsl.SizeBudgetBridge
import Computational.Proofs.GameHop.ReductionDsl.CostUB

/-!
# Costed `LibsignalSim` Reduction Witness

Constructs `simProgFast` and `simProgInst` (`Refine.SimProg`) with linear `O(q)` step cost and
quadratic `O(q^2)` total cost within `ratchetCostBudget`, replacing cubic nested list scans in
`LibsignalSim.simProg` with single-pass table scans.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalSession

open OracleComp OracleSpec CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst
  LibsignalSession HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme
  WireAEAD FSAEAD

section SimCosted

variable {Pt : Type} [DecidableEq Pt] [Zero Pt]

local instance instInhabitedPtSim : Inhabited Pt := ⟨0⟩

section SimFastDefs

open ReductionDsl Computational.Proofs.ReductionDsl.Notation

private abbrev compTblTy {S0 : Sig} : Ty S0 :=
  .prod (.tbl (.tbl .bool)) (.tbl (.tbl .bool))

private def compTblEmptyE {S0 : Sig} {O' : Ops S0} {Γ} :
    Expr O' Γ compTblTy :=
  .pair (.tconst (.tconst (.bool false))) (.tconst (.tconst (.bool false)))

private def compTblInsertE {S0 : Sig} {O' : Ops S0} {Γ}
    (m : Expr O' Γ compTblTy) (pos : Expr O' Γ SM.posTy) :
    Expr O' Γ compTblTy :=
  .letE (.pair m pos)
    (let m0 : Expr O' _ compTblTy := .fst .v0
     let pos0 : Expr O' _ SM.posTy := .snd .v0
     let sub := SM.pGet m0 (SM.posSender pos0)
     let row := .tget sub (SM.posEpoch pos0)
     SM.pSet m0 (SM.posSender pos0)
       (.tset sub (SM.posEpoch pos0) (.tset row (SM.posIdx pos0) (.bool true))))

private def compTblGetE {S0 : Sig} {O' : Ops S0} {Γ}
    (m : Expr O' Γ compTblTy) (pos : Expr O' Γ SM.posTy) :
    Expr O' Γ .bool :=
  .letE (.pair m pos)
    (let m0 : Expr O' _ compTblTy := .fst .v0
     let pos0 : Expr O' _ SM.posTy := .snd .v0
     .tget (.tget (SM.pGet m0 (SM.posSender pos0)) (SM.posEpoch pos0)) (SM.posIdx pos0))

private def compTblOfListE {S0 : Sig} {O' : Ops S0} {Γ}
    (K : ℕ) (xs : Expr O' Γ (.list SM.posTy)) :
    Expr O' Γ compTblTy :=
  .foldrB K xs compTblEmptyE (compTblInsertE .v1 .v0)

variable {PQ PQC : Type} [SampleableType PQC] {ℓ : ℕ}
variable (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)

local notation "S" => LibsignalSim.simSig PQ PQC Pt ℓ
local notation "OO" => LibsignalSim.simOps (ℓ := ℓ) P Dh encT decT
local notation "SIface" => LibsignalSim.simIface PQ PQC Pt ℓ

private def mCorrAllowedFastE {restT : Ty S}
    {O' : Ops S} {Γ} (K : ℕ)
    (s : Expr O' Γ (LibsignalSim.mirTy (.prod SM.posTy restT)))
    (p : Expr O' Γ .bool) : Expr O' Γ .bool :=
  .letE (.pair s p)
    (let s0 : Expr O' _ (LibsignalSim.mirTy (.prod SM.posTy restT)) := .fst .v0
     .letE (compTblOfListE K (LibsignalSim.mComp s0))
       (.and
         (.not (.anyB K (LibsignalSim.mChall (.fst .v1))
           (SM.boolEq (SM.posSender .v0) (SM.otherE (.snd .v2)))))
         (.not (.anyB K (LibsignalSim.mTrans (.fst .v1))
           (.and (SM.boolEq (SM.posSender (.fst .v0)) (SM.otherE (.snd .v2)))
             (.not (compTblGetE .v1 (.fst .v0))))))))

private def mAfterCorrFastE {restT : Ty S}
    {O' : Ops S} {Γ} (K : ℕ)
    (s : Expr O' Γ (LibsignalSim.mirTy (.prod SM.posTy restT)))
    (p : Expr O' Γ .bool) :
    Expr O' Γ (LibsignalSim.mirTy (.prod SM.posTy restT)) :=
  .letE (.pair s p)
    (let s0 : Expr O' _ (LibsignalSim.mirTy (.prod SM.posTy restT)) := .fst .v0
     let initAcc : Expr O' _ (.prod (.list SM.posTy) compTblTy) :=
       .pair (LibsignalSim.mComp s0) (compTblOfListE K (LibsignalSim.mComp s0))
     .letE
       (.fst (.foldrB K (LibsignalSim.mTrans s0) initAcc
         (.ite (.and (SM.boolEq (SM.posSender (.fst .v0)) (SM.otherE (.snd .v2)))
                     (.not (compTblGetE (.snd .v1) (.fst .v0))))
           (.pair (.cons (.fst .v0) (.fst .v1)) (compTblInsertE (.snd .v1) (.fst .v0)))
           .v1)))
       (let s0' : Expr O' _ (LibsignalSim.mirTy (.prod SM.posTy restT)) := .fst .v1
        let p0' : Expr O' _ .bool := .snd .v1
        let s1 : Expr O' _ (LibsignalSim.mirTy (.prod SM.posTy restT)) :=
          LibsignalSim.mMk (LibsignalSim.mB s0') (LibsignalSim.mWin s0')
            (LibsignalSim.mEpoch s0') (LibsignalSim.mIdx s0') (LibsignalSim.mTL s0')
            (LibsignalSim.mTrans s0') (LibsignalSim.mChall s0') .v0
            (LibsignalSim.mMaxAcc s0') (LibsignalSim.mLeaks s0') (LibsignalSim.mCorrs s0')
        let s2 : Expr O' _ (LibsignalSim.mirTy (.prod SM.posTy restT)) :=
          LibsignalSim.mLeakE s1
            (SM.maxN (.fst (LibsignalSim.mEpoch s0')) (.snd (LibsignalSim.mEpoch s0')))
        LibsignalSim.mMk (LibsignalSim.mB s2) (LibsignalSim.mWin s2) (LibsignalSim.mEpoch s2)
          (LibsignalSim.mIdx s2) (LibsignalSim.mTL s2) (LibsignalSim.mTrans s2)
          (LibsignalSim.mChall s2) (LibsignalSim.mComp s2) (LibsignalSim.mMaxAcc s2)
          (LibsignalSim.mLeaks s2)
          (.cons (.pair p0' (SM.pGet (LibsignalSim.mEpoch s0') p0')) (LibsignalSim.mCorrs s2))))

private def inTFastE (K : ℕ) {Γ}
    (s : Expr OO Γ LibsignalSim.simStateTy) (qParty : Expr OO Γ .bool)
    (c : Expr OO Γ (LibsignalSim.fig8CTy PQ PQC Pt ℓ)) : Expr OO Γ .bool :=
  .letE (.pair s (.pair qParty c))
    (let s0 : Expr OO _ LibsignalSim.simStateTy := .fst .v0
     let qp0 : Expr OO _ .bool := .fst (.snd .v0)
     let c0 : Expr OO _ (LibsignalSim.fig8CTy PQ PQC Pt ℓ) := .snd (.snd .v0)
     .and
       (.anyB K (LibsignalSim.ssHonest s0)
         (.op (O := OO) LibsignalSim.SimOp.eqFig8C (.pair (.snd .v0) (.snd (.snd .v1)))))
       (SM.isSomeE
         (LibsignalSim.mInTransitE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
           K (LibsignalSim.ssMir s0) (SM.otherE qp0)
           (.op (O := OO) LibsignalSim.SimOp.toWire c0))))

private def fwdFastC (K : ℕ) {Γ}
    (s : Expr OO Γ LibsignalSim.simStateTy) (qParty : Expr OO Γ .bool)
    (c : Expr OO Γ (LibsignalSim.fig8CTy PQ PQC Pt ℓ)) :
    Comp OO SIface Γ (.opt (LibsignalSim.fig8RrTy PQ PQC Pt ℓ)) :=
  .ite (inTFastE P Dh encT decT K s qParty c)
    (.query (I := SIface) SM.SMTag.dl (.pair qParty c))
    (.query (I := SIface) SM.SMTag.ij (.pair qParty c))

private def simRecvNewChainNormalFastC (K qep : ℕ) {Γ} :
    Comp OO SIface
      (LibsignalSim.parsedRecvTy (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ) ::
        .prod LibsignalSim.simStateTy (.prod .bool (.prod (.base .wire) .bool)) :: Γ)
      (.prod (.opt (LibsignalSim.simRrTy PQ PQC Pt ℓ)) LibsignalSim.simStateTy) :=
  rdsl [(pq', (i0, (pk, (T?0, lct)))), (s1, (q1, (w1, del1)))] do
    let sAmb := LibsignalSim.sAmbE (P := P) (Dh := Dh) (encT := encT) (decT := decT) s1 q1
    if SM.orE (LibsignalSim.mInWinE (LibsignalSim.ssMir s1) q1)
        (SM.orE (25000 < i0 - 1) (SM.leN (nat (2 ^ 32)) i0)) then
      return (some (.inl ()), sAmb)
    else
      match T?0 with
      | none => return (some (.inl ()), sAmb)
      | some pt =>
        let hc := LibsignalSim.honestCE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
          K s1 q1 w1
        let epNext := SM.pGet (LibsignalSim.mEpoch (LibsignalSim.ssMir s1)) q1 + 1
        res ← fwdFastC P Dh encT decT K s1 q1
          (LibsignalSim.mkCE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
            hc lct epNext (some pt))
        return LibsignalSim.onAnswerE (P := P) (Dh := Dh) (encT := encT) (decT := decT) K qep
          sAmb q1 w1 del1 none pk pq' res

private def simRecvFastC (K qep : ℕ) {Γ}
    (s : Expr OO Γ LibsignalSim.simStateTy) (qParty : Expr OO Γ .bool)
    (w : Expr OO Γ (.base .wire)) (isDel : Expr OO Γ .bool) :
    Comp OO SIface Γ (.prod (.opt (LibsignalSim.simRrTy PQ PQC Pt ℓ)) LibsignalSim.simStateTy) :=
  rdsl do
    (s0, (q0, (w0, del0))) ← return (s, (qParty, (w, isDel)))
    let inTrOpt :=
      LibsignalSim.mInTransitE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
        K (LibsignalSim.ssMir s0) (SM.otherE q0) w0
    let refuse :=
      SM.orE (LibsignalSim.mWin (LibsignalSim.ssMir s0))
        (SM.orE (del0 && !(SM.isSomeE inTrOpt))
          ((!del0) &&
            (SM.orE (SM.isSomeE inTrOpt)
              (SM.orE (!(LibsignalSim.mSafeInjE (LibsignalSim.ssMir s0)))
                (!(Expr.op (O := OO) LibsignalSim.SimOp.injOK w0))))))
    if refuse then
      return (none, s0)
    else
      match LibsignalSim.parseRecvE (P := P) (Dh := Dh) (encT := encT) (decT := decT) (raw (2 ^ 32))
          (q0, (SM.pGet (LibsignalSim.ssPq s0) q0, w0)) with
      | none => return (some (.inl ()), s0)
      | some (pq', (i1, (pk0, (T?0, lct1)))) =>
        let hc := LibsignalSim.honestCE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
          K s0 q0 w0
        match LibsignalSim.findChainE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
            (SM.pGet (LibsignalSim.ssChains s0) q0, pk0) with
        | none =>
          if LibsignalSim.evictedHonestE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
              s0 q0 hc then
            return (some (.inl ()), s0)
          else if Expr.op (O := OO) LibsignalSim.SimOp.isZeroPt T?0 then
            return (some (.inl ()), s0)
          else
            raw (simRecvNewChainNormalFastC P Dh encT decT K qep)
        | some (ci1, g0) =>
          if Expr.op (O := OO) LibsignalSim.SimOp.chainRejects (g0.2.2, i1) then
            return (some (.inl ()), s0)
          else
            res ← fwdFastC P Dh encT decT K s0 q0
              (LibsignalSim.mkCE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
                hc lct1 g0.2.1 T?0)
            return LibsignalSim.onAnswerE (P := P) (Dh := Dh) (encT := encT) (decT := decT) K qep
              s0 q0 w0 del0 (some ci1) pk0 pq' res

private def simCorrFastC (K : ℕ) {Γ}
    (s : Expr OO Γ LibsignalSim.simStateTy) (qParty : Expr OO Γ .bool) :
    Comp OO SIface Γ (.prod (.opt (.base .ghostSt)) LibsignalSim.simStateTy) :=
  rdsl do
    (s0, q0) ← return (s, qParty)
    let refuse :=
      SM.orE (LibsignalSim.mWin (LibsignalSim.ssMir s0))
        (SM.orE (!(mCorrAllowedFastE K (LibsignalSim.ssMir s0) q0))
          (SM.orE (LibsignalSim.mInWinE (LibsignalSim.ssMir s0) q0)
            (!(LibsignalSim.mNoSpkCorrE (LibsignalSim.ssMir s0) q0))))
    if refuse then
      return (none, s0)
    else
      crOpt ← query (I := SIface) SM.SMTag.cr q0
      match crOpt with
      | none => return (none, s0)
      | some st =>
        let chains' :=
          if q0 && (LibsignalSim.mEpoch (LibsignalSim.ssMir s0)).2 == 0 then
            (LibsignalSim.revealSpkChainsE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
              ((LibsignalSim.ssChains s0).1, st),
             (LibsignalSim.ssChains s0).2)
          else
            LibsignalSim.ssChains s0
        let nextSt :=
          LibsignalSim.ssMk (mAfterCorrFastE K (LibsignalSim.ssMir s0) q0)
            (LibsignalSim.ssPq s0) (LibsignalSim.ssPn s0) (LibsignalSim.ssUnackA s0)
            (LibsignalSim.ssHonest s0) chains'
            (LibsignalSim.ssAmb s0) (LibsignalSim.ssStopped s0)
        let ghostOut :=
          LibsignalSim.toGhostE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
            (q0,
              (st,
                (SM.pGet (LibsignalSim.ssPn s0) q0,
                  (SM.pGet chains' q0,
                    (LibsignalSim.ssUnackA s0,
                      (SM.pGet (LibsignalSim.ssPq s0) q0,
                        SM.pGet (LibsignalSim.mEpoch (LibsignalSim.ssMir s0)) q0))))))
        return (some ghostOut, nextSt)

private def simHandleFastC (K qep : ℕ) :
    Comp OO SIface
      [LibsignalSim.simStateTy (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ),
       (LibsignalSim.simCodec PQ PQC Pt ℓ).Q]
      (.prod (LibsignalSim.simCodec PQ PQC Pt ℓ).R
        (LibsignalSim.simStateTy (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ))) :=
  rdsl [s, qry] do
    match qry with
    | .inl (.inl (.inl (.inl (qp, (m₀, r))))) =>
      (out, s') ← LibsignalSim.guardC (P := P) (Dh := Dh) (encT := encT) (decT := decT) s
        (LibsignalSim.simSendC (P := P) (Dh := Dh) (encT := encT) (decT := decT) qep s qp m₀ none r)
      return (.inl (.inl (.inl (.inl out))), s')
    | .inl (.inl (.inl (.inr (qp, (m₀, (m₁, r)))))) =>
      (out, s') ← LibsignalSim.guardC (P := P) (Dh := Dh) (encT := encT) (decT := decT) s
        (LibsignalSim.simSendC (P := P) (Dh := Dh) (encT := encT) (decT := decT)
          qep s qp m₀ (some m₁) r)
      return (.inl (.inl (.inl (.inr out))), s')
    | .inl (.inl (.inr (qp, w))) =>
      (out, s') ← LibsignalSim.guardC (P := P) (Dh := Dh) (encT := encT) (decT := decT) s
        (simRecvFastC P Dh encT decT K qep s qp w true)
      return (.inl (.inl (.inr out)), s')
    | .inl (.inr (qp, w)) =>
      (out, s') ← LibsignalSim.guardC (P := P) (Dh := Dh) (encT := encT) (decT := decT) s
        (simRecvFastC P Dh encT decT K qep s qp w false)
      return (.inl (.inr out), s')
    | .inr qp =>
      (out, s') ← LibsignalSim.guardC (P := P) (Dh := Dh) (encT := encT) (decT := decT) s
        (simCorrFastC P Dh encT decT K s qp)
      return (.inr out, s')

private def simProgFast [Inhabited PQ] (K qep : ℕ) :
    CostedReduction OO SIface
      (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
      (LibsignalSim.simCodec PQ PQC Pt ℓ) .unit .unit .bool .bool where
  σ := LibsignalSim.simStateTy (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ)
  init := LibsignalSim.simInitC P Dh encT decT
  handle := simHandleFastC P Dh encT decT K qep
  finish := LibsignalSim.simFinishC P Dh encT decT none

end SimFastDefs

section SimFastEval

private def compTblEnc (l : List SM.Pos) : (ℕ → ℕ → Bool) × (ℕ → ℕ → Bool) :=
  ((fun ep idx => l.contains ⟨.A, ep, idx⟩),
   (fun ep idx => l.contains ⟨.B, ep, idx⟩))

private theorem compTblInsertE_eval {S0 : ReductionDsl.Sig} {O' : ReductionDsl.Ops S0} {Γ}
    (m : ReductionDsl.Expr O' Γ compTblTy) (pos : ReductionDsl.Expr O' Γ SM.posTy)
    (ρ : ReductionDsl.Env Γ) (l : List SM.Pos) (p₀ : SM.Pos)
    (hm : m.eval ρ = compTblEnc l) (hpos : pos.eval ρ = SM.posEnc p₀) :
    (compTblInsertE m pos).eval ρ = compTblEnc (p₀ :: l) := by
  rcases p₀ with ⟨sender, ep₀, idx₀⟩
  cases sender
  · simp only [compTblInsertE, compTblEnc, SM.posSender, SM.posEpoch, SM.posIdx, SM.pGet, SM.pSet,
      hm, hpos, SM.posEnc, SM.partyEnc, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0,
      ReductionDsl.Env.get, ↓reduceIte, Bool.false_eq_true, Prod.mk.injEq]
    constructor
    · funext ep idx
      by_cases hep : ep = ep₀
      · subst hep
        by_cases hidx : idx = idx₀
        · subst hidx; rw [Bool.eq_iff_iff]; simp
        · rw [Bool.eq_iff_iff]; simp [hidx]
      · rw [Bool.eq_iff_iff]; simp [hep]
    · funext ep idx; rw [Bool.eq_iff_iff]; simp
  · simp only [compTblInsertE, compTblEnc, SM.posSender, SM.posEpoch, SM.posIdx, SM.pGet, SM.pSet,
      hm, hpos, SM.posEnc, SM.partyEnc, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0,
      ReductionDsl.Env.get, ↓reduceIte, Prod.mk.injEq]
    constructor
    · funext ep idx; rw [Bool.eq_iff_iff]; simp
    · funext ep idx
      by_cases hep : ep = ep₀
      · subst hep
        by_cases hidx : idx = idx₀
        · subst hidx; rw [Bool.eq_iff_iff]; simp
        · rw [Bool.eq_iff_iff]; simp [hidx]
      · rw [Bool.eq_iff_iff]; simp [hep]

private theorem compTblGetE_eval {S0 : ReductionDsl.Sig} {O' : ReductionDsl.Ops S0} {Γ}
    (m : ReductionDsl.Expr O' Γ compTblTy) (pos : ReductionDsl.Expr O' Γ SM.posTy)
    (ρ : ReductionDsl.Env Γ) (l : List SM.Pos) (p₀ : SM.Pos)
    (hm : m.eval ρ = compTblEnc l) (hpos : pos.eval ρ = SM.posEnc p₀) :
    (compTblGetE m pos).eval ρ = l.contains p₀ := by
  rcases p₀ with ⟨sender, ep, idx⟩
  cases sender <;>
    simp [compTblGetE, compTblEnc, SM.posSender, SM.posEpoch, SM.posIdx, SM.pGet,
      hm, hpos, SM.posEnc, SM.partyEnc, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0,
      ReductionDsl.Env.get]

private theorem compTblOfListE_eval {S0 : ReductionDsl.Sig} {O' : ReductionDsl.Ops S0} {Γ}
    (K : ℕ) (xs : ReductionDsl.Expr O' Γ (.list SM.posTy))
    (ρ : ReductionDsl.Env Γ) (l : List SM.Pos)
    (hlen : l.length ≤ K) (hxs : xs.eval ρ = l.map SM.posEnc) :
    (compTblOfListE K xs).eval ρ = compTblEnc l := by
  have htake : (l.map SM.posEnc).take K = l.map SM.posEnc :=
    List.take_of_length_le (by simpa using hlen)
  simp only [compTblOfListE, ReductionDsl.Expr.eval, hxs, htake]
  have hemp : (compTblEmptyE (O' := O')).eval ρ = compTblEnc [] := by
    ext <;> simp [compTblEmptyE, compTblEnc, ReductionDsl.Expr.eval]
  rw [hemp]
  clear hlen hxs htake
  induction l with
  | nil => rfl
  | cons p ps ih =>
    rw [List.map_cons, List.foldr_cons, ih]
    exact compTblInsertE_eval .v1 .v0 _ ps p rfl rfl

private theorem any_and_wire_eq {α β : Type} [DecidableEq β]
    (l : List (α × β)) (f : β → α) (p : α → Bool) (c₀ : β)
    (hl : ∀ wc ∈ l, wc.1 = f wc.2) :
    ((l.any fun wc => decide (wc.2 = c₀)) && p (f c₀)) =
      (l.any fun wc => decide (wc.2 = c₀) && p wc.1) := by
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨⟨wc, hmem, hc⟩, hp⟩ => ⟨wc, hmem, hc, by rwa [hl wc hmem, hc]⟩,
    fun ⟨wc, hmem, hc, hp⟩ => ⟨⟨wc, hmem, hc⟩, by rwa [← hc, ← hl wc hmem]⟩⟩

section SimFastCongr

variable {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC] {ℓ : ℕ}
variable (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)

local notation "S" => LibsignalSim.simSig PQ PQC Pt ℓ
local notation "OO" => LibsignalSim.simOps (ℓ := ℓ) P Dh encT decT
local notation "SIface" => LibsignalSim.simIface PQ PQC Pt ℓ

private def HonestWireInv (s : LibsignalSim.SimState PQ Pt ℓ) : Prop :=
  ∀ wc ∈ s.honest, wc.1 = LibsignalSim.toWire wc.2

private def SimFastInv (K m : ℕ) (v : (@LibsignalSim.simStateTy PQ PQC Pt ℓ).denote) : Prop :=
  LibsignalSim.SimBoundInv K m v ∧ HonestWireInv (Pt := Pt) (LibsignalSim.simStateDec v)

set_option linter.unusedSimpArgs false in
omit [DecidableEq Pt] [Zero Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem mCorrAllowedFastE_eval_eq {O' : ReductionDsl.Ops S} {Γ} (K : ℕ)
    (s : ReductionDsl.Expr O' Γ LibsignalSim.simMirTy)
    (p : ReductionDsl.Expr O' Γ .bool) (ρ : ReductionDsl.Env Γ)
    (st : SM.GameState Unit (Plain ℓ) (List (BitVec 8))) (Q : Party)
    (hTrans : st.trans.length ≤ K) (hChall : st.chall.length ≤ K) (hComp : st.comp.length ≤ K)
    (hs : s.eval ρ = LibsignalSim.simMirEnc st) (hp : p.eval ρ = SM.partyEnc Q) :
    (mCorrAllowedFastE (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ) K s p).eval ρ =
      (LibsignalSim.mCorrAllowedE K s p).eval ρ := by
  rw [LibsignalSim.mCorrAllowedE_eval K s p ρ st Q hTrans hChall hComp hs hp]
  let ρ₁ := ReductionDsl.Env.cons (t := .prod LibsignalSim.simMirTy .bool)
    (LibsignalSim.simMirEnc (PQ := PQ) (PQC := PQC) (Pt := Pt) st, SM.partyEnc Q) ρ
  have hmc : (LibsignalSim.mComp (O' := O') (.fst .v0)).eval ρ₁ = st.comp.map SM.posEnc := rfl
  have htbl : (compTblOfListE (O' := O') K (LibsignalSim.mComp (.fst .v0))).eval ρ₁ =
      compTblEnc st.comp := compTblOfListE_eval (O' := O') K _ ρ₁ st.comp hComp hmc
  have htr : ((st.trans.map (LibsignalSim.simRecEnc (ℓ := ℓ))).take K) =
      st.trans.map LibsignalSim.simRecEnc := List.take_of_length_le (by simpa using hTrans)
  have hch : ((st.chall.map SM.posEnc).take K) = st.chall.map SM.posEnc :=
    List.take_of_length_le (by simpa using hChall)
  have hget : ∀ (r : SM.Record (Plain ℓ) (List (BitVec 8))) {Γ'} (ρ' : ReductionDsl.Env Γ'),
      (compTblGetE (O' := O') .v1 (.fst .v0)).eval
        (ReductionDsl.Env.cons (t := LibsignalSim.simRecTy (ℓ := ℓ)) (LibsignalSim.simRecEnc r)
          (ReductionDsl.Env.cons (t := compTblTy) (compTblEnc st.comp) ρ')) =
        st.comp.contains r.pos :=
    fun r {_} ρ' => compTblGetE_eval (O' := O') .v1 (.fst .v0)
      (ReductionDsl.Env.cons (t := LibsignalSim.simRecTy (ℓ := ℓ)) (LibsignalSim.simRecEnc r)
        (ReductionDsl.Env.cons (t := compTblTy) (compTblEnc st.comp) ρ')) st.comp r.pos rfl rfl
  dsimp only [ReductionDsl.Expr.v0, ReductionDsl.Expr.v1] at hget
  unfold mCorrAllowedFastE
  simp only [ReductionDsl.Expr.eval, hs, hp]
  change (let t := (compTblOfListE (O' := O') K (LibsignalSim.mComp (.fst .v0))).eval ρ₁; _) = _
  rw [htbl]
  simp only [ρ₁, LibsignalSim.mChall, LibsignalSim.mTrans, LibsignalSim.simMirEnc,
    ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Expr.v2,
    ReductionDsl.Env.get, hch, htr, List.any_map, Function.comp_def, hget,
    SM.GameState.corrAllowed, SM.boolEq, SM.posSender, SM.otherE, SM.posEnc, SM.partyEnc]
  simp only [LibsignalSim.simRecEnc, SM.posEnc]
  congr 1 <;> congr 1 <;> congr 1 <;> funext x
  · rcases x with ⟨sx, _, _⟩; cases sx <;> cases Q <;> rfl
  · rcases x with ⟨⟨sx, _, _⟩, _, _⟩; cases sx <;> cases Q <;> rfl

set_option linter.unusedSimpArgs false in
omit [DecidableEq Pt] [Zero Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem mAfterCorrFastE_eval_eq {O' : ReductionDsl.Ops S} {Γ} (K : ℕ)
    (s : ReductionDsl.Expr O' Γ LibsignalSim.simMirTy)
    (p : ReductionDsl.Expr O' Γ .bool) (ρ : ReductionDsl.Env Γ)
    (st : SM.GameState Unit (Plain ℓ) (List (BitVec 8))) (Q : Party)
    (hTrans : st.trans.length ≤ K) (hComp : st.comp.length ≤ K)
    (hCompU : ∃ U : List SM.Pos, U.length ≤ K ∧
      Computational.Proofs.GameHop.CompDedup.CountLe st.comp U ∧ ∀ r ∈ st.trans, r.pos ∈ U)
    (hs : s.eval ρ = LibsignalSim.simMirEnc st) (hp : p.eval ρ = SM.partyEnc Q) :
    (mAfterCorrFastE (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ) K s p).eval ρ =
      (LibsignalSim.mAfterCorrE K s p).eval ρ := by
  rw [LibsignalSim.mAfterCorrE_eval K s p ρ st Q hTrans hCompU hs hp]
  let ρ₁ := ReductionDsl.Env.cons (t := .prod LibsignalSim.simMirTy .bool)
    (LibsignalSim.simMirEnc (PQ := PQ) (PQC := PQC) (Pt := Pt) st, SM.partyEnc Q) ρ
  have hmc : (LibsignalSim.mComp (O' := O') (.fst .v0)).eval ρ₁ = st.comp.map SM.posEnc := rfl
  have htbl : (compTblOfListE (O' := O') K (LibsignalSim.mComp (.fst .v0))).eval ρ₁ =
      compTblEnc st.comp := compTblOfListE_eval (O' := O') K _ ρ₁ st.comp hComp hmc
  have htr : ((st.trans.map (LibsignalSim.simRecEnc (ℓ := ℓ))).take K) =
      st.trans.map LibsignalSim.simRecEnc := List.take_of_length_le (by simpa using hTrans)
  let compOut (rs : List (SM.Record (Plain ℓ) (List (BitVec 8)))) : List SM.Pos :=
    Computational.Proofs.GameHop.CompDedup.dedupPrepend
      ((rs.filter (fun r => r.pos.sender == Q.other)).map (·.pos)) st.comp
  let stepE : ReductionDsl.Expr O'
      (LibsignalSim.simRecTy (ℓ := ℓ) :: .prod (.list SM.posTy) compTblTy ::
        .prod LibsignalSim.simMirTy .bool :: Γ)
      (.prod (.list SM.posTy) compTblTy) :=
    .ite (.and (SM.boolEq (SM.posSender (.fst .v0)) (SM.otherE (.snd .v2)))
                (.not (compTblGetE (.snd .v1) (.fst .v0))))
      (.pair (.cons (.fst .v0) (.fst .v1)) (compTblInsertE (.snd .v1) (.fst .v0))) .v1
  have hfold : ∀ rs : List (SM.Record (Plain ℓ) (List (BitVec 8))),
      (rs.map LibsignalSim.simRecEnc).foldr
        (fun x acc => stepE.eval (ReductionDsl.Env.cons x (ReductionDsl.Env.cons acc ρ₁)))
        (st.comp.map SM.posEnc, compTblEnc st.comp) =
      ((compOut rs).map SM.posEnc, compTblEnc (compOut rs)) := by
    intro rs; induction rs with
    | nil => rfl
    | cons r rs ih =>
      rw [List.map_cons, List.foldr_cons, ih]
      let c := compOut rs
      let ρc := ReductionDsl.Env.cons (t := LibsignalSim.simRecTy (ℓ := ℓ)) (LibsignalSim.simRecEnc r)
        (ReductionDsl.Env.cons (t := .prod (.list SM.posTy) compTblTy) (c.map SM.posEnc, compTblEnc c) ρ₁)
      have hsend_eq : (SM.boolEq (O' := O') (SM.posSender (.fst .v0)) (SM.otherE (.snd .v2))).eval ρc =
          (r.pos.sender == Q.other) := by
        cases h1 : r.pos.sender <;> cases Q <;>
          simp [ρc, SM.boolEq, SM.posSender, SM.otherE, LibsignalSim.simRecEnc, SM.posEnc,
            SM.partyEnc, h1, ρ₁, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0,
            ReductionDsl.Expr.v2, ReductionDsl.Env.get]
      have hget := compTblGetE_eval (O' := O') (.snd .v1) (.fst .v0) ρc c r.pos rfl rfl
      have hins := compTblInsertE_eval (O' := O') (.snd .v1) (.fst .v0) ρc c r.pos rfl rfl
      have hv0_fst : (ReductionDsl.Expr.fst (O := O') .v0).eval ρc = SM.posEnc r.pos := rfl
      have hv1_fst : (ReductionDsl.Expr.fst (O := O') .v1).eval ρc = c.map SM.posEnc := rfl
      have hv1_eq : (ReductionDsl.Expr.v1 (O := O')).eval ρc = (c.map SM.posEnc, compTblEnc c) := rfl
      change (if ((SM.boolEq (O' := O') (SM.posSender (.fst .v0)) (SM.otherE (.snd .v2))).eval ρc &&
                  !(compTblGetE (O' := O') (.snd .v1) (.fst .v0)).eval ρc) = true then
                ((ReductionDsl.Expr.fst (O := O') .v0).eval ρc ::
                   (ReductionDsl.Expr.fst (O := O') .v1).eval ρc,
                 (compTblInsertE (O' := O') (.snd .v1) (.fst .v0)).eval ρc)
              else (ReductionDsl.Expr.v1 (O := O')).eval ρc) = _
      rw [hsend_eq, hget, hins, hv0_fst, hv1_fst, hv1_eq]
      by_cases hsnd : (r.pos.sender == Q.other) = true
      · have hflt : List.filter (fun x => x.pos.sender == Q.other) (r :: rs) =
            r :: List.filter (fun x => x.pos.sender == Q.other) rs :=
          List.filter_cons_of_pos hsnd
        have hc_eq : compOut (r :: rs) = if c.contains r.pos then c else r.pos :: c := by
          dsimp only [compOut]
          rw [hflt, List.map_cons, Computational.Proofs.GameHop.CompDedup.dedupPrepend_cons]
        rw [hc_eq, hsnd, Bool.true_and]
        cases hc : c.contains r.pos <;> simp
      · have hsndF : (r.pos.sender == Q.other) = false := Bool.eq_false_iff.mpr hsnd
        have hflt : List.filter (fun x => x.pos.sender == Q.other) (r :: rs) =
            List.filter (fun x => x.pos.sender == Q.other) rs :=
          List.filter_cons_of_neg hsnd
        have hc_eq : compOut (r :: rs) = c := by dsimp only [compOut]; rw [hflt]
        rw [hc_eq, hsndF]; simp
  have hbody₁ : (ReductionDsl.Expr.fst (.foldrB K (LibsignalSim.mTrans (.fst .v0))
      (.pair (LibsignalSim.mComp (.fst .v0)) (compTblOfListE K (LibsignalSim.mComp (.fst .v0))))
      stepE)).eval ρ₁ = (compOut st.trans).map SM.posEnc := by
    simp only [ReductionDsl.Expr.eval, hmc, htbl]
    have hmt : (LibsignalSim.mTrans (O' := O') (.fst .v0)).eval ρ₁ =
        st.trans.map LibsignalSim.simRecEnc := rfl
    rw [hmt, htr, hfold st.trans]
  unfold mAfterCorrFastE
  rw [ReductionDsl.Expr.eval]
  have hsp : (ReductionDsl.Expr.pair s p).eval ρ =
      (LibsignalSim.simMirEnc (PQ := PQ) (PQC := PQC) (Pt := Pt) st, SM.partyEnc Q) :=
    Prod.ext hs hp
  rw [hsp, ReductionDsl.Expr.eval]
  change (ReductionDsl.Expr.eval _
    (ReductionDsl.Env.cons (t := .list SM.posTy)
      ((ReductionDsl.Expr.fst (.foldrB K (LibsignalSim.mTrans (.fst .v0))
        (.pair (LibsignalSim.mComp (.fst .v0)) (compTblOfListE K (LibsignalSim.mComp (.fst .v0))))
        stepE)).eval ρ₁) ρ₁)) = _
  rw [hbody₁]
  cases Q <;> cases htl : st.tL <;>
    simp [Computational.Proofs.GameHop.CompDedup.afterCorrDedup, SM.GameState.leak, SM.maxOpt,
      LibsignalSim.mLeakE, SM.maxOptE, htl, ρ₁, compOut,
      LibsignalSim.mMk, LibsignalSim.mB, LibsignalSim.mWin, LibsignalSim.mEpoch,
      LibsignalSim.mIdx, LibsignalSim.mTL, LibsignalSim.mTrans, LibsignalSim.mChall,
      LibsignalSim.mComp, LibsignalSim.mMaxAcc, LibsignalSim.mLeaks, LibsignalSim.mCorrs,
      LibsignalSim.simMirEnc, SM.pGet, SM.maxN, SM.leN, Nat.ble_eq, Nat.max_def, SM.partyEnc,
      ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Env.get]

set_option linter.unusedSimpArgs false in
omit [Inhabited PQ] [SampleableType PQC] in
private theorem inTFastE_eval_eq (K : ℕ) {Γ}
    (s : ReductionDsl.Expr OO Γ LibsignalSim.simStateTy)
    (qParty : ReductionDsl.Expr OO Γ .bool)
    (c : ReductionDsl.Expr OO Γ (LibsignalSim.fig8CTy PQ PQC Pt ℓ))
    (ρ : ReductionDsl.Env Γ) (st : LibsignalSim.SimState PQ Pt ℓ) (Q : Party)
    (hTrans : st.mir.trans.length ≤ K) (hHonest : st.honest.length ≤ K)
    (hWire : HonestWireInv (Pt := Pt) st)
    (hs : s.eval ρ = LibsignalSim.simStateEnc st) (hq : qParty.eval ρ = SM.partyEnc Q) :
    (inTFastE P Dh encT decT K s qParty c).eval ρ =
      (LibsignalSim.inTE P Dh encT decT K s qParty c).eval ρ := by
  let c₀ := c.eval ρ
  rw [LibsignalSim.inTE_eval P Dh encT decT K s qParty c ρ st Q c₀ hTrans hHonest hs hq rfl]
  let ρ₁ := ReductionDsl.Env.cons
    (t := .prod LibsignalSim.simStateTy (.prod .bool (LibsignalSim.fig8CTy PQ PQC Pt ℓ)))
    (LibsignalSim.simStateEnc st, (SM.partyEnc Q, c₀)) ρ
  have htake : st.honest.take K = st.honest := List.take_of_length_le hHonest
  have hoth : (SM.otherE (O' := OO) (.fst (.snd .v0))).eval ρ₁ = SM.partyEnc Q.other := by
    cases Q <;> rfl
  have hmTr := LibsignalSim.mInTransitE_eval (P := P) (Dh := Dh) (encT := encT) (decT := decT)
    K (LibsignalSim.ssMir (.fst .v0)) (SM.otherE (.fst (.snd .v0)))
    (.op (O := OO) LibsignalSim.SimOp.toWire (.snd (.snd .v0))) ρ₁ st.mir Q.other hTrans rfl hoth
  have hw : ((ReductionDsl.Expr.op (O := OO) LibsignalSim.SimOp.toWire (.snd (.snd .v0))).eval ρ₁) =
      LibsignalSim.toWire c₀ := rfl
  rw [hw] at hmTr
  have hisSome : (SM.isSomeE
      (LibsignalSim.mInTransitE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
        K (LibsignalSim.ssMir (.fst .v0)) (SM.otherE (.fst (.snd .v0)))
        (.op (O := OO) LibsignalSim.SimOp.toWire (.snd (.snd .v0))))).eval ρ₁ =
      (st.mir.inTransit Q.other (LibsignalSim.toWire c₀)).isSome := by
    simp only [SM.isSomeE, ReductionDsl.Expr.eval, hmTr]
    cases st.mir.inTransit Q.other (LibsignalSim.toWire c₀) <;> rfl
  unfold inTFastE
  rw [ReductionDsl.Expr.eval]
  have hspq : (ReductionDsl.Expr.pair s (.pair qParty c)).eval ρ =
      (LibsignalSim.simStateEnc st, (SM.partyEnc Q, c₀)) :=
    Prod.ext hs (Prod.ext hq rfl)
  rw [hspq, ReductionDsl.Expr.eval]
  change ((ReductionDsl.Expr.anyB K _ _).eval ρ₁ && (SM.isSomeE _).eval ρ₁) = _
  rw [hisSome]
  simp only [ρ₁, c₀, LibsignalSim.ssHonest, LibsignalSim.simStateEnc, LibsignalSim.simOps,
    ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Env.get, htake]
  exact any_and_wire_eq st.honest LibsignalSim.toWire
    (fun w => (st.mir.inTransit Q.other w).isSome) (c.eval ρ) hWire

omit [Inhabited PQ] in
private theorem fwdFastC_eval_eq (K : ℕ) {Γ}
    (s : ReductionDsl.Expr OO Γ LibsignalSim.simStateTy)
    (qParty : ReductionDsl.Expr OO Γ .bool)
    (c : ReductionDsl.Expr OO Γ (LibsignalSim.fig8CTy PQ PQC Pt ℓ))
    (ρ : ReductionDsl.Env Γ) (st : LibsignalSim.SimState PQ Pt ℓ) (Q : Party)
    (hTrans : st.mir.trans.length ≤ K) (hHonest : st.honest.length ≤ K)
    (hWire : HonestWireInv (Pt := Pt) st)
    (hs : s.eval ρ = LibsignalSim.simStateEnc st) (hq : qParty.eval ρ = SM.partyEnc Q) :
    (fwdFastC P Dh encT decT K s qParty c).eval ρ =
      (LibsignalSim.fwdC P Dh encT decT K s qParty c).eval ρ := by
  simp only [fwdFastC, LibsignalSim.fwdC, ReductionDsl.Comp.eval,
    inTFastE_eval_eq P Dh encT decT K s qParty c ρ st Q hTrans hHonest hWire hs hq]

omit [Inhabited PQ] in
private theorem simRecvNewChainNormalFastC_eval_eq (K qep : ℕ) {Γ}
    (ρ : ReductionDsl.Env
      (LibsignalSim.parsedRecvTy (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ) ::
        .prod LibsignalSim.simStateTy (.prod .bool (.prod (.base .wire) .bool)) :: Γ))
    (st : LibsignalSim.SimState PQ Pt ℓ) (Q : Party)
    (hTrans : st.mir.trans.length ≤ K) (hHonest : st.honest.length ≤ K)
    (hWire : HonestWireInv (Pt := Pt) st)
    (hs : (ReductionDsl.Expr.fst (O := OO) .v1).eval ρ = LibsignalSim.simStateEnc st)
    (hq : (ReductionDsl.Expr.fst (O := OO) (.snd .v1)).eval ρ = SM.partyEnc Q) :
    (simRecvNewChainNormalFastC P Dh encT decT K qep).eval ρ =
      (LibsignalSim.simRecvNewChainNormalC P Dh encT decT K qep).eval ρ := by
  simp only [simRecvNewChainNormalFastC, LibsignalSim.simRecvNewChainNormalC,
    ReductionDsl.Comp.eval]
  split
  · rfl
  · cases hopt : (ReductionDsl.Expr.fst (O := OO) (.snd (.snd (.snd .v0)))).eval ρ with
    | none => rfl
    | some pt =>
      dsimp only
      let ρ' := ReductionDsl.Env.cons (t := (.base .pt : ReductionDsl.Ty S)) pt ρ
      have hs' : (ReductionDsl.Expr.fst (O := OO) .v2).eval ρ' = LibsignalSim.simStateEnc st := by
        simpa [ρ', ReductionDsl.Expr.eval, ReductionDsl.Expr.v1, ReductionDsl.Expr.v2,
          ReductionDsl.Env.get] using hs
      have hq' : (ReductionDsl.Expr.fst (O := OO) (.snd .v2)).eval ρ' = SM.partyEnc Q := by
        simpa [ρ', ReductionDsl.Expr.eval, ReductionDsl.Expr.v1, ReductionDsl.Expr.v2,
          ReductionDsl.Env.get] using hq
      rw [fwdFastC_eval_eq P Dh encT decT K (.fst .v2) (.fst (.snd .v2)) _ ρ'
        st Q hTrans hHonest hWire hs' hq']

omit [Inhabited PQ] in
private theorem simRecvFastC_eval_eq (K qep : ℕ) {Γ}
    (s : ReductionDsl.Expr OO Γ LibsignalSim.simStateTy)
    (qParty : ReductionDsl.Expr OO Γ .bool)
    (w : ReductionDsl.Expr OO Γ (.base .wire)) (isDel : ReductionDsl.Expr OO Γ .bool)
    (ρ : ReductionDsl.Env Γ) (st : LibsignalSim.SimState PQ Pt ℓ) (Q : Party)
    (hBound : LibsignalSim.SimStateBounded K st) (hWire : HonestWireInv (Pt := Pt) st)
    (hs : s.eval ρ = LibsignalSim.simStateEnc st) (hq : qParty.eval ρ = SM.partyEnc Q) :
    (simRecvFastC P Dh encT decT K qep s qParty w isDel).eval ρ =
      (LibsignalSim.simRecvC P Dh encT decT K qep none s qParty w isDel).eval ρ := by
  let ρ₁ := ReductionDsl.Env.cons
    (t := .prod LibsignalSim.simStateTy (.prod .bool (.prod (.base .wire) .bool)))
    (s.eval ρ, (qParty.eval ρ, (w.eval ρ, isDel.eval ρ))) ρ
  have hpair : (ReductionDsl.Expr.pair s (.pair qParty (.pair w isDel))).eval ρ =
      (s.eval ρ, (qParty.eval ρ, (w.eval ρ, isDel.eval ρ))) := rfl
  simp only [simRecvFastC, LibsignalSim.simRecvC, ReductionDsl.Comp.eval, pure_bind, hpair]
  split
  · rfl
  · cases hp : (LibsignalSim.parseRecvE (P := P) (Dh := Dh) (encT := encT) (decT := decT) (2 ^ 32)
        (.pair (.fst (.snd .v0)) (.pair (SM.pGet (LibsignalSim.ssPq (.fst .v0)) (.fst (.snd .v0)))
          (.fst (.snd (.snd .v0)))))).eval ρ₁ with
    | none => rfl
    | some parsed =>
      dsimp only
      let ρ₂ := ReductionDsl.Env.cons
        (t := LibsignalSim.parsedRecvTy (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ)) parsed ρ₁
      have hs₂ : (ReductionDsl.Expr.fst (O := OO) .v1).eval ρ₂ = LibsignalSim.simStateEnc st := by
        simp [ρ₂, ρ₁, hs, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1, ReductionDsl.Env.get]
      have hq₂ : (ReductionDsl.Expr.fst (O := OO) (.snd .v1)).eval ρ₂ = SM.partyEnc Q := by
        simp [ρ₂, ρ₁, hq, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1, ReductionDsl.Env.get]
      cases hf : (LibsignalSim.findChainE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
          (.pair (SM.pGet (LibsignalSim.ssChains (.fst .v1)) (.fst (.snd .v1)))
            (.fst (.snd (.snd .v0))))).eval ρ₂ with
      | none =>
        dsimp only
        split
        · rfl
        · split
          · rfl
          · exact simRecvNewChainNormalFastC_eval_eq P Dh encT decT K qep ρ₂ st Q
              hBound.trans_le hBound.honest_le hWire hs₂ hq₂
      | some cg =>
        dsimp only
        split
        · rfl
        · let ρ₃ := ReductionDsl.Env.cons
            (t := .prod .nat (LibsignalSim.ghostChainTy PQ PQC Pt ℓ)) cg ρ₂
          have hs₃ : (ReductionDsl.Expr.fst (O := OO) .v2).eval ρ₃ = LibsignalSim.simStateEnc st := by
            simpa [ρ₃, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1, ReductionDsl.Expr.v2,
              ReductionDsl.Env.get] using hs₂
          have hq₃ : (ReductionDsl.Expr.fst (O := OO) (.snd .v2)).eval ρ₃ = SM.partyEnc Q := by
            simpa [ρ₃, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1, ReductionDsl.Expr.v2,
              ReductionDsl.Env.get] using hq₂
          rw [fwdFastC_eval_eq P Dh encT decT K (.fst .v2) (.fst (.snd .v2)) _ ρ₃ st Q
            hBound.trans_le hBound.honest_le hWire hs₃ hq₃]

omit [Inhabited PQ] [SampleableType PQC] in
private theorem pure_pair_ssMk_eval_congr {Γ}
    (g : ReductionDsl.Expr OO Γ (.opt (.base .ghostSt)))
    (m₁ m₂ : ReductionDsl.Expr OO Γ LibsignalSim.simMirTy) (pq pn ua ho ch am stp : _)
    (ρ : ReductionDsl.Env Γ) (h : m₁.eval ρ = m₂.eval ρ) :
    (pure ((ReductionDsl.Expr.pair g (LibsignalSim.ssMk m₁ pq pn ua ho ch am stp)).eval ρ) :
      LibsignalSim.Fig8Comp Pt ℓ _) =
    pure ((ReductionDsl.Expr.pair g (LibsignalSim.ssMk m₂ pq pn ua ho ch am stp)).eval ρ) := by
  dsimp only [LibsignalSim.ssMk, ReductionDsl.Expr.eval]; rw [h]

omit [Inhabited PQ] in
private theorem simCorrFastC_eval_eq (K : ℕ) {Γ}
    (s : ReductionDsl.Expr OO Γ LibsignalSim.simStateTy)
    (qParty : ReductionDsl.Expr OO Γ .bool)
    (ρ : ReductionDsl.Env Γ) (st : LibsignalSim.SimState PQ Pt ℓ) (Q : Party)
    (hBound : LibsignalSim.SimStateBounded K st)
    (hs : s.eval ρ = LibsignalSim.simStateEnc st) (hq : qParty.eval ρ = SM.partyEnc Q) :
    (simCorrFastC P Dh encT decT K s qParty).eval ρ =
      (LibsignalSim.simCorrC P Dh encT decT K s qParty).eval ρ := by
  let ρ₁ := ReductionDsl.Env.cons (t := .prod LibsignalSim.simStateTy .bool)
    (s.eval ρ, qParty.eval ρ) ρ
  have hpair : (ReductionDsl.Expr.pair s qParty).eval ρ = (s.eval ρ, qParty.eval ρ) := rfl
  have hmir : (LibsignalSim.ssMir (O' := OO) (.fst .v0)).eval ρ₁ = LibsignalSim.simMirEnc st.mir := by
    simp [ρ₁, hs, LibsignalSim.ssMir, LibsignalSim.simStateEnc, ReductionDsl.Expr.eval,
      ReductionDsl.Expr.v0, ReductionDsl.Env.get]
  have hqp : (ReductionDsl.Expr.snd (O := OO) .v0).eval ρ₁ = SM.partyEnc Q := by
    simp [ρ₁, hq, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get]
  have hca := mCorrAllowedFastE_eval_eq (PQ := PQ) (PQC := PQC) (Pt := Pt) (O' := OO) K
    (LibsignalSim.ssMir (.fst .v0)) (.snd .v0) ρ₁ st.mir Q
    hBound.trans_le hBound.chall_le hBound.comp_le hmir hqp
  have href : (SM.orE (O' := OO) (LibsignalSim.mWin (LibsignalSim.ssMir (.fst .v0)))
      (SM.orE (.not (mCorrAllowedFastE K (LibsignalSim.ssMir (.fst .v0)) (.snd .v0)))
        (SM.orE (LibsignalSim.mInWinE (LibsignalSim.ssMir (.fst .v0)) (.snd .v0))
          (.not (LibsignalSim.mNoSpkCorrE (LibsignalSim.ssMir (.fst .v0)) (.snd .v0)))))).eval ρ₁ =
    (SM.orE (O' := OO) (LibsignalSim.mWin (LibsignalSim.ssMir (.fst .v0)))
      (SM.orE (.not (LibsignalSim.mCorrAllowedE K (LibsignalSim.ssMir (.fst .v0)) (.snd .v0)))
        (SM.orE (LibsignalSim.mInWinE (LibsignalSim.ssMir (.fst .v0)) (.snd .v0))
          (.not (LibsignalSim.mNoSpkCorrE (LibsignalSim.ssMir (.fst .v0)) (.snd .v0)))))).eval ρ₁ := by
    simp only [SM.orE, ReductionDsl.Expr.eval, hca]; rfl
  simp only [simCorrFastC, LibsignalSim.simCorrC, ReductionDsl.Comp.eval, pure_bind, hpair]
  change (if (SM.orE _ _).eval ρ₁ = true then _ else _) =
    (if (SM.orE _ _).eval ρ₁ = true then _ else _)
  rw [href]
  split
  · rfl
  · refine bind_congr fun crOpt => ?_
    cases crOpt with
    | none => rfl
    | some gst =>
      have hv0 : (ReductionDsl.Expr.v0 (O := OO)).eval
          (ReductionDsl.Env.cons (t := (.opt (.base .fig8st) : ReductionDsl.Ty S)) (some gst) ρ₁) =
          some gst := rfl
      rw [hv0]
      dsimp only []
      let ρ₂ := ReductionDsl.Env.cons (t := (.base .fig8st : ReductionDsl.Ty S)) gst
        (ReductionDsl.Env.cons (t := (.opt (.base .fig8st) : ReductionDsl.Ty S)) (some gst) ρ₁)
      have hmir₂ : (LibsignalSim.ssMir (O' := OO) (.fst .v2)).eval ρ₂ =
          LibsignalSim.simMirEnc st.mir := by
        dsimp only [ρ₂, LibsignalSim.ssMir, ReductionDsl.Expr.eval,
          ReductionDsl.Expr.v0, ReductionDsl.Expr.v2, ReductionDsl.Env.get] at hmir ⊢
        exact hmir
      have hqp₂ : (ReductionDsl.Expr.snd (O := OO) .v2).eval ρ₂ = SM.partyEnc Q := by
        dsimp only [ρ₂, ReductionDsl.Expr.eval,
          ReductionDsl.Expr.v0, ReductionDsl.Expr.v2, ReductionDsl.Env.get] at hqp ⊢
        exact hqp
      have hac := mAfterCorrFastE_eval_eq (PQ := PQ) (PQC := PQC) (Pt := Pt) (O' := OO) K
        (LibsignalSim.ssMir (.fst .v2)) (.snd .v2) ρ₂ st.mir Q
        hBound.trans_le hBound.comp_le hBound.comp_u hmir₂ hqp₂
      exact pure_pair_ssMk_eval_congr P Dh encT decT _ _ _ _ _ _ _ _ _ _ ρ₂ hac

omit [Inhabited PQ] in
private theorem guardC_eval_congr {Γ t} (s : ReductionDsl.Expr OO Γ LibsignalSim.simStateTy)
    (b₁ b₂ : ReductionDsl.Comp OO SIface Γ (.prod (.opt t) LibsignalSim.simStateTy))
    (ρ : ReductionDsl.Env Γ) (h : b₁.eval ρ = b₂.eval ρ) :
    (LibsignalSim.guardC P Dh encT decT s b₁).eval ρ =
      (LibsignalSim.guardC P Dh encT decT s b₂).eval ρ := by
  simp only [LibsignalSim.guardC, ReductionDsl.Comp.eval, h]

omit [DecidableEq Pt] [Zero Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem bind_lhs_congr {ι : Type} {spec : OracleSpec ι} {α β : Type}
    {x₁ x₂ : OracleComp spec α} {k : α → OracleComp spec β} (h : x₁ = x₂) :
    (x₁ >>= k) = (x₂ >>= k) :=
  h ▸ rfl

private theorem simProgFast_impl_inr_eq (K qep : ℕ)
    (t : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (v : (@LibsignalSim.simStateTy PQ PQC Pt ℓ).denote)
    (hBound : LibsignalSim.SimStateBounded K (LibsignalSim.simStateDec v))
    (hWire : HonestWireInv (Pt := Pt) (LibsignalSim.simStateDec v)) :
    (((simProgFast P Dh encT decT K qep).impl (.inr t)).run v) =
      (((LibsignalSim.simProg P Dh encT decT K qep).impl (.inr t)).run v) := by
  let st := LibsignalSim.simStateDec v
  have hv : v = LibsignalSim.simStateEnc st := (LibsignalSim.simStateEnc_simStateDec v).symm
  rw [hv]
  rcases t with (((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q
  · rfl
  · rfl
  · unfold ReductionDsl.CostedReduction.impl ReductionDsl.handlerImpl simProgFast
      LibsignalSim.simProg LibsignalSim.simRunProg simHandleFastC LibsignalSim.simHandleC
      LibsignalSim.simCodec
    simp only [StateT.run_mk, ReductionDsl.Comp.eval, ReductionDsl.Expr.eval,
      ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Env.get, bind_assoc, pure_bind]
    refine bind_lhs_congr (guardC_eval_congr P Dh encT decT _ _ _ _
      (simRecvFastC_eval_eq P Dh encT decT K qep _ _ _ _ _ st Q hBound hWire rfl rfl))
  · unfold ReductionDsl.CostedReduction.impl ReductionDsl.handlerImpl simProgFast
      LibsignalSim.simProg LibsignalSim.simRunProg simHandleFastC LibsignalSim.simHandleC
      LibsignalSim.simCodec
    simp only [StateT.run_mk, ReductionDsl.Comp.eval, ReductionDsl.Expr.eval,
      ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Env.get, bind_assoc, pure_bind]
    refine bind_lhs_congr (guardC_eval_congr P Dh encT decT _ _ _ _
      (simRecvFastC_eval_eq P Dh encT decT K qep _ _ _ _ _ st Q hBound hWire rfl rfl))
  · unfold ReductionDsl.CostedReduction.impl ReductionDsl.handlerImpl simProgFast
      LibsignalSim.simProg LibsignalSim.simRunProg simHandleFastC LibsignalSim.simHandleC
      LibsignalSim.simCodec
    simp only [StateT.run_mk, ReductionDsl.Comp.eval, ReductionDsl.Expr.eval,
      ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Env.get, bind_assoc, pure_bind]
    refine bind_lhs_congr (guardC_eval_congr P Dh encT decT _ _ _ _
      (simCorrFastC_eval_eq P Dh encT decT K _ _ _ st Q hBound rfl rfl))

omit [DecidableEq Pt] [Zero Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem guard_honestWire {α : Type}
    (x : StateT (LibsignalSim.SimState PQ Pt ℓ) (LibsignalSim.Fig8Comp Pt ℓ) (Option α))
    (st : LibsignalSim.SimState PQ Pt ℓ) (hWire : HonestWireInv (Pt := Pt) st)
    (hx : ∀ r ∈ support (x.run st), HonestWireInv (Pt := Pt) r.2) :
    ∀ r ∈ support ((LibsignalSim.«guard» x).run st),
      HonestWireInv (Pt := Pt) r.2 := by
  intro r hr
  unfold LibsignalSim.«guard» at hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
  cases h : st.stopped
  · simp only [h, Bool.false_eq_true, ↓reduceIte] at hr; exact hx r hr
  · simp only [h, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact hWire

omit [DecidableEq Pt] [Zero Pt] [Inhabited PQ] in
private theorem simSend_honestWire (qep : ℕ) (Q : Party) (m₀ : Plain ℓ)
    (chal : Option (Plain ℓ)) (rCoins : Option PQC) (st : LibsignalSim.SimState PQ Pt ℓ)
    (hWire : HonestWireInv (Pt := Pt) st) :
    ∀ r ∈ support ((LibsignalSim.simSend P qep Q m₀ chal rCoins).run st),
      HonestWireInv (Pt := Pt) r.2 := by
  intro r hr
  unfold LibsignalSim.simSend at hr
  rw [StateT.run_bind, StateT.run_get, pure_bind] at hr
  by_cases h1 : (st.mir.win || !(noBobSendInEpoch0 st.mir Q)) = true
  · simp only [h1, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact hWire
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hr
    rcases hep : st.mir.epMgmt 3 qep Q rCoins.isSome with _ | s₁
    · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact hWire
    · simp only [hep] at hr
      by_cases h2 : (chal.isSome && !s₁.safeCh 3 Q) = true
      · simp only [h2, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact hWire
      · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hr
        suffices hpost : ∀ (rq : PQC) (rc : Option (BitVec 256)),
            r ∈ support ((do
              let pn := if s₁.epoch Q ≠ st.mir.epoch Q then
                BitVec.ofNat 32 (st.mir.idx Q - 1) else st.pn Q
              match LibsignalSim.mkPub (P := P) st Q rq pn with
              | none => return none
              | some (pq', pub) =>
                let res ← match chal with
                  | none => LibsignalSim.liftQ (SM.transmitQuery (St := LibsignalSim.Fig8St Pt) Q (pub, m₀) rc)
                  | some m₁ => LibsignalSim.liftQ (SM.challQuery (St := LibsignalSim.Fig8St Pt) Q (pub, m₀) (pub, m₁) rc)
                match res with
                | none => return none
                | some c =>
                  let w := LibsignalSim.toWire c
                  let rec' : SM.Record (Plain ℓ) (List (BitVec 8)) :=
                    ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, w⟩
                  let mir' := s₁.record 3 Q () rec' chal.isSome
                  LibsignalSim.putS { st with
                    mir := mir', pq := Function.update st.pq Q pq',
                    pn := Function.update st.pn Q pn,
                    honest := (w, c) :: st.honest }
                  return some w).run st) →
              HonestWireInv (Pt := Pt) r.2 by
          rcases rCoins with _ | rq₀
          · simp only [LibsignalSim.coin, LibsignalSim.liftQ, LibsignalSim.stateT_lift_run,
              StateT.run_bind, bind_assoc, pure_bind, mem_support_bind_iff] at hr
            obtain ⟨rq, -, hr⟩ := hr; exact hpost rq none hr
          · simp only [LibsignalSim.coin, LibsignalSim.liftQ, LibsignalSim.stateT_lift_run,
              StateT.run_bind, bind_map_left, bind_assoc, pure_bind, mem_support_bind_iff] at hr
            obtain ⟨c, -, hr⟩ := hr; exact hpost rq₀ (some c) hr
        intro rq rc hr
        dsimp only [] at hr
        rcases hpub : LibsignalSim.mkPub (P := P) st Q rq
            (if s₁.epoch Q ≠ st.mir.epoch Q then BitVec.ofNat 32 (st.mir.idx Q - 1) else st.pn Q)
            with _ | ⟨pq', pub⟩
        · simp only [hpub, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact hWire
        · simp only [hpub] at hr
          generalize chal.isSome = bChal at hr
          obtain ⟨res, hr⟩ : ∃ res : Option (LibsignalSim.Fig8C Pt),
              r ∈ support ((match res with
                | none => pure none
                | some c => do
                  LibsignalSim.putS { st with
                    mir := s₁.record 3 Q () ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, LibsignalSim.toWire c⟩ bChal,
                    pq := Function.update st.pq Q pq',
                    pn := Function.update st.pn Q
                      (if s₁.epoch Q ≠ st.mir.epoch Q then BitVec.ofNat 32 (st.mir.idx Q - 1)
                       else st.pn Q),
                    honest := (LibsignalSim.toWire c, c) :: st.honest }
                  pure (some (LibsignalSim.toWire c))).run st) := by
            rcases chal with _ | m₁ <;>
              (simp only [LibsignalSim.liftQ, LibsignalSim.stateT_lift_run, StateT.run_bind,
                 bind_assoc, pure_bind, mem_support_bind_iff] at hr;
               obtain ⟨res, -, hr⟩ := hr; exact ⟨res, hr⟩)
          rcases res with _ | c
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
            subst hr; exact hWire
          · simp only [LibsignalSim.putS, StateT.run_bind, StateT.run_set, StateT.run_pure,
              pure_bind, support_pure, Set.mem_singleton_iff] at hr
            subst hr
            intro wc hwc
            rcases List.mem_cons.mp hwc with rfl | hmem
            · rfl
            · exact hWire wc hmem

omit [DecidableEq Pt] [Zero Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem onAnswer_honest_eq (qep : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (SM.RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (st : LibsignalSim.SimState PQ Pt ℓ) :
    ∀ r ∈ support ((LibsignalSim.onAnswer qep Q w isDel ci? T pq' res).run st),
      r.2.honest = st.honest := by
  intro r hr
  unfold LibsignalSim.onAnswer LibsignalSim.onAccept LibsignalSim.putS at hr
  cases res with
  | none => simp at hr; rcases hr with rfl; rfl
  | some rr =>
    cases rr with
    | rejected => simp at hr; rcases hr with rfl; rfl
    | accepted t i pm =>
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
      split_ifs at hr
      · cases htr : st.mir.inTransit Q.other w <;>
          simp [htr, StateT.run_set] at hr <;>
          rcases hr with rfl <;> rfl
      · simp [StateT.run_pure] at hr; rcases hr with rfl; rfl
      · simp [StateT.run_set] at hr; rcases hr with rfl; rfl
      · simp [StateT.run_set] at hr; rcases hr with rfl; rfl

omit [DecidableEq Pt] [Zero Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem ite_putS_bind_run {α : Type} (b : Bool) (s' s : LibsignalSim.SimState PQ Pt ℓ)
    (m : StateT (LibsignalSim.SimState PQ Pt ℓ) (LibsignalSim.Fig8Comp Pt ℓ) α) :
    (if b then do LibsignalSim.putS s'; m else m).run s =
      m.run (if b then s' else s) := by
  cases b
  · rfl
  · simp only [↓reduceIte, LibsignalSim.putS, StateT.run_bind, StateT.run_set, pure_bind]

omit [Inhabited PQ] [SampleableType PQC] in
private theorem simRecv_none_honestWire (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (st : LibsignalSim.SimState PQ Pt ℓ) (hWire : HonestWireInv (Pt := Pt) st) :
    ∀ r ∈ support ((LibsignalSim.simRecv P encT decT qep none Q w isDel).run st),
      HonestWireInv (Pt := Pt) r.2 := by
  intro r hr
  suffices h : r.2.honest = st.honest by intro wc hwc; exact hWire wc (h ▸ hwc)
  unfold LibsignalSim.simRecv at hr
  rw [StateT.run_bind, StateT.run_get, pure_bind] at hr
  by_cases hwin : st.mir.win = true
  · simp only [hwin, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; rfl
  · simp only [hwin, Bool.false_eq_true, ↓reduceIte] at hr
    by_cases hdelRef : (isDel && (st.mir.inTransit Q.other w).isNone) = true
    · simp only [hdelRef, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; rfl
    · simp only [hdelRef, Bool.false_eq_true, ↓reduceIte] at hr
      by_cases hinjRef : (!isDel && ((st.mir.inTransit Q.other w).isSome ||
          !(st.mir.safeInj 3) || !(ratchetKeyAdmissible P.codec decT encT w))) = true
      · simp only [hinjRef, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; rfl
      · simp only [hinjRef, Bool.false_eq_true, ↓reduceIte] at hr
        by_cases hlen : w.length < 9
        · simp only [hlen, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; rfl
        · simp only [hlen, ↓reduceIte] at hr
          rcases hwire : (LibsignalSession.signalWireCodec P.codec).parse (w.take (w.length - 8))
              with _ | ⟨h, rest⟩
          · simp only [hwire, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
            subst hr; rfl
          · simp only [hwire] at hr
            by_cases haddr : (!(addressCheckPasses h.addresses (P.expectedAddrs Q))) = true
            · simp only [haddr, ↓reduceIte, StateT.run_pure, support_pure,
                Set.mem_singleton_iff] at hr
              subst hr; rfl
            · simp only [haddr, Bool.false_eq_true, ↓reduceIte] at hr
              rcases hspqr : P.spqr.recv (st.pq Q) h.pqRatchet with _ | ⟨pq', salt⟩
              · simp only [hspqr, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
                subst hr; rfl
              · simp only [hspqr] at hr
                rcases hidx : (st.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey)
                    with _ | ci
                · simp only [hidx] at hr
                  set honestC := (st.honest.find? fun wc =>
                    wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)
                  by_cases hevCond :
                      ((honestC.map fun c => decide (c.1.1 ≠ st.mir.epoch Q + 1)) == some true) = true
                  · simp only [hevCond, ↓reduceIte, StateT.run_pure, support_pure,
                      Set.mem_singleton_iff] at hr
                    subst hr; rfl
                  · simp only [hevCond, Bool.false_eq_true, ↓reduceIte] at hr
                    by_cases hzCond : (decT h.senderRatchetKey == some 0) = true
                    · simp only [hzCond, ↓reduceIte, StateT.run_pure, support_pure,
                        Set.mem_singleton_iff] at hr
                      subst hr; rfl
                    · simp only [hzCond, Bool.false_eq_true, ↓reduceIte] at hr
                      rw [ite_putS_bind_run] at hr
                      set amb := LibsignalSim.inReceiveOnlyEpoch st.mir Q ||
                        (Q == Party.A && (st.chains Q).any (·.key.isNone))
                      set stAmb := if amb then { st with amb := st.amb + 1 } else st
                      have hAmb_h : stAmb.honest = st.honest := by
                        dsimp only [stAmb]; split_ifs <;> rfl
                      have hnone : ((none : Option ℕ) == some st.amb) = false := rfl
                      simp only [hnone, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hr
                      by_cases hinw : (LibsignalSim.inReceiveOnlyEpoch st.mir Q ||
                          decide (25000 < h.counter.toNat + 1 - 1) ||
                          decide (2 ^ 32 ≤ h.counter.toNat + 1)) = true
                      · simp only [hinw, ↓reduceIte, StateT.run_pure, support_pure,
                          Set.mem_singleton_iff] at hr
                        subst hr; exact hAmb_h
                      · simp only [hinw, Bool.false_eq_true, ↓reduceIte] at hr
                        rcases hdec : decT h.senderRatchetKey with _ | T
                        · simp only [hdec, StateT.run_pure, support_pure,
                            Set.mem_singleton_iff] at hr
                          subst hr; exact hAmb_h
                        · simp only [hdec, StateT.run_bind, LibsignalSim.fwd_run_eq, bind_assoc,
                            pure_bind, mem_support_bind_iff] at hr
                          obtain ⟨res, -, hr⟩ := hr
                          exact (onAnswer_honest_eq qep Q w isDel none _ _ res stAmb r hr).trans hAmb_h
                · simp only [hidx] at hr
                  set g := (st.chains Q).getD ci ⟨none, 0, 0, []⟩
                  by_cases hrej : g.rejects (h.counter.toNat + 1) = true
                  · simp only [hrej, ↓reduceIte, StateT.run_pure, support_pure,
                      Set.mem_singleton_iff] at hr
                    subst hr; rfl
                  · simp only [hrej, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
                      LibsignalSim.fwd_run_eq, bind_assoc, pure_bind, mem_support_bind_iff] at hr
                    obtain ⟨res, -, hr⟩ := hr
                    exact onAnswer_honest_eq qep Q w isDel (some ci) _ _ res st r hr

omit [DecidableEq Pt] [Zero Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem simCorrDedup_honestWire (Q : Party) (st : LibsignalSim.SimState PQ Pt ℓ)
    (hWire : HonestWireInv (Pt := Pt) st) :
    ∀ r ∈ support ((LibsignalSim.simCorrDedup P Dh encT Q).run st),
      HonestWireInv (Pt := Pt) r.2 := by
  intro r hr
  suffices h : r.2.honest = st.honest by intro wc hwc; exact hWire wc (h ▸ hwc)
  unfold LibsignalSim.simCorrDedup at hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
  by_cases h1 : (st.mir.win || !(st.mir.corrAllowed Q) ||
      LibsignalSim.inReceiveOnlyEpoch st.mir Q ||
      !(noAliceCorrWhileAliceBelowEpoch10 st.mir Q)) = true
  · simp only [h1, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; rfl
  · simp only [h1, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨⟨res, s_res⟩, hres, hr⟩ := hr
    have hsres : s_res = st := by simp [LibsignalSim.liftQ] at hres; exact hres.2.symm
    rw [hsres] at hr
    rcases res with _ | fig8st
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; rfl
    · simp only [LibsignalSim.putS, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hr
      subst hr; rfl

omit [Inhabited PQ] in
private theorem simImplDedup_honestWire (qep : ℕ)
    (t : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (st : LibsignalSim.SimState PQ Pt ℓ) (hWire : HonestWireInv (Pt := Pt) st) :
    ∀ r ∈ support ((LibsignalSim.simImplDedup P Dh encT decT qep none (.inr t)).run st),
      HonestWireInv (Pt := Pt) r.2 := by
  rcases t with (((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q
  · exact guard_honestWire _ st hWire (simSend_honestWire P qep Q m₀ none r st hWire)
  · exact guard_honestWire _ st hWire (simSend_honestWire P qep Q m₀ (some m₁) r st hWire)
  · exact guard_honestWire _ st hWire (simRecv_none_honestWire P encT decT qep Q w true st hWire)
  · exact guard_honestWire _ st hWire (simRecv_none_honestWire P encT decT qep Q w false st hWire)
  · exact guard_honestWire _ st hWire (simCorrDedup_honestWire P Dh encT Q st hWire)

end SimFastCongr

end SimFastEval

/-- Concrete `Refine.SimProg` witness backed by `simProgFast`. -/
def simProgInst {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (q qep : ℕ) :
    Refine.SimProg PQ PQC Pt ℓ P Dh encT decT :=
  simProgFast (ℓ := ℓ) P Dh encT decT q qep

theorem evalSim_simProgInst {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (q qep : ℕ)
    (A : SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
    (hq : SM.MakesAtMostQueries A q) :
    Refine.evalSim (simProgInst (ℓ := ℓ) P Dh encT decT q qep) A =
      Refine.sim P ℓ Dh encT decT qep A := by
  let R₁ := simProgFast (ℓ := ℓ) P Dh encT decT q qep
  let R₂ := LibsignalSim.simProg (ℓ := ℓ) P Dh encT decT q qep
  suffices heq : R₁.eval (fun _ => A) () = R₂.eval (fun _ => A) () by
    exact heq.trans (LibsignalSim.simProg_eval (ℓ := ℓ) P Dh encT decT q qep A q hq le_rfl)
  have hinit_inv : ∀ r ∈ support (R₁.init.eval (.cons () .nil)),
      SimFastInv (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ) q q r.2 := by
    rintro ⟨u₀, (s₀ : (@LibsignalSim.simStateTy PQ PQC Pt ℓ).denote)⟩ hr
    change (u₀, s₀) ∈ support ((LibsignalSim.simInitC (ℓ := ℓ) P Dh encT decT).eval (.cons () .nil)) at hr
    rw [LibsignalSim.simInitC_eval, mem_support_bind_iff] at hr
    obtain ⟨pqrKey, -, hr⟩ := hr
    rw [support_pure, Set.mem_singleton_iff] at hr
    injection hr with _ hs₀; subst hs₀
    exact ⟨(LibsignalSim.simBoundInv_simStateEnc q q _).mpr (LibsignalSim.SimStateInv.init le_rfl _ _),
      by simp [HonestWireInv, LibsignalSim.simStateDec_simStateEnc, LibsignalSim.initSim]⟩
  have hstep : ∀ m t s, SimFastInv (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ) q (m + 1) s →
      (Prod.map id id <$> (R₁.impl (.inr t)).run s) = (R₂.impl (.inr t)).run s ∧
      ∀ r ∈ support ((R₁.impl (.inr t)).run s),
        SimFastInv (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ) q m r.2 := by
    intro m t s hs
    have heq : (R₁.impl (.inr t)).run s = (R₂.impl (.inr t)).run s :=
      simProgFast_impl_inr_eq P Dh encT decT q qep t s hs.1.toBounded hs.2
    refine ⟨by rw [heq, Prod.map_id]; exact id_map _, fun r hr => ?_⟩
    rw [heq] at hr
    obtain ⟨habs, hinvB⟩ := LibsignalSim.simRunProg_step P Dh encT decT q qep none m t s hs.1
    refine ⟨hinvB r hr, ?_⟩
    have hmem : (r.1, LibsignalSim.simStateDec r.2) ∈
        support ((LibsignalSim.simImplDedup P Dh encT decT qep none (.inr t)).run
          (LibsignalSim.simStateDec s)) := by
      rw [← habs, support_map, Set.mem_image]; exact ⟨r, hr, rfl⟩
    exact simImplDedup_honestWire P Dh encT decT qep t (LibsignalSim.simStateDec s) hs.2 _ hmem
  have hqb : A.IsQueryBoundP
      (ReductionDsl.isGameQuery (G := SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))) q :=
    (LibsignalSim.makesAtMostQueries_iff_isGameQuery A q).mp hq
  exact R₁.eval_eq_simulateQ_of_abs id
    (SimFastInv (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ) q)
    (fun u => R₂.init.eval (.cons u .nil)) R₂.impl
    (fun s b => R₂.finish.eval (.cons s (.cons b .nil))) q ()
    (by simp [R₁, R₂, simProgFast, LibsignalSim.simProg, LibsignalSim.simRunProg, map_eq_bind_pure_comp])
    hinit_inv (fun _ _ => rfl) hstep (fun _ _ _ => rfl)
    (fun _ hle hv => ⟨hv.1.mono hle, hv.2⟩) (fun _ => A) (fun _ => hqb)

section SimCostHelpers

open Computational.Proofs.GameHop.ReductionDsl.CostUB

variable {PQ PQC : Type} [SampleableType PQC] {ℓ : ℕ}
variable (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)

local notation "S" => LibsignalSim.simSig PQ PQC Pt ℓ
local notation "OO" => LibsignalSim.simOps (ℓ := ℓ) P Dh encT decT

private lemma bits_five : ReductionDsl.bits 5 = 3 := rfl
private lemma bits_ten : ReductionDsl.bits 10 = 4 := rfl
private lemma bits_25k : ReductionDsl.bits 25000 = 15 := rfl
private lemma bits_2p32 : ReductionDsl.bits (2 ^ 32) = 33 := rfl

private lemma simSendC_cost_le (qep : ℕ) {Γ} (s : ReductionDsl.Expr OO Γ LibsignalSim.simStateTy)
    (qParty : ReductionDsl.Expr OO Γ .bool) (m₀ : ReductionDsl.Expr OO Γ (.base .plain))
    (chal : ReductionDsl.Expr OO Γ (.opt (.base .plain)))
    (r : ReductionDsl.Expr OO Γ (.opt (.base .pqc))) :
    (LibsignalSim.simSendC (P := P) (Dh := Dh) (encT := encT) (decT := decT)
      qep s qParty m₀ chal r).cost ≤
      exprCostUB s + exprCostUB qParty + exprCostUB m₀ + exprCostUB chal + exprCostUB r +
        5 * ReductionDsl.bits qep + 4000 := by
  refine (compCost_le_costUB _).trans ?_
  simp only [LibsignalSim.simSendC, LibsignalSim.simDrawSendCoinsC,
    LibsignalSim.simSendPostCoinsC, LibsignalSim.simSendPostQueryC,
    LibsignalSim.spqrSendPubE, LibsignalSim.mNoBobEpoch0E, LibsignalSim.mEpMgmtE,
    LibsignalSim.mSafeChE, LibsignalSim.mLeakE, LibsignalSim.mRecordE,
    LibsignalSim.ssMk, LibsignalSim.ssMir, LibsignalSim.ssPq, LibsignalSim.ssPn,
    LibsignalSim.ssUnackA, LibsignalSim.ssHonest, LibsignalSim.ssChains,
    LibsignalSim.ssAmb, LibsignalSim.ssStopped,
    LibsignalSim.mMk, LibsignalSim.mB, LibsignalSim.mWin, LibsignalSim.mEpoch,
    LibsignalSim.mIdx, LibsignalSim.mTL, LibsignalSim.mTrans, LibsignalSim.mChall,
    LibsignalSim.mComp, LibsignalSim.mMaxAcc, LibsignalSim.mLeaks, LibsignalSim.mCorrs,
    SM.orE, SM.isSomeE, SM.pGet, SM.pSet, SM.sendsInE, SM.healedByE, SM.leN,
    SM.maxOptE, SM.maxN, SM.posIdx,
    ReductionDsl.Expr.v0, ReductionDsl.Expr.v1,
    LibsignalSim.simOps, LibsignalSim.simOpCost, LibsignalSim.simIface,
    LibsignalSim.simParamIface, LibsignalSim.simParamSamplers,
    ReductionDsl.unifSamplers, LibsignalSim.simBaseSampCost,
    dsl_cost, exprCostUB, Nat.reduceAdd]
  omega

private lemma simRecvC_cost_le (K qep : ℕ) {Γ} (s : ReductionDsl.Expr OO Γ LibsignalSim.simStateTy)
    (qParty : ReductionDsl.Expr OO Γ .bool) (w : ReductionDsl.Expr OO Γ (.base .wire))
    (isDel : ReductionDsl.Expr OO Γ .bool) :
    (LibsignalSim.simRecvC (P := P) (Dh := Dh) (encT := encT) (decT := decT)
      K qep none s qParty w isDel).cost ≤
      exprCostUB s + exprCostUB qParty + exprCostUB w + exprCostUB isDel +
        5 * ReductionDsl.bits qep + 5000 * K + 1000 * (K * K) + 26010 := by
  have hqep1 : ReductionDsl.bits (qep + 1) ≤ ReductionDsl.bits qep + 1 := by
    have hadd := ReductionDsl.bits_add qep 1
    have h1 : ReductionDsl.bits 1 = 1 := rfl
    have hb := ReductionDsl.one_le_bits qep
    omega
  refine (compCost_le_costUB _).trans ?_
  simp only [LibsignalSim.simRecvC, LibsignalSim.simRecvNewChainNormalC,
    LibsignalSim.onAnswerE, LibsignalSim.onAcceptE, LibsignalSim.onAcceptPreE,
    LibsignalSim.fwdC, LibsignalSim.inTE, LibsignalSim.honestCE, LibsignalSim.mkCE,
    LibsignalSim.evictedHonestE, LibsignalSim.sAmbE, LibsignalSim.ambCondE,
    LibsignalSim.spkAmbE, LibsignalSim.hasUnknownKeyE, LibsignalSim.findChainE,
    LibsignalSim.modifyChainAcceptE, LibsignalSim.pushChainE, LibsignalSim.parseRecvE,
    LibsignalSim.mInTransitE, LibsignalSim.mSafeInjE, LibsignalSim.mInWinE,
    LibsignalSim.mChallContainsE, LibsignalSim.mCompContainsE, LibsignalSim.mTrivialE,
    LibsignalSim.mAcceptE, LibsignalSim.mDeleteE,
    LibsignalSim.ssSetMir, LibsignalSim.ssSetAmb, LibsignalSim.ssSetMirWin,
    LibsignalSim.mSetWin, LibsignalSim.srecPos, LibsignalSim.srecCt,
    LibsignalSim.ssMk, LibsignalSim.ssMir, LibsignalSim.ssPq, LibsignalSim.ssPn,
    LibsignalSim.ssUnackA, LibsignalSim.ssHonest, LibsignalSim.ssChains,
    LibsignalSim.ssAmb, LibsignalSim.ssStopped,
    LibsignalSim.mMk, LibsignalSim.mB, LibsignalSim.mWin, LibsignalSim.mEpoch,
    LibsignalSim.mIdx, LibsignalSim.mTL, LibsignalSim.mTrans, LibsignalSim.mChall,
    LibsignalSim.mComp, LibsignalSim.mMaxAcc, LibsignalSim.mLeaks, LibsignalSim.mCorrs,
    SM.orE, SM.isSomeE, SM.otherE, SM.pGet, SM.pSet, SM.sendsInE, SM.healedByE,
    SM.leN, SM.minN, SM.maxN, SM.maxAccSet, SM.maxAccGet,
    SM.posEq, SM.posSender, SM.posEpoch, SM.posIdx, SM.boolEq, SM.senderOfE,
    LibsignalSim.simOps, LibsignalSim.simOpCost, LibsignalSim.simIface,
    LibsignalSim.simParamIface, bits_five, bits_25k, bits_2p32,
    dsl_cost, Nat.reduceAdd]
  nlinarith [Nat.zero_le (K * K)]

private lemma simCorrC_cost_le (K : ℕ) {Γ} (s : ReductionDsl.Expr OO Γ LibsignalSim.simStateTy)
    (qParty : ReductionDsl.Expr OO Γ .bool) :
    (LibsignalSim.simCorrC (P := P) (Dh := Dh) (encT := encT) (decT := decT)
      K s qParty).cost ≤
      exprCostUB s + exprCostUB qParty + 1000 * K + 1000 * (K * K) + 8000 := by
  refine (compCost_le_costUB _).trans ?_
  simp only [LibsignalSim.simCorrC, LibsignalSim.mCorrAllowedE, LibsignalSim.mCompContainsE,
    LibsignalSim.mInWinE, LibsignalSim.mNoSpkCorrE, LibsignalSim.mAfterCorrE,
    LibsignalSim.mLeakE, LibsignalSim.revealSpkChainsE, LibsignalSim.toGhostE,
    LibsignalSim.ssMk, LibsignalSim.ssMir, LibsignalSim.ssPq, LibsignalSim.ssPn,
    LibsignalSim.ssUnackA, LibsignalSim.ssHonest, LibsignalSim.ssChains,
    LibsignalSim.ssAmb, LibsignalSim.ssStopped,
    LibsignalSim.mMk, LibsignalSim.mB, LibsignalSim.mWin, LibsignalSim.mEpoch,
    LibsignalSim.mIdx, LibsignalSim.mTL, LibsignalSim.mTrans, LibsignalSim.mChall,
    LibsignalSim.mComp, LibsignalSim.mMaxAcc, LibsignalSim.mLeaks, LibsignalSim.mCorrs,
    SM.orE, SM.otherE, SM.pGet, SM.sendsInE, SM.leN, SM.maxOptE, SM.maxN,
    SM.posEq, SM.posSender, SM.posEpoch, SM.posIdx, SM.boolEq,
    LibsignalSim.simOps, LibsignalSim.simOpCost, LibsignalSim.simIface,
    LibsignalSim.simParamIface, bits_ten,
    dsl_cost, Nat.reduceAdd]
  nlinarith [Nat.zero_le (K * K)]

end SimCostHelpers

private abbrev simCtxBase (PQ PQC : Type) (ℓ : ℕ) :
    List (ReductionDsl.Ty (LibsignalSim.simSig PQ PQC Pt ℓ)) :=
  [LibsignalSim.simStateTy (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ),
   (LibsignalSim.simCodec PQ PQC Pt ℓ).Q]

private abbrev simQ1Ty (PQ PQC : Type) (ℓ : ℕ) :
    ReductionDsl.Ty (LibsignalSim.simSig PQ PQC Pt ℓ) :=
  .sum (.prod .bool (.prod (.base .plain) (.opt (.base .pqc))))
    (.prod .bool (.prod (.base .plain) (.prod (.base .plain) (.opt (.base .pqc)))))

private abbrev simQ2Ty (PQ PQC : Type) (ℓ : ℕ) :
    ReductionDsl.Ty (LibsignalSim.simSig PQ PQC Pt ℓ) :=
  .sum (simQ1Ty (Pt := Pt) PQ PQC ℓ) (.prod .bool (.base .wire))

private abbrev simQ3Ty (PQ PQC : Type) (ℓ : ℕ) :
    ReductionDsl.Ty (LibsignalSim.simSig PQ PQC Pt ℓ) :=
  .sum (simQ2Ty (Pt := Pt) PQ PQC ℓ) (.prod .bool (.base .wire))

private abbrev simCtxCr (PQ PQC : Type) (ℓ : ℕ) :
    List (ReductionDsl.Ty (LibsignalSim.simSig PQ PQC Pt ℓ)) :=
  .bool :: simCtxBase (Pt := Pt) PQ PQC ℓ

private abbrev simCtxIj (PQ PQC : Type) (ℓ : ℕ) :
    List (ReductionDsl.Ty (LibsignalSim.simSig PQ PQC Pt ℓ)) :=
  .prod .bool (.base .wire) :: simQ3Ty (Pt := Pt) PQ PQC ℓ :: simCtxBase (Pt := Pt) PQ PQC ℓ

private abbrev simCtxDl (PQ PQC : Type) (ℓ : ℕ) :
    List (ReductionDsl.Ty (LibsignalSim.simSig PQ PQC Pt ℓ)) :=
  .prod .bool (.base .wire) :: simQ2Ty (Pt := Pt) PQ PQC ℓ :: simQ3Ty (Pt := Pt) PQ PQC ℓ ::
    simCtxBase (Pt := Pt) PQ PQC ℓ

private abbrev simCtxTr (PQ PQC : Type) (ℓ : ℕ) :
    List (ReductionDsl.Ty (LibsignalSim.simSig PQ PQC Pt ℓ)) :=
  .prod .bool (.prod (.base .plain) (.opt (.base .pqc))) ::
    simQ1Ty (Pt := Pt) PQ PQC ℓ :: simQ2Ty (Pt := Pt) PQ PQC ℓ :: simQ3Ty (Pt := Pt) PQ PQC ℓ ::
    simCtxBase (Pt := Pt) PQ PQC ℓ

private abbrev simCtxCh (PQ PQC : Type) (ℓ : ℕ) :
    List (ReductionDsl.Ty (LibsignalSim.simSig PQ PQC Pt ℓ)) :=
  .prod .bool (.prod (.base .plain) (.prod (.base .plain) (.opt (.base .pqc)))) ::
    simQ1Ty (Pt := Pt) PQ PQC ℓ :: simQ2Ty (Pt := Pt) PQ PQC ℓ :: simQ3Ty (Pt := Pt) PQ PQC ℓ ::
    simCtxBase (Pt := Pt) PQ PQC ℓ

lemma simHandleC_cost_le {PQ PQC : Type} [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (K qep : ℕ) :
    (LibsignalSim.simHandleC (ℓ := ℓ) P Dh encT decT K qep none).cost ≤
      5 * ReductionDsl.bits qep + 5000 * K + 1000 * (K * K) + 31010 := by
  have hb_tr := simSendC_cost_le P Dh encT decT qep (Γ := simCtxTr (Pt := Pt) PQ PQC ℓ)
    .v4 (.fst .v0) (.fst (.snd .v0)) .none (.snd (.snd .v0))
  have hb_ch := simSendC_cost_le P Dh encT decT qep (Γ := simCtxCh (Pt := Pt) PQ PQC ℓ)
    .v4 (.fst .v0) (.fst (.snd .v0)) (.some (.fst (.snd (.snd .v0)))) (.snd (.snd (.snd .v0)))
  have hb_dl := simRecvC_cost_le P Dh encT decT K qep (Γ := simCtxDl (Pt := Pt) PQ PQC ℓ)
    .v3 (.fst .v0) (.snd .v0) (.bool true)
  have hb_ij := simRecvC_cost_le P Dh encT decT K qep (Γ := simCtxIj (Pt := Pt) PQ PQC ℓ)
    .v2 (.fst .v0) (.snd .v0) (.bool false)
  have hb_cr := simCorrC_cost_le P Dh encT decT K (Γ := simCtxCr (Pt := Pt) PQ PQC ℓ)
    .v1 .v0
  simp only [dsl_cost, Nat.reduceAdd] at hb_tr hb_ch hb_dl hb_ij hb_cr
  simp only [LibsignalSim.simHandleC, LibsignalSim.guardC, LibsignalSim.ssStopped,
    ReductionDsl.Comp.cost, ReductionDsl.Expr.cost, dsl_cost, Nat.reduceAdd]
  omega

private lemma sim_bits_small_consts :
    ReductionDsl.bits 0 = 1 ∧ ReductionDsl.bits 1 = 1 ∧ ReductionDsl.bits 2 ≤ 2 ∧
      ReductionDsl.bits 3 ≤ 2 ∧ ReductionDsl.bits 4 ≤ 3 ∧ ReductionDsl.bits 5 ≤ 3 ∧
      ReductionDsl.bits 10 ≤ 4 ∧ ReductionDsl.bits 2000 ≤ 11 ∧
      ReductionDsl.bits 25000 ≤ 15 ∧ ReductionDsl.bits (2 ^ 32) ≤ 33 :=
  ⟨rfl, rfl, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

private lemma sim_expr_size_v0 {S0 : ReductionDsl.Sig} {O' : ReductionDsl.Ops S0}
    {t : ReductionDsl.Ty S0} {Γ : List (ReductionDsl.Ty S0)} :
    (ReductionDsl.Expr.v0 (O := O') (t := t) (Γ := Γ)).size = 1 := rfl
private lemma sim_expr_size_v1 {S0 : ReductionDsl.Sig} {O' : ReductionDsl.Ops S0}
    {a t : ReductionDsl.Ty S0} {Γ : List (ReductionDsl.Ty S0)} :
    (ReductionDsl.Expr.v1 (O := O') (a := a) (t := t) (Γ := Γ)).size = 1 := rfl
private lemma sim_expr_size_v2 {S0 : ReductionDsl.Sig} {O' : ReductionDsl.Ops S0}
    {a b t : ReductionDsl.Ty S0} {Γ : List (ReductionDsl.Ty S0)} :
    (ReductionDsl.Expr.v2 (O := O') (a := a) (b := b) (t := t) (Γ := Γ)).size = 1 := rfl
private lemma sim_expr_size_v3 {S0 : ReductionDsl.Sig} {O' : ReductionDsl.Ops S0}
    {a b c t : ReductionDsl.Ty S0} {Γ : List (ReductionDsl.Ty S0)} :
    (ReductionDsl.Expr.v3 (O := O') (a := a) (b := b) (c := c) (t := t) (Γ := Γ)).size = 1 := rfl
private lemma sim_expr_size_v4 {S0 : ReductionDsl.Sig} {O' : ReductionDsl.Ops S0}
    {a b c d t : ReductionDsl.Ty S0} {Γ : List (ReductionDsl.Ty S0)} :
    (ReductionDsl.Expr.v4 (O := O') (a := a) (b := b) (c := c) (d := d) (t := t) (Γ := Γ)).size = 1 := rfl

set_option linter.unusedSimpArgs false in
private lemma simSendC_size_le {PQ PQC : Type} [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) {Γ}
    (s : ReductionDsl.Expr (LibsignalSim.simOps (ℓ := ℓ) P Dh encT decT) Γ LibsignalSim.simStateTy)
    (qParty : ReductionDsl.Expr (LibsignalSim.simOps (ℓ := ℓ) P Dh encT decT) Γ .bool)
    (m₀ : ReductionDsl.Expr (LibsignalSim.simOps (ℓ := ℓ) P Dh encT decT) Γ (.base .plain))
    (chal : ReductionDsl.Expr (LibsignalSim.simOps (ℓ := ℓ) P Dh encT decT) Γ (.opt (.base .plain)))
    (r : ReductionDsl.Expr (LibsignalSim.simOps (ℓ := ℓ) P Dh encT decT) Γ (.opt (.base .pqc))) :
    (LibsignalSim.simSendC (P := P) (Dh := Dh) (encT := encT) (decT := decT)
        qep s qParty m₀ chal r).size ≤
      20 * (s.size + qParty.size + m₀.size + chal.size + r.size) +
        8 * ReductionDsl.bits qep + 20000 := by
  rcases sim_bits_small_consts with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb10, hb2000, hb25000, hb32⟩
  simp only [LibsignalSim.simSendC, LibsignalSim.simDrawSendCoinsC,
    LibsignalSim.simSendPostCoinsC, LibsignalSim.simSendPostQueryC,
    LibsignalSim.spqrSendPubE, LibsignalSim.mNoBobEpoch0E, LibsignalSim.mEpMgmtE,
    LibsignalSim.mSafeChE, LibsignalSim.mLeakE, LibsignalSim.mRecordE,
    LibsignalSim.ssMk, LibsignalSim.ssMir, LibsignalSim.ssPq, LibsignalSim.ssPn,
    LibsignalSim.ssUnackA, LibsignalSim.ssHonest, LibsignalSim.ssChains,
    LibsignalSim.ssAmb, LibsignalSim.ssStopped,
    LibsignalSim.mMk, LibsignalSim.mB, LibsignalSim.mWin, LibsignalSim.mEpoch,
    LibsignalSim.mIdx, LibsignalSim.mTL, LibsignalSim.mTrans, LibsignalSim.mChall,
    LibsignalSim.mComp, LibsignalSim.mMaxAcc, LibsignalSim.mLeaks, LibsignalSim.mCorrs,
    SM.orE, SM.isSomeE, SM.pGet, SM.pSet, SM.sendsInE, SM.healedByE, SM.leN,
    SM.maxOptE, SM.maxN, SM.posIdx, LibsignalSim.simOps,
    ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Expr.v2,
    ReductionDsl.Expr.v3, ReductionDsl.Expr.v4, ReductionDsl.Expr.v5,
    ReductionDsl.Comp.size, ReductionDsl.Expr.size,
    maxForwardJumps, maxMessageKeys, maxReceiverChains]
  omega

set_option linter.unusedSimpArgs false in
private lemma simRecvC_size_le {PQ PQC : Type} [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (K qep : ℕ) {Γ}
    (s : ReductionDsl.Expr (LibsignalSim.simOps (ℓ := ℓ) P Dh encT decT) Γ LibsignalSim.simStateTy)
    (qParty : ReductionDsl.Expr (LibsignalSim.simOps (ℓ := ℓ) P Dh encT decT) Γ .bool)
    (w : ReductionDsl.Expr (LibsignalSim.simOps (ℓ := ℓ) P Dh encT decT) Γ (.base .wire))
    (isDel : ReductionDsl.Expr (LibsignalSim.simOps (ℓ := ℓ) P Dh encT decT) Γ .bool) :
    (LibsignalSim.simRecvC (P := P) (Dh := Dh) (encT := encT) (decT := decT)
        K qep none s qParty w isDel).size ≤
      20 * (s.size + qParty.size + w.size + isDel.size) +
        50 * ReductionDsl.bits K + 8 * ReductionDsl.bits qep +
        8 * ReductionDsl.bits (qep + 1) + 50000 := by
  rcases sim_bits_small_consts with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb10, hb2000, hb25000, hb32⟩
  have h1K := ReductionDsl.one_le_bits K
  have hK1 : ReductionDsl.bits (K + 1) ≤ ReductionDsl.bits K + 1 := by
    have h := ReductionDsl.bits_add K 1; rw [hb1] at h; omega
  have h2K : ReductionDsl.bits (2 * K) ≤ ReductionDsl.bits K + 2 := by
    have h := ReductionDsl.bits_mul 2 K; omega
  simp only [LibsignalSim.simRecvC, LibsignalSim.simRecvNewChainNormalC,
    LibsignalSim.onAnswerE, LibsignalSim.onAcceptE, LibsignalSim.onAcceptPreE,
    LibsignalSim.fwdC, LibsignalSim.inTE, LibsignalSim.honestCE, LibsignalSim.mkCE,
    LibsignalSim.evictedHonestE, LibsignalSim.sAmbE, LibsignalSim.ambCondE,
    LibsignalSim.spkAmbE, LibsignalSim.hasUnknownKeyE, LibsignalSim.findChainE,
    LibsignalSim.modifyChainAcceptE, LibsignalSim.pushChainE, LibsignalSim.parseRecvE,
    LibsignalSim.mInTransitE, LibsignalSim.mSafeInjE, LibsignalSim.mInWinE,
    LibsignalSim.mChallContainsE, LibsignalSim.mCompContainsE, LibsignalSim.mTrivialE,
    LibsignalSim.mAcceptE, LibsignalSim.mDeleteE,
    LibsignalSim.ssSetMir, LibsignalSim.ssSetAmb, LibsignalSim.ssSetMirWin,
    LibsignalSim.mSetWin, LibsignalSim.srecPos, LibsignalSim.srecCt,
    LibsignalSim.ssMk, LibsignalSim.ssMir, LibsignalSim.ssPq, LibsignalSim.ssPn,
    LibsignalSim.ssUnackA, LibsignalSim.ssHonest, LibsignalSim.ssChains,
    LibsignalSim.ssAmb, LibsignalSim.ssStopped,
    LibsignalSim.mMk, LibsignalSim.mB, LibsignalSim.mWin, LibsignalSim.mEpoch,
    LibsignalSim.mIdx, LibsignalSim.mTL, LibsignalSim.mTrans, LibsignalSim.mChall,
    LibsignalSim.mComp, LibsignalSim.mMaxAcc, LibsignalSim.mLeaks, LibsignalSim.mCorrs,
    SM.orE, SM.isSomeE, SM.otherE, SM.pGet, SM.pSet, SM.sendsInE, SM.healedByE,
    SM.leN, SM.minN, SM.maxN, SM.maxAccSet, SM.maxAccGet,
    SM.posEq, SM.posSender, SM.posEpoch, SM.posIdx, SM.boolEq, SM.senderOfE,
    ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Expr.v2,
    ReductionDsl.Expr.v3, ReductionDsl.Expr.v4, ReductionDsl.Expr.v5,
    ReductionDsl.Comp.size, ReductionDsl.Expr.size,
    maxForwardJumps, maxMessageKeys, maxReceiverChains]
  omega

set_option linter.unusedSimpArgs false in
private lemma simCorrC_size_le {PQ PQC : Type} [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (K : ℕ) {Γ}
    (s : ReductionDsl.Expr (LibsignalSim.simOps (ℓ := ℓ) P Dh encT decT) Γ LibsignalSim.simStateTy)
    (qParty : ReductionDsl.Expr (LibsignalSim.simOps (ℓ := ℓ) P Dh encT decT) Γ .bool) :
    (LibsignalSim.simCorrC (P := P) (Dh := Dh) (encT := encT) (decT := decT) K s qParty).size ≤
      20 * (s.size + qParty.size) + 50 * ReductionDsl.bits K + 20000 := by
  rcases sim_bits_small_consts with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb10, hb2000, hb25000, hb32⟩
  have h1K := ReductionDsl.one_le_bits K
  have hK1 : ReductionDsl.bits (K + 1) ≤ ReductionDsl.bits K + 1 := by
    have h := ReductionDsl.bits_add K 1; rw [hb1] at h; omega
  have h2K : ReductionDsl.bits (2 * K) ≤ ReductionDsl.bits K + 2 := by
    have h := ReductionDsl.bits_mul 2 K; omega
  simp only [LibsignalSim.simCorrC, LibsignalSim.mCorrAllowedE, LibsignalSim.mCompContainsE,
    LibsignalSim.mInWinE, LibsignalSim.mNoSpkCorrE, LibsignalSim.mAfterCorrE,
    LibsignalSim.mLeakE, LibsignalSim.revealSpkChainsE, LibsignalSim.toGhostE,
    LibsignalSim.ssMk, LibsignalSim.ssMir, LibsignalSim.ssPq, LibsignalSim.ssPn,
    LibsignalSim.ssUnackA, LibsignalSim.ssHonest, LibsignalSim.ssChains,
    LibsignalSim.ssAmb, LibsignalSim.ssStopped,
    LibsignalSim.mMk, LibsignalSim.mB, LibsignalSim.mWin, LibsignalSim.mEpoch,
    LibsignalSim.mIdx, LibsignalSim.mTL, LibsignalSim.mTrans, LibsignalSim.mChall,
    LibsignalSim.mComp, LibsignalSim.mMaxAcc, LibsignalSim.mLeaks, LibsignalSim.mCorrs,
    SM.orE, SM.otherE, SM.pGet, SM.sendsInE, SM.leN, SM.maxOptE, SM.maxN,
    SM.posEq, SM.posSender, SM.posEpoch, SM.posIdx, SM.boolEq,
    ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Expr.v2,
    ReductionDsl.Expr.v3, ReductionDsl.Expr.v4, ReductionDsl.Expr.v5,
    ReductionDsl.Comp.size, ReductionDsl.Expr.size,
    maxForwardJumps, maxMessageKeys, maxReceiverChains]
  omega

set_option linter.unusedSimpArgs false in
lemma simProg_size_le {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (q qep : ℕ)
    (hbqep : ReductionDsl.bits qep ≤ 2 ^ 18 + 20 * ReductionDsl.bits (ratchetCostBudget q qep)) :
    (LibsignalSim.simProg (ℓ := ℓ) P Dh encT decT q qep).size ≤
      ReductionDsl.reductionSizeBudget + 2 ^ 12 * ReductionDsl.bits (ratchetCostBudget q qep) := by
  let R₀ := LibsignalSim.simProg (ℓ := ℓ) P Dh encT decT q qep
  rcases sim_bits_small_consts with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb10, hb2000, hb25000, hb32⟩
  have h1qep := ReductionDsl.one_le_bits qep
  have hq_le_bud : q ≤ ratchetCostBudget q qep := by
    unfold ratchetCostBudget maxForwardJumps; nlinarith
  have hbq_le : ReductionDsl.bits q ≤ ReductionDsl.bits (ratchetCostBudget q qep) :=
    Computational.Proofs.ReductionDsl.SizeBudgetBridge.bits_mono hq_le_bud
  have hbq1 : ReductionDsl.bits (qep + 1) ≤ ReductionDsl.bits qep + 1 := by
    have h := ReductionDsl.bits_add qep 1; rw [hb1] at h; omega
  have hinit_sz : R₀.init.size ≤ 5000 := by
    simp only [R₀, LibsignalSim.simProg, LibsignalSim.simRunProg, LibsignalSim.simInitC,
      LibsignalSim.initSimE, LibsignalSim.initChainAE, LibsignalSim.ssMk,
      LibsignalSim.initSimMirE, LibsignalSim.mMk,
      ReductionDsl.Expr.v0, ReductionDsl.Comp.size, ReductionDsl.Expr.size]
    omega
  have hfin_sz : R₀.finish.size ≤ 100 := by
    simp only [R₀, LibsignalSim.simProg, LibsignalSim.simRunProg, LibsignalSim.simFinishC,
      ReductionDsl.Expr.v1, ReductionDsl.Comp.size, ReductionDsl.Expr.size]
    omega
  have hhdl_sz : R₀.handle.size ≤ 200 * ReductionDsl.bits q + 50 * ReductionDsl.bits qep + 200000 := by
    have hs_tr := simSendC_size_le P Dh encT decT qep (Γ := simCtxTr (Pt := Pt) PQ PQC ℓ)
      .v4 (.fst .v0) (.fst (.snd .v0)) .none (.snd (.snd .v0))
    have hs_ch := simSendC_size_le P Dh encT decT qep (Γ := simCtxCh (Pt := Pt) PQ PQC ℓ)
      .v4 (.fst .v0) (.fst (.snd .v0)) (.some (.fst (.snd (.snd .v0)))) (.snd (.snd (.snd .v0)))
    have hs_dl := simRecvC_size_le P Dh encT decT q qep (Γ := simCtxDl (Pt := Pt) PQ PQC ℓ)
      .v3 (.fst .v0) (.snd .v0) (.bool true)
    have hs_ij := simRecvC_size_le P Dh encT decT q qep (Γ := simCtxIj (Pt := Pt) PQ PQC ℓ)
      .v2 (.fst .v0) (.snd .v0) (.bool false)
    have hs_cr := simCorrC_size_le P Dh encT decT q (Γ := simCtxCr (Pt := Pt) PQ PQC ℓ)
      .v1 .v0
    simp only [ReductionDsl.Expr.size, sim_expr_size_v0, sim_expr_size_v1,
      sim_expr_size_v2, sim_expr_size_v3, sim_expr_size_v4]
      at hs_tr hs_ch hs_dl hs_ij hs_cr
    dsimp only [R₀, LibsignalSim.simProg, LibsignalSim.simRunProg]
    simp only [LibsignalSim.simHandleC, LibsignalSim.guardC, LibsignalSim.ssStopped,
      ReductionDsl.Comp.size, ReductionDsl.Expr.size,
      sim_expr_size_v0, sim_expr_size_v1, sim_expr_size_v2, sim_expr_size_v3, sim_expr_size_v4]
    omega
  change R₀.size ≤ _
  simp only [ReductionDsl.CostedReduction.size, ReductionDsl.reductionSizeBudget]
  omega

section SimFastBounds

open Computational.Proofs.GameHop.ReductionDsl.CostUB

private lemma simRecvFastC_cost_le {PQ PQC : Type} [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (K qep : ℕ) {Γ}
    (s : ReductionDsl.Expr (LibsignalSim.simOps (ℓ := ℓ) P Dh encT decT) Γ LibsignalSim.simStateTy)
    (qParty : ReductionDsl.Expr (LibsignalSim.simOps (ℓ := ℓ) P Dh encT decT) Γ .bool)
    (w : ReductionDsl.Expr (LibsignalSim.simOps (ℓ := ℓ) P Dh encT decT) Γ (.base .wire))
    (isDel : ReductionDsl.Expr (LibsignalSim.simOps (ℓ := ℓ) P Dh encT decT) Γ .bool) :
    (simRecvFastC P Dh encT decT K qep s qParty w isDel).cost ≤
      exprCostUB s + exprCostUB qParty + exprCostUB w + exprCostUB isDel +
        5 * ReductionDsl.bits qep + 5000 * K + 28000 := by
  have hqep1 : ReductionDsl.bits (qep + 1) ≤ ReductionDsl.bits qep + 1 := by
    have hadd := ReductionDsl.bits_add qep 1
    have h1 : ReductionDsl.bits 1 = 1 := rfl
    have hb := ReductionDsl.one_le_bits qep
    omega
  refine (compCost_le_costUB _).trans ?_
  simp only [simRecvFastC, simRecvNewChainNormalFastC, fwdFastC, inTFastE,
    LibsignalSim.onAnswerE, LibsignalSim.onAcceptE, LibsignalSim.onAcceptPreE,
    LibsignalSim.honestCE, LibsignalSim.mkCE,
    LibsignalSim.evictedHonestE, LibsignalSim.sAmbE, LibsignalSim.ambCondE,
    LibsignalSim.spkAmbE, LibsignalSim.hasUnknownKeyE, LibsignalSim.findChainE,
    LibsignalSim.modifyChainAcceptE, LibsignalSim.pushChainE, LibsignalSim.parseRecvE,
    LibsignalSim.mInTransitE, LibsignalSim.mSafeInjE, LibsignalSim.mInWinE,
    LibsignalSim.mChallContainsE, LibsignalSim.mCompContainsE, LibsignalSim.mTrivialE,
    LibsignalSim.mAcceptE, LibsignalSim.mDeleteE,
    LibsignalSim.ssSetMir, LibsignalSim.ssSetAmb, LibsignalSim.ssSetMirWin,
    LibsignalSim.mSetWin, LibsignalSim.srecPos, LibsignalSim.srecCt,
    LibsignalSim.ssMk, LibsignalSim.ssMir, LibsignalSim.ssPq, LibsignalSim.ssPn,
    LibsignalSim.ssUnackA, LibsignalSim.ssHonest, LibsignalSim.ssChains,
    LibsignalSim.ssAmb, LibsignalSim.ssStopped,
    LibsignalSim.mMk, LibsignalSim.mB, LibsignalSim.mWin, LibsignalSim.mEpoch,
    LibsignalSim.mIdx, LibsignalSim.mTL, LibsignalSim.mTrans, LibsignalSim.mChall,
    LibsignalSim.mComp, LibsignalSim.mMaxAcc, LibsignalSim.mLeaks, LibsignalSim.mCorrs,
    SM.orE, SM.isSomeE, SM.otherE, SM.pGet, SM.pSet, SM.sendsInE, SM.healedByE,
    SM.leN, SM.minN, SM.maxN, SM.maxAccSet, SM.maxAccGet,
    SM.posEq, SM.posSender, SM.posEpoch, SM.posIdx, SM.boolEq, SM.senderOfE,
    LibsignalSim.simOps, LibsignalSim.simOpCost, LibsignalSim.simIface,
    LibsignalSim.simParamIface, bits_five, bits_25k, bits_2p32,
    dsl_cost, Nat.reduceAdd]
  omega

private lemma simCorrFastC_cost_le {PQ PQC : Type} [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (K : ℕ) {Γ}
    (s : ReductionDsl.Expr (LibsignalSim.simOps (ℓ := ℓ) P Dh encT decT) Γ LibsignalSim.simStateTy)
    (qParty : ReductionDsl.Expr (LibsignalSim.simOps (ℓ := ℓ) P Dh encT decT) Γ .bool) :
    (simCorrFastC P Dh encT decT K s qParty).cost ≤
      exprCostUB s + exprCostUB qParty + 5000 * K + 10000 := by
  refine (compCost_le_costUB _).trans ?_
  simp only [simCorrFastC, mCorrAllowedFastE, mAfterCorrFastE,
    compTblOfListE, compTblInsertE, compTblGetE, compTblEmptyE,
    LibsignalSim.mInWinE, LibsignalSim.mNoSpkCorrE,
    LibsignalSim.mLeakE, LibsignalSim.revealSpkChainsE, LibsignalSim.toGhostE,
    LibsignalSim.ssMk, LibsignalSim.ssMir, LibsignalSim.ssPq, LibsignalSim.ssPn,
    LibsignalSim.ssUnackA, LibsignalSim.ssHonest, LibsignalSim.ssChains,
    LibsignalSim.ssAmb, LibsignalSim.ssStopped,
    LibsignalSim.mMk, LibsignalSim.mB, LibsignalSim.mWin, LibsignalSim.mEpoch,
    LibsignalSim.mIdx, LibsignalSim.mTL, LibsignalSim.mTrans, LibsignalSim.mChall,
    LibsignalSim.mComp, LibsignalSim.mMaxAcc, LibsignalSim.mLeaks, LibsignalSim.mCorrs,
    SM.orE, SM.otherE, SM.pGet, SM.pSet, SM.sendsInE, SM.leN, SM.maxOptE, SM.maxN,
    SM.posSender, SM.posEpoch, SM.posIdx, SM.boolEq,
    LibsignalSim.simOps, LibsignalSim.simOpCost, LibsignalSim.simIface,
    LibsignalSim.simParamIface, bits_ten,
    dsl_cost, Nat.reduceAdd]
  omega

private lemma simHandleFastC_cost_le {PQ PQC : Type} [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (K qep : ℕ) :
    (simHandleFastC (ℓ := ℓ) P Dh encT decT K qep).cost ≤
      5 * ReductionDsl.bits qep + 5000 * K + 33000 := by
  have hb_tr := simSendC_cost_le P Dh encT decT qep (Γ := simCtxTr (Pt := Pt) PQ PQC ℓ)
    .v4 (.fst .v0) (.fst (.snd .v0)) .none (.snd (.snd .v0))
  have hb_ch := simSendC_cost_le P Dh encT decT qep (Γ := simCtxCh (Pt := Pt) PQ PQC ℓ)
    .v4 (.fst .v0) (.fst (.snd .v0)) (.some (.fst (.snd (.snd .v0)))) (.snd (.snd (.snd .v0)))
  have hb_dl := simRecvFastC_cost_le P Dh encT decT K qep (Γ := simCtxDl (Pt := Pt) PQ PQC ℓ)
    .v3 (.fst .v0) (.snd .v0) (.bool true)
  have hb_ij := simRecvFastC_cost_le P Dh encT decT K qep (Γ := simCtxIj (Pt := Pt) PQ PQC ℓ)
    .v2 (.fst .v0) (.snd .v0) (.bool false)
  have hb_cr := simCorrFastC_cost_le P Dh encT decT K (Γ := simCtxCr (Pt := Pt) PQ PQC ℓ)
    .v1 .v0
  simp only [dsl_cost, Nat.reduceAdd] at hb_tr hb_ch hb_dl hb_ij hb_cr
  simp only [simHandleFastC, LibsignalSim.guardC, LibsignalSim.ssStopped,
    ReductionDsl.Comp.cost, ReductionDsl.Expr.cost, dsl_cost, Nat.reduceAdd]
  omega

set_option linter.unusedSimpArgs false in
private lemma simRecvFastC_size_le {PQ PQC : Type} [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (K qep : ℕ) {Γ}
    (s : ReductionDsl.Expr (LibsignalSim.simOps (ℓ := ℓ) P Dh encT decT) Γ LibsignalSim.simStateTy)
    (qParty : ReductionDsl.Expr (LibsignalSim.simOps (ℓ := ℓ) P Dh encT decT) Γ .bool)
    (w : ReductionDsl.Expr (LibsignalSim.simOps (ℓ := ℓ) P Dh encT decT) Γ (.base .wire))
    (isDel : ReductionDsl.Expr (LibsignalSim.simOps (ℓ := ℓ) P Dh encT decT) Γ .bool) :
    (simRecvFastC P Dh encT decT K qep s qParty w isDel).size ≤
      20 * (s.size + qParty.size + w.size + isDel.size) +
        50 * ReductionDsl.bits K + 8 * ReductionDsl.bits qep +
        8 * ReductionDsl.bits (qep + 1) + 50000 := by
  rcases sim_bits_small_consts with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb10, hb2000, hb25000, hb32⟩
  have h1K := ReductionDsl.one_le_bits K
  have hK1 : ReductionDsl.bits (K + 1) ≤ ReductionDsl.bits K + 1 := by
    have h := ReductionDsl.bits_add K 1; rw [hb1] at h; omega
  have h2K : ReductionDsl.bits (2 * K) ≤ ReductionDsl.bits K + 2 := by
    have h := ReductionDsl.bits_mul 2 K; omega
  simp only [simRecvFastC, simRecvNewChainNormalFastC, fwdFastC, inTFastE,
    LibsignalSim.onAnswerE, LibsignalSim.onAcceptE, LibsignalSim.onAcceptPreE,
    LibsignalSim.honestCE, LibsignalSim.mkCE,
    LibsignalSim.evictedHonestE, LibsignalSim.sAmbE, LibsignalSim.ambCondE,
    LibsignalSim.spkAmbE, LibsignalSim.hasUnknownKeyE, LibsignalSim.findChainE,
    LibsignalSim.modifyChainAcceptE, LibsignalSim.pushChainE, LibsignalSim.parseRecvE,
    LibsignalSim.mInTransitE, LibsignalSim.mSafeInjE, LibsignalSim.mInWinE,
    LibsignalSim.mChallContainsE, LibsignalSim.mCompContainsE, LibsignalSim.mTrivialE,
    LibsignalSim.mAcceptE, LibsignalSim.mDeleteE,
    LibsignalSim.ssSetMir, LibsignalSim.ssSetAmb, LibsignalSim.ssSetMirWin,
    LibsignalSim.mSetWin, LibsignalSim.srecPos, LibsignalSim.srecCt,
    LibsignalSim.ssMk, LibsignalSim.ssMir, LibsignalSim.ssPq, LibsignalSim.ssPn,
    LibsignalSim.ssUnackA, LibsignalSim.ssHonest, LibsignalSim.ssChains,
    LibsignalSim.ssAmb, LibsignalSim.ssStopped,
    LibsignalSim.mMk, LibsignalSim.mB, LibsignalSim.mWin, LibsignalSim.mEpoch,
    LibsignalSim.mIdx, LibsignalSim.mTL, LibsignalSim.mTrans, LibsignalSim.mChall,
    LibsignalSim.mComp, LibsignalSim.mMaxAcc, LibsignalSim.mLeaks, LibsignalSim.mCorrs,
    SM.orE, SM.isSomeE, SM.otherE, SM.pGet, SM.pSet, SM.sendsInE, SM.healedByE,
    SM.leN, SM.minN, SM.maxN, SM.maxAccSet, SM.maxAccGet,
    SM.posEq, SM.posSender, SM.posEpoch, SM.posIdx, SM.boolEq, SM.senderOfE,
    ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Expr.v2,
    ReductionDsl.Expr.v3, ReductionDsl.Expr.v4, ReductionDsl.Expr.v5,
    ReductionDsl.Comp.size, ReductionDsl.Expr.size,
    maxForwardJumps, maxMessageKeys, maxReceiverChains]
  omega

set_option linter.unusedSimpArgs false in
private lemma simCorrFastC_size_le {PQ PQC : Type} [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (K : ℕ) {Γ}
    (s : ReductionDsl.Expr (LibsignalSim.simOps (ℓ := ℓ) P Dh encT decT) Γ LibsignalSim.simStateTy)
    (qParty : ReductionDsl.Expr (LibsignalSim.simOps (ℓ := ℓ) P Dh encT decT) Γ .bool) :
    (simCorrFastC P Dh encT decT K s qParty).size ≤
      20 * (s.size + qParty.size) + 50 * ReductionDsl.bits K + 20000 := by
  rcases sim_bits_small_consts with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb10, hb2000, hb25000, hb32⟩
  have h1K := ReductionDsl.one_le_bits K
  have hK1 : ReductionDsl.bits (K + 1) ≤ ReductionDsl.bits K + 1 := by
    have h := ReductionDsl.bits_add K 1; rw [hb1] at h; omega
  have h2K : ReductionDsl.bits (2 * K) ≤ ReductionDsl.bits K + 2 := by
    have h := ReductionDsl.bits_mul 2 K; omega
  simp only [simCorrFastC, mCorrAllowedFastE, mAfterCorrFastE,
    compTblOfListE, compTblInsertE, compTblGetE, compTblEmptyE,
    LibsignalSim.mInWinE, LibsignalSim.mNoSpkCorrE,
    LibsignalSim.mLeakE, LibsignalSim.revealSpkChainsE, LibsignalSim.toGhostE,
    LibsignalSim.ssMk, LibsignalSim.ssMir, LibsignalSim.ssPq, LibsignalSim.ssPn,
    LibsignalSim.ssUnackA, LibsignalSim.ssHonest, LibsignalSim.ssChains,
    LibsignalSim.ssAmb, LibsignalSim.ssStopped,
    LibsignalSim.mMk, LibsignalSim.mB, LibsignalSim.mWin, LibsignalSim.mEpoch,
    LibsignalSim.mIdx, LibsignalSim.mTL, LibsignalSim.mTrans, LibsignalSim.mChall,
    LibsignalSim.mComp, LibsignalSim.mMaxAcc, LibsignalSim.mLeaks, LibsignalSim.mCorrs,
    SM.orE, SM.otherE, SM.pGet, SM.pSet, SM.sendsInE, SM.leN, SM.maxOptE, SM.maxN,
    SM.posEq, SM.posSender, SM.posEpoch, SM.posIdx, SM.boolEq,
    ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Expr.v2,
    ReductionDsl.Expr.v3, ReductionDsl.Expr.v4, ReductionDsl.Expr.v5,
    ReductionDsl.Comp.size, ReductionDsl.Expr.size,
    maxForwardJumps, maxMessageKeys, maxReceiverChains]
  omega

set_option linter.unusedSimpArgs false in
private lemma simProgFast_size_le {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (q qep : ℕ)
    (hbqep : ReductionDsl.bits qep ≤ 2 ^ 18 + 20 * ReductionDsl.bits (ratchetCostBudget q qep)) :
    (simProgFast (ℓ := ℓ) P Dh encT decT q qep).size ≤
      ReductionDsl.reductionSizeBudget + 2 ^ 12 * ReductionDsl.bits (ratchetCostBudget q qep) := by
  let R₀ := simProgFast (ℓ := ℓ) P Dh encT decT q qep
  rcases sim_bits_small_consts with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb10, hb2000, hb25000, hb32⟩
  have h1qep := ReductionDsl.one_le_bits qep
  have hq_le_bud : q ≤ ratchetCostBudget q qep := by
    unfold ratchetCostBudget maxForwardJumps; nlinarith
  have hbq_le : ReductionDsl.bits q ≤ ReductionDsl.bits (ratchetCostBudget q qep) :=
    Computational.Proofs.ReductionDsl.SizeBudgetBridge.bits_mono hq_le_bud
  have hbq1 : ReductionDsl.bits (qep + 1) ≤ ReductionDsl.bits qep + 1 := by
    have h := ReductionDsl.bits_add qep 1; rw [hb1] at h; omega
  have hinit_sz : R₀.init.size ≤ 5000 := by
    simp only [R₀, simProgFast, LibsignalSim.simInitC,
      LibsignalSim.initSimE, LibsignalSim.initChainAE, LibsignalSim.ssMk,
      LibsignalSim.initSimMirE, LibsignalSim.mMk,
      ReductionDsl.Expr.v0, ReductionDsl.Comp.size, ReductionDsl.Expr.size]
    omega
  have hfin_sz : R₀.finish.size ≤ 100 := by
    simp only [R₀, simProgFast, LibsignalSim.simFinishC,
      ReductionDsl.Expr.v1, ReductionDsl.Comp.size, ReductionDsl.Expr.size]
    omega
  have hhdl_sz : R₀.handle.size ≤ 200 * ReductionDsl.bits q + 50 * ReductionDsl.bits qep + 200000 := by
    have hs_tr := simSendC_size_le P Dh encT decT qep (Γ := simCtxTr (Pt := Pt) PQ PQC ℓ)
      .v4 (.fst .v0) (.fst (.snd .v0)) .none (.snd (.snd .v0))
    have hs_ch := simSendC_size_le P Dh encT decT qep (Γ := simCtxCh (Pt := Pt) PQ PQC ℓ)
      .v4 (.fst .v0) (.fst (.snd .v0)) (.some (.fst (.snd (.snd .v0)))) (.snd (.snd (.snd .v0)))
    have hs_dl := simRecvFastC_size_le P Dh encT decT q qep (Γ := simCtxDl (Pt := Pt) PQ PQC ℓ)
      .v3 (.fst .v0) (.snd .v0) (.bool true)
    have hs_ij := simRecvFastC_size_le P Dh encT decT q qep (Γ := simCtxIj (Pt := Pt) PQ PQC ℓ)
      .v2 (.fst .v0) (.snd .v0) (.bool false)
    have hs_cr := simCorrFastC_size_le P Dh encT decT q (Γ := simCtxCr (Pt := Pt) PQ PQC ℓ)
      .v1 .v0
    simp only [ReductionDsl.Expr.size, sim_expr_size_v0, sim_expr_size_v1,
      sim_expr_size_v2, sim_expr_size_v3, sim_expr_size_v4]
      at hs_tr hs_ch hs_dl hs_ij hs_cr
    dsimp only [R₀, simProgFast]
    simp only [simHandleFastC, LibsignalSim.guardC, LibsignalSim.ssStopped,
      ReductionDsl.Comp.size, ReductionDsl.Expr.size,
      sim_expr_size_v0, sim_expr_size_v1, sim_expr_size_v2, sim_expr_size_v3, sim_expr_size_v4]
    omega
  change R₀.size ≤ _
  simp only [ReductionDsl.CostedReduction.size, ReductionDsl.reductionSizeBudget]
  omega

private lemma simProgFast_totalQueries_le {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (q qep : ℕ) :
    (simProgFast (ℓ := ℓ) P Dh encT decT q qep).totalQueries (fun _ => 1) (fun _ => 0) q ≤ q := by
  have hdl : ∀ {Γ} (s : ReductionDsl.Expr (LibsignalSim.simOps (ℓ := ℓ) P Dh encT decT) Γ LibsignalSim.simStateTy)
      (qp : ReductionDsl.Expr (LibsignalSim.simOps (ℓ := ℓ) P Dh encT decT) Γ .bool)
      (w : ReductionDsl.Expr (LibsignalSim.simOps (ℓ := ℓ) P Dh encT decT) Γ (.base .wire))
      (del : ReductionDsl.Expr (LibsignalSim.simOps (ℓ := ℓ) P Dh encT decT) Γ .bool),
      (simRecvFastC P Dh encT decT q qep s qp w del).queries (fun _ => 1) (fun _ => 0) = 1 := by
    intro Γ s qp w del
    simp [simRecvFastC, simRecvNewChainNormalFastC, fwdFastC, ReductionDsl.Comp.queries]
  have hcr : ∀ {Γ} (s : ReductionDsl.Expr (LibsignalSim.simOps (ℓ := ℓ) P Dh encT decT) Γ LibsignalSim.simStateTy)
      (qp : ReductionDsl.Expr (LibsignalSim.simOps (ℓ := ℓ) P Dh encT decT) Γ .bool),
      (simCorrFastC P Dh encT decT q s qp).queries (fun _ => 1) (fun _ => 0) = 1 := by
    intro Γ s qp
    simp [simCorrFastC, ReductionDsl.Comp.queries]
  have hhdl : (simHandleFastC (ℓ := ℓ) P Dh encT decT q qep).queries (fun _ => 1) (fun _ => 0) ≤ 1 := by
    simp only [simHandleFastC, LibsignalSim.guardC_queries, LibsignalSim.simSendC_queries,
      hdl, hcr, ReductionDsl.Comp.queries]
    omega
  simp only [ReductionDsl.CostedReduction.totalQueries, simProgFast,
    LibsignalSim.simInitC_queries, LibsignalSim.simFinishC_queries, zero_add, add_zero]
  exact Nat.mul_le_mul_left q hhdl |>.trans (by omega)

private lemma simProgFast_totalCost_le {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (q qep : ℕ) :
    (simProgFast (ℓ := ℓ) P Dh encT decT q qep).totalCost q ≤ ratchetCostBudget q qep := by
  have hhdl := simHandleFastC_cost_le (ℓ := ℓ) P Dh encT decT q qep
  simp only [ReductionDsl.CostedReduction.totalCost, simProgFast,
    LibsignalSim.simInitC_cost, LibsignalSim.simFinishC_cost]
  have hstep : max 1 ((simHandleFastC (ℓ := ℓ) P Dh encT decT q qep).cost + 6) ≤
      5 * ReductionDsl.bits qep + 5000 * q + 33200 := by
    omega
  have hmul : q * max 1 ((simHandleFastC (ℓ := ℓ) P Dh encT decT q qep).cost + 6) ≤
      5 * (q * ReductionDsl.bits qep) + 5000 * (q * q) + 33200 * q := by
    calc q * max 1 ((simHandleFastC (ℓ := ℓ) P Dh encT decT q qep).cost + 6)
        ≤ q * (5 * ReductionDsl.bits qep + 5000 * q + 33200) := Nat.mul_le_mul_left q hstep
      _ = 5 * (q * ReductionDsl.bits qep) + 5000 * (q * q) + 33200 * q := by ring
  have hrhs : ratchetCostBudget q qep =
      102400000 * (q * q) + 204800000 * q + 102400000 +
      4096 * (q * q * ReductionDsl.bits qep) +
      8192 * (q * ReductionDsl.bits qep) + 4096 * ReductionDsl.bits qep := by
    unfold ratchetCostBudget maxForwardJumps; ring
  rw [hrhs]
  omega

end SimFastBounds

theorem simProgInst_bounds_of_bits_le [SampleableType Pt] {PQ PQC : Type} [Inhabited PQ]
    [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (q qep : ℕ)
    (hbqep : ReductionDsl.bits qep ≤ 2 ^ 18 + 20 * ReductionDsl.bits (ratchetCostBudget q qep)) :
    simCostedBounds q qep (simProgInst (ℓ := ℓ) P Dh encT decT q qep) :=
  gredBounded_of_bounds
    (simProgFast_totalCost_le P Dh encT decT q qep)
    (simProgFast_size_le P Dh encT decT q qep hbqep)
    (simProgFast_totalQueries_le P Dh encT decT q qep)
    (LibsignalSim.simOps_sizeHonest (ℓ := ℓ) P Dh encT decT)
    (LibsignalSim.simSamplers_sizeHonest PQ PQC Pt ℓ)

theorem simProgInst_bounds [SampleableType Pt] {PQ PQC : Type} [Inhabited PQ]
    [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (q qep : ℕ)
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    simCostedBounds q qep (simProgInst (ℓ := ℓ) P Dh encT decT q qep) := by
  apply simProgInst_bounds_of_bits_le P Dh encT decT q qep
  have hbud : qep ≤ ratchetCostBudget q qep := by
    unfold ratchetCostBudget maxForwardJumps
    have hb1 : 1 ≤ ReductionDsl.bits qep := ReductionDsl.one_le_bits qep
    nlinarith
  have hbits := Computational.Proofs.ReductionDsl.SizeBudgetBridge.bits_mono hbud
  omega

end SimCosted

end CryptoVerification.LibsignalSession

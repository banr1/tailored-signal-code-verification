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
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvNewCost
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvNewSkip

/-!
# New-Epoch Receive Branch and Outer `semRecvHookS` Wrapper for `simFig8`

Proves `.eval` correctness for the fresh-epoch receive branch `recvNewOfFwdC`
(`SimFig8RecvNewSpec`), the outer `semRecvHookS` dispatcher `recvHookOfBranchesC`, and the
deliver/inject arm wrappers of `simFig8OracleSan`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvNew

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Ops Expr Comp Iface bits liftRen
  atomicSig atomicSessionOps fig8SmIface
  B PK PtT fig8CtT fig8CtV lctT lctV
  partyToBool recvResultT recvResultEnc recvResultDec)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalSession (ratchetCostBudget)
open CryptoVerification.E2E (Bytes paramsV1)
open CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32
  ratchetKeyAdmissible)
open CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C SimState SimCStateBounded simParseRecvC
  inReceiveOnlyEpoch)
open CryptoGames.Ratchet.LibsignalSimC (LibsignalToModularSchemeSimState)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoGames.SM (RecvResult partyEnc orE orE_eval boolEq isSomeE otherE senderOfE pGet)
open Computational.Proofs.Game.PromotedCostedReds.SanOracleCore
  (semFwdAnswerHookS semFwdEvictHookS semFwdHookS semRecvHookS semHandleHookDedupS)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8State
  (eLet eMapOpt sOpPure scBase scSetBase ssMir ssPq ssHonest ssChains ssAmb ssStopped ssSetAmb
   mWin mEpoch mSafeInjE mSafeInjE_eval mInTransitE mInWinE
   findChainIdxE eval_findChainIdxE anyChainKeyNoneE)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8Crypto
  (parseOutT parseOutV parseRecvAtomicC parseRecvAtomicC_eval
   lctSaltEqOfLctAtomicE injOKAtomicE isZeroPtOptAtomicE isZeroPtOptAtomicE_eval
   partyToBool_eq_partyEnc)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanOracle (simFig8OracleSan)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanCoupling (SanSnapExtra)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost
  (simMirT simBaseT simFullT simMirEnc simBaseEnc simFullEnc simFullDec simFullDec_simFullEnc
   ghostChainEnc fig8IdSemHook)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost
  (atomicSessionOpDescBits atomicCompDescBits)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvNewCost
  (recvOutT fwdHookInpT recvSameInpT recvNewInpT recvHookInpT smRecvArgT
   callSub1C rejOutE mkCAtomicE recvNewEvictedE recvNewSaltEqE recvNewSCAmbE
   recvNewRangeBadE recvRefuseE honestLookupE
   recvNewOfFwdC recvHookOfBranchesC recvArmC semRecvNewBranch
   recvNewOfFwdC_queries recvNewOfFwdC_cost recvNewOfFwdC_descBits_le)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvNewSkip
  (callSub1C_eval mkCAtomicE_eval recvNewEvictedE_eval recvNewSaltEqE_eval
   recvNewSCAmbE_eval recvNewRangeBadE_eval recvRefuseE_eval honestLookupE_eval
   recvNewOfFwdC_eval_reject recvHookOfBranchesC_eval_prefix)

section Proofs

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (K : MlKem)
  (Dh : DHFun (BitVec 256) Pt)
  (encPt : Pt → List (BitVec 8))
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (lam : Pt)

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem sCAmb_bounded {q : ℕ} {sC : LibsignalToModularSchemeSimState Bytes Pt ℓ}
    (amb : Bool) (hbnd : SimCStateBounded q sC) :
    SimCStateBounded q
      { sC with base := if amb then { sC.base with amb := sC.base.amb + 1 } else sC.base } := by
  cases amb <;>
    exact ⟨⟨hbnd.base.trans_le, hbnd.base.chall_le, hbnd.base.honest_le,
      hbnd.base.comp_u, hbnd.base.chainsA_le, hbnd.base.chainsB_le⟩,
      hbnd.sent_le, hbnd.snaps_le⟩

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem sCAmb_sanSnapExtra {sC : LibsignalToModularSchemeSimState Bytes Pt ℓ}
    (amb : Bool) (hsna : SanSnapExtra C K sC) :
    SanSnapExtra C K
      { sC with base := if amb then { sC.base with amb := sC.base.amb + 1 } else sC.base } := by
  cases amb <;> exact ⟨hsna.1, hsna.2.1, hsna.2.2⟩

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem pGet_mEpoch_eval {O' : Ops ASig} {Γ : List (Ty ASig)}
    (sCE : Expr O' Γ (simFullT ℓ Pt)) (qBE : Expr O' Γ .bool) (ρ : Env Γ)
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ) (Q : Party)
    (hs : sCE.eval ρ = simFullEnc sC) (hq : qBE.eval ρ = partyEnc Q) :
    (pGet (mEpoch (ssMir (scBase sCE))) qBE).eval ρ = sC.base.mir.epoch Q := by
  cases Q <;>
    simp [pGet, mEpoch, ssMir, scBase, simFullEnc, simBaseEnc, simMirEnc,
      partyEnc, Expr.eval, Expr.v0, hs, hq]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem pGet_ssPq_eval {O' : Ops ASig} {Γ : List (Ty ASig)}
    (sCE : Expr O' Γ (simFullT ℓ Pt)) (qBE : Expr O' Γ .bool) (ρ : Env Γ)
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ) (Q : Party)
    (hs : sCE.eval ρ = simFullEnc sC) (hq : qBE.eval ρ = partyEnc Q) :
    (pGet (ssPq (scBase sCE)) qBE).eval ρ = sC.base.pq Q := by
  cases Q <;>
    simp [pGet, ssPq, scBase, simFullEnc, simBaseEnc, partyEnc, Expr.eval, Expr.v0, hs, hq]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem pGet_ssChains_eval {O' : Ops ASig} {Γ : List (Ty ASig)}
    (sCE : Expr O' Γ (simFullT ℓ Pt)) (qBE : Expr O' Γ .bool) (ρ : Env Γ)
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ) (Q : Party)
    (hs : sCE.eval ρ = simFullEnc sC) (hq : qBE.eval ρ = partyEnc Q) :
    (pGet (ssChains (scBase sCE)) qBE).eval ρ =
      (sC.base.chains Q).map ghostChainEnc := by
  cases Q <;>
    simp [pGet, ssChains, scBase, simFullEnc, simBaseEnc, partyEnc, Expr.eval, Expr.v0, hs, hq]

omit [DecidableEq Pt] [Zero Pt] in
private theorem map_rejOutE_eval {O' : Ops ASig} {Γ : List (Ty ASig)}
    (sCE : Expr O' Γ (simFullT ℓ Pt)) (ρ : Env Γ)
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ)
    (hs : sCE.eval ρ = simFullEnc sC) :
    (Prod.map (Option.map recvResultDec) simFullDec <$>
      (Comp.ret (I := fig8SmIface ℓ Pt) (rejOutE sCE)).eval ρ) =
    pure (some .rejected, sC) := by
  simp [rejOutE, Comp.eval, Expr.eval, hs, recvResultDec, simFullDec_simFullEnc]

/-- Main `.eval` correctness of `recvNewOfFwdC` against `semRecvNewBranch`, dispatching
both `semFwdEvictHookS` and `semFwdHookS` through a single `fwdHookC` invocation. -/
theorem recvNewOfFwdC_eval
    (idA idB : IdentityKey) (qep q B T Kc : ℕ)
    (fwdHookC : Comp AOps (fig8SmIface ℓ Pt) [fwdHookInpT ℓ Pt] (recvOutT ℓ Pt))
    (hfwd : ∀ sC₀ Q₀ w₀ isDel₀ ci?₀ pk₀ pq'₀ honestC₀ c'₀,
      SimCStateBounded q sC₀ →
      SanSnapExtra C K sC₀ →
      (Prod.map (Option.map recvResultDec) simFullDec <$>
        fwdHookC.eval (.cons (simFullEnc sC₀, (partyToBool Q₀, (w₀, (isDel₀,
          (ci?₀, (pk₀, (pq'₀, (honestC₀.map fig8CtV, fig8CtV c'₀)))))))) .nil)) =
      (Prod.map id Prod.fst <$>
        semFwdHookS (paramsV1 C K idA idB) Dh encPt encT lam T Kc
          (fig8IdSemHook (PQC := BitVec 512) none) qep B
          sC₀ () Q₀ w₀ isDel₀ ci?₀ pk₀ pq'₀ honestC₀ c'₀))
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ)
    (Q : Party) (w : Bytes) (isDel : Bool)
    (pq' : Bytes) (i : ℕ) (pk : PublicKey) (T? : Option Pt)
    (lct : ℕ × LibsignalCiphertextWithSalt32)
    (honestC : Option (Fig8C Pt))
    (hbnd : SimCStateBounded q sC)
    (hsna : SanSnapExtra C K sC) :
    (Prod.map (Option.map recvResultDec) simFullDec <$>
      (recvNewOfFwdC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) fwdHookC).eval
        (.cons (simFullEnc sC, (partyToBool Q, (w, (isDel,
          (parseOutV (pq', (i, (pk, (T?, lct)))),
            honestC.map fig8CtV))))) .nil)) =
    semRecvNewBranch (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (lam := lam) idA idB qep B T Kc
      sC Q w isDel pq' i pk T? lct honestC := by
  have hch : (sC.base.chains Q).length ≤ 5 := (hsna.2.1 Q).1
  set ep1 := sC.base.mir.epoch Q + 1
  set evicted := (honestC.map fun c => decide (c.1.1 ≠ ep1)) == some true
  set saltEq := (honestC.map fun c => decide (c.2.2.2 = lct.2.2)) == some true
  set rangeBad := inReceiveOnlyEpoch sC.base.mir Q || decide (25000 < i - 1) || decide (2 ^ 32 ≤ i)
  by_cases hevS : (evicted && saltEq) = true
  · exact recvNewOfFwdC_eval_reject C K Dh encPt encT decT lam idA idB qep B T Kc fwdHookC
      sC Q w isDel pq' i pk T? lct honestC hch (Or.inl hevS)
  · by_cases hT0 : (T? == some 0) = true
    · exact recvNewOfFwdC_eval_reject C K Dh encPt encT decT lam idA idB qep B T Kc fwdHookC
        sC Q w isDel pq' i pk T? lct honestC hch (Or.inr (Or.inl hT0))
    · by_cases hrng : rangeBad = true
      · exact recvNewOfFwdC_eval_reject C K Dh encPt encT decT lam idA idB qep B T Kc fwdHookC
          sC Q w isDel pq' i pk T? lct honestC hch (Or.inr (Or.inr (Or.inl hrng)))
      · cases T? with
        | none =>
          exact recvNewOfFwdC_eval_reject C K Dh encPt encT decT lam idA idB qep B T Kc fwdHookC
            sC Q w isDel pq' i pk none lct honestC hch (Or.inr (Or.inr (Or.inr rfl)))
        | some T₀ =>
          have hevS_f : (evicted && saltEq) = false := Bool.eq_false_iff.mpr hevS
          have hT0_f : (some T₀ == some 0) = false := Bool.eq_false_iff.mpr hT0
          have hrng_f : rangeBad = false := Bool.eq_false_iff.mpr hrng
          let inpV : (recvNewInpT ℓ Pt).denote := (simFullEnc sC, (partyToBool Q, (w, (isDel,
            (parseOutV (ℓ := ℓ) (Pt := Pt) (pq', (i, (pk, (some T₀, lct)))),
              honestC.map fig8CtV)))))
          let ρ₀ : Env [recvNewInpT ℓ Pt] := .cons inpV .nil
          have hs0 : (Expr.fst (Expr.v0 (O := AOps))).eval ρ₀ = simFullEnc sC := rfl
          have hq0 : (Expr.fst (.snd (Expr.v0 (O := AOps)))).eval ρ₀ = partyEnc Q :=
            partyToBool_eq_partyEnc Q
          have hep0 : (Expr.add (pGet (mEpoch (ssMir (scBase (.fst .v0)))) (.fst (.snd .v0)))
              (.nat 1) : Expr AOps [recvNewInpT ℓ Pt] .nat).eval ρ₀ = ep1 := by
            simp [Expr.eval, pGet_mEpoch_eval (.fst .v0) (.fst (.snd .v0)) ρ₀ sC Q hs0 hq0, ep1]
          have hearly :
              (orE
                (.and (recvNewEvictedE (.snd (.snd (.snd (.snd (.snd .v0)))))
                    (.add (pGet (mEpoch (ssMir (scBase (.fst .v0)))) (.fst (.snd .v0))) (.nat 1)))
                  (recvNewSaltEqE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                    (encT := encT) (decT := decT) (lam := lam)
                    (.snd (.snd (.snd (.snd (.snd .v0)))))
                    (.snd (.snd (.snd (.snd (.fst (.snd (.snd (.snd (.snd .v0)))))))))))
                (isZeroPtOptAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                  (encT := encT) (decT := decT) (lam := lam)
                  (.fst (.snd (.snd (.snd (.fst (.snd (.snd (.snd (.snd .v0))))))))))).eval ρ₀ =
              false := by
            have h1 := recvNewEvictedE_eval (O' := AOps)
              (.snd (.snd (.snd (.snd (.snd .v0)))))
              (.add (pGet (mEpoch (ssMir (scBase (.fst .v0)))) (.fst (.snd .v0))) (.nat 1))
              ρ₀ honestC ep1 rfl hep0
            have h2 := recvNewSaltEqE_eval C K Dh encPt encT decT lam
              (.snd (.snd (.snd (.snd (.snd .v0)))))
              (.snd (.snd (.snd (.snd (.fst (.snd (.snd (.snd (.snd .v0)))))))))
              ρ₀ honestC lct rfl rfl
            have h3 := isZeroPtOptAtomicE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
              (encT := encT) (decT := decT) (lam := lam)
              (.fst (.snd (.snd (.snd (.fst (.snd (.snd (.snd (.snd .v0))))))))) ρ₀
            change _ = false
            rw [orE_eval]
            simp only [Expr.eval] at h3 ⊢
            rw [h1, h2, h3]
            change (evicted && saltEq || (some T₀ == some 0)) = false
            rw [hevS_f, hT0_f]
            rfl
          let amb := inReceiveOnlyEpoch sC.base.mir Q ||
            (Q == Party.A && (sC.base.chains Q).any (·.key.isNone))
          let sCAmb : LibsignalToModularSchemeSimState Bytes Pt ℓ :=
            { sC with base := if amb then { sC.base with amb := sC.base.amb + 1 } else sC.base }
          have hsAmb0 : (recvNewSCAmbE (O' := AOps) (.fst .v0) (.fst (.snd .v0))).eval ρ₀ =
              simFullEnc sCAmb :=
            recvNewSCAmbE_eval (.fst .v0) (.fst (.snd .v0)) ρ₀ sC Q hch hs0 hq0
          let ρ₁ : Env [simFullT ℓ Pt, recvNewInpT ℓ Pt] := .cons (simFullEnc sCAmb) ρ₀
          have hrng1 : (recvNewRangeBadE (O' := AOps) (.fst .v1) (.fst (.snd .v1))
              (.fst (.snd (.fst (.snd (.snd (.snd (.snd .v1)))))))).eval ρ₁ = false := by
            rw [recvNewRangeBadE_eval (.fst .v1) (.fst (.snd .v1))
              (.fst (.snd (.fst (.snd (.snd (.snd (.snd .v1))))))) ρ₁ sC Q i
              rfl (by exact partyToBool_eq_partyEnc Q) rfl]
            exact hrng_f
          let ρ₂ : Env [PtT, simFullT ℓ Pt, recvNewInpT ℓ Pt] := .cons T₀ ρ₁
          have hs2 : (Expr.fst (Expr.v2 (O := AOps))).eval ρ₂ = simFullEnc sC := rfl
          have hq2 : (Expr.fst (.snd (Expr.v2 (O := AOps)))).eval ρ₂ = partyEnc Q :=
            partyToBool_eq_partyEnc Q
          have hep2_raw :
              (pGet (mEpoch (ssMir (scBase (.fst .v2)))) (.fst (.snd .v2)) :
                Expr AOps [PtT, simFullT ℓ Pt, recvNewInpT ℓ Pt] .nat).eval ρ₂ =
              sC.base.mir.epoch Q :=
            pGet_mEpoch_eval (.fst .v2) (.fst (.snd .v2)) ρ₂ sC Q hs2 hq2
          have hep2 : (Expr.add (pGet (mEpoch (ssMir (scBase (.fst .v2)))) (.fst (.snd .v2)))
              (.nat 1) : Expr AOps [PtT, simFullT ℓ Pt, recvNewInpT ℓ Pt] .nat).eval ρ₂ = ep1 := by
            simp [Expr.eval, hep2_raw, ep1]
          have hev2 : (recvNewEvictedE (O' := AOps) (.snd (.snd (.snd (.snd (.snd .v2)))))
              (.add (pGet (mEpoch (ssMir (scBase (.fst .v2)))) (.fst (.snd .v2))) (.nat 1))).eval ρ₂ =
              evicted :=
            recvNewEvictedE_eval (.snd (.snd (.snd (.snd (.snd .v2))))) _ ρ₂ honestC ep1 rfl hep2
          have hsafe2 : (mSafeInjE (O' := AOps) (ssMir (scBase .v1))).eval ρ₂ =
              sCAmb.base.mir.safeInj 3 :=
            mSafeInjE_eval (ssMir (scBase .v1)) ρ₂ sCAmb.base.mir rfl
          have hbndAmb : SimCStateBounded q sCAmb := sCAmb_bounded amb hbnd
          have hsnaAmb : SanSnapExtra C K sCAmb := sCAmb_sanSnapExtra C K amb hsna
          let t0_2 : Expr AOps [PtT, simFullT ℓ Pt, recvNewInpT ℓ Pt] PtT := .v0
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
          let honestArg2 : Expr AOps [PtT, simFullT ℓ Pt, recvNewInpT ℓ Pt]
              (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))) :=
            .ite evicted2 .none honestC2
          let c'Arg2 : Expr AOps [PtT, simFullT ℓ Pt, recvNewInpT ℓ Pt]
              (fig8CtT (ℓ := ℓ) (Pt := Pt)) :=
            .ite evicted2
              (.pair (.pair ep1_2 (.some t0_2)) lct2)
              (mkCAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                (encT := encT) (decT := decT) (lam := lam)
                honestC2 ep1_2 (.some t0_2) lct2)
          let fwdInp2 : Expr AOps [PtT, simFullT ℓ Pt, recvNewInpT ℓ Pt] (fwdHookInpT ℓ Pt) :=
            .pair sCAmb2 (.pair qB2 (.pair w2 (.pair isDel2 (.pair .none
              (.pair pk2 (.pair pq'2 (.pair honestArg2 c'Arg2)))))))
          have hstep_lhs :
              (recvNewOfFwdC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                (encT := encT) (decT := decT) (lam := lam) fwdHookC).eval ρ₀ =
              (Comp.ite evictProbeRej2 (.ret (rejOutE sCAmb2))
                (callSub1C fwdHookC fwdInp2)).eval ρ₂ := by
            dsimp only [recvNewOfFwdC]
            rw [Comp.eval, hearly]
            simp only [Bool.false_eq_true, ↓reduceIte]
            rw [Comp.eval, Comp.eval, hsAmb0, pure_bind]
            change (Comp.ite _ _ _).eval ρ₁ = _
            rw [Comp.eval, hrng1]
            simp only [Bool.false_eq_true, ↓reduceIte]
            rfl
          rw [hstep_lhs]
          unfold semRecvNewBranch
          change _ = Prod.map id Prod.fst <$>
            (if (evicted && saltEq) = true then _
             else if (some T₀ == some 0) = true then _
             else if rangeBad = true then _
             else _)
          rw [hevS_f, hT0_f, hrng_f]
          simp only [Bool.false_eq_true, ↓reduceIte]
          change _ = Prod.map id Prod.fst <$> (if evicted = true then _ else _)
          cases hev_bool : evicted
          ·
            simp only [Bool.false_eq_true, ↓reduceIte]
            have hprobe_f : evictProbeRej2.eval ρ₂ = false := by
              simp [evictProbeRej2, evicted2, ep1_2, honestC2, sC2, qB2, inp2, Expr.eval, hev2, hev_bool]
            rw [Comp.eval, hprobe_f]
            simp only [Bool.false_eq_true, ↓reduceIte]
            rw [callSub1C_eval]
            have hmkC := mkCAtomicE_eval C K Dh encPt encT decT lam
              honestC2 ep1_2 (.some t0_2) lct2 ρ₂ honestC ep1 (some T₀) lct rfl hep2 rfl rfl
            have harg :
                fwdInp2.eval ρ₂ =
                (simFullEnc sCAmb, (partyToBool Q, (w, (isDel,
                  (none, (pk, (pq', (honestC.map fig8CtV,
                    (mkCAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                      (encT := encT) (decT := decT) (lam := lam)
                      honestC2 ep1_2 (.some t0_2) lct2).eval ρ₂)))))))) := by
              simp only [fwdInp2, honestArg2, c'Arg2, evicted2, ep1_2, honestC2, sC2, qB2, w2,
                isDel2, pq'2, pk2, lct2, parsed2, inp2, sCAmb2, t0_2,
                Expr.eval, hev2, hev_bool]
              rfl
            rw [harg, hmkC]
            exact hfwd sCAmb Q w isDel none pk pq' honestC _ hbndAmb hsnaAmb
          ·
            simp only [↓reduceIte]
            unfold semFwdEvictHookS
            change _ = Prod.map id Prod.fst <$>
              (if (isDel && !(sCAmb.base.mir.safeInj 3)) = true then _ else _)
            by_cases hinjRej : (isDel && !(sCAmb.base.mir.safeInj 3)) = true
            · have hprobe_t : evictProbeRej2.eval ρ₂ = true := by
                simp only [evictProbeRej2, evicted2, ep1_2, honestC2, sC2, qB2, isDel2, inp2,
                  sCAmb2, Expr.eval, hev2, hev_bool, hsafe2]
                exact hinjRej
              rw [Comp.eval, hprobe_t]
              simp only [↓reduceIte]
              rw [map_rejOutE_eval sCAmb2 ρ₂ sCAmb rfl, hinjRej]
              simp only [↓reduceIte, fig8IdSemHook, pure_bind, map_pure, Prod.map, id_eq]
              rfl
            · have hinjRej_f : (isDel && !(sCAmb.base.mir.safeInj 3)) = false :=
                Bool.eq_false_iff.mpr hinjRej
              have hprobe_f : evictProbeRej2.eval ρ₂ = false := by
                simp only [evictProbeRej2, evicted2, ep1_2, honestC2, sC2, qB2, isDel2, inp2,
                  sCAmb2, Expr.eval, hev2, hev_bool, hsafe2]
                exact hinjRej_f
              rw [Comp.eval, hprobe_f]
              simp only [Bool.false_eq_true, ↓reduceIte]
              rw [callSub1C_eval]
              have harg :
                  fwdInp2.eval ρ₂ =
                  (simFullEnc sCAmb, (partyToBool Q, (w, (isDel,
                    (none, (pk, (pq', ((none : Option (Fig8C Pt)).map fig8CtV,
                      fig8CtV (ℓ := ℓ) ((ep1, some T₀), lct))))))))) := by
                simp only [fwdInp2, honestArg2, c'Arg2, evicted2, ep1_2, honestC2, sC2, qB2, w2,
                  isDel2, pq'2, pk2, lct2, parsed2, inp2, sCAmb2, t0_2,
                  Expr.eval, hev2, hev_bool, hep2_raw, ep1]
                rfl
              rw [harg, hinjRej_f]
              simp only [Bool.false_eq_true, ↓reduceIte]
              rw [hfwd sCAmb Q w isDel none pk pq' none ((ep1, some T₀), lct) hbndAmb hsnaAmb]
              rfl

/-- Packaged specification for the new-epoch (`findIdx? = none`) receive branch at
`(L, B, T, Kc) = (q, 2 ^ 32 + q + 2, 50000 * q, 25001 * q + 25000)`. -/
structure SimFig8RecvNewSpec (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) where
  comp : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
    [recvNewInpT ℓ Pt] (recvOutT ℓ Pt)
  hq : comp.queries (fun _ => 1) (fun _ => 0) ≤ 1
  hcost : ℓ < 10 ^ 6 →
    comp.cost ≤ 24010005 + 20000000 * q + 128 * bits (qep + 1)
  hdesc : ℓ < 10 ^ 6 →
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) comp ≤
      275010 + 256 * bits (ratchetCostBudget q (qep + 1) + (qep + 1))
  heval : ℓ < 10 ^ 6 →
    ∀ sC Q w isDel pq' i pk T? lct honestC,
      SimCStateBounded q sC →
      SanSnapExtra C K sC →
      (Prod.map (Option.map recvResultDec) simFullDec <$>
        comp.eval (.cons (simFullEnc sC, (partyToBool Q, (w, (isDel,
          (parseOutV (pq', (i, (pk, (T?, lct)))),
            honestC.map fig8CtV))))) .nil)) =
      semRecvNewBranch (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (lam := lam) idA idB qep
        (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000)
        sC Q w isDel pq' i pk T? lct honestC

def simFig8RecvNewSpec_of_fwd
    (idA idB : IdentityKey) (qep q : ℕ)
    (fwdHookC : Comp AOps (fig8SmIface ℓ Pt) [fwdHookInpT ℓ Pt] (recvOutT ℓ Pt))
    (hfwd_q : fwdHookC.queries (fun _ => 1) (fun _ => 0) ≤ 1)
    (hfwd_cost : ℓ < 10 ^ 6 →
      fwdHookC.cost ≤ 24000005 + 20000000 * q + 128 * bits (qep + 1))
    (hfwd_desc : ℓ < 10 ^ 6 →
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) fwdHookC ≤
        250010 + 256 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)))
    (hfwd_eval : ℓ < 10 ^ 6 →
      ∀ sC₀ Q₀ w₀ isDel₀ ci?₀ pk₀ pq'₀ honestC₀ c'₀,
        SimCStateBounded q sC₀ →
        SanSnapExtra C K sC₀ →
        (Prod.map (Option.map recvResultDec) simFullDec <$>
          fwdHookC.eval (.cons (simFullEnc sC₀, (partyToBool Q₀, (w₀, (isDel₀,
            (ci?₀, (pk₀, (pq'₀, (honestC₀.map fig8CtV, fig8CtV c'₀)))))))) .nil)) =
        (Prod.map id Prod.fst <$>
          semFwdHookS (paramsV1 C K idA idB) Dh encPt encT lam
            (50000 * q) (25001 * q + 25000) (fig8IdSemHook (PQC := BitVec 512) none)
            qep (2 ^ 32 + q + 2) sC₀ () Q₀ w₀ isDel₀ ci?₀ pk₀ pq'₀ honestC₀ c'₀)) :
    SimFig8RecvNewSpec Pt ℓ C K idA idB Dh encPt encT decT lam qep q where
  comp := recvNewOfFwdC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) fwdHookC
  hq := by
    rw [recvNewOfFwdC_queries]
    exact hfwd_q
  hcost hℓ := by
    have hc := recvNewOfFwdC_cost C K Dh encPt encT decT lam fwdHookC
    have hf := hfwd_cost hℓ
    omega
  hdesc hℓ := by
    have hd := recvNewOfFwdC_descBits_le C K Dh encPt encT decT lam fwdHookC
      (fun _ => 8) (fun _ => 8)
    have hf := hfwd_desc hℓ
    omega
  heval hℓ sC Q w isDel pq' i pk T? lct honestC hbnd hsna :=
    recvNewOfFwdC_eval C K Dh encPt encT decT lam idA idB qep q
      (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000)
      fwdHookC (hfwd_eval hℓ) sC Q w isDel pq' i pk T? lct honestC hbnd hsna

/-- Full `.eval` correctness of `recvHookOfBranchesC` against `semRecvHookS`. -/
theorem recvHookOfBranchesC_eval
    (idA idB : IdentityKey) (q qep B T Kc : ℕ)
    (sameBranchC : Comp AOps (fig8SmIface ℓ Pt) [recvSameInpT ℓ Pt] (recvOutT ℓ Pt))
    (newBranchC : Comp AOps (fig8SmIface ℓ Pt) [recvNewInpT ℓ Pt] (recvOutT ℓ Pt))
    (hsame : ∀ sC₀ Q₀ w₀ isDel₀ pq'₀ i₀ pk₀ T?₀ lct₀ honestC₀ ci₀,
      SimCStateBounded q sC₀ →
      SanSnapExtra C K sC₀ →
      (Prod.map (Option.map recvResultDec) simFullDec <$>
        sameBranchC.eval (.cons (simFullEnc sC₀, (partyToBool Q₀, (w₀, (isDel₀,
          (parseOutV (pq'₀, (i₀, (pk₀, (T?₀, lct₀)))),
            (honestC₀.map fig8CtV, ci₀)))))) .nil)) =
      Prod.map id Prod.fst <$>
        (let g := (sC₀.base.chains Q₀).getD ci₀ ⟨none, 0, 0, []⟩
         if g.rejects i₀ then
           pure (some .rejected, (sC₀, ()))
         else
           semFwdHookS (paramsV1 C K idA idB) Dh encPt encT lam T Kc
             (fig8IdSemHook (PQC := BitVec 512) none) qep B sC₀ () Q₀ w₀ isDel₀
             (some ci₀) pk₀ pq'₀ honestC₀
             (match honestC₀ with
              | some c => if c.2.2.2 = lct₀.2.2 then c else ((g.epoch, T?₀), lct₀)
              | none => ((g.epoch, T?₀), lct₀))))
    (hnew : ∀ sC₀ Q₀ w₀ isDel₀ pq'₀ i₀ pk₀ T?₀ lct₀ honestC₀,
      SimCStateBounded q sC₀ →
      SanSnapExtra C K sC₀ →
      (Prod.map (Option.map recvResultDec) simFullDec <$>
        newBranchC.eval (.cons (simFullEnc sC₀, (partyToBool Q₀, (w₀, (isDel₀,
          (parseOutV (pq'₀, (i₀, (pk₀, (T?₀, lct₀)))),
            honestC₀.map fig8CtV))))) .nil)) =
      semRecvNewBranch (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (lam := lam) idA idB qep B T Kc
        sC₀ Q₀ w₀ isDel₀ pq'₀ i₀ pk₀ T?₀ lct₀ honestC₀)
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ)
    (Q : Party) (w : Bytes) (isDel : Bool)
    (hbnd : SimCStateBounded q sC)
    (hsna : SanSnapExtra C K sC) :
    (Prod.map (Option.map recvResultDec) simFullDec <$>
      (recvHookOfBranchesC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam)
        idA idB q sameBranchC newBranchC).eval
        (.cons (simFullEnc sC, (partyToBool Q, (w, isDel))) .nil)) =
    (Prod.map id Prod.fst <$>
      semRecvHookS (paramsV1 C K idA idB) Dh encPt encT decT lam T Kc
        (fig8IdSemHook (PQC := BitVec 512) none) qep B sC () Q w isDel) := by
  set refuse :=
    sC.base.stopped || sC.base.mir.win ||
      (isDel && (sC.base.mir.inTransit Q.other w).isNone) ||
      (!isDel && ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
        !(ratchetKeyAdmissible protoSignalCodec decT encT w)))
  by_cases href : refuse = true
  · exact recvHookOfBranchesC_eval_prefix C K Dh encPt encT decT lam idA idB q qep B T Kc
      sameBranchC newBranchC sC Q w isDel hbnd.base.trans_le hsna (Or.inl href)
  · have href_f : refuse = false := Bool.eq_false_iff.mpr href
    cases hparse : simParseRecvC (paramsV1 C K idA idB) decT (2 ^ 32) (partyEnc Q) (sC.base.pq Q) w with
    | none =>
      exact recvHookOfBranchesC_eval_prefix C K Dh encPt encT decT lam idA idB q qep B T Kc
        sameBranchC newBranchC sC Q w isDel hbnd.base.trans_le hsna (Or.inr hparse)
    | some parsed =>
      rcases parsed with ⟨pq', i, pk, T?, lct⟩
      let inp0 := (simFullEnc sC, (partyToBool Q, (w, isDel)))
      let ρ₀ : Env [recvHookInpT ℓ Pt] := .cons inp0 .nil
      have hq0 : (Expr.fst (.snd (Expr.v0 (O := AOps)))).eval ρ₀ = partyEnc Q :=
        partyToBool_eq_partyEnc Q
      have hrefE :
          (recvRefuseE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)
            q (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
            (.snd (.snd (.snd .v0)))).eval ρ₀ = false := by
        rw [recvRefuseE_eval C K Dh encPt encT decT lam q _ _ _ _ ρ₀ sC Q w isDel
          hbnd.base.trans_le rfl hq0 rfl rfl]
        exact href_f
      have hpq0 : (pGet (ssPq (scBase (.fst .v0))) (.fst (.snd .v0)) :
          Expr AOps [recvHookInpT ℓ Pt] (ReductionDsl.B 32)).eval ρ₀ = sC.base.pq Q :=
        pGet_ssPq_eval (.fst .v0) (.fst (.snd .v0)) ρ₀ sC Q rfl hq0
      have hparseE := parseRecvAtomicC_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam)
        (fig8SmIface ℓ Pt) idA idB (2 ^ 32) (.fst (.snd .v0))
        (pGet (ssPq (scBase (.fst .v0))) (.fst (.snd .v0)))
        (.fst (.snd (.snd .v0))) ρ₀ (partyEnc Q) (sC.base.pq Q) w
        hq0 hpq0 rfl (hsna.1 Q)
      rw [hparse] at hparseE
      let parsedV := parseOutV (ℓ := ℓ) (Pt := Pt) (pq', (i, (pk, (T?, lct))))
      let ρ₁ : Env [parseOutT ℓ Pt, .opt (parseOutT ℓ Pt), recvHookInpT ℓ Pt] :=
        .cons parsedV (.cons (some parsedV) ρ₀)
      let honestC := (sC.base.honest.find? fun wc =>
        wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)
      have hhonE :
          (honestLookupE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)
            q (.fst .v2) (.fst (.snd .v2)) (.fst (.snd (.snd .v2)))).eval ρ₁ =
          honestC.map fig8CtV :=
        honestLookupE_eval C K Dh encPt encT decT lam q _ _ _ ρ₁ sC Q w
          hbnd.base.honest_le rfl (by exact partyToBool_eq_partyEnc Q) rfl
      let ρ₂ : Env [.opt (fig8CtT (ℓ := ℓ) (Pt := Pt)), parseOutT ℓ Pt,
          .opt (parseOutT ℓ Pt), recvHookInpT ℓ Pt] := .cons (honestC.map fig8CtV) ρ₁
      have hchE : (pGet (ssChains (scBase (.fst .v3))) (.fst (.snd .v3)) :
          Expr AOps _ _).eval ρ₂ = (sC.base.chains Q).map ghostChainEnc :=
        pGet_ssChains_eval (.fst .v3) (.fst (.snd .v3)) ρ₂ sC Q rfl
          (by exact partyToBool_eq_partyEnc Q)
      have hfindE :
          (findChainIdxE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)
            (pGet (ssChains (scBase (.fst .v3))) (.fst (.snd .v3)))
            (.fst (.snd (.snd .v1)))).eval ρ₂ =
          (sC.base.chains Q).findIdx? (fun g => g.key == some pk) :=
        eval_findChainIdxE _ _ ρ₂ (sC.base.chains Q) hchE (hsna.2.1 Q).1
      have hlhs :
          (recvHookOfBranchesC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)
            idA idB q sameBranchC newBranchC).eval ρ₀ =
          (Comp.caseOpt
            (findChainIdxE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
              (encT := encT) (decT := decT) (lam := lam)
              (pGet (ssChains (scBase (.fst .v3))) (.fst (.snd .v3)))
              (.fst (.snd (.snd .v1))))
            (callSub1C newBranchC
              (.pair (.fst .v3) (.pair (.fst (.snd .v3)) (.pair (.fst (.snd (.snd .v3)))
                (.pair (.snd (.snd (.snd .v3))) (.pair .v1 .v0))))))
            (callSub1C sameBranchC
              (.pair (.fst .v4) (.pair (.fst (.snd .v4)) (.pair (.fst (.snd (.snd .v4)))
                (.pair (.snd (.snd (.snd .v4))) (.pair .v2 (.pair .v1 .v0)))))))).eval ρ₂ := by
        dsimp only [recvHookOfBranchesC]
        rw [Comp.eval, hrefE]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [Comp.eval, hparseE, Option.map_some, pure_bind]
        rw [Comp.eval]
        change ((Comp.ret _).bind _).eval ρ₁ = _
        rw [Comp.eval, Comp.eval, hhonE, pure_bind]
      rw [hlhs, Comp.eval, hfindE]
      have hcodec : (paramsV1 C K idA idB).codec = protoSignalCodec := rfl
      conv_rhs =>
        arg 2
        unfold semRecvHookS
        simp only [hcodec, href_f, Bool.false_eq_true, ↓reduceIte, hparse, refuse]
      rcases hidx : (sC.base.chains Q).findIdx? (fun g => g.key == some pk) with _ | ci <;>
        simp only [hidx]
      · rw [callSub1C_eval]
        exact hnew sC Q w isDel pq' i pk T? lct honestC hbnd hsna
      · rw [callSub1C_eval]
        exact hsame sC Q w isDel pq' i pk T? lct honestC ci hbnd hsna

theorem recvArmC_eval (isDel : Bool)
    (recvHookC : Comp AOps (fig8SmIface ℓ Pt) [recvHookInpT ℓ Pt] (recvOutT ℓ Pt))
    (s_raw : (simFullT ℓ Pt).denote) (qB : Bool) (w : Bytes) :
    (recvArmC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) isDel recvHookC).eval
      (.cons s_raw (.cons (qB, w) .nil)) =
    recvHookC.eval (.cons (s_raw, (qB, (w, isDel))) .nil) := by
  rw [recvArmC, callSub1C_eval]
  rfl

omit [SampleableType Pt] in
theorem simFig8OracleSan_deliver_eq
    (idA idB : IdentityKey) (qep B T Kc Bsk : ℕ)
    (Q : Party) (w : Bytes) (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ) :
    ((simFig8OracleSan (paramsV1 C K idA idB) Dh encPt encT decT lam qep B T Kc Bsk
      (.inr (.inl (.inl (.inr (Q, w)))))).run sC) =
    (Prod.map id Prod.fst <$>
      semRecvHookS (paramsV1 C K idA idB) Dh encPt encT decT lam T Kc
        (fig8IdSemHook (PQC := BitVec 512) none) qep B sC () Q w true) := by
  simp only [simFig8OracleSan, StateT.run_mk, semHandleHookDedupS, fig8IdSemHook, pure_bind]
  rw [map_eq_bind_pure_comp, bind_assoc]
  simp [Function.comp]
  congr 1

omit [SampleableType Pt] in
theorem simFig8OracleSan_inject_eq
    (idA idB : IdentityKey) (qep B T Kc Bsk : ℕ)
    (Q : Party) (w : Bytes) (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ) :
    ((simFig8OracleSan (paramsV1 C K idA idB) Dh encPt encT decT lam qep B T Kc Bsk
      (.inr (.inl (.inr (Q, w))))).run sC) =
    (Prod.map id Prod.fst <$>
      semRecvHookS (paramsV1 C K idA idB) Dh encPt encT decT lam T Kc
        (fig8IdSemHook (PQC := BitVec 512) none) qep B sC () Q w false) := rfl

end Proofs

end Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvNew

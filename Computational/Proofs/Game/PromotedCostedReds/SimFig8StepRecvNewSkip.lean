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

/-!
# Prefix and Early-Reject Lemmas for `simFig8` New-Epoch Receive

Proves `.eval` specifications for the pure wire and guard helpers, early-rejection branches of
`recvNewOfFwdC`, and the refusal and parse-error prefix of `recvHookOfBranchesC`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvNewSkip

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Env Ops Expr Comp Iface
  atomicSig atomicSessionOps fig8SmIface AtomicPureOp
  B PtT fig8CtT fig8CtV lctT lctV
  partyToBool recvResultDec)
open CryptoGames (Party)
open CryptoGames.CKA (DHFun)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (Bytes paramsV1)
open CryptoGames.Ratchet.LibsignalInst (LibsignalCiphertextWithSalt32 ratchetKeyAdmissible)
open CryptoGames.Ratchet.LibsignalSim (Fig8C simParseRecvC inReceiveOnlyEpoch)
open CryptoGames.Ratchet.LibsignalSimC (LibsignalToModularSchemeSimState)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoGames.SM (partyEnc orE isSomeE otherE senderOfE ite_eval orE_eval isSomeE_eval
  otherE_eval senderOfE_eval boolEq_eval pGet find?_map_eq)
open Computational.Proofs.Game.PromotedCostedReds.SanOracleCore (semRecvHookS)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8State
  (sOpPure eval_sOpPure eLet eval_eLet eMapOpt eval_eMapOpt
   mWin mEpoch mSafeInjE mSafeInjE_eval mInTransitE mInTransitE_eval mInWinE mInWinE_eval
   anyChainKeyNoneE eval_anyChainKeyNoneE
   ssMir ssPq ssHonest ssChains ssAmb ssStopped ssSetAmb eval_ssSetAmb
   scBase scSetBase eval_scSetBase)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8Crypto
  (parseOutV lctSaltEqOfLctAtomicE lctSaltEqOfLctAtomicE_eval injOKAtomicE_eval
   isZeroPtOptAtomicE isZeroPtOptAtomicE_eval parseRecvAtomicC_eval)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanCoupling (SanSnapExtra)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost
  (simBaseT simFullT simRecEnc simMirEnc ghostChainEnc honestPairEnc simBaseEnc simFullEnc
   simFullDec simFullDec_simFullEnc fig8IdSemHook)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvNewCost
  (recvOutT fwdHookInpT recvSameInpT recvNewInpT recvHookInpT
   wkTop1Comp callSub1C rejOutE noneOutE
   mkCAtomicE recvNewEvictedE recvNewSaltEqE recvNewSCAmbE recvNewRangeBadE
   recvRefuseE honestLookupE recvNewOfFwdC recvHookOfBranchesC semRecvNewBranch)

section SkipLemmas

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (K : MlKem)
  (Dh : DHFun (BitVec 256) Pt)
  (encPt : Pt → List (BitVec 8))
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (lam : Pt)

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem partyToBool_eq_partyEnc (Q : Party) : partyToBool Q = partyEnc Q := by
  cases Q <;> rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem callSub1C_eval {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {a t : Ty S}
    (c : Comp O I [a] t) (argE : Expr O Γ a) (ρ : Env Γ) :
    (callSub1C c argE).eval ρ = c.eval (.cons (argE.eval ρ) .nil) := by
  simp only [callSub1C, wkTop1Comp, Comp.eval, pure_bind]
  exact Comp.renameM_eval c fun ⦃_⦄ v => by
    cases v with
    | zero => rfl
    | succ w => nomatch w

theorem mkCAtomicE_eval {Γ : List (Ty ASig)}
    (honestCE : Expr AOps Γ (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))))
    (tE : Expr AOps Γ .nat) (tOptE : Expr AOps Γ (.opt PtT))
    (lctE : Expr AOps Γ (lctT (ℓ := ℓ) (Pt := Pt))) (ρ : Env Γ)
    (honestC : Option (Fig8C Pt)) (t : ℕ) (T? : Option Pt)
    (lct : ℕ × LibsignalCiphertextWithSalt32)
    (hh : honestCE.eval ρ = honestC.map fig8CtV)
    (ht : tE.eval ρ = t) (hT : tOptE.eval ρ = T?) (hl : lctE.eval ρ = lctV lct) :
    (mkCAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam)
      honestCE tE tOptE lctE).eval ρ =
    fig8CtV (match honestC with
      | some c => if c.2.2.2 = lct.2.2 then c else ((t, T?), lct)
      | none => ((t, T?), lct)) := by
  have _ : Nonempty (SampleableType Pt) := ⟨inferInstance⟩
  unfold mkCAtomicE
  rw [eval_eLet]
  have hp : (Expr.pair honestCE (.pair (.pair tE tOptE) lctE)).eval ρ =
      (honestC.map fig8CtV, fig8CtV ((t, T?), lct)) := by
    simp [Expr.eval, hh, ht, hT, hl, fig8CtV]
  rw [hp]
  rcases honestC with _ | c
  · simp [Expr.eval, Expr.v0]
  · simp only [Option.map_some, Expr.eval, Expr.v0]
    set ρ₂ : Env (fig8CtT (ℓ := ℓ) (Pt := Pt) ::
        .prod (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))) (fig8CtT (ℓ := ℓ) (Pt := Pt)) :: Γ) :=
      .cons (fig8CtV c) (.cons (some (fig8CtV c), fig8CtV ((t, T?), lct)) ρ)
    change (Expr.ite
      (lctSaltEqOfLctAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) .v0 (.snd (.snd .v1)))
      .v0 (.snd .v1)).eval ρ₂ = _
    rw [ite_eval, lctSaltEqOfLctAtomicE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) .v0 (.snd (.snd .v1)) ρ₂ c lct rfl rfl]
    by_cases h : c.2.2.2 = lct.2.2 <;> simp [h, ρ₂, Expr.eval, Expr.v0, Expr.v1]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem recvNewEvictedE_eval {O' : Ops ASig} {Γ : List (Ty ASig)}
    (honestCE : Expr O' Γ (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))))
    (ep1E : Expr O' Γ .nat) (ρ : Env Γ)
    (honestC : Option (Fig8C Pt)) (ep1 : ℕ)
    (hh : honestCE.eval ρ = honestC.map fig8CtV) (hep : ep1E.eval ρ = ep1) :
    (recvNewEvictedE honestCE ep1E).eval ρ =
      ((honestC.map fun c => decide (c.1.1 ≠ ep1)) == some true) := by
  unfold recvNewEvictedE
  rw [eval_eLet]
  rcases honestC with _ | c
  · simp [hh, hep, Expr.eval, Expr.v0]
  · simp only [hh, hep, Option.map_some, Expr.eval, Expr.v0, Expr.v1, fig8CtV]
    by_cases h : c.1.1 = ep1 <;> simp [h]

theorem recvNewSaltEqE_eval {Γ : List (Ty ASig)}
    (honestCE : Expr AOps Γ (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))))
    (lctE : Expr AOps Γ (lctT (ℓ := ℓ) (Pt := Pt))) (ρ : Env Γ)
    (honestC : Option (Fig8C Pt)) (lct : ℕ × LibsignalCiphertextWithSalt32)
    (hh : honestCE.eval ρ = honestC.map fig8CtV) (hl : lctE.eval ρ = lctV lct) :
    (recvNewSaltEqE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) honestCE lctE).eval ρ =
      ((honestC.map fun c => decide (c.2.2.2 = lct.2.2)) == some true) := by
  have _ : Nonempty (SampleableType Pt) := ⟨inferInstance⟩
  unfold recvNewSaltEqE
  rw [eval_eLet]
  have hp : (Expr.pair honestCE lctE).eval ρ = (honestC.map fig8CtV, lctV lct) := by
    simp [Expr.eval, hh, hl]
  rw [hp]
  rcases honestC with _ | c
  · simp [Expr.eval, Expr.v0]
  · simp only [Option.map_some, Expr.eval, Expr.v0]
    set ρ₂ : Env (fig8CtT (ℓ := ℓ) (Pt := Pt) ::
        .prod (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))) (lctT (ℓ := ℓ) (Pt := Pt)) :: Γ) :=
      .cons (fig8CtV c) (.cons (some (fig8CtV c), lctV lct) ρ)
    change (lctSaltEqOfLctAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) .v0 (.snd .v1)).eval ρ₂ = _
    rw [lctSaltEqOfLctAtomicE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) .v0 (.snd .v1) ρ₂ c lct rfl rfl]
    by_cases h : c.2.2.2 = lct.2.2 <;> simp [h]

omit [SampleableType Pt] in
theorem recvNewSCAmbE_eval {O' : Ops ASig} {Γ : List (Ty ASig)}
    (sCE : Expr O' Γ (simFullT ℓ Pt)) (qBE : Expr O' Γ .bool) (ρ : Env Γ)
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ) (Q : Party)
    (hch : (sC.base.chains Q).length ≤ 5)
    (hs : sCE.eval ρ = simFullEnc sC) (hq : qBE.eval ρ = partyEnc Q) :
    (recvNewSCAmbE sCE qBE).eval ρ =
      simFullEnc { sC with base :=
        if (inReceiveOnlyEpoch sC.base.mir Q ||
            (Q == Party.A && (sC.base.chains Q).any (·.key.isNone)))
        then { sC.base with amb := sC.base.amb + 1 }
        else sC.base } := by
  have _ : Nonempty (DecidableEq Pt × Zero Pt) := ⟨(inferInstance, inferInstance)⟩
  unfold recvNewSCAmbE
  rw [eval_eLet]
  have hp : (Expr.pair sCE qBE).eval ρ = (simFullEnc sC, partyEnc Q) := by
    simp [Expr.eval, hs, hq]
  rw [hp]
  set ρ₁ : Env (.prod (simFullT ℓ Pt) .bool :: Γ) := .cons (simFullEnc sC, partyEnc Q) ρ
  have hw : (mInWinE (ssMir (scBase (.fst (Expr.v0 (O := O')))))
      (.snd (Expr.v0 (O := O')))).eval ρ₁ =
      inReceiveOnlyEpoch sC.base.mir Q :=
    mInWinE_eval _ _ ρ₁ sC.base.mir Q
      (by simp [ρ₁, ssMir, scBase, Expr.eval, Expr.v0, simFullEnc, simBaseEnc])
      (by simp [ρ₁, Expr.eval, Expr.v0])
  have hch' : (pGet (ssChains (scBase (.fst (Expr.v0 (O := O')))))
      (.snd (Expr.v0 (O := O')))).eval ρ₁ =
      (sC.base.chains Q).map ghostChainEnc := by
    cases Q <;> rfl
  have hany : (anyChainKeyNoneE (pGet (ssChains (scBase (.fst (Expr.v0 (O := O')))))
      (.snd (Expr.v0 (O := O'))))).eval ρ₁ =
      (sC.base.chains Q).any (·.key.isNone) :=
    eval_anyChainKeyNoneE _ ρ₁ (sC.base.chains Q) hch' hch
  have hset : (scSetBase (.fst (Expr.v0 (O := O')))
      (ssSetAmb (scBase (.fst (Expr.v0 (O := O'))))
        (.add (ssAmb (scBase (.fst (Expr.v0 (O := O'))))) (.nat 1)))).eval ρ₁ =
      simFullEnc { sC with base := { sC.base with amb := sC.base.amb + 1 } } := by
    apply eval_scSetBase _ _ ρ₁ sC _ rfl
    exact eval_ssSetAmb _ _ ρ₁ sC.base rfl
  have hCond : (orE (mInWinE (ssMir (scBase (.fst (Expr.v0 (O := O')))))
        (.snd (Expr.v0 (O := O'))))
      (.and (.not (.snd (Expr.v0 (O := O'))))
        (anyChainKeyNoneE (pGet (ssChains (scBase (.fst (Expr.v0 (O := O')))))
          (.snd (Expr.v0 (O := O'))))))).eval ρ₁ =
      (inReceiveOnlyEpoch sC.base.mir Q ||
        (Q == Party.A && (sC.base.chains Q).any (·.key.isNone))) := by
    rw [orE_eval, hw]
    simp only [Expr.eval, hany]
    cases Q <;> simp [ρ₁, Expr.eval, Expr.v0, partyEnc]
  rw [ite_eval, hCond]
  split_ifs with hamb
  · exact hset
  · rfl

omit [SampleableType Pt] in
theorem recvNewRangeBadE_eval {O' : Ops ASig} {Γ : List (Ty ASig)}
    (sCE : Expr O' Γ (simFullT ℓ Pt)) (qBE : Expr O' Γ .bool)
    (iE : Expr O' Γ .nat) (ρ : Env Γ)
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ) (Q : Party) (i : ℕ)
    (hs : sCE.eval ρ = simFullEnc sC) (hq : qBE.eval ρ = partyEnc Q)
    (hi : iE.eval ρ = i) :
    (recvNewRangeBadE sCE qBE iE).eval ρ =
      (inReceiveOnlyEpoch sC.base.mir Q || decide (25000 < i - 1) || decide (2 ^ 32 ≤ i)) := by
  have _ : Nonempty (DecidableEq Pt × Zero Pt) := ⟨(inferInstance, inferInstance)⟩
  unfold recvNewRangeBadE
  have hw : (mInWinE (ssMir (scBase sCE)) qBE).eval ρ = inReceiveOnlyEpoch sC.base.mir Q :=
    mInWinE_eval _ _ ρ sC.base.mir Q
      (by simp [scBase, ssMir, Expr.eval, hs, simFullEnc, simBaseEnc]) hq
  rw [orE_eval, orE_eval, hw]
  simp only [Expr.eval, hi]
  congr 1
  by_cases hlt : i < 4294967296
  · have hle : ¬ (4294967296 ≤ i) := by omega
    simp [hlt, hle]
  · have hle : 4294967296 ≤ i := by omega
    simp [hlt, hle]

theorem recvRefuseE_eval (Lq : ℕ) {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (wE : Expr AOps Γ (B (ℓ := ℓ) (Pt := Pt) 32)) (isDelE : Expr AOps Γ .bool)
    (ρ : Env Γ)
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ) (Q : Party) (w : Bytes) (isDel : Bool)
    (htr : sC.base.mir.trans.length ≤ Lq)
    (hs : sCE.eval ρ = simFullEnc sC) (hq : qBE.eval ρ = partyEnc Q)
    (hw : wE.eval ρ = w) (hd : isDelE.eval ρ = isDel) :
    (recvRefuseE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) Lq sCE qBE wE isDelE).eval ρ =
      (sC.base.stopped || sC.base.mir.win ||
        (isDel && (sC.base.mir.inTransit Q.other w).isNone) ||
        (!isDel && ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
          !(ratchetKeyAdmissible protoSignalCodec decT encT w)))) := by
  have _ : Nonempty (SampleableType Pt) := ⟨inferInstance⟩
  unfold recvRefuseE
  rw [eval_eLet]
  have hp : (Expr.pair sCE (.pair qBE (.pair wE isDelE))).eval ρ =
      (simFullEnc sC, (partyEnc Q, (w, isDel))) := by
    simp [Expr.eval, hs, hq, hw, hd]
  rw [hp]
  set ρ₁ : Env (recvHookInpT ℓ Pt :: Γ) := .cons (simFullEnc sC, (partyEnc Q, (w, isDel))) ρ
  rw [eval_eLet]
  have hinTr : (isSomeE (mInTransitE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) Lq
      (ssMir (scBase (.fst .v0))) (otherE (.fst (.snd .v0)))
      (.fst (.snd (.snd .v0))))).eval ρ₁ =
      (sC.base.mir.inTransit Q.other w).isSome := by
    rw [isSomeE_eval, mInTransitE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) Lq _ _ _ ρ₁ sC.base.mir Q.other htr
      (by simp [ρ₁, ssMir, scBase, Expr.eval, Expr.v0, simFullEnc, simBaseEnc])
      (by cases Q <;> simp [ρ₁, otherE_eval, Expr.eval, Expr.v0, partyEnc, Party.other])]
    simp [ρ₁, Expr.eval, Expr.v0]
  rw [hinTr]
  set ρ₂ : Env (.bool :: recvHookInpT ℓ Pt :: Γ) :=
    .cons (sC.base.mir.inTransit Q.other w).isSome ρ₁
  have hsafe : (mSafeInjE (ssMir (scBase (.fst (Expr.v1 (O := AOps)))))).eval ρ₂ =
      sC.base.mir.safeInj 3 :=
    mSafeInjE_eval _ ρ₂ sC.base.mir
      (by simp [ρ₂, ρ₁, ssMir, scBase, Expr.eval, Expr.v1, simFullEnc, simBaseEnc])
  simp only [orE_eval, Expr.eval, hsafe, injOKAtomicE_eval]
  simp only [ρ₂, ρ₁, ssStopped, mWin, ssMir, scBase, Expr.eval, Expr.v0, Expr.v1,
    simFullEnc, simBaseEnc, simMirEnc]
  cases sC.base.mir.inTransit Q.other w <;> rfl

theorem honestLookupE_eval (Lq : ℕ) {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (wE : Expr AOps Γ (B (ℓ := ℓ) (Pt := Pt) 32)) (ρ : Env Γ)
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ) (Q : Party) (w : Bytes)
    (hhon : sC.base.honest.length ≤ Lq)
    (hs : sCE.eval ρ = simFullEnc sC) (hq : qBE.eval ρ = partyEnc Q)
    (hw : wE.eval ρ = w) :
    (honestLookupE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) Lq sCE qBE wE).eval ρ =
      ((sC.base.honest.find? fun wc =>
        wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map fig8CtV := by
  have _ : Nonempty (SampleableType Pt) := ⟨inferInstance⟩
  have htake : (sC.base.honest.map (honestPairEnc (ℓ := ℓ) (Pt := Pt))).take Lq =
      sC.base.honest.map (honestPairEnc (ℓ := ℓ) (Pt := Pt)) :=
    List.take_of_length_le (by simpa using hhon)
  unfold honestLookupE
  rw [eval_eLet, eval_eMapOpt]
  simp only [ssHonest, scBase, Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ,
    eval_sOpPure, AtomicPureOp.eval, boolEq_eval, senderOfE_eval, otherE_eval,
    hs, hq, hw, simFullEnc, simBaseEnc, htake]
  rw [find?_map_eq, Option.map_map, Option.map_map]
  congr 1
  congr 1
  funext ⟨w', c⟩
  cases hsnd : Party.senderOf c.1.1 <;> cases Q <;> by_cases h : w' = w <;>
    simp [honestPairEnc, fig8CtV, partyEnc, Party.other, hsnd, h]

theorem recvNewOfFwdC_eval_reject
    (idA idB : IdentityKey) (qep B T Kc : ℕ)
    (fwdHookC : Comp AOps (fig8SmIface ℓ Pt) [fwdHookInpT ℓ Pt] (recvOutT ℓ Pt))
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ)
    (Q : Party) (w : Bytes) (isDel : Bool)
    (pq' : Bytes) (i : ℕ) (pk : PublicKey) (T? : Option Pt)
    (lct : ℕ × LibsignalCiphertextWithSalt32)
    (honestC : Option (Fig8C Pt))
    (hch : (sC.base.chains Q).length ≤ 5)
    (hrej :
      (((honestC.map fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true) &&
        ((honestC.map fun c => decide (c.2.2.2 = lct.2.2)) == some true)) = true ∨
      (T? == some 0) = true ∨
      (inReceiveOnlyEpoch sC.base.mir Q || decide (25000 < i - 1) || decide (2 ^ 32 ≤ i)) = true ∨
      T? = none) :
    (Prod.map (Option.map recvResultDec) simFullDec <$>
      (recvNewOfFwdC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) fwdHookC).eval
        (.cons (simFullEnc sC, (partyToBool Q, (w, (isDel,
          (parseOutV (pq', (i, (pk, (T?, lct)))),
            honestC.map fig8CtV))))) .nil)) =
    semRecvNewBranch (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (lam := lam) idA idB qep B T Kc
      sC Q w isDel pq' i pk T? lct honestC := by
  set ρ₀ : Env [recvNewInpT ℓ Pt] :=
    .cons (simFullEnc sC, (partyToBool Q, (w, (isDel,
      (parseOutV (pq', (i, (pk, (T?, lct)))), honestC.map fig8CtV))))) .nil
  unfold recvNewOfFwdC semRecvNewBranch
  dsimp only []
  set evicted := (honestC.map fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true
  set saltEq := (honestC.map fun c => decide (c.2.2.2 = lct.2.2)) == some true
  set rangeBad := inReceiveOnlyEpoch sC.base.mir Q || decide (25000 < i - 1) || decide (2 ^ 32 ≤ i)
  set amb := inReceiveOnlyEpoch sC.base.mir Q ||
    (Q == Party.A && (sC.base.chains Q).any (·.key.isNone))
  set sCAmb : LibsignalToModularSchemeSimState Bytes Pt ℓ :=
    { sC with base := if amb then { sC.base with amb := sC.base.amb + 1 } else sC.base }
  simp only [Comp.eval]
  have hep0 : (Expr.add (pGet (mEpoch (ssMir (scBase (.fst (Expr.v0 (O := AOps))))))
      (.fst (.snd (Expr.v0 (O := AOps))))) (.nat 1)).eval ρ₀ = sC.base.mir.epoch Q + 1 := by
    cases Q <;> simp [ρ₀, pGet, mEpoch, ssMir, scBase, Expr.eval, Expr.v0,
      simFullEnc, simBaseEnc, simMirEnc, partyToBool]
  have hev0 : (recvNewEvictedE (.snd (.snd (.snd (.snd (.snd .v0)))))
      (.add (pGet (mEpoch (ssMir (scBase (.fst .v0)))) (.fst (.snd .v0)))
        (.nat 1))).eval ρ₀ = evicted :=
    recvNewEvictedE_eval _ _ ρ₀ honestC (sC.base.mir.epoch Q + 1) rfl hep0
  have hsa0 : (recvNewSaltEqE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam)
      (.snd (.snd (.snd (.snd (.snd .v0)))))
      (.snd (.snd (.snd (.snd (.fst (.snd (.snd (.snd (.snd .v0)))))))))).eval ρ₀ = saltEq :=
    recvNewSaltEqE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) _ _ ρ₀ honestC lct rfl rfl
  have htz0 : (isZeroPtOptAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam)
      (.fst (.snd (.snd (.snd (.fst (.snd (.snd (.snd (.snd .v0)))))))))).eval ρ₀ =
      (T? == some 0) :=
    isZeroPtOptAtomicE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) _ ρ₀
  have hearly0 : (orE
      (.and (recvNewEvictedE (.snd (.snd (.snd (.snd (.snd (Expr.v0 (O := AOps)))))))
          (.add (pGet (mEpoch (ssMir (scBase (.fst .v0)))) (.fst (.snd .v0))) (.nat 1)))
        (recvNewSaltEqE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (.snd (.snd (.snd (.snd (.snd .v0)))))
          (.snd (.snd (.snd (.snd (.fst (.snd (.snd (.snd (.snd .v0)))))))))))
      (isZeroPtOptAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam)
        (.fst (.snd (.snd (.snd (.fst (.snd (.snd (.snd (.snd .v0))))))))))).eval ρ₀ =
      ((evicted && saltEq) || (T? == some 0)) := by
    rw [orE_eval]
    simp only [Expr.eval, hev0, hsa0, htz0]
  rw [hearly0]
  by_cases hearly1 : (evicted && saltEq) = true
  · simp [hearly1, rejOutE, ρ₀, Expr.eval, Expr.v0, recvResultDec, simFullDec_simFullEnc]
  · have hearly1' : (evicted && saltEq) = false := Bool.eq_false_iff.mpr hearly1
    simp only [hearly1', Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    by_cases hearly2 : (T? == some 0) = true
    · simp [hearly2, rejOutE, ρ₀, Expr.eval, Expr.v0, recvResultDec, simFullDec_simFullEnc]
    · simp only [hearly2, Bool.false_eq_true, ↓reduceIte, pure_bind]
      have hamb0 : (recvNewSCAmbE (O' := AOps) (.fst .v0) (.fst (.snd .v0))).eval ρ₀ =
          simFullEnc sCAmb :=
        recvNewSCAmbE_eval (O' := AOps) _ _ ρ₀ sC Q hch rfl (partyToBool_eq_partyEnc Q)
      rw [hamb0]
      set ρ₁ : Env [simFullT ℓ Pt, recvNewInpT ℓ Pt] := .cons (simFullEnc sCAmb) ρ₀
      have hrng : (recvNewRangeBadE (O' := AOps) (.fst .v1) (.fst (.snd .v1))
          (.fst (.snd (.fst (.snd (.snd (.snd (.snd .v1)))))))).eval ρ₁ = rangeBad :=
        recvNewRangeBadE_eval (O' := AOps) _ _ _ ρ₁ sC Q i rfl (partyToBool_eq_partyEnc Q) rfl
      rw [hrng]
      by_cases hbad : rangeBad = true
      · simp [hbad, rejOutE, ρ₁, Expr.eval, Expr.v0, recvResultDec, simFullDec_simFullEnc]
      · simp only [hbad, Bool.false_eq_true, ↓reduceIte]
        have hTnone : T? = none := by
          rcases hrej with h1 | h2 | h3 | h4
          · exact absurd h1 hearly1
          · exact absurd h2 hearly2
          · exact absurd h3 hbad
          · exact h4
        subst hTnone
        simp [rejOutE, ρ₁, ρ₀, parseOutV, Expr.eval, Expr.v0, Expr.v1,
          recvResultDec, simFullDec_simFullEnc]

theorem recvHookOfBranchesC_eval_prefix
    (idA idB : IdentityKey) (Lq qep B T Kc : ℕ)
    (sameBranchC : Comp AOps (fig8SmIface ℓ Pt) [recvSameInpT ℓ Pt] (recvOutT ℓ Pt))
    (newBranchC : Comp AOps (fig8SmIface ℓ Pt) [recvNewInpT ℓ Pt] (recvOutT ℓ Pt))
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ)
    (Q : Party) (w : Bytes) (isDel : Bool)
    (htr : sC.base.mir.trans.length ≤ Lq)
    (hsna : SanSnapExtra C K sC)
    (hpref :
      (sC.base.stopped || sC.base.mir.win ||
        (isDel && (sC.base.mir.inTransit Q.other w).isNone) ||
        (!isDel && ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
          !(ratchetKeyAdmissible protoSignalCodec decT encT w)))) = true ∨
      simParseRecvC (paramsV1 C K idA idB) decT (2 ^ 32) (partyEnc Q) (sC.base.pq Q) w = none) :
    (Prod.map (Option.map recvResultDec) simFullDec <$>
      (recvHookOfBranchesC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam)
        idA idB Lq sameBranchC newBranchC).eval
        (.cons (simFullEnc sC, (partyToBool Q, (w, isDel))) .nil)) =
    (Prod.map id Prod.fst <$>
      semRecvHookS (paramsV1 C K idA idB) Dh encPt encT decT lam T Kc
        (fig8IdSemHook (PQC := BitVec 512) none) qep B sC () Q w isDel) := by
  set ρ₀ : Env [recvHookInpT ℓ Pt] := .cons (simFullEnc sC, (partyToBool Q, (w, isDel))) .nil
  set refuse := sC.base.stopped || sC.base.mir.win ||
    (isDel && (sC.base.mir.inTransit Q.other w).isNone) ||
    (!isDel && ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
      !(ratchetKeyAdmissible protoSignalCodec decT encT w)))
  unfold recvHookOfBranchesC semRecvHookS
  simp only [Comp.eval]
  have href0 : (recvRefuseE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) Lq
      (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))).eval ρ₀ =
      refuse :=
    recvRefuseE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) Lq _ _ _ _ ρ₀ sC Q w isDel htr
      rfl (partyToBool_eq_partyEnc Q) rfl rfl
  rw [href0]
  have hcodec : (paramsV1 C K idA idB).codec = protoSignalCodec := rfl
  rw [hcodec]
  change (Prod.map (Option.map recvResultDec) simFullDec <$>
      (if refuse = true then _ else _)) =
    (Prod.map id Prod.fst <$> (if refuse = true then _ else _))
  by_cases href : refuse = true
  · simp [href, noneOutE, ρ₀, Expr.eval, Expr.v0, simFullDec_simFullEnc]
  · have hparse :
        simParseRecvC (paramsV1 C K idA idB) decT (2 ^ 32) (partyEnc Q) (sC.base.pq Q) w = none :=
      hpref.resolve_left href
    simp only [href, Bool.false_eq_true, ↓reduceIte]
    have hpq : (pGet (ssPq (scBase (.fst (Expr.v0 (O := AOps)))))
        (.fst (.snd (Expr.v0 (O := AOps))))).eval ρ₀ = sC.base.pq Q := by
      cases Q <;> simp [ρ₀, pGet, ssPq, scBase, Expr.eval, Expr.v0,
        simFullEnc, simBaseEnc, partyToBool]
    have hpC := parseRecvAtomicC_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (fig8SmIface ℓ Pt) idA idB (2 ^ 32)
      (.fst (.snd .v0)) (pGet (ssPq (scBase (.fst .v0))) (.fst (.snd .v0)))
      (.fst (.snd (.snd .v0))) ρ₀ (partyEnc Q) (sC.base.pq Q) w
      (partyToBool_eq_partyEnc Q) hpq rfl (hsna.1 Q)
    rw [hpC, hparse]
    simp [rejOutE, ρ₀, Expr.eval, Expr.v0, Expr.v1, recvResultDec,
      simFullDec_simFullEnc]

end SkipLemmas

end Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvNewSkip

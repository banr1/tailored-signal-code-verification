/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvSameCost
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvSameKept

/-!
# Existing-Epoch Receive Branch for the Atomic `simFig8` Step

Proves `.eval` correctness for the resync and forward-hook subprograms (`SimFig8FwdHookSpec`),
the existing-chain receive branch (`SimFig8RecvSameSpec`), and the parameterized receive handler
`recvHookOfNewAtomicC`.
-/

@[expose] public section

set_option autoImplicit false

open Computational.Proofs.Game.PromotedCostedReds.SanOracleCore (evalCKS figS fsS semFwdAnswerHookS semFwdEvictHookS semFwdHookS semHandleHookDedupS semRecvHookS semResyncHookS)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanOracle (simFig8OracleSan)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvSameCost (fwaC' fwaCi? fwaIsDel fwaPk fwaPq' fwaQ fwaSC fwaW fwdAnsInpT fwdHookInpT fwhC' fwhHonest fwhIsDel fwhQ fwhSC fwhToAnsInp fwhW inTransitHonestE mkCE poI poLct poPk poT? recvHookOfNewAtomicC recvNewSiteCtx recvOutT recvSameBranchAtomicC recvSameBranchAtomicC_cost recvSameBranchAtomicC_descBits_le recvSameBranchAtomicC_queries recvSameInpT resyncInpT rsmCi rsmHonest rsmParsed rsmQ rsmSC rsyC rsyCi? rsyPk rsyPq' rsyQ rsyR rsySC rsyW scUpdateKeptRecv semFwdAnswerAtomicC semFwdHookAtomicC semFwdHookAtomicC_cost semFwdHookAtomicC_descBits_le semFwdHookAtomicC_queries semResyncAtomicC smRrFullT)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvSameKept (evalCKSAtomicC_eval honestFindE_eval inTransitHonestE_eval mkCE_eval onAcceptPureAtomicC_eval onAnswerPureAtomicC_eval recvRefuseE_eval)
open ReductionDsl (B Comp Env Expr Iface Ops PlainT Sig Ty atomicSessionOps atomicSig bits boolToParty fig8CtOfV fig8CtT fig8CtV fig8SmIface lpubT lpubV partyToBool recvResultDec recvResultEnc recvResultT smRrEnc)

namespace Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvSame

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Ops Iface Expr Comp handlerImpl bits
  atomicSig atomicSessionOps fig8SmIface e2eSessionCodec GhostStT B PlainT PK PtT
  lpubT lpubV lctT lctV fig8CtT fig8CtV fig8CtOfV smQT smRT smRrT smRrEnc
  recvResultT recvResultEnc recvResultDec partyToBool boolToParty SMTag)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32
  ratchetKeyAdmissible)
open CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C SimFig8C Fig8Comp GhostChain SimState
  SimStateBounded SimCStateBounded inReceiveOnlyEpoch simParseRecvC onAcceptPure onAnswerPure)
open CryptoGames.Ratchet.LibsignalSimC (Kept LibsignalToModularSchemeSimState)
open CryptoGames.SM (RecvResult partyEnc partyDec pGet pSet otherE otherE_eval pGet_eval pSet_eval
  ite_eval)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey GhostState)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalSession (ratchetCostBudget)
open CryptoVerification.E2E (Bytes paramsV1)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost
  (atomicSessionOpDescBits atomicExprDescBits atomicCompDescBits)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost
  (simFullT simFullEnc simFullDec simFullDec_simFullEnc simBaseT simBaseEnc simBaseDec
   simBaseDec_simBaseEnc keptT keptEnc keptDec keptDec_keptEnc sentEntryEnc sentEntryDec
   sentEntryDec_sentEntryEnc snapEnc snapDec snapDec_snapEnc ghostChainEnc fig8CtOfV_fig8CtV
   fig8IdSemHook)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8State
  (scBase scKept scSent scSnaps scMk ssMir ssPq ssChains getChainDE eval_getChainDE
   eval_ghostRejectsE eval_findChainIdxE mSafeInjE mSafeInjE_eval)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8Crypto
  (kDecOutT kDecOutV parseOutT parseOutV parseRecvAtomicC_eval partyToBool_eq_partyEnc)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept
  (eqFig8CAtomicE eqFig8CAtomicE_eval keptRecvAtomicE keptRecvAtomicE_eval)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanCoupling (SanSnapExtra)

/-- Semantic existing-epoch (`findIdx? = some ci`) sub-branch of `semRecvHookS` with
`fig8IdSemHook none` (projecting away the `Unit` extra state). -/
def semRecvSameBranch {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt)
    (qep B T Kc : ℕ)
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ)
    (Q : Party) (w : Bytes) (isDel : Bool)
    (pq' : Bytes) (i : ℕ) (pk : PublicKey) (T? : Option Pt)
    (lct : ℕ × LibsignalCiphertextWithSalt32)
    (honestC : Option (SimFig8C Pt)) (ci : ℕ) :
    Fig8Comp Pt ℓ (Option (RecvResult (Plain ℓ)) × LibsignalToModularSchemeSimState Bytes Pt ℓ) :=
  let P := paramsV1 C K idA idB
  let mkC (t : ℕ) (T : Option Pt) : SimFig8C Pt :=
    match honestC with
    | some c => if c.2.2.2 = lct.2.2 then c else ((t, T), lct)
    | none => ((t, T), lct)
  let g := (sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩
  if g.rejects i then
    pure (some .rejected, sC)
  else
    Prod.map id Prod.fst <$>
      semFwdHookS P Dh encPt encT lam T Kc (fig8IdSemHook (PQC := BitVec 512) none)
        qep B sC () Q w isDel (some ci) pk pq' honestC (mkC g.epoch T?)

/-- Semantic new-epoch (`findIdx? = none`) sub-branch of `semRecvHookS` with
`fig8IdSemHook none` (projecting away the `Unit` extra state). -/
def semRecvNewBranch {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt)
    (qep B T Kc : ℕ)
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ)
    (Q : Party) (w : Bytes) (isDel : Bool)
    (pq' : Bytes) (i : ℕ) (pk : PublicKey) (T? : Option Pt)
    (lct : ℕ × LibsignalCiphertextWithSalt32)
    (honestC : Option (SimFig8C Pt)) :
    Fig8Comp Pt ℓ (Option (RecvResult (Plain ℓ)) × LibsignalToModularSchemeSimState Bytes Pt ℓ) :=
  let P := paramsV1 C K idA idB
  let mkC (t : ℕ) (T : Option Pt) : SimFig8C Pt :=
    match honestC with
    | some c => if c.2.2.2 = lct.2.2 then c else ((t, T), lct)
    | none => ((t, T), lct)
  let evicted := (honestC.map fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true
  let saltEq := (honestC.map fun c => decide (c.2.2.2 = lct.2.2)) == some true
  let amb := inReceiveOnlyEpoch sC.base.mir Q ||
    (Q == CryptoGames.Party.A && (sC.base.chains Q).any (·.key.isNone))
  let sCAmb : LibsignalToModularSchemeSimState Bytes Pt ℓ :=
    { sC with base := if amb then { sC.base with amb := sC.base.amb + 1 } else sC.base }
  if evicted && saltEq then
    pure (some .rejected, sC)
  else if T? == some 0 then
    pure (some .rejected, sC)
  else if inReceiveOnlyEpoch sC.base.mir Q || decide (25000 < i - 1) || decide (2 ^ 32 ≤ i) then
    pure (some .rejected, sCAmb)
  else
    match T? with
    | none => pure (some .rejected, sCAmb)
    | some T₀ =>
      if evicted then
        Prod.map id Prod.fst <$>
          semFwdEvictHookS P Dh encPt encT lam T (fig8IdSemHook (PQC := BitVec 512) none)
            qep sCAmb () Q w isDel pk pq' ((sC.base.mir.epoch Q + 1, some T₀), lct)
      else
        Prod.map id Prod.fst <$>
          semFwdHookS P Dh encPt encT lam T Kc (fig8IdSemHook (PQC := BitVec 512) none)
            qep B sCAmb () Q w isDel none pk pq' honestC (mkC (sC.base.mir.epoch Q + 1) (some T₀))

noncomputable section

section EvalTheorems

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
variable {ℓ : ℕ} {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
variable {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem boolToParty_partyToBool (Q : Party) : boolToParty (partyToBool Q) = Q := by
  cases Q <;> rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem recvResultDec_recvResultEnc (x : RecvResult (Plain ℓ)) :
    recvResultDec (Pt := Pt) (recvResultEnc (ℓ := ℓ) (Pt := Pt) x) = x := by
  cases x <;> rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem option_map_recvResultDec_enc (rr : Option (RecvResult (Plain ℓ))) :
    (rr.map (recvResultEnc (ℓ := ℓ) (Pt := Pt))).map (recvResultDec (Pt := Pt)) = rr := by
  cases rr <;> simp [recvResultDec_recvResultEnc]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem getD_skipped_le (cs : List GhostChain) (ci : ℕ)
    (hsk : ∀ g ∈ cs, g.skipped.length ≤ 2000) :
    (cs.getD ci ⟨none, 0, 0, []⟩).skipped.length ≤ 2000 := by
  induction cs generalizing ci with
  | nil => simp
  | cons hd tl ih =>
    cases ci with
    | zero => exact hsk hd (.head _)
    | succ k => exact ih k fun g hg => hsk g (.tail _ hg)

private theorem query_dl_eval {Γ : List (Ty (atomicSig ℓ Pt))}
    (argE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ
      (.prod .bool (fig8CtT (ℓ := ℓ) (Pt := Pt))))
    (ρ : Env Γ) (Q : Party) (c : SimFig8C Pt)
    (harg : argE.eval ρ = (partyToBool Q, fig8CtV c)) :
    (ReductionDsl.Comp.query (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (I := fig8SmIface ℓ Pt) ReductionDsl.SMTag.dl argE).eval ρ =
    (Option.map (smRrEnc (ℓ := ℓ) (Pt := Pt) fun (pub, m) => (lpubV pub, m)) <$>
      CryptoGames.SM.deliverQuery (St := Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256)
        (C := Fig8C Pt) Q c) := by
  have hpair : (boolToParty (argE.eval ρ).1, fig8CtOfV (argE.eval ρ).2) = (Q, c) := by
    rw [harg, boolToParty_partyToBool, fig8CtOfV_fig8CtV]
  simp only [ReductionDsl.Comp.eval, fig8SmIface]
  rw [hpair]
  rfl

private theorem query_ij_eval {Γ : List (Ty (atomicSig ℓ Pt))}
    (argE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ
      (.prod .bool (fig8CtT (ℓ := ℓ) (Pt := Pt))))
    (ρ : Env Γ) (Q : Party) (c : SimFig8C Pt)
    (harg : argE.eval ρ = (partyToBool Q, fig8CtV c)) :
    (ReductionDsl.Comp.query (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (I := fig8SmIface ℓ Pt) ReductionDsl.SMTag.ij argE).eval ρ =
    (Option.map (smRrEnc (ℓ := ℓ) (Pt := Pt) fun (pub, m) => (lpubV pub, m)) <$>
      CryptoGames.SM.injectQuery (St := Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256)
        (C := Fig8C Pt) Q c) := by
  have hpair : (boolToParty (argE.eval ρ).1, fig8CtOfV (argE.eval ρ).2) = (Q, c) := by
    rw [harg, boolToParty_partyToBool, fig8CtOfV_fig8CtV]
  simp only [ReductionDsl.Comp.eval, fig8SmIface]
  rw [hpair]
  rfl

omit [SampleableType Pt] in
private theorem scMk_scKept_eval {Γ : List (Ty (atomicSig ℓ Pt))}
    (baseE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (simBaseT ℓ Pt))
    (sCE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (simFullT ℓ Pt))
    (ρ : Env Γ) (base' : SimState Bytes Pt ℓ) (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ)
    (hb : baseE.eval ρ = simBaseEnc base') (hsC : sCE.eval ρ = simFullEnc sC) :
    (scMk baseE (scKept sCE) (scSent sCE) (scSnaps sCE)).eval ρ =
      simFullEnc { sC with base := base' } := by
  simp [scMk, scKept, scSent, scSnaps, ReductionDsl.Expr.eval, hb, hsC, simFullEnc]

omit [SampleableType Pt] in
private theorem scMk_updateKeptRecv_eval (idA idB : IdentityKey) (T : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (baseE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (simBaseT ℓ Pt))
    (sCE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (simFullT ℓ Pt))
    (qBE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .bool)
    (cE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (ρ : Env Γ) (base' : SimState Bytes Pt ℓ) (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ)
    (Q : Party) (c : SimFig8C Pt)
    (hb : baseE.eval ρ = simBaseEnc base') (hsC : sCE.eval ρ = simFullEnc sC)
    (hqB : qBE.eval ρ = partyToBool Q) (hc : cE.eval ρ = fig8CtV c) :
    (scMk baseE (scUpdateKeptRecv idA idB T sCE qBE cE) (scSent sCE) (scSnaps sCE)).eval ρ =
      simFullEnc
        { { sC with
            kept := Function.update sC.kept Q
              (CryptoGames.Ratchet.LibsignalSimC.Kept.recv (ℓ := ℓ)
                (fig := figS (ℓ := ℓ) (paramsV1 C K idA idB) Dh encPt encT lam T)
                (fs := fsS (ℓ := ℓ) (paramsV1 C K idA idB) encT T) c (sC.kept Q)) }
          with base := base' } := by
  have hkept_ab : (scKept sCE).eval ρ = (keptEnc (sC.kept .A), keptEnc (sC.kept .B)) := by
    simp [scKept, ReductionDsl.Expr.eval, hsC, simFullEnc]
  have hqEnc : qBE.eval ρ = partyEnc Q := by rw [hqB, partyToBool_eq_partyEnc]
  have hpGet : (pGet (scKept sCE) qBE).eval ρ = keptEnc (sC.kept Q) :=
    pGet_eval (scKept sCE) qBE ρ (fun R => keptEnc (sC.kept R)) Q hkept_ab hqEnc
  have hkRecv := keptRecvAtomicE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB T (pGet (scKept sCE) qBE) cE ρ
    (sC.kept Q) c hpGet hc
  have hpSet := pSet_eval (scKept sCE) qBE
    (keptRecvAtomicE idA idB T (pGet (scKept sCE) qBE) cE) ρ
    (fun R => keptEnc (sC.kept R)) Q hkept_ab hqEnc
  rw [scMk, scUpdateKeptRecv]
  simp only [ReductionDsl.Expr.eval, hb, hsC, hpSet, hkRecv, scSent, scSnaps, simFullEnc]
  cases Q <;> rfl

private theorem eval_ret {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {t : Ty S} (e : Expr O Γ t) (ρ : Env Γ) :
    (ReductionDsl.Comp.ret (I := I) e).eval ρ = pure (e.eval ρ) := rfl

private theorem eval_bind {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {t u : Ty S} (m : Comp O I Γ t) (k : Comp O I (t :: Γ) u) (ρ : Env Γ) :
    (ReductionDsl.Comp.bind m k).eval ρ = (m.eval ρ >>= fun x => k.eval (.cons x ρ)) := rfl

private theorem eval_bind_ret {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {t u : Ty S} (e : Expr O Γ t) (k : Comp O I (t :: Γ) u) (ρ : Env Γ) :
    (ReductionDsl.Comp.bind (.ret e) k).eval ρ = k.eval (.cons (e.eval ρ) ρ) :=
  pure_bind (e.eval ρ) (fun x => k.eval (.cons x ρ))

private theorem eval_ite {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {t : Ty S} (b : Expr O Γ .bool) (c d : Comp O I Γ t) (ρ : Env Γ) :
    (ReductionDsl.Comp.ite b c d).eval ρ = if b.eval ρ then c.eval ρ else d.eval ρ := rfl

private theorem eval_caseOpt {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {t u : Ty S} (e : Expr O Γ (.opt t))
    (n : Comp O I Γ u) (s : Comp O I (t :: Γ) u) (ρ : Env Γ) :
    (ReductionDsl.Comp.caseOpt e n s).eval ρ =
      match e.eval ρ with
      | none => n.eval ρ
      | some x => s.eval (.cons x ρ) := by
  rcases h : e.eval ρ with _ | x <;> simp [ReductionDsl.Comp.eval, h]

private theorem eval_caseOpt_v0_none {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ : List (Ty S)} {t u : Ty S}
    (n : Comp O I (.opt t :: Γ) u) (s : Comp O I (t :: .opt t :: Γ) u) (ρ : Env Γ) :
    (ReductionDsl.Comp.caseOpt .v0 n s).eval (.cons (t := .opt t) none ρ) =
      n.eval (.cons (t := .opt t) none ρ) := rfl

private theorem eval_caseOpt_v0_some {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ : List (Ty S)} {t u : Ty S} (x : t.denote)
    (n : Comp O I (.opt t :: Γ) u) (s : Comp O I (t :: .opt t :: Γ) u) (ρ : Env Γ) :
    (ReductionDsl.Comp.caseOpt .v0 n s).eval (.cons (t := .opt t) (some x) ρ) =
      s.eval (.cons (t := t) x (.cons (t := .opt t) (some x) ρ)) := rfl

private theorem eval_caseSum_v0_inl {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ : List (Ty S)} {t₁ t₂ u : Ty S} (x : t₁.denote)
    (l : Comp O I (t₁ :: .sum t₁ t₂ :: Γ) u)
    (r : Comp O I (t₂ :: .sum t₁ t₂ :: Γ) u) (ρ : Env Γ) :
    (ReductionDsl.Comp.caseSum .v0 l r).eval (.cons (t := .sum t₁ t₂) (.inl x) ρ) =
      l.eval (.cons (t := t₁) x (.cons (t := .sum t₁ t₂) (.inl x) ρ)) := rfl

private theorem eval_caseSum_v0_inr {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ : List (Ty S)} {t₁ t₂ u : Ty S} (y : t₂.denote)
    (l : Comp O I (t₁ :: .sum t₁ t₂ :: Γ) u)
    (r : Comp O I (t₂ :: .sum t₁ t₂ :: Γ) u) (ρ : Env Γ) :
    (ReductionDsl.Comp.caseSum .v0 l r).eval (.cons (t := .sum t₁ t₂) (.inr y) ρ) =
      r.eval (.cons (t := t₂) y (.cons (t := .sum t₁ t₂) (.inr y) ρ)) := rfl

private theorem eval_ret_rejected {Γ : List (Ty (atomicSig ℓ Pt))}
    (sCE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (simFullT ℓ Pt))
    (ρ : Env Γ) (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ)
    (hsC : sCE.eval ρ = simFullEnc sC) :
    (Prod.map (Option.map recvResultDec) simFullDec <$>
      (ReductionDsl.Comp.ret (I := fig8SmIface ℓ Pt) (.pair (.some (.inl .unit)) sCE)).eval ρ) =
    pure (some .rejected, sC) := by
  rw [eval_ret, map_pure]
  change pure (some (recvResultDec (.inl ())), simFullDec (sCE.eval ρ)) = _
  rw [hsC, simFullDec_simFullEnc]
  rfl

private theorem eval_ret_none {Γ : List (Ty (atomicSig ℓ Pt))}
    (sCE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (simFullT ℓ Pt))
    (ρ : Env Γ) (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ)
    (hsC : sCE.eval ρ = simFullEnc sC) :
    (Prod.map (Option.map recvResultDec) simFullDec <$>
      (ReductionDsl.Comp.ret (I := fig8SmIface ℓ Pt) (.pair .none sCE)).eval ρ) =
    pure (none, sC) := by
  rw [eval_ret, map_pure]
  change pure (none, simFullDec (sCE.eval ρ)) = _
  rw [hsC, simFullDec_simFullEnc]

theorem semResyncAtomicC_eval (idA idB : IdentityKey) (L qep T : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (inpE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (resyncInpT ℓ Pt))
    (ρ : Env Γ)
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ)
    (Q : Party) (w : Bytes) (ci? : Option ℕ) (Tpk : PublicKey) (pq' : Bytes)
    (c : SimFig8C Pt) (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ)))
    (hinp : inpE.eval ρ =
      (simFullEnc sC, (partyToBool Q, (w, (ci?, (Tpk, (pq', (fig8CtV c, r.map kDecOutV))))))))
    (hbnd : SimCStateBounded L sC)
    (hextra : SanSnapExtra C K sC) :
    (Prod.map (Option.map recvResultDec) simFullDec <$>
      (semResyncAtomicC (Pt := Pt) (ℓ := ℓ) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
        idA idB L qep T inpE).eval ρ) =
    (Prod.map id Prod.fst <$>
      semResyncHookS (paramsV1 C K idA idB) Dh encPt encT lam T
        (fig8IdSemHook (PQC := BitVec 512) none)
        qep sC () Q w ci? Tpk pq' c r) := by
  unfold semResyncAtomicC semResyncHookS
  rw [eval_bind_ret, hinp, eval_caseOpt]
  have hrsyR :
      (rsyR (O' := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) .v0).eval
        (ReductionDsl.Env.cons (t := resyncInpT ℓ Pt)
          (simFullEnc sC, (partyToBool Q, (w, (ci?, (Tpk, (pq', (fig8CtV c, r.map kDecOutV))))))) ρ) =
      r.map kDecOutV := rfl
  rw [hrsyR]
  rcases r with _ | ⟨t, i, pub, m'⟩
  · dsimp only [Option.map]
    rw [map_pure]
    exact eval_ret_rejected (rsySC .v0) _ sC rfl
  · dsimp only [Option.map]
    let v0 : (resyncInpT ℓ Pt).denote :=
      (simFullEnc sC, (partyToBool Q, (w, (ci?, (Tpk, (pq',
        (fig8CtV c, some (kDecOutV (t, (i, (pub, m')))))))))))
    let ρ0 := ReductionDsl.Env.cons (t := resyncInpT ℓ Pt) v0 ρ
    let ρ1 := ReductionDsl.Env.cons (t := kDecOutT ℓ Pt) (kDecOutV (t, (i, (pub, m')))) ρ0
    rw [eval_bind]
    have hqdl := query_dl_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (.pair (rsyQ .v1) (rsyC .v1)) ρ1 Q c rfl
    rw [hqdl]
    dsimp only [fig8IdSemHook]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    refine bind_congr fun res => ?_
    rcases res with _ | ⟨⟩ | ⟨t', i', pm'⟩
    · dsimp only [Option.map]
      rw [eval_caseOpt_v0_none, eval_ret, pure_bind]
      change pure (some CryptoGames.SM.RecvResult.rejected, simFullDec (simFullEnc sC)) = _
      rw [simFullDec_simFullEnc]; rfl
    · dsimp only [Option.map, smRrEnc]
      rw [eval_caseOpt_v0_some, eval_caseSum_v0_inl, eval_ret, pure_bind]
      change pure (some CryptoGames.SM.RecvResult.rejected, simFullDec (simFullEnc sC)) = _
      rw [simFullDec_simFullEnc]; rfl
    · rw [Option.map_some]
      dsimp only [smRrEnc]
      rw [eval_caseOpt_v0_some, eval_caseSum_v0_inr, eval_bind]
      let pmV : (ReductionDsl.Ty.opt (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) (PlainT (ℓ := ℓ) (Pt := Pt)))).denote :=
        pm'.map fun (pub, m) => (lpubV pub, m)
      let resV : (ReductionDsl.Ty.opt (smRrFullT ℓ Pt)).denote := some (.inr (t', (i', pmV)))
      let ρ2 := ReductionDsl.Env.cons (t := .opt (smRrFullT ℓ Pt)) resV ρ1
      let ρ4 := ReductionDsl.Env.cons
        (t := .prod .nat (.prod .nat (.opt (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) (PlainT (ℓ := ℓ) (Pt := Pt))))))
        (t', (i', pmV))
        (ReductionDsl.Env.cons (t := smRrFullT ℓ Pt) (.inr (t', (i', pmV))) ρ2)
      have hacc := onAcceptPureAtomicC_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) L qep
        (.pair (scBase (rsySC .v4))
          (.pair (rsyQ .v4)
            (.pair (rsyW .v4)
              (.pair (.bool true)
                (.pair (.fst .v3)
                  (.pair (.fst (.snd .v3))
                    (.pair (.snd (.snd (.snd .v3)))
                      (.pair (rsyCi? .v4)
                        (.pair (rsyPk .v4) (rsyPq' .v4))))))))))
        ρ4 sC.base Q w true t i m' ci? Tpk pq' rfl
        hbnd.base.trans_le hbnd.base.chall_le hbnd.base.comp_le (hextra.2.1 Q)
      dsimp only [ρ4, ρ2, resV, pmV, ρ1, ρ0, v0] at hacc
      rw [hacc, pure_bind, eval_ret, pure_bind]
      let accOut := onAcceptPure qep Q w true t i m' ci? Tpk pq' sC.base
      let ρ5 := ReductionDsl.Env.cons (t := .prod (.opt (recvResultT (ℓ := ℓ) (Pt := Pt))) (simBaseT ℓ Pt))
        (accOut.1.map recvResultEnc, simBaseEnc accOut.2) ρ4
      have hsc := scMk_updateKeptRecv_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) idA idB T
        (.snd .v0) (rsySC .v5) (rsyQ .v5) (rsyC .v5) ρ5 accOut.2 sC Q c rfl rfl rfl rfl
      change pure (Prod.map (Option.map recvResultDec) simFullDec
        (accOut.1.map recvResultEnc,
          (scMk (.snd .v0) (scUpdateKeptRecv idA idB T (rsySC .v5) (rsyQ .v5) (rsyC .v5))
            (scSent (rsySC .v5)) (scSnaps (rsySC .v5))).eval ρ5)) = _
      rw [hsc]
      change pure ((accOut.1.map recvResultEnc).map recvResultDec, simFullDec (simFullEnc _)) = _
      rw [option_map_recvResultDec_enc, simFullDec_simFullEnc]
      rfl

theorem semFwdAnswerAtomicC_eval (idA idB : IdentityKey) (L qep T : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (inpE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (fwdAnsInpT ℓ Pt))
    (ρ : Env Γ)
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ)
    (Q : Party) (w : Bytes) (isDel : Bool) (ci? : Option ℕ) (Tpk : PublicKey) (pq' : Bytes)
    (c' : SimFig8C Pt)
    (hinp : inpE.eval ρ =
      (simFullEnc sC, (partyToBool Q, (w, (isDel, (ci?, (Tpk, (pq', fig8CtV c'))))))))
    (hbnd : SimCStateBounded L sC)
    (hextra : SanSnapExtra C K sC) :
    (Prod.map (Option.map recvResultDec) simFullDec <$>
      (semFwdAnswerAtomicC (Pt := Pt) (ℓ := ℓ) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
        idA idB L qep T inpE).eval ρ) =
    (Prod.map id Prod.fst <$>
      semFwdAnswerHookS (paramsV1 C K idA idB) Dh encPt encT lam T
        (fig8IdSemHook (PQC := BitVec 512) none)
        qep sC () Q w isDel ci? Tpk pq' c') := by
  unfold semFwdAnswerAtomicC semFwdAnswerHookS
  rw [eval_bind_ret, hinp, eval_bind]
  set v0 : (fwdAnsInpT ℓ Pt).denote :=
    (simFullEnc sC, (partyToBool Q, (w, (isDel, (ci?, (Tpk, (pq', fig8CtV c')))))))
  set ρ0 := ReductionDsl.Env.cons (t := fwdAnsInpT ℓ Pt) v0 ρ
  have hinT := inTransitHonestE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) L (fwaSC .v0) (fwaQ .v0) (fwaC' .v0)
    ρ0 sC Q c' rfl rfl rfl hbnd.base.honest_le hbnd.base.trans_le hextra.2.2.2
  set inT := sC.base.honest.any fun wc =>
    decide (wc.2 = c') && (sC.base.mir.inTransit Q.other wc.1).isSome
  set qComp : Fig8Comp Pt ℓ (Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ))) :=
    if inT then
      CryptoGames.SM.deliverQuery (St := Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt) Q c'
    else
      CryptoGames.SM.injectQuery (St := Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt) Q c'
  have hq :
      (ReductionDsl.Comp.ite (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
        (t := .opt (smRrFullT ℓ Pt))
        (inTransitHonestE L (fwaSC .v0) (fwaQ .v0) (fwaC' .v0))
        (ReductionDsl.Comp.query (I := fig8SmIface ℓ Pt) ReductionDsl.SMTag.dl (.pair (fwaQ .v0) (fwaC' .v0)))
        (ReductionDsl.Comp.query (I := fig8SmIface ℓ Pt) ReductionDsl.SMTag.ij (.pair (fwaQ .v0) (fwaC' .v0)))).eval ρ0 =
      (Option.map (smRrEnc (ℓ := ℓ) (Pt := Pt) fun (pub, m) => (lpubV pub, m)) <$> qComp) := by
    rw [eval_ite, hinT]
    by_cases h : inT = true
    · simp only [h, ↓reduceIte, qComp]
      exact query_dl_eval (.pair (fwaQ .v0) (fwaC' .v0)) ρ0 Q c' rfl
    · simp only [h, Bool.false_eq_true, ↓reduceIte, qComp]
      exact query_ij_eval (.pair (fwaQ .v0) (fwaC' .v0)) ρ0 Q c' rfl
  have hsh :
      (if inT then (fig8IdSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ) none).onDl Q c' ()
       else (fig8IdSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ) none).onIj Q c' ()) =
      (qComp >>= fun res => pure (res, ())) := by
    by_cases h : inT = true <;> simp [h, qComp, fig8IdSemHook]
  dsimp only
  rw [hq, hsh]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  refine bind_congr fun res => ?_
  rw [eval_bind]
  have hans := onAnswerPureAtomicC_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) L qep
    (.pair (scBase (fwaSC .v1))
      (.pair (fwaQ .v1)
        (.pair (fwaW .v1)
          (.pair (fwaIsDel .v1)
            (.pair (fwaCi? .v1)
              (.pair (fwaPk .v1)
                (.pair (fwaPq' .v1) .v0)))))))
    (ReductionDsl.Env.cons (t := .opt (smRrFullT ℓ Pt))
      (res.map (smRrEnc (ℓ := ℓ) (Pt := Pt) fun (pub, m) => (lpubV pub, m))) ρ0)
    sC.base Q w isDel ci? Tpk pq' res rfl
    hbnd.base.trans_le hbnd.base.chall_le hbnd.base.comp_le (hextra.2.1 Q)
  rw [hans, pure_bind, eval_ret, pure_bind]
  clear hans
  let AOps := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
  rcases res with _ | ⟨⟩ | ⟨t', i', pm'⟩
  · let ansOut := onAnswerPure qep Q w isDel ci? Tpk pq' none sC.base
    let ρ2 := ReductionDsl.Env.cons (t := .prod (.opt (recvResultT (ℓ := ℓ) (Pt := Pt))) (simBaseT ℓ Pt))
      (ansOut.1.map recvResultEnc, simBaseEnc ansOut.2)
      (ReductionDsl.Env.cons (t := .opt (smRrFullT ℓ Pt)) none ρ0)
    have hsc := scMk_scKept_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (.snd .v0) (fwaSC .v2) ρ2 ansOut.2 sC rfl rfl
    change pure (Prod.map (Option.map recvResultDec) simFullDec
      (ansOut.1.map recvResultEnc,
        (scMk (O' := AOps) (.snd .v0) (scKept (fwaSC .v2))
          (scSent (fwaSC .v2)) (scSnaps (fwaSC .v2))).eval ρ2)) = _
    rw [hsc]
    change pure ((ansOut.1.map recvResultEnc).map recvResultDec, simFullDec (simFullEnc _)) = _
    rw [option_map_recvResultDec_enc, simFullDec_simFullEnc]; rfl
  · let ansOut := onAnswerPure qep Q w isDel ci? Tpk pq' (some .rejected) sC.base
    let ρ2 := ReductionDsl.Env.cons (t := .prod (.opt (recvResultT (ℓ := ℓ) (Pt := Pt))) (simBaseT ℓ Pt))
      (ansOut.1.map recvResultEnc, simBaseEnc ansOut.2)
      (ReductionDsl.Env.cons (t := .opt (smRrFullT ℓ Pt)) (some (.inl ())) ρ0)
    have hsc := scMk_scKept_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (.snd .v0) (fwaSC .v2) ρ2 ansOut.2 sC rfl rfl
    change pure (Prod.map (Option.map recvResultDec) simFullDec
      (ansOut.1.map recvResultEnc,
        (scMk (O' := AOps) (.snd .v0) (scKept (fwaSC .v2))
          (scSent (fwaSC .v2)) (scSnaps (fwaSC .v2))).eval ρ2)) = _
    rw [hsc]
    change pure ((ansOut.1.map recvResultEnc).map recvResultDec, simFullDec (simFullEnc _)) = _
    rw [option_map_recvResultDec_enc, simFullDec_simFullEnc]; rfl
  · let ansOut := onAnswerPure qep Q w isDel ci? Tpk pq' (some (.accepted t' i' pm')) sC.base
    let ρ2 := ReductionDsl.Env.cons (t := .prod (.opt (recvResultT (ℓ := ℓ) (Pt := Pt))) (simBaseT ℓ Pt))
      (ansOut.1.map recvResultEnc, simBaseEnc ansOut.2)
      (ReductionDsl.Env.cons (t := .opt (smRrFullT ℓ Pt))
        ((some (CryptoGames.SM.RecvResult.accepted t' i' pm')).map
          (smRrEnc (ℓ := ℓ) (Pt := Pt) fun (pub, m) => (lpubV pub, m))) ρ0)
    have hsc := scMk_updateKeptRecv_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) idA idB T
      (.snd .v0) (fwaSC .v2) (fwaQ .v2) (fwaC' .v2) ρ2 ansOut.2 sC Q c' rfl rfl rfl rfl
    change pure (Prod.map (Option.map recvResultDec) simFullDec
      (ansOut.1.map recvResultEnc,
        (scMk (O' := AOps) (.snd .v0)
          (scUpdateKeptRecv idA idB T (fwaSC .v2) (fwaQ .v2) (fwaC' .v2))
          (scSent (fwaSC .v2)) (scSnaps (fwaSC .v2))).eval ρ2)) = _
    rw [hsc]
    change pure ((ansOut.1.map recvResultEnc).map recvResultDec, simFullDec (simFullEnc _)) = _
    rw [option_map_recvResultDec_enc, simFullDec_simFullEnc]; rfl

theorem semFwdHookAtomicC_eval (idA idB : IdentityKey) (L qep B_cap T Kc : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (inpE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (fwdHookInpT ℓ Pt))
    (ρ : Env Γ)
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ)
    (Q : Party) (w : Bytes) (isDel : Bool) (ci? : Option ℕ) (Tpk : PublicKey) (pq' : Bytes)
    (honestC : Option (SimFig8C Pt)) (c' : SimFig8C Pt)
    (hinp : inpE.eval ρ =
      (simFullEnc sC, (partyToBool Q, (w, (isDel,
        (ci?, (Tpk, (pq', (honestC.map fig8CtV, fig8CtV c')))))))))
    (hbnd : SimCStateBounded L sC)
    (hextra : SanSnapExtra C K sC) :
    (Prod.map (Option.map recvResultDec) simFullDec <$>
      (semFwdHookAtomicC (Pt := Pt) (ℓ := ℓ) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
        idA idB L qep B_cap T Kc inpE).eval ρ) =
    (Prod.map id Prod.fst <$>
      semFwdHookS (paramsV1 C K idA idB) Dh encPt encT lam T Kc
        (fig8IdSemHook (PQC := BitVec 512) none)
        qep B_cap sC () Q w isDel ci? Tpk pq' honestC c') := by
  unfold semFwdHookAtomicC semFwdHookS
  rw [eval_bind_ret, hinp, eval_caseOpt]
  have hfwhH :
      (fwhHonest (O' := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) .v0).eval
        (ReductionDsl.Env.cons (t := fwdHookInpT ℓ Pt)
          (simFullEnc sC, (partyToBool Q, (w, (isDel,
            (ci?, (Tpk, (pq', (honestC.map fig8CtV, fig8CtV c')))))))) ρ) =
      honestC.map fig8CtV := rfl
  rw [hfwhH]
  rcases honestC with _ | c
  · dsimp only [Option.map]
    exact semFwdAnswerAtomicC_eval idA idB L qep T (fwhToAnsInp .v0) _
      sC Q w isDel ci? Tpk pq' c' rfl hbnd hextra
  · dsimp only [Option.map]
    let v0 : (fwdHookInpT ℓ Pt).denote :=
      (simFullEnc sC, (partyToBool Q, (w, (isDel,
        (ci?, (Tpk, (pq', (some (fig8CtV c), fig8CtV c'))))))))
    let ρ0 := ReductionDsl.Env.cons (t := fwdHookInpT ℓ Pt) v0 ρ
    let ρ1 := ReductionDsl.Env.cons (t := fig8CtT (ℓ := ℓ) (Pt := Pt)) (fig8CtV c) ρ0
    rw [eval_ite]
    let AOps := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
    have heqC := eqFig8CAtomicE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) .v0 (fwhC' .v1) ρ1 c c' rfl rfl
    have hsafe := mSafeInjE_eval (O' := AOps)
      (ssMir (scBase (fwhSC .v1))) ρ1 sC.base.mir rfl
    have hcond_eq :
        (ReductionDsl.Expr.and (O := AOps) (.not (eqFig8CAtomicE .v0 (fwhC' .v1)))
          (.and (fwhIsDel .v1) (.not (mSafeInjE (ssMir (scBase (fwhSC .v1))))))).eval ρ1 =
        (!(decide (c = c')) && (isDel && !(sC.base.mir.safeInj 3))) := by
      change (!(eqFig8CAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) .v0 (fwhC' .v1)).eval ρ1 &&
        (isDel && !(mSafeInjE (O' := AOps) (ssMir (scBase (fwhSC .v1)))).eval ρ1)) = _
      rw [heqC, hsafe]
    rw [hcond_eq]
    by_cases hcond : (!(decide (c = c')) && (isDel && !(sC.base.mir.safeInj 3))) = true
    · simp only [hcond, ↓reduceIte]
      rw [eval_bind]
      have hevCK := evalCKSAtomicC_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) idA idB L B_cap T Kc
        (.pair (fwhSC .v1) (.pair (fwhQ .v1) (.pair (fwhW .v1) (.pair .v0 (fwhC' .v1)))))
        ρ1 sC Q w c c' rfl hbnd.sent_le hbnd.snaps_le hextra.2.2.1
      rw [hevCK]
      rcases hev : evalCKS (paramsV1 C K idA idB) Dh encPt encT lam T Kc B_cap sC Q w c c' with _ | r
      · dsimp only [Option.map, fig8IdSemHook]
        rw [pure_bind, eval_caseOpt_v0_none, pure_bind, map_pure]
        exact eval_ret_rejected (fwhSC .v2) _ sC rfl
      · dsimp only [Option.map]
        rw [pure_bind, eval_caseOpt_v0_some]
        exact semResyncAtomicC_eval idA idB L qep T _
          (ReductionDsl.Env.cons (t := .opt (kDecOutT ℓ Pt)) (r.map kDecOutV)
            (ReductionDsl.Env.cons (t := .opt (.opt (kDecOutT ℓ Pt))) (some (r.map kDecOutV)) ρ1))
          sC Q w ci? Tpk pq' c r rfl hbnd hextra
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte]
      exact semFwdAnswerAtomicC_eval idA idB L qep T (fwhToAnsInp .v1) ρ1
        sC Q w isDel ci? Tpk pq' c' rfl hbnd hextra

theorem recvSameBranchAtomicC_eval (idA idB : IdentityKey) (L qep B_cap T Kc : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (inpE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (recvSameInpT ℓ Pt))
    (ρ : Env Γ)
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ)
    (Q : Party) (w : Bytes) (isDel : Bool)
    (pq' : Bytes) (i : ℕ) (pk : PublicKey) (T? : Option Pt)
    (lct : ℕ × LibsignalCiphertextWithSalt32)
    (honestC : Option (SimFig8C Pt)) (ci : ℕ)
    (hinp : inpE.eval ρ =
      (simFullEnc sC, (partyToBool Q, (w, (isDel,
        (parseOutV (pq', (i, (pk, (T?, lct)))), (honestC.map fig8CtV, ci)))))))
    (hbnd : SimCStateBounded L sC)
    (hextra : SanSnapExtra C K sC) :
    (Prod.map (Option.map recvResultDec) simFullDec <$>
      (recvSameBranchAtomicC (Pt := Pt) (ℓ := ℓ) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
        idA idB L qep B_cap T Kc inpE).eval ρ) =
    semRecvSameBranch C K idA idB Dh encPt encT lam qep B_cap T Kc
      sC Q w isDel pq' i pk T? lct honestC ci := by
  unfold recvSameBranchAtomicC semRecvSameBranch
  rw [eval_bind_ret, hinp, eval_ite]
  set v0 : (recvSameInpT ℓ Pt).denote :=
    (simFullEnc sC, (partyToBool Q, (w, (isDel,
      (parseOutV (pq', (i, (pk, (T?, lct)))), (honestC.map fig8CtV, ci))))))
  set ρ0 := ReductionDsl.Env.cons (t := recvSameInpT ℓ Pt) v0 ρ
  set g := (sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩
  have hch_ab :
      (ssChains (scBase (rsmSC (O' := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) .v0))).eval ρ0 =
      ((sC.base.chains .A).map ghostChainEnc, (sC.base.chains .B).map ghostChainEnc) := rfl
  have hqEnc : (rsmQ (O' := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) .v0).eval ρ0 = partyEnc Q :=
    partyToBool_eq_partyEnc Q
  have hpGet :
      (pGet (ssChains (scBase (rsmSC (O' := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) .v0)))
        (rsmQ .v0)).eval ρ0 = (sC.base.chains Q).map ghostChainEnc :=
    pGet_eval (ssChains (scBase (rsmSC .v0))) (rsmQ .v0) ρ0
      (fun R => (sC.base.chains R).map ghostChainEnc) Q hch_ab hqEnc
  have hg := eval_getChainDE
    (O' := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
    (pGet (ssChains (scBase (rsmSC .v0))) (rsmQ .v0)) (rsmCi .v0) ρ0
    (sC.base.chains Q) hpGet (hextra.2.1 Q).1
  have hrejE := eval_ghostRejectsE
    (O' := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
    (getChainDE (pGet (ssChains (scBase (rsmSC .v0))) (rsmQ .v0)) (rsmCi .v0))
    (poI (rsmParsed .v0)) ρ0 g hg (getD_skipped_le (sC.base.chains Q) ci (hextra.2.1 Q).2)
  rw [hrejE]
  change (Prod.map (Option.map recvResultDec) simFullDec <$>
    (if g.rejects i then _ else _)) = _
  by_cases hrej : g.rejects i = true
  · simp only [hrej, ↓reduceIte]
    exact eval_ret_rejected (rsmSC .v0) ρ0 sC rfl
  · simp only [hrej, Bool.false_eq_true, ↓reduceIte]
    let AOps := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
    have hgep :
        (ReductionDsl.Expr.fst (.snd (getChainDE (O' := AOps)
          (pGet (ssChains (scBase (rsmSC .v0))) (rsmQ .v0)) (rsmCi .v0)))).eval ρ0 = g.epoch := by
      change ((getChainDE (O' := AOps)
        (pGet (ssChains (scBase (rsmSC .v0))) (rsmQ .v0)) (rsmCi .v0)).eval ρ0).2.1 = g.epoch
      rw [hg]
      rfl
    let c' : SimFig8C Pt :=
      match honestC with
      | some c => if c.2.2.2 = lct.2.2 then c else ((g.epoch, T?), lct)
      | none => ((g.epoch, T?), lct)
    have hmkC := mkCE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (rsmHonest .v0)
      (.fst (.snd (getChainDE (pGet (ssChains (scBase (rsmSC .v0))) (rsmQ .v0)) (rsmCi .v0))))
      (poT? (rsmParsed .v0)) (poLct (rsmParsed .v0))
      ρ0 honestC g.epoch T? lct rfl hgep rfl rfl
    refine semFwdHookAtomicC_eval (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT)
      (lam := lam) idA idB L qep B_cap T Kc _ ρ0
      sC Q w isDel (some ci) pk pq' honestC c' ?_ hbnd hextra
    change (simFullEnc sC, (partyToBool Q, (w, (isDel, (some ci, (pk, (pq',
      (honestC.map fig8CtV,
        (mkCE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT)
          (lam := lam) (rsmHonest .v0)
          (.fst (.snd (getChainDE (pGet (ssChains (scBase (rsmSC .v0))) (rsmQ .v0)) (rsmCi .v0))))
          (poT? (rsmParsed .v0)) (poLct (rsmParsed .v0))).eval ρ0)))))))) = _
    rw [hmkC]
    rcases honestC with _ | c
    · rfl
    · by_cases hs : c.2.2.2 = lct.2.2 <;> simp only [c', hs, ↓reduceIte]

/-- `.eval` correctness of the parameterized full receive handler `recvHookOfNewAtomicC` against
`semRecvHookS` (`fig8IdSemHook none`). -/
theorem recvHookOfNewAtomicC_eval (idA idB : IdentityKey) (L qep B_cap T Kc : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (sCE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (simFullT ℓ Pt))
    (qBE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .bool)
    (wE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (B 32))
    (isDelE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .bool)
    (newBranchC : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      (recvNewSiteCtx ℓ Pt (.prod (simFullT ℓ Pt) (.prod .bool (.prod (B 32) .bool)) :: Γ))
      (recvOutT ℓ Pt))
    (hnew : ∀ (ρ' : Env (recvNewSiteCtx ℓ Pt
        (.prod (simFullT ℓ Pt) (.prod .bool (.prod (B 32) .bool)) :: Γ)))
        (sC₀ : LibsignalToModularSchemeSimState Bytes Pt ℓ)
        (Q₀ : Party) (w₀ : Bytes) (isDel₀ : Bool)
        (pq'₀ : Bytes) (i₀ : ℕ) (pk₀ : PublicKey) (T?₀ : Option Pt)
        (lct₀ : ℕ × LibsignalCiphertextWithSalt32) (honestC₀ : Option (SimFig8C Pt)),
      ρ'.get .zero =
        (simFullEnc sC₀, (partyToBool Q₀, (w₀, (isDel₀,
          (parseOutV (pq'₀, (i₀, (pk₀, (T?₀, lct₀)))), honestC₀.map fig8CtV))))) →
      SimCStateBounded L sC₀ →
      SanSnapExtra C K sC₀ →
      (Prod.map (Option.map recvResultDec) simFullDec <$> newBranchC.eval ρ') =
        semRecvNewBranch C K idA idB Dh encPt encT lam qep B_cap T Kc
          sC₀ Q₀ w₀ isDel₀ pq'₀ i₀ pk₀ T?₀ lct₀ honestC₀)
    (ρ : Env Γ)
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ)
    (Q : Party) (w : Bytes) (isDel : Bool)
    (hsC : sCE.eval ρ = simFullEnc sC)
    (hqB : qBE.eval ρ = partyToBool Q)
    (hw : wE.eval ρ = w)
    (hisDel : isDelE.eval ρ = isDel)
    (hbnd : SimCStateBounded L sC)
    (hextra : SanSnapExtra C K sC) :
    (Prod.map (Option.map recvResultDec) simFullDec <$>
      (recvHookOfNewAtomicC (Pt := Pt) (ℓ := ℓ) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
        idA idB L qep B_cap T Kc sCE qBE wE isDelE newBranchC).eval ρ) =
    (Prod.map id Prod.fst <$>
      semRecvHookS (paramsV1 C K idA idB) Dh encPt encT decT lam T Kc
        (fig8IdSemHook (PQC := BitVec 512) none)
        qep B_cap sC () Q w isDel) := by
  unfold recvHookOfNewAtomicC semRecvHookS
  have hpair :
      (ReductionDsl.Expr.pair sCE (.pair qBE (.pair wE isDelE))).eval ρ =
      (simFullEnc sC, (partyToBool Q, (w, isDel))) := by
    simp [ReductionDsl.Expr.eval, hsC, hqB, hw, hisDel]
  rw [eval_bind_ret, hpair, eval_ite]
  set v0 : (ReductionDsl.Ty.prod (simFullT ℓ Pt) (.prod .bool (.prod (B 32) .bool))).denote :=
    (simFullEnc sC, (partyToBool Q, (w, isDel)))
  set ρ0 := ReductionDsl.Env.cons (t := .prod (simFullT ℓ Pt) (.prod .bool (.prod (B 32) .bool))) v0 ρ
  have href := recvRefuseE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) L
    (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))
    ρ0 sC Q w isDel rfl rfl rfl rfl hbnd.base.trans_le
  have hcodec : (paramsV1 C K idA idB).codec = protoSignalCodec := rfl
  rw [href, hcodec]
  set refuse := sC.base.stopped || sC.base.mir.win ||
    (isDel && (sC.base.mir.inTransit Q.other w).isNone) ||
    (!isDel && ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
      !(ratchetKeyAdmissible protoSignalCodec decT encT w)))
  by_cases hrefB : refuse = true
  · simp only [hrefB, ↓reduceIte, map_pure]
    exact eval_ret_none (.fst .v0) ρ0 sC rfl
  · simp only [hrefB, Bool.false_eq_true, ↓reduceIte]
    rw [eval_bind]
    have hpq_ab :
        (ssPq (scBase (O' := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (.fst .v0))).eval ρ0 =
        (sC.base.pq .A, sC.base.pq .B) := rfl
    have hqEnc0 :
        (ReductionDsl.Expr.fst (.snd (ReductionDsl.Expr.v0 (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)))).eval ρ0 =
        partyEnc Q := partyToBool_eq_partyEnc Q
    have hpqGet :
        (pGet (ssPq (scBase (O' := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (.fst .v0)))
          (.fst (.snd .v0))).eval ρ0 = sC.base.pq Q :=
      pGet_eval (ssPq (scBase (.fst .v0))) (.fst (.snd .v0)) ρ0 sC.base.pq Q hpq_ab hqEnc0
    have hparse := parseRecvAtomicC_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (fig8SmIface ℓ Pt) idA idB (2 ^ 32)
      (.fst (.snd .v0)) (pGet (ssPq (scBase (.fst .v0))) (.fst (.snd .v0)))
      (.fst (.snd (.snd .v0))) ρ0 (partyEnc Q) (sC.base.pq Q) w
      hqEnc0 hpqGet rfl (hextra.1 Q)
    rw [hparse]
    rcases hp : simParseRecvC (paramsV1 C K idA idB) decT (2 ^ 32) (partyEnc Q) (sC.base.pq Q) w
      with _ | ⟨pq', i, pk, T?, lct⟩
    · rw [Option.map_none, pure_bind, eval_caseOpt_v0_none, map_pure]
      exact eval_ret_rejected (.fst .v1) (ReductionDsl.Env.cons (t := .opt (parseOutT ℓ Pt)) none ρ0) sC rfl
    · rw [Option.map_some, pure_bind, eval_caseOpt_v0_some]
      let pv := parseOutV (ℓ := ℓ) (Pt := Pt) (pq', (i, (pk, (T?, lct))))
      let ρ2 := ReductionDsl.Env.cons (t := parseOutT ℓ Pt) pv
        (ReductionDsl.Env.cons (t := .opt (parseOutT ℓ Pt)) (some pv) ρ0)
      have hhon := honestFindE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) L
        (.fst .v2) (.fst (.snd .v2)) (.fst (.snd (.snd .v2)))
        ρ2 sC Q w rfl rfl rfl hbnd.base.honest_le
      rw [eval_bind_ret, hhon, eval_caseOpt]
      let honestC := (sC.base.honest.find? fun wc =>
        wc.1 == w && CryptoGames.Party.senderOf wc.2.1.1 == Q.other).map (·.2)
      let ρ3 := ReductionDsl.Env.cons (t := .opt (fig8CtT (ℓ := ℓ) (Pt := Pt))) (honestC.map fig8CtV) ρ2
      have hch_ab3 :
          (ssChains (scBase (O' := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (.fst .v3))).eval ρ3 =
          ((sC.base.chains .A).map ghostChainEnc, (sC.base.chains .B).map ghostChainEnc) := rfl
      have hqEnc3 :
          (ReductionDsl.Expr.fst (.snd (ReductionDsl.Expr.v3 (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)))).eval ρ3 =
          partyEnc Q := partyToBool_eq_partyEnc Q
      have hpGet3 :
          (pGet (ssChains (scBase (O' := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (.fst .v3)))
            (.fst (.snd .v3))).eval ρ3 = (sC.base.chains Q).map ghostChainEnc :=
        pGet_eval (ssChains (scBase (.fst .v3))) (.fst (.snd .v3)) ρ3
          (fun R => (sC.base.chains R).map ghostChainEnc) Q hch_ab3 hqEnc3
      have hfci := eval_findChainIdxE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam)
        (pGet (ssChains (scBase (.fst .v3))) (.fst (.snd .v3))) (poPk .v1)
        ρ3 (sC.base.chains Q) hpGet3 (hextra.2.1 Q).1
      rw [hfci]
      have hpk3 :
          (some ((poPk (O' := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) .v1).eval ρ3) :
            Option PublicKey) = some pk := rfl
      rw [hpk3]
      rcases hci : (sC.base.chains Q).findIdx? (fun g => g.key == some pk) with _ | ci
      · simp only [hci]
        rw [eval_bind_ret]
        refine Trans.trans (hnew _ sC Q w isDel pq' i pk T? lct honestC rfl hbnd hextra) ?_
        unfold semRecvNewBranch
        dsimp only [honestC]
        by_cases h1 : (((sC.base.honest.find? fun wc =>
              wc.1 == w && CryptoGames.Party.senderOf wc.2.1.1 == Q.other).map (·.2) |>.map
              fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true &&
            ((sC.base.honest.find? fun wc =>
              wc.1 == w && CryptoGames.Party.senderOf wc.2.1.1 == Q.other).map (·.2) |>.map
              fun c => decide (c.2.2.2 = lct.2.2)) == some true) = true
        · simp only [h1, ↓reduceIte, map_pure]; rfl
        · simp only [h1, Bool.false_eq_true, ↓reduceIte]
          by_cases h2 : (T? == some 0) = true
          · simp only [h2, ↓reduceIte, map_pure]; rfl
          · simp only [h2, Bool.false_eq_true, ↓reduceIte]
            by_cases h3 : (inReceiveOnlyEpoch sC.base.mir Q || decide (25000 < i - 1) || decide (2 ^ 32 ≤ i)) = true
            · simp only [h3, ↓reduceIte, map_pure]; rfl
            · simp only [h3, Bool.false_eq_true, ↓reduceIte]
              rcases T? with _ | T₀
              · simp only [map_pure]; rfl
              · by_cases h4 : (((sC.base.honest.find? fun wc =>
                    wc.1 == w && CryptoGames.Party.senderOf wc.2.1.1 == Q.other).map (·.2) |>.map
                    fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true) = true
                · simp only [h4, ↓reduceIte]
                · simp only [h4, Bool.false_eq_true, ↓reduceIte]
                  rcases (sC.base.honest.find? fun wc =>
                    wc.1 == w && CryptoGames.Party.senderOf wc.2.1.1 == Q.other) with _ | wc <;> rfl
      · simp only [hci]
        refine Trans.trans
          (recvSameBranchAtomicC_eval (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT)
            (lam := lam) idA idB L qep B_cap T Kc _ _
            sC Q w isDel pq' i pk T? lct honestC ci rfl hbnd hextra) ?_
        unfold semRecvSameBranch
        dsimp only [honestC]
        by_cases hrej : ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects i = true
        · simp only [hrej, ↓reduceIte, map_pure]; rfl
        · simp only [hrej, Bool.false_eq_true, ↓reduceIte]
          rcases (sC.base.honest.find? fun wc =>
            wc.1 == w && CryptoGames.Party.senderOf wc.2.1.1 == Q.other) with _ | wc <;> rfl

omit [SampleableType Pt] in
theorem simFig8OracleSan_deliver_eq (idA idB : IdentityKey) (qep B_cap T Kc Bsk : ℕ)
    (Q : Party) (w : Bytes) (s_raw : (simFullT ℓ Pt).denote) :
    ((simFig8OracleSan (paramsV1 C K idA idB) Dh encPt encT decT lam qep B_cap T Kc Bsk
      (.inr (.inl (.inl (.inr (Q, w)))))).run (simFullDec s_raw)) =
    (Prod.map id Prod.fst <$>
      semRecvHookS (paramsV1 C K idA idB) Dh encPt encT decT lam T Kc
        (fig8IdSemHook (PQC := BitVec 512) none)
        qep B_cap (simFullDec s_raw) () Q w true) := by
  unfold simFig8OracleSan semHandleHookDedupS
  dsimp only [StateT.run, StateT.mk, fig8IdSemHook]
  simp only [pure_bind, map_eq_bind_pure_comp, Function.comp_def, bind_assoc]
  refine bind_congr fun ⟨_, _, _⟩ => rfl

omit [SampleableType Pt] in
theorem simFig8OracleSan_inject_eq (idA idB : IdentityKey) (qep B_cap T Kc Bsk : ℕ)
    (Q : Party) (w : Bytes) (s_raw : (simFullT ℓ Pt).denote) :
    ((simFig8OracleSan (paramsV1 C K idA idB) Dh encPt encT decT lam qep B_cap T Kc Bsk
      (.inr (.inl (.inr (Q, w))))).run (simFullDec s_raw)) =
    (Prod.map id Prod.fst <$>
      semRecvHookS (paramsV1 C K idA idB) Dh encPt encT decT lam T Kc
        (fig8IdSemHook (PQC := BitVec 512) none)
        qep B_cap (simFullDec s_raw) () Q w false) := rfl

end EvalTheorems

/-- Specification for the concrete atomic `Comp` implementing `semFwdHookS` at
`(L, B, T, Kc) = (q, 2 ^ 32 + q + 2, 50000 * q, 25001 * q + 25000)`. -/
structure SimFig8FwdHookSpec (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) where
  comp : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
    [fwdHookInpT ℓ Pt] (recvOutT ℓ Pt)
  hq : comp.queries (fun _ => 1) (fun _ => 0) ≤ 1
  hcost : ℓ < 10 ^ 6 →
    comp.cost ≤ 24000005 + 20000000 * q + 128 * bits (qep + 1)
  hdesc : ℓ < 10 ^ 6 →
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) comp ≤
      250010 + 256 * bits (ratchetCostBudget q (qep + 1) + (qep + 1))
  heval : ℓ < 10 ^ 6 →
    ∀ sC Q w isDel ci? pk pq' honestC c',
      SimCStateBounded q sC →
      SanSnapExtra C K sC →
      (Prod.map (Option.map recvResultDec) simFullDec <$>
        comp.eval (.cons (simFullEnc sC, (partyToBool Q, (w, (isDel,
          (ci?, (pk, (pq', (honestC.map fig8CtV, fig8CtV c')))))))) .nil)) =
      (Prod.map id Prod.fst <$>
        semFwdHookS (paramsV1 C K idA idB) Dh encPt encT lam
          (50000 * q) (25001 * q + 25000) (fig8IdSemHook (PQC := BitVec 512) none)
          qep (2 ^ 32 + q + 2) sC () Q w isDel ci? pk pq' honestC c')

theorem simFig8FwdHookSpec_cost_aux {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) (_hℓ : ℓ < 10 ^ 6) :
    (semFwdHookAtomicC (Pt := Pt) (ℓ := ℓ) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q qep
      (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (Γ := [fwdHookInpT ℓ Pt]) .v0).cost ≤
      24000005 + 20000000 * q + 128 * bits (qep + 1) := by
  have h := semFwdHookAtomicC_cost (Pt := Pt) (ℓ := ℓ) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q qep
    (Γ := [fwdHookInpT ℓ Pt]) .v0 _hℓ
  simp only [ReductionDsl.Expr.cost, ReductionDsl.Expr.v0] at h
  dsimp only [ReductionDsl.Expr.v0]
  omega

def simFig8FwdHookSpec {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) :
    SimFig8FwdHookSpec Pt ℓ C K idA idB Dh encPt encT decT lam qep q where
  comp := semFwdHookAtomicC idA idB q qep (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) .v0
  hq := semFwdHookAtomicC_queries idA idB q qep .v0
  hcost hℓ := simFig8FwdHookSpec_cost_aux ℓ C K idA idB Dh encPt encT decT lam qep q hℓ
  hdesc hℓ := by
    have h := semFwdHookAtomicC_descBits_le (Pt := Pt) (ℓ := ℓ) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q qep
      (Γ := [fwdHookInpT ℓ Pt]) .v0 hℓ
    simp only [atomicExprDescBits, ReductionDsl.Expr.v0,
      Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost.varIdx,
      Computational.Proofs.Game.PromotedCostedReds.SimFig8State.bits_zero] at h
    dsimp only [ReductionDsl.Expr.v0]
    omega
  heval _ sC Q w isDel ci? pk pq' honestC c' hbnd hextra :=
    semFwdHookAtomicC_eval idA idB q qep (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) .v0 _
      sC Q w isDel ci? pk pq' honestC c' rfl hbnd hextra

/-- Specification for the concrete atomic `Comp` implementing the existing/same-epoch
(`findIdx? = some ci`) receive sub-branch `semRecvSameBranch` at
`(L, B, T, Kc) = (q, 2 ^ 32 + q + 2, 50000 * q, 25001 * q + 25000)`. -/
structure SimFig8RecvSameSpec (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) where
  comp : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
    [recvSameInpT ℓ Pt] (recvOutT ℓ Pt)
  hq : comp.queries (fun _ => 1) (fun _ => 0) ≤ 1
  hcost : ℓ < 10 ^ 6 →
    comp.cost ≤ 25000005 + 20000000 * q + 128 * bits (qep + 1)
  hdesc : ℓ < 10 ^ 6 →
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) comp ≤
      260010 + 256 * bits (ratchetCostBudget q (qep + 1) + (qep + 1))
  heval : ℓ < 10 ^ 6 →
    ∀ sC Q w isDel pq' i pk T? lct honestC ci,
      SimCStateBounded q sC →
      SanSnapExtra C K sC →
      (Prod.map (Option.map recvResultDec) simFullDec <$>
        comp.eval (.cons (simFullEnc sC, (partyToBool Q, (w, (isDel,
          (parseOutV (pq', (i, (pk, (T?, lct)))),
            (honestC.map fig8CtV, ci)))))) .nil)) =
      semRecvSameBranch C K idA idB Dh encPt encT lam qep
        (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000)
        sC Q w isDel pq' i pk T? lct honestC ci

theorem simFig8RecvSameSpec_cost_aux {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) (_hℓ : ℓ < 10 ^ 6) :
    (recvSameBranchAtomicC (Pt := Pt) (ℓ := ℓ) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q qep
      (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (Γ := [recvSameInpT ℓ Pt]) .v0).cost ≤
      25000005 + 20000000 * q + 128 * bits (qep + 1) := by
  have h := recvSameBranchAtomicC_cost (Pt := Pt) (ℓ := ℓ) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q qep
    (Γ := [recvSameInpT ℓ Pt]) .v0 _hℓ
  simp only [ReductionDsl.Expr.cost, ReductionDsl.Expr.v0] at h
  dsimp only [ReductionDsl.Expr.v0]
  omega

def simFig8RecvSameSpec {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) :
    SimFig8RecvSameSpec Pt ℓ C K idA idB Dh encPt encT decT lam qep q where
  comp := recvSameBranchAtomicC idA idB q qep (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) .v0
  hq := recvSameBranchAtomicC_queries idA idB q qep .v0
  hcost hℓ := simFig8RecvSameSpec_cost_aux ℓ C K idA idB Dh encPt encT decT lam qep q hℓ
  hdesc hℓ := by
    have h := recvSameBranchAtomicC_descBits_le (Pt := Pt) (ℓ := ℓ) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q qep
      (Γ := [recvSameInpT ℓ Pt]) .v0 hℓ
    simp only [atomicExprDescBits, ReductionDsl.Expr.v0,
      Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost.varIdx,
      Computational.Proofs.Game.PromotedCostedReds.SimFig8State.bits_zero] at h
    dsimp only [ReductionDsl.Expr.v0]
    omega
  heval _ sC Q w isDel pq' i pk T? lct honestC ci hbnd hextra :=
    recvSameBranchAtomicC_eval idA idB q qep (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) .v0 _
      sC Q w isDel pq' i pk T? lct honestC ci rfl hbnd hextra

end

end Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvSame

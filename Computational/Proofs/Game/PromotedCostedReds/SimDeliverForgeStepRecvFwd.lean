/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStepRecvFwdCost
public import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStepRecvFwdSkip

/-!
# Receive Pipeline Equivalence for `SimDeliverForge`

Proves semantic `.eval` equivalence for the atomic `SimDeliverForge` receive pipeline `dfRecvHookC`
against `semRecvHookS` with `deliverForgeSemHook`.
-/

@[expose] public section

set_option autoImplicit false

open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStepRecvFwdCost (dfFwdEvictInT dfFwdInT dfRecvInT dfRecvNewInT dfRecvOutDec dfRecvOutT dfRecvSameInT dfStepDec dfStepEnc dfStepT fwdAnswerC fwdEvictC fwdEvictedE fwdHookC fwdInTE fwdNoneOutE fwdOnAcceptC fwdRecvDispatchC fwdRecvDispatchC_cost fwdRecvDispatchC_descBits_le fwdRecvDispatchC_queries fwdRecvNewC fwdRecvNewC_cost fwdRecvNewC_descBits_le fwdRecvNewC_queries fwdRecvSameC fwdRecvSameC_cost fwdRecvSameC_descBits_le fwdRecvSameC_queries fwdRefuseE fwdRejOutE fwdSaltEqE fwdScAmbE)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStepRecvFwdSkip (dfStepDec_dfStepEnc dfStepEnc_dfStepDec fwdEvalCKSC_eval fwdEvictedE_eval fwdHonestCE_eval fwdInTE_eval fwdMkCE_eval fwdNewGuardRejectE_eval fwdNoneOutE_eval fwdOnAcceptC_eval fwdProbeC_eval fwdRefuseE_eval fwdRejOutE_eval fwdResyncC_eval fwdSaltEqE_eval fwdScAcceptUpdateE_eval fwdScAmbE_eval)
open ReductionDsl (B Comp Env Expr PK PlainT PtT Ty atomicSessionOps atomicSig bits boolToParty fig8CtOfV fig8CtT fig8CtV fig8SmIfaceDF lpubT lpubV smRrDec smRrEnc smRrT)

namespace Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStepRecvFwd

open OracleSpec OracleComp
open _root_.ReductionDsl (Ty Expr Comp Env SMTagDF bits atomicSig atomicSessionOps fig8SmIfaceDF
  B PK PlainT PtT lpubT lpubV lpubOfV lctT lctV fig8CtT fig8CtV fig8CtOfV
  smRrT smRrEnc smRrDec partyToBool boolToParty)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32)
open CryptoGames.Ratchet.LibsignalSim (Fig8C SimFig8C GhostChain SimState SimCStateBounded
  inReceiveOnlyEpoch simParseRecvC onAcceptPure onAnswerPure deliverForgeSemHook)
open CryptoGames.Ratchet.LibsignalSimC (Kept LibsignalToModularSchemeSimState)
open CryptoGames.SM (RecvResult partyEnc partyDec pGet)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalSession (ratchetCostBudget)
open CryptoVerification.E2E (Bytes paramsV1)
open Computational.Proofs.Game.PromotedCostedReds.SanOracleCore
  (figS fsS evalCKS semFwdAnswerHookS semResyncHookS semFwdEvictHookS semFwdHookS semRecvHookS)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanCoupling (SanSnapExtra)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost
  (simBaseT simFullT simBaseEnc simBaseDec simFullEnc simFullDec ghostChainEnc)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8State
  (scBase ssMir ssPq ssChains mEpoch mSafeInjE mSafeInjE_eval
   getChainDE eval_getChainDE ghostRejectsE eval_ghostRejectsE
   findChainIdxE eval_findChainIdxE)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8Crypto
  (kDecOutT kDecOutV parseOutT parseOutV isZeroPtOptAtomicE isZeroPtOptAtomicE_eval
   parseRecvAtomicC parseRecvAtomicC_eval)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept
  (eqFig8CAtomicE eqFig8CAtomicE_eval defaultMcAtomicE defaultMcAtomicE_eval)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost
  (atomicSessionOpDescBits atomicCompDescBits)

noncomputable section

section RecvFwdProofs

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
  (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
  (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
local notation "IDF" => fig8SmIfaceDF ℓ Pt

def semRecvNewBranchDF (qep B T Kc : ℕ)
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ) (ex : List (Fig8C Pt))
    (Q : Party) (w : Bytes) (isDel : Bool)
    (pq' : Bytes) (i : ℕ) (pk : PublicKey) (T? : Option Pt)
    (lct : ℕ × LibsignalCiphertextWithSalt32)
    (honestC : Option (SimFig8C Pt)) :
    OracleComp
      (unifSpec + CryptoGames.SM.specDF (CryptoGames.Ratchet.LibsignalSim.SimFig8St Pt)
        (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt))
      (Option (RecvResult (Plain ℓ)) ×
        (LibsignalToModularSchemeSimState Bytes Pt ℓ × List (Fig8C Pt))) :=
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
    pure (some .rejected, (sC, ex))
  else if T? == some 0 then
    pure (some .rejected, (sC, ex))
  else if inReceiveOnlyEpoch sC.base.mir Q || decide (25000 < i - 1) || decide (2 ^ 32 ≤ i) then
    pure (some .rejected, (sCAmb, ex))
  else
    match T? with
    | none => pure (some .rejected, (sCAmb, ex))
    | some T₀ =>
      if evicted then
        semFwdEvictHookS P Dh encPt encT lam T
          (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ))
          qep sCAmb ex Q w isDel pk pq' ((sC.base.mir.epoch Q + 1, some T₀), lct)
      else
        semFwdHookS P Dh encPt encT lam T Kc
          (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ))
          qep B sCAmb ex Q w isDel none pk pq' honestC (mkC (sC.base.mir.epoch Q + 1) (some T₀))

def semRecvSameBranchDF (qep B T Kc : ℕ)
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ) (ex : List (Fig8C Pt))
    (Q : Party) (w : Bytes) (isDel : Bool)
    (pq' : Bytes) (i : ℕ) (pk : PublicKey) (T? : Option Pt)
    (lct : ℕ × LibsignalCiphertextWithSalt32)
    (honestC : Option (SimFig8C Pt)) (ci : ℕ) :
    OracleComp
      (unifSpec + CryptoGames.SM.specDF (CryptoGames.Ratchet.LibsignalSim.SimFig8St Pt)
        (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt))
      (Option (RecvResult (Plain ℓ)) ×
        (LibsignalToModularSchemeSimState Bytes Pt ℓ × List (Fig8C Pt))) :=
  let P := paramsV1 C K idA idB
  let mkC (t : ℕ) (T : Option Pt) : SimFig8C Pt :=
    match honestC with
    | some c => if c.2.2.2 = lct.2.2 then c else ((t, T), lct)
    | none => ((t, T), lct)
  let g := (sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩
  if g.rejects i then
    pure (some .rejected, (sC, ex))
  else
    semFwdHookS P Dh encPt encT lam T Kc
      (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ))
      qep B sC ex Q w isDel (some ci) pk pq' honestC (mkC g.epoch T?)

/-- Full atomic `semRecvHookS` `Comp` over `fig8SmIfaceDF ℓ Pt`. -/
def dfRecvHookC (qep q : ℕ) :
    Comp AOps IDF [dfRecvInT ℓ Pt] (dfRecvOutT ℓ Pt) :=
  fwdRecvDispatchC C K idA idB Dh encPt encT decT lam q
    (fwdRecvNewC C K idA idB Dh encPt encT decT lam qep q)
    (fwdRecvSameC C K idA idB Dh encPt encT decT lam qep q)

theorem dfRecvHookC_queries (qep q : ℕ) :
    (dfRecvHookC (Pt := Pt) (ℓ := ℓ) C K idA idB Dh encPt encT decT lam qep q).queries
      (fun _ => 1) (fun _ => 0) ≤ 1 :=
  fwdRecvDispatchC_queries C K idA idB Dh encPt encT decT lam q
    (fwdRecvNewC C K idA idB Dh encPt encT decT lam qep q)
    (fwdRecvSameC C K idA idB Dh encPt encT decT lam qep q)
    (fwdRecvNewC_queries C K idA idB Dh encPt encT decT lam qep q)
    (fwdRecvSameC_queries C K idA idB Dh encPt encT decT lam qep q)

theorem dfRecvHookC_cost (qep q : ℕ) (hℓ : ℓ < 10 ^ 6) :
    (dfRecvHookC (Pt := Pt) (ℓ := ℓ) C K idA idB Dh encPt encT decT lam qep q).cost ≤
      185000000 + 40000000 * q + 512 * bits (qep + 1) :=
  Nat.le_trans
    (fwdRecvDispatchC_cost C K idA idB Dh encPt encT decT lam q hℓ
      (fwdRecvNewC C K idA idB Dh encPt encT decT lam qep q)
      (fwdRecvSameC C K idA idB Dh encPt encT decT lam qep q))
    (by
      have hn := fwdRecvNewC_cost (Pt := Pt) (ℓ := ℓ) C K idA idB Dh encPt encT decT lam qep q hℓ
      have hs := fwdRecvSameC_cost (Pt := Pt) (ℓ := ℓ) C K idA idB Dh encPt encT decT lam qep q hℓ
      omega)

theorem dfRecvHookC_descBits_le (qep q : ℕ) (hℓ : ℓ < 10 ^ 6) :
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
      (dfRecvHookC (Pt := Pt) (ℓ := ℓ) C K idA idB Dh encPt encT decT lam qep q) ≤
      (2 ^ 20 + 2 ^ 18) + (2 ^ 12 + 2 ^ 10) * bits (ratchetCostBudget q (qep + 1) + (qep + 1)) :=
  Nat.le_trans
    (fwdRecvDispatchC_descBits_le C K idA idB Dh encPt encT decT lam qep q hℓ
      (fwdRecvNewC C K idA idB Dh encPt encT decT lam qep q)
      (fwdRecvSameC C K idA idB Dh encPt encT decT lam qep q))
    (by
      have hn := fwdRecvNewC_descBits_le C K idA idB Dh encPt encT decT lam qep q hℓ
      have hs := fwdRecvSameC_descBits_le C K idA idB Dh encPt encT decT lam qep q hℓ
      omega)

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem simBaseEnc_simBaseDec_local (v : (simBaseT ℓ Pt).denote) :
    simBaseEnc (ℓ := ℓ) (Pt := Pt) (simBaseDec v) = v := by
  have h := dfStepEnc_dfStepDec (ℓ := ℓ) (Pt := Pt)
    ((v, ((⟨none, fun _ => none⟩, ⟨none, fun _ => none⟩), ([], []))), [])
  exact congrArg (fun x => x.1.1) h

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem smRrEnc_smRrDec_id
    (v : (smRrT (ℓ := ℓ) (Pt := Pt) (PlainT (ℓ := ℓ) (Pt := Pt))).denote) :
    smRrEnc (ℓ := ℓ) (Pt := Pt) (msgT := PlainT (ℓ := ℓ) (Pt := Pt)) id
      (smRrDec (ℓ := ℓ) (Pt := Pt) (msgT := PlainT (ℓ := ℓ) (Pt := Pt)) id v) = v := by
  rcases v with ⟨⟨⟩⟩ | ⟨t, i, _ | m⟩ <;> rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem smRrDec_smRrEnc_id (r : RecvResult (Plain ℓ)) :
    smRrDec (ℓ := ℓ) (Pt := Pt) (msgT := PlainT (ℓ := ℓ) (Pt := Pt)) id
      (smRrEnc (ℓ := ℓ) (Pt := Pt) (msgT := PlainT (ℓ := ℓ) (Pt := Pt)) id r) = r := by
  cases r with
  | rejected => rfl
  | accepted t i m? => cases m? <;> rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem eval_bind_ret {S0 : _root_.ReductionDsl.Sig} {O0 : _root_.ReductionDsl.Ops S0}
    {ι : Type} {T : OracleSpec ι} {I0 : _root_.ReductionDsl.Iface S0 T}
    {Γ : List (Ty S0)} {a b : Ty S0}
    (e : Expr O0 Γ a) (k : Comp O0 I0 (a :: Γ) b) (ρ : Env Γ)
    (v : a.denote) (hv : e.eval ρ = v) :
    (ReductionDsl.Comp.bind (.ret e) k).eval ρ = k.eval (.cons v ρ) := by
  simp only [ReductionDsl.Comp.eval, hv, pure_bind]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem eval_ite_comp {S0 : _root_.ReductionDsl.Sig} {O0 : _root_.ReductionDsl.Ops S0}
    {ι : Type} {T : OracleSpec ι} {I0 : _root_.ReductionDsl.Iface S0 T}
    {Γ : List (Ty S0)} {b : Ty S0}
    (c : Expr O0 Γ .bool) (t e : Comp O0 I0 Γ b) (ρ : Env Γ)
    (bv : Bool) (hb : c.eval ρ = bv) :
    (ReductionDsl.Comp.ite c t e).eval ρ = (if bv then t.eval ρ else e.eval ρ) := by
  simp only [ReductionDsl.Comp.eval, hb]

private theorem fwdOnAcceptC_eval_raw (qep Lq : ℕ) {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ (simBaseT ℓ Pt))
    (ci?E : Expr AOps Γ (.opt .nat)) (pkE : Expr AOps Γ PK)
    (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32)) (isDelE : Expr AOps Γ .bool)
    (tE iE : Expr AOps Γ .nat) (mE : Expr AOps Γ (PlainT (ℓ := ℓ) (Pt := Pt)))
    (pq'E : Expr AOps Γ (B 32))
    (ρ : Env Γ) (s : SimState Bytes Pt ℓ) (ci? : Option ℕ) (pk : PublicKey)
    (Q : Party) (w : Bytes) (isDel : Bool) (t i : ℕ) (m : Plain ℓ) (pq' : Bytes)
    (hs : sE.eval ρ = simBaseEnc s) (hci : ci?E.eval ρ = ci?) (hpk : pkE.eval ρ = pk)
    (hq : qBE.eval ρ = partyEnc Q) (hw : wE.eval ρ = w) (hd : isDelE.eval ρ = isDel)
    (ht : tE.eval ρ = t) (hi : iE.eval ρ = i) (hm : mE.eval ρ = m) (hpq : pq'E.eval ρ = pq')
    (hbnd : CryptoGames.Ratchet.LibsignalSim.SimStateBounded Lq s)
    (hCs : (s.chains Q).length ≤ 5) (hSk : ∀ g ∈ s.chains Q, g.skipped.length ≤ 2000) :
    (fwdOnAcceptC C K Dh encPt encT decT lam qep Lq
      sE ci?E pkE qBE wE isDelE tE iE mE pq'E).eval ρ =
    pure (let p := onAcceptPure qep Q w isDel t i m ci? pk pq' s
      (p.1.map (smRrEnc (ℓ := ℓ) (Pt := Pt) (msgT := PlainT (ℓ := ℓ) (Pt := Pt)) id),
        simBaseEnc p.2)) := by
  have hev := fwdOnAcceptC_eval (Pt := Pt) (ℓ := ℓ) C K Dh encPt encT decT lam qep Lq
    sE ci?E pkE qBE wE isDelE tE iE mE pq'E ρ s ci? pk Q w isDel t i m pq'
    hs hci hpk hq hw hd ht hi hm hpq hbnd hCs hSk
  let encP : Option (RecvResult (Plain ℓ)) × SimState Bytes Pt ℓ →
      (ReductionDsl.Ty.prod (.opt (smRrT (ℓ := ℓ) (Pt := Pt) (PlainT (ℓ := ℓ) (Pt := Pt))))
        (simBaseT ℓ Pt)).denote :=
    Prod.map (Option.map (smRrEnc (ℓ := ℓ) (Pt := Pt) (msgT := PlainT (ℓ := ℓ) (Pt := Pt)) id))
      simBaseEnc
  have hret := congrArg (Functor.map encP) hev
  have hcomp : (fun a => encP (Prod.map (Option.map (smRrDec id)) simBaseDec a)) = id := by
    funext ⟨rr?, b_raw⟩
    simp only [encP, Prod.map, simBaseEnc_simBaseDec_local, id_eq]
    congr 1
    cases rr? with
    | none => rfl
    | some v => exact congrArg some (smRrEnc_smRrDec_id v)
  rw [Functor.map_map, hcomp, id_map, map_pure] at hret
  exact hret

private theorem query_dlDF_atomic_eval {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool) (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (ρ : Env Γ) (Q : Party) (c' : Fig8C Pt)
    (hq : qBE.eval ρ = partyEnc Q) (hc' : c'E.eval ρ = fig8CtV c') :
    (ReductionDsl.Comp.query (O := AOps) (I := IDF) ReductionDsl.SMTagDF.dl (.pair qBE c'E)).eval ρ =
      Option.map (smRrEnc fun (pub, m) => (lpubV pub, m)) <$>
        CryptoGames.SM.Construction.DeliverForge.deliverQueryDF
          (St := CryptoGames.Ratchet.LibsignalSim.SimFig8St Pt)
          (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256)
          (C := SimFig8C Pt) Q c' := by
  have hbp : boolToParty (partyEnc Q) = Q := by cases Q <;> rfl
  have hct : fig8CtOfV (ℓ := ℓ) (Pt := Pt) (fig8CtV c') = c' :=
    SimFig8LoopAndCost.fig8CtOfV_fig8CtV c'
  simp only [ReductionDsl.Comp.eval, ReductionDsl.Expr.eval, fig8SmIfaceDF]
  rw [hq, hc', hbp, hct]
  rfl

private theorem query_ijDF_atomic_eval {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool) (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (ρ : Env Γ) (Q : Party) (c' : Fig8C Pt)
    (hq : qBE.eval ρ = partyEnc Q) (hc' : c'E.eval ρ = fig8CtV c') :
    (ReductionDsl.Comp.query (O := AOps) (I := IDF) ReductionDsl.SMTagDF.ij (.pair qBE c'E)).eval ρ =
      Option.map (smRrEnc fun (pub, m) => (lpubV pub, m)) <$>
        CryptoGames.SM.Construction.DeliverForge.injectQueryDF
          (St := CryptoGames.Ratchet.LibsignalSim.SimFig8St Pt)
          (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256)
          (C := SimFig8C Pt) Q c' := by
  have hbp : boolToParty (partyEnc Q) = Q := by cases Q <;> rfl
  have hct : fig8CtOfV (ℓ := ℓ) (Pt := Pt) (fig8CtV c') = c' :=
    SimFig8LoopAndCost.fig8CtOfV_fig8CtV c'
  simp only [ReductionDsl.Comp.eval, ReductionDsl.Expr.eval, fig8SmIfaceDF]
  rw [hq, hc', hbp, hct]
  rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem eval_bind_comp {S0 : _root_.ReductionDsl.Sig} {O0 : _root_.ReductionDsl.Ops S0}
    {ι : Type} {T : OracleSpec ι} {I0 : _root_.ReductionDsl.Iface S0 T}
    {Γ : List (Ty S0)} {a b : Ty S0}
    (m : Comp O0 I0 Γ a) (k : Comp O0 I0 (a :: Γ) b) (ρ : Env Γ) :
    (ReductionDsl.Comp.bind m k).eval ρ = (m.eval ρ >>= fun v => k.eval (.cons v ρ)) := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem eval_caseOpt_none {S0 : _root_.ReductionDsl.Sig} {O0 : _root_.ReductionDsl.Ops S0}
    {ι : Type} {T : OracleSpec ι} {I0 : _root_.ReductionDsl.Iface S0 T}
    {Γ : List (Ty S0)} {a b : Ty S0}
    (e : Expr O0 Γ (.opt a)) (n : Comp O0 I0 Γ b) (s : Comp O0 I0 (a :: Γ) b)
    (ρ : Env Γ) (ho : e.eval ρ = none) :
    (ReductionDsl.Comp.caseOpt e n s).eval ρ = n.eval ρ := by
  simp [ReductionDsl.Comp.eval, ho]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem eval_caseOpt_some {S0 : _root_.ReductionDsl.Sig} {O0 : _root_.ReductionDsl.Ops S0}
    {ι : Type} {T : OracleSpec ι} {I0 : _root_.ReductionDsl.Iface S0 T}
    {Γ : List (Ty S0)} {a b : Ty S0}
    (e : Expr O0 Γ (.opt a)) (n : Comp O0 I0 Γ b) (s : Comp O0 I0 (a :: Γ) b)
    (ρ : Env Γ) (x : a.denote) (ho : e.eval ρ = some x) :
    (ReductionDsl.Comp.caseOpt e n s).eval ρ = s.eval (.cons x ρ) := by
  simp [ReductionDsl.Comp.eval, ho]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem eval_caseSum_inl {S0 : _root_.ReductionDsl.Sig} {O0 : _root_.ReductionDsl.Ops S0}
    {ι : Type} {T : OracleSpec ι} {I0 : _root_.ReductionDsl.Iface S0 T}
    {Γ : List (Ty S0)} {a b c : Ty S0}
    (e : Expr O0 Γ (.sum a b)) (l : Comp O0 I0 (a :: Γ) c) (r : Comp O0 I0 (b :: Γ) c)
    (ρ : Env Γ) (x : a.denote) (hs : e.eval ρ = .inl x) :
    (ReductionDsl.Comp.caseSum e l r).eval ρ = l.eval (.cons x ρ) := by
  simp [ReductionDsl.Comp.eval, hs]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem eval_caseSum_inr {S0 : _root_.ReductionDsl.Sig} {O0 : _root_.ReductionDsl.Ops S0}
    {ι : Type} {T : OracleSpec ι} {I0 : _root_.ReductionDsl.Iface S0 T}
    {Γ : List (Ty S0)} {a b c : Ty S0}
    (e : Expr O0 Γ (.sum a b)) (l : Comp O0 I0 (a :: Γ) c) (r : Comp O0 I0 (b :: Γ) c)
    (ρ : Env Γ) (y : b.denote) (hs : e.eval ρ = .inr y) :
    (ReductionDsl.Comp.caseSum e l r).eval ρ = r.eval (.cons y ρ) := by
  simp [ReductionDsl.Comp.eval, hs]

private theorem eval_ret_rej {Γ : List (Ty ASig)}
    {stE : Expr AOps Γ (dfStepT ℓ Pt)} {ρ : Env Γ}
    (st : LibsignalToModularSchemeSimState Bytes Pt ℓ × List (Fig8C Pt))
    (hst : dfStepDec (stE.eval ρ) = st) :
    dfRecvOutDec <$> (ReductionDsl.Comp.ret (I := IDF) (fwdRejOutE C K Dh encPt encT decT lam stE)).eval ρ =
      pure (some .rejected, st) := by
  simp only [ReductionDsl.Comp.eval, map_pure]
  rw [fwdRejOutE_eval, hst]

private theorem eval_ret_none {Γ : List (Ty ASig)}
    {stE : Expr AOps Γ (dfStepT ℓ Pt)} {ρ : Env Γ}
    (st : LibsignalToModularSchemeSimState Bytes Pt ℓ × List (Fig8C Pt))
    (hst : dfStepDec (stE.eval ρ) = st) :
    dfRecvOutDec <$> (ReductionDsl.Comp.ret (I := IDF) (fwdNoneOutE C K Dh encPt encT decT lam stE)).eval ρ =
      pure (none, st) := by
  simp only [ReductionDsl.Comp.eval, map_pure]
  rw [fwdNoneOutE_eval, hst]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem sanSnapExtra_chains {sC : LibsignalToModularSchemeSimState Bytes Pt ℓ}
    (hextra : SanSnapExtra C K sC) (Q : Party) :
    (sC.base.chains Q).length ≤ 5 ∧ ∀ g ∈ sC.base.chains Q, g.skipped.length ≤ 2000 :=
  hextra.2.1 Q

theorem fwdAnswerC_eval (qep Lq T : ℕ) (_hℓ : ℓ < 10 ^ 6) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (dfStepT ℓ Pt)) (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32))
    (isDelE : Expr AOps Γ .bool) (ci?E : Expr AOps Γ (.opt .nat))
    (pkE : Expr AOps Γ PK) (pq'E : Expr AOps Γ (B 32))
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (ρ : Env Γ) (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ) (ex : List (Fig8C Pt))
    (Q : Party) (w : Bytes) (isDel : Bool) (ci? : Option ℕ)
    (pk : PublicKey) (pq' : Bytes) (c' : Fig8C Pt)
    (hst : stE.eval ρ = dfStepEnc (sC, ex)) (hq : qBE.eval ρ = partyEnc Q)
    (hw : wE.eval ρ = w) (hd : isDelE.eval ρ = isDel) (hci : ci?E.eval ρ = ci?)
    (hpk : pkE.eval ρ = pk) (hpq : pq'E.eval ρ = pq') (hc' : c'E.eval ρ = fig8CtV c')
    (hbnd : SimCStateBounded Lq sC) (hextra : SanSnapExtra C K sC) :
    (dfRecvOutDec <$>
      (fwdAnswerC C K idA idB Dh encPt encT decT lam qep Lq T
        stE qBE wE isDelE ci?E pkE pq'E c'E).eval ρ) =
    semFwdAnswerHookS (paramsV1 C K idA idB) Dh encPt encT lam T
      (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ))
      qep sC ex Q w isDel ci? pk pq' c' := by
  dsimp only [fwdAnswerC, semFwdAnswerHookS]
  let tupV : (ReductionDsl.Ty.prod (dfStepT ℓ Pt) (.prod .bool (.prod (B 32)
      (.prod .bool (.prod (.opt .nat) (.prod PK (.prod (B 32) (fig8CtT (ℓ := ℓ) (Pt := Pt))))))))).denote :=
    (dfStepEnc (sC, ex), (partyEnc Q, (w, (isDel, (ci?, (pk, (pq', fig8CtV c')))))))
  let ρ1 := ReductionDsl.Env.cons tupV ρ
  rw [eval_bind_ret _ _ _ tupV (by simp [ReductionDsl.Expr.eval, tupV, hst, hq, hw, hd, hci, hpk, hpq, hc']),
    eval_bind_comp]
  let inTB := sC.base.honest.any fun wc =>
    decide (wc.2 = c') && (sC.base.mir.inTransit Q.other wc.1).isSome
  have hinT : (fwdInTE C K Dh encPt encT decT lam Lq
      (scBase (.fst (.fst .v0))) (.fst (.snd .v0))
      (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))))).eval ρ1 = inTB :=
    fwdInTE_eval C K Dh encPt encT decT lam Lq _ _ _ ρ1 sC.base Q c'
      rfl rfl rfl hbnd.base.honest_le hbnd.base.trans_le
      hextra.2.2.2
  rw [eval_ite_comp _ _ _ _ inTB hinT]
  have hdl := query_dlDF_atomic_eval C K Dh encPt encT decT lam
    (.fst (.snd .v0)) (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))) ρ1 Q c' rfl rfl
  have hij := query_ijDF_atomic_eval C K Dh encPt encT decT lam
    (.fst (.snd .v0)) (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))) ρ1 Q c' rfl rfl
  have hqEq :
      (if inTB
        then (ReductionDsl.Comp.query (O := AOps) (I := IDF) ReductionDsl.SMTagDF.dl
          (.pair (.fst (.snd .v0)) (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))))).eval ρ1
        else (ReductionDsl.Comp.query (O := AOps) (I := IDF) ReductionDsl.SMTagDF.ij
          (.pair (.fst (.snd .v0)) (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))))).eval ρ1) =
      Option.map (smRrEnc fun (pub, m) => (lpubV pub, m)) <$>
        (if inTB
          then CryptoGames.SM.Construction.DeliverForge.deliverQueryDF Q c'
          else CryptoGames.SM.Construction.DeliverForge.injectQueryDF Q c') := by
    cases inTB <;> simp [hdl, hij]
  have hshEq :
      (if inTB
        then (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ)).onDl Q c' ex
        else (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ)).onIj Q c' ex) =
      (fun r => (r, ex)) <$>
        (if inTB
          then CryptoGames.SM.Construction.DeliverForge.deliverQueryDF Q c'
          else CryptoGames.SM.Construction.DeliverForge.injectQueryDF Q c') := by
    cases inTB <;> simp [deliverForgeSemHook, map_eq_bind_pure_comp]
  change dfRecvOutDec <$> ((if inTB then _ else _) >>= _) = (if inTB then _ else _) >>= _
  rw [hqEq, hshEq, map_bind, bind_map_left, bind_map_left]
  congr 1; funext res
  have hex_rt : List.map (fig8CtOfV (ℓ := ℓ) (Pt := Pt)) (ex.map fig8CtV) = ex := by
    rw [List.map_map]
    have hid : (fig8CtOfV (ℓ := ℓ) (Pt := Pt) ∘ fig8CtV) = id := by
      funext x; exact SimFig8LoopAndCost.fig8CtOfV_fig8CtV x
    simp [hid]
  rcases res with _ | (_ | ⟨t, i, pm?⟩)
  · simp only [Option.map, onAnswerPure]
    rw [eval_caseOpt_none _ _ _ _ rfl]
    exact eval_ret_rej C K Dh encPt encT decT lam (sC, ex) (dfStepDec_dfStepEnc (sC, ex))
  · simp only [Option.map, smRrEnc, onAnswerPure]
    let msgPairT := ReductionDsl.Ty.prod (lpubT (ℓ := ℓ) (Pt := Pt)) (PlainT (ℓ := ℓ) (Pt := Pt))
    let rejV : (smRrT (ℓ := ℓ) (Pt := Pt) msgPairT).denote := .inl ()
    rw [eval_caseOpt_some _ _ _ _ rejV rfl, eval_caseSum_inl _ _ _ _ () rfl]
    exact eval_ret_rej C K Dh encPt encT decT lam (sC, ex) (dfStepDec_dfStepEnc (sC, ex))
  · simp only [Option.map, smRrEnc, onAnswerPure]
    let msgPairT := ReductionDsl.Ty.prod (lpubT (ℓ := ℓ) (Pt := Pt)) (PlainT (ℓ := ℓ) (Pt := Pt))
    let rrV : (smRrT (ℓ := ℓ) (Pt := Pt) msgPairT).denote :=
      smRrEnc (ℓ := ℓ) (Pt := Pt) (msgT := msgPairT) (fun (pub, m) => (lpubV pub, m))
        (.accepted t i pm?)
    let accV : (ReductionDsl.Ty.prod .nat (.prod .nat (.opt msgPairT))).denote :=
      (t, (i, pm?.map fun (pub, m) => (lpubV pub, m)))
    rw [eval_caseOpt_some _ _ _ _ rrV rfl, eval_caseSum_inr _ _ _ _ accV rfl, eval_bind_comp]
    let ρ4 := ReductionDsl.Env.cons (t := .prod .nat (.prod .nat (.opt msgPairT))) accV
      (ReductionDsl.Env.cons (t := smRrT (ℓ := ℓ) (Pt := Pt) msgPairT) rrV
        (ReductionDsl.Env.cons (t := .opt (smRrT (ℓ := ℓ) (Pt := Pt) msgPairT)) (some rrV) ρ1))
    have hmE : (ReductionDsl.Expr.caseOpt (O := AOps) (.snd (.snd .v0))
        (.snd (.fst (defaultMcAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam))))
        (.snd .v0)).eval ρ4 = (pm?.map (·.2)).getD default := by
      rcases pm? with _ | ⟨pub, m⟩ <;> simp [ρ4, accV, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, defaultMcAtomicE_eval]
    have hacc := fwdOnAcceptC_eval_raw C K Dh encPt encT decT lam qep Lq
      (scBase (.fst (.fst .v3)))
      (.fst (.snd (.snd (.snd (.snd .v3)))))
      (.fst (.snd (.snd (.snd (.snd (.snd .v3))))))
      (.fst (.snd .v3))
      (.fst (.snd (.snd .v3)))
      (.fst (.snd (.snd (.snd .v3))))
      (.fst .v0) (.fst (.snd .v0))
      (.caseOpt (.snd (.snd .v0))
        (.snd (.fst (defaultMcAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam))))
        (.snd .v0))
      (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))
      ρ4 sC.base ci? pk Q w isDel t i ((pm?.map (·.2)).getD default) pq'
      rfl rfl rfl rfl rfl rfl rfl rfl hmE rfl
      hbnd.base (sanSnapExtra_chains C K hextra Q).1 (sanSnapExtra_chains C K hextra Q).2
    erw [hacc]
    simp only [pure_bind, ReductionDsl.Comp.eval, map_pure]
    let p := onAcceptPure qep Q w isDel t i ((pm?.map (·.2)).getD default) ci? pk pq' sC.base
    let ρ5 := ReductionDsl.Env.cons
      (t := .prod (.opt (smRrT (ℓ := ℓ) (Pt := Pt) (PlainT (ℓ := ℓ) (Pt := Pt)))) (simBaseT ℓ Pt))
      (p.1.map (smRrEnc (ℓ := ℓ) (Pt := Pt) (msgT := PlainT (ℓ := ℓ) (Pt := Pt)) id),
        simBaseEnc p.2) ρ4
    have hsc := fwdScAcceptUpdateE_eval C K idA idB Dh encPt encT decT lam T
      (.fst (.fst .v4)) (.snd .v0) (.fst (.snd .v4))
      (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v4)))))))
      ρ5 sC p.2 Q c' rfl rfl rfl rfl
    dsimp only [dfRecvOutDec, dfStepDec, ReductionDsl.Expr.eval]
    erw [hsc]
    have hrr :
        ((p.1.map (smRrEnc (ℓ := ℓ) (Pt := Pt) (msgT := PlainT (ℓ := ℓ) (Pt := Pt)) id)).map
          (smRrDec id)) = p.1 := by
      cases hp1 : p.1 with
      | none => rfl
      | some r0 => exact congrArg some (smRrDec_smRrEnc_id r0)
    exact congrArg pure (Prod.ext hrr (Prod.ext rfl hex_rt))

theorem fwdEvictC_eval (qep q : ℕ) (hℓ : ℓ < 10 ^ 6) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (dfStepT ℓ Pt)) (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32))
    (isDelE : Expr AOps Γ .bool) (pkE : Expr AOps Γ PK) (pq'E : Expr AOps Γ (B 32))
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (ρ : Env Γ) (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ) (ex : List (Fig8C Pt))
    (Q : Party) (w : Bytes) (isDel : Bool)
    (pk : PublicKey) (pq' : Bytes) (c' : Fig8C Pt)
    (hst : stE.eval ρ = dfStepEnc (sC, ex)) (hq : qBE.eval ρ = partyEnc Q)
    (hw : wE.eval ρ = w) (hd : isDelE.eval ρ = isDel)
    (hpk : pkE.eval ρ = pk) (hpq : pq'E.eval ρ = pq') (hc' : c'E.eval ρ = fig8CtV c')
    (hbnd : SimCStateBounded q sC) (hex : ex.length ≤ q) (hextra : SanSnapExtra C K sC) :
    (dfRecvOutDec <$>
      (fwdEvictC C K idA idB Dh encPt encT decT lam qep q
        stE qBE wE isDelE pkE pq'E c'E).eval ρ) =
    semFwdEvictHookS (paramsV1 C K idA idB) Dh encPt encT lam (50000 * q)
      (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ))
      qep sC ex Q w isDel pk pq' c' := by
  dsimp only [fwdEvictC, semFwdEvictHookS]
  let tupV : (dfFwdEvictInT ℓ Pt).denote :=
    (dfStepEnc (sC, ex), (partyEnc Q, (w, (isDel, (pk, (pq', fig8CtV c'))))))
  let ρ1 := ReductionDsl.Env.cons tupV ρ
  rw [eval_bind_ret _ _ _ tupV (by simp [ReductionDsl.Expr.eval, tupV, hst, hq, hw, hd, hpk, hpq, hc'])]
  have hsafe : (mSafeInjE (O' := AOps) (ssMir (scBase (.fst (.fst .v0))))).eval ρ1 =
      sC.base.mir.safeInj 3 :=
    mSafeInjE_eval _ ρ1 sC.base.mir rfl
  have hcond : (ReductionDsl.Expr.and (O := AOps) (.fst (.snd (.snd (.snd .v0))))
      (.not (mSafeInjE (ssMir (scBase (.fst (.fst .v0))))))).eval ρ1 =
      (isDel && !(sC.base.mir.safeInj 3)) := by
    dsimp only [ReductionDsl.Expr.eval]
    rw [hsafe]
    rfl
  rw [eval_ite_comp _ _ _ _ (isDel && !(sC.base.mir.safeInj 3)) hcond]
  by_cases hc : (isDel && !(sC.base.mir.safeInj 3)) = true
  · simp only [hc, ↓reduceIte, eval_bind_comp]
    have hpr := fwdProbeC_eval C K Dh encPt encT decT lam q
      (.fst (.snd .v0)) (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))) (.snd (.fst .v0))
      ρ1 Q c' ex rfl rfl rfl hex
    rw [← hpr, map_bind, bind_map_left]
    congr 1; funext ex_raw
    exact eval_ret_rej C K Dh encPt encT decT lam (sC, ex_raw.map fig8CtOfV)
      (Prod.ext (SimFig8LoopAndCost.simFullDec_simFullEnc sC) rfl)
  · have hcf : (isDel && !(sC.base.mir.safeInj 3)) = false :=
      Bool.eq_false_iff.mpr hc
    simp only [hcf, Bool.false_eq_true, ↓reduceIte]
    exact fwdAnswerC_eval C K idA idB Dh encPt encT decT lam qep q (50000 * q) hℓ
      (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
      (.fst (.snd (.snd (.snd .v0)))) .none
      (.fst (.snd (.snd (.snd (.snd .v0)))))
      (.fst (.snd (.snd (.snd (.snd (.snd .v0))))))
      (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))
      ρ1 sC ex Q w isDel none pk pq' c'
      rfl rfl rfl rfl rfl rfl rfl rfl hbnd hextra

theorem fwdHookC_eval (qep q : ℕ) (hℓ : ℓ < 10 ^ 6) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (dfStepT ℓ Pt)) (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32))
    (isDelE : Expr AOps Γ .bool) (ci?E : Expr AOps Γ (.opt .nat))
    (pkE : Expr AOps Γ PK) (pq'E : Expr AOps Γ (B 32))
    (honestCE : Expr AOps Γ (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))))
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (ρ : Env Γ) (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ) (ex : List (Fig8C Pt))
    (Q : Party) (w : Bytes) (isDel : Bool) (ci? : Option ℕ)
    (pk : PublicKey) (pq' : Bytes) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt)
    (hst : stE.eval ρ = dfStepEnc (sC, ex)) (hq : qBE.eval ρ = partyEnc Q)
    (hw : wE.eval ρ = w) (hd : isDelE.eval ρ = isDel) (hci : ci?E.eval ρ = ci?)
    (hpk : pkE.eval ρ = pk) (hpq : pq'E.eval ρ = pq')
    (hhc : honestCE.eval ρ = honestC.map fig8CtV) (hc' : c'E.eval ρ = fig8CtV c')
    (hbnd : SimCStateBounded q sC) (hex : ex.length ≤ q) (hextra : SanSnapExtra C K sC) :
    (dfRecvOutDec <$>
      (fwdHookC C K idA idB Dh encPt encT decT lam qep q
        stE qBE wE isDelE ci?E pkE pq'E honestCE c'E).eval ρ) =
    semFwdHookS (paramsV1 C K idA idB) Dh encPt encT lam (50000 * q) (25001 * q + 25000)
      (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ))
      qep (2 ^ 32) sC ex Q w isDel ci? pk pq' honestC c' := by
  dsimp only [fwdHookC, semFwdHookS]
  let tupV : (dfFwdInT ℓ Pt).denote :=
    (dfStepEnc (sC, ex), (partyEnc Q, (w, (isDel, (ci?, (pk, (pq', (honestC.map fig8CtV, fig8CtV c'))))))))
  let ρ1 := ReductionDsl.Env.cons tupV ρ
  rw [eval_bind_ret _ _ _ tupV (by simp [ReductionDsl.Expr.eval, tupV, hst, hq, hw, hd, hci, hpk, hpq, hhc, hc'])]
  rcases honestC with _ | c
  · rw [eval_caseOpt_none _ _ _ _ rfl]
    exact fwdAnswerC_eval C K idA idB Dh encPt encT decT lam qep q (50000 * q) hℓ
      (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
      (.fst (.snd (.snd (.snd .v0)))) (.fst (.snd (.snd (.snd (.snd .v0)))))
      (.fst (.snd (.snd (.snd (.snd (.snd .v0))))))
      (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))))
      (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))))
      ρ1 sC ex Q w isDel ci? pk pq' c'
      rfl rfl rfl rfl rfl rfl rfl rfl hbnd hextra
  · rw [eval_caseOpt_some _ _ _ _ (fig8CtV (ℓ := ℓ) (Pt := Pt) c) rfl]
    let ρ2 := ReductionDsl.Env.cons (t := fig8CtT (ℓ := ℓ) (Pt := Pt)) (fig8CtV (ℓ := ℓ) (Pt := Pt) c) ρ1
    have heqc := eqFig8CAtomicE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) .v0
      (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1))))))))
      ρ2 c c' rfl rfl
    have hsafe : (mSafeInjE (O' := AOps) (ssMir (scBase (.fst (.fst .v1))))).eval ρ2 =
        sC.base.mir.safeInj 3 :=
      mSafeInjE_eval _ ρ2 sC.base.mir rfl
    have hcond : (ReductionDsl.Expr.and (O := AOps)
        (.not (eqFig8CAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) .v0
          (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1))))))))))
        (.and (.fst (.snd (.snd (.snd .v1))))
          (.not (mSafeInjE (ssMir (scBase (.fst (.fst .v1)))))))).eval ρ2 =
        (!(decide (c = c')) && (isDel && !(sC.base.mir.safeInj 3))) := by
      dsimp only [ReductionDsl.Expr.eval]
      rw [heqc, hsafe]
      rfl
    rw [eval_ite_comp _ _ _ _ (!(decide (c = c')) && (isDel && !(sC.base.mir.safeInj 3))) hcond]
    by_cases hg : (!(decide (c = c')) && (isDel && !(sC.base.mir.safeInj 3))) = true
    · simp only [hg, ↓reduceIte, eval_bind_comp]
      have hev := fwdEvalCKSC_eval C K idA idB Dh encPt encT decT lam
        q (50000 * q) (25001 * q + 25000) (2 ^ 32) hℓ
        (.fst (.fst .v1)) (.fst (.snd .v1)) (.fst (.snd (.snd .v1))) .v0
        (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1))))))))
        ρ2 sC Q w c c' rfl rfl rfl rfl rfl hbnd hextra
      rw [hev, pure_bind]
      rcases hck : evalCKS (paramsV1 C K idA idB) Dh encPt encT lam
          (50000 * q) (25001 * q + 25000) (2 ^ 32) sC Q w c c' with _ | r
      · simp only [Option.map]
        rw [eval_caseOpt_none _ _ _ _ rfl, eval_bind_comp]
        let ρ3 := ReductionDsl.Env.cons (t := .opt (.opt (kDecOutT ℓ Pt))) none ρ2
        have hpr := fwdProbeC_eval C K Dh encPt encT decT lam q
          (.fst (.snd .v2))
          (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v2))))))))
          (.snd (.fst .v2))
          ρ3 Q c' ex rfl rfl rfl hex
        rw [← hpr, map_bind, bind_map_left]
        congr 1; funext ex_raw
        exact eval_ret_rej C K Dh encPt encT decT lam (sC, ex_raw.map fig8CtOfV)
          (Prod.ext (SimFig8LoopAndCost.simFullDec_simFullEnc sC) rfl)
      · simp only [Option.map]
        let rV : (ReductionDsl.Ty.opt (kDecOutT ℓ Pt)).denote := r.map (kDecOutV (ℓ := ℓ) (Pt := Pt))
        rw [eval_caseOpt_some _ _ _ _ rV rfl]
        let ρ4 := ReductionDsl.Env.cons (t := .opt (kDecOutT ℓ Pt)) rV
          (ReductionDsl.Env.cons (t := .opt (.opt (kDecOutT ℓ Pt))) (some rV) ρ2)
        exact fwdResyncC_eval C K idA idB Dh encPt encT decT lam qep q (50000 * q) hℓ
          (.fst .v3) (.fst (.snd .v3)) (.fst (.snd (.snd .v3)))
          (.fst (.snd (.snd (.snd (.snd .v3)))))
          (.fst (.snd (.snd (.snd (.snd (.snd .v3))))))
          (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))
          .v2 .v0
          ρ4 sC ex Q w ci? pk pq' c r
          rfl rfl rfl rfl rfl rfl rfl rfl hbnd hextra
    · have hgf : (!(decide (c = c')) && (isDel && !(sC.base.mir.safeInj 3))) = false :=
        Bool.eq_false_iff.mpr hg
      simp only [hgf, Bool.false_eq_true, ↓reduceIte]
      exact fwdAnswerC_eval C K idA idB Dh encPt encT decT lam qep q (50000 * q) hℓ
        (.fst .v1) (.fst (.snd .v1)) (.fst (.snd (.snd .v1)))
        (.fst (.snd (.snd (.snd .v1)))) (.fst (.snd (.snd (.snd (.snd .v1)))))
        (.fst (.snd (.snd (.snd (.snd (.snd .v1))))))
        (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v1)))))))
        (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1))))))))
        ρ2 sC ex Q w isDel ci? pk pq' c'
        rfl rfl rfl rfl rfl rfl rfl rfl hbnd hextra

theorem fwdRecvNewC_eval (qep q : ℕ) (hℓ : ℓ < 10 ^ 6)
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ) (ex : List (Fig8C Pt))
    (Q : Party) (w : Bytes) (isDel : Bool)
    (pq' : Bytes) (i : ℕ) (pk : PublicKey) (T? : Option Pt)
    (lct : ℕ × LibsignalCiphertextWithSalt32)
    (honestC : Option (Fig8C Pt))
    (hbnd : SimCStateBounded q sC) (hex : ex.length ≤ q) (hextra : SanSnapExtra C K sC) :
    (dfRecvOutDec <$>
      (fwdRecvNewC C K idA idB Dh encPt encT decT lam qep q).eval
        (.cons (dfStepEnc (sC, ex), (partyEnc Q, (w, (isDel,
          (parseOutV (pq', (i, (pk, (T?, lct)))), honestC.map fig8CtV))))) .nil)) =
    semRecvNewBranchDF C K idA idB Dh encPt encT lam qep (2 ^ 32) (50000 * q) (25001 * q + 25000)
      sC ex Q w isDel pq' i pk T? lct honestC := by
  let ρ0 : Env [dfRecvNewInT ℓ Pt] :=
    .cons (dfStepEnc (sC, ex), (partyEnc Q, (w, (isDel,
      (parseOutV (pq', (i, (pk, (T?, lct)))), honestC.map fig8CtV))))) .nil
  let evicted := (honestC.map fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true
  let saltEq := (honestC.map fun c => decide (c.2.2.2 = lct.2.2)) == some true
  let amb := inReceiveOnlyEpoch sC.base.mir Q ||
    (Q == CryptoGames.Party.A && (sC.base.chains Q).any (·.key.isNone))
  let sCAmb : LibsignalToModularSchemeSimState Bytes Pt ℓ :=
    { sC with base := if amb then { sC.base with amb := sC.base.amb + 1 } else sC.base }
  dsimp only [fwdRecvNewC, semRecvNewBranchDF]
  change _ =
    if evicted && saltEq then pure (some CryptoGames.SM.RecvResult.rejected, (sC, ex))
    else if T? == some 0 then pure (some CryptoGames.SM.RecvResult.rejected, (sC, ex))
    else if inReceiveOnlyEpoch sC.base.mir Q || decide (25000 < i - 1) || decide (2 ^ 32 ≤ i) then
      pure (some CryptoGames.SM.RecvResult.rejected, (sCAmb, ex))
    else match T? with
      | none => pure (some CryptoGames.SM.RecvResult.rejected, (sCAmb, ex))
      | some T₀ =>
        if evicted then
          semFwdEvictHookS (paramsV1 C K idA idB) Dh encPt encT lam (50000 * q)
            (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ))
            qep sCAmb ex Q w isDel pk pq' ((sC.base.mir.epoch Q + 1, some T₀), lct)
        else
          semFwdHookS (paramsV1 C K idA idB) Dh encPt encT lam (50000 * q) (25001 * q + 25000)
            (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ))
            qep (2 ^ 32) sCAmb ex Q w isDel none pk pq' honestC
            (match honestC with
              | some c => if c.2.2.2 = lct.2.2 then c else ((sC.base.mir.epoch Q + 1, some T₀), lct)
              | none => ((sC.base.mir.epoch Q + 1, some T₀), lct))
  have hev0 : (fwdEvictedE C K Dh encPt encT decT lam
      (.snd (.snd (.snd (.snd (.snd .v0))))) (scBase (.fst (.fst .v0))) (.fst (.snd .v0))).eval ρ0 =
      evicted :=
    fwdEvictedE_eval C K Dh encPt encT decT lam _ _ _ ρ0 honestC sC.base Q rfl rfl rfl
  have hsalt0 : (fwdSaltEqE C K Dh encPt encT decT lam
      (.snd (.snd (.snd (.snd (.snd .v0)))))
      (.snd (.snd (.snd (.snd (.fst (.snd (.snd (.snd (.snd .v0)))))))))).eval ρ0 = saltEq :=
    fwdSaltEqE_eval C K Dh encPt encT decT lam _ _ ρ0 honestC lct rfl rfl
  have hc1 : (ReductionDsl.Expr.and (O := AOps)
      (fwdEvictedE C K Dh encPt encT decT lam (.snd (.snd (.snd (.snd (.snd .v0)))))
        (scBase (.fst (.fst .v0))) (.fst (.snd .v0)))
      (fwdSaltEqE C K Dh encPt encT decT lam (.snd (.snd (.snd (.snd (.snd .v0)))))
        (.snd (.snd (.snd (.snd (.fst (.snd (.snd (.snd (.snd .v0))))))))))).eval ρ0 =
      (evicted && saltEq) := by
    dsimp only [ReductionDsl.Expr.eval]; rw [hev0, hsalt0]
  rw [eval_ite_comp _ _ _ _ (evicted && saltEq) hc1]
  by_cases h1 : (evicted && saltEq) = true
  · simp only [h1, ↓reduceIte]
    exact eval_ret_rej C K Dh encPt encT decT lam (sC, ex) (dfStepDec_dfStepEnc (sC, ex))
  · simp only [Bool.eq_false_iff.mpr h1, Bool.false_eq_true, ↓reduceIte]
    have hz0 : (isZeroPtOptAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam)
        (.fst (.snd (.snd (.snd (.fst (.snd (.snd (.snd (.snd .v0)))))))))).eval ρ0 =
        (T? == some 0) :=
      isZeroPtOptAtomicE_eval _ ρ0
    rw [eval_ite_comp _ _ _ _ (T? == some 0) hz0]
    by_cases h2 : (T? == some 0) = true
    · simp only [h2, ↓reduceIte]
      exact eval_ret_rej C K Dh encPt encT decT lam (sC, ex) (dfStepDec_dfStepEnc (sC, ex))
    · simp only [Bool.eq_false_iff.mpr h2, Bool.false_eq_true, ↓reduceIte]
      have hscAmb0 := fwdScAmbE_eval C K Dh encPt encT decT lam
        (.fst (.fst .v0)) (.fst (.snd .v0)) ρ0 sC Q rfl rfl (sanSnapExtra_chains C K hextra Q).1
      have hstAmb0 : (ReductionDsl.Expr.pair (O := AOps)
          (fwdScAmbE C K Dh encPt encT decT lam (.fst (.fst .v0)) (.fst (.snd .v0)))
          (.snd (.fst .v0))).eval ρ0 = dfStepEnc (sCAmb, ex) := by
        dsimp only [ReductionDsl.Expr.eval, dfStepEnc]; rw [hscAmb0]; rfl
      have hg0 := fwdNewGuardRejectE_eval C K Dh encPt encT decT lam
        (scBase (.fst (.fst .v0))) (.fst (.snd .v0))
        (.fst (.snd (.fst (.snd (.snd (.snd (.snd .v0))))))) ρ0 sC.base Q i rfl rfl rfl
      rw [eval_ite_comp _ _ _ _ _ hg0]
      by_cases h3 : (inReceiveOnlyEpoch sC.base.mir Q || decide (25000 < i - 1) ||
          decide (2 ^ 32 ≤ i)) = true
      · simp only [h3, ↓reduceIte]
        exact eval_ret_rej C K Dh encPt encT decT lam (sCAmb, ex)
          (by rw [hstAmb0, dfStepDec_dfStepEnc])
      · simp only [Bool.eq_false_iff.mpr h3, Bool.false_eq_true, ↓reduceIte]
        rcases T? with _ | T₀
        · rw [eval_caseOpt_none _ _ _ _ rfl]
          exact eval_ret_rej C K Dh encPt encT decT lam (sCAmb, ex)
            (by rw [hstAmb0, dfStepDec_dfStepEnc])
        · let T₀V : (PtT (ℓ := ℓ) (Pt := Pt)).denote := T₀
          rw [eval_caseOpt_some _ _ _ _ T₀V rfl]
          let ρ1 := ReductionDsl.Env.cons (t := PtT (ℓ := ℓ) (Pt := Pt)) T₀V ρ0
          have hbndAmb : SimCStateBounded q sCAmb := by
            dsimp only [sCAmb]
            cases amb <;> exact ⟨⟨hbnd.base.trans_le, hbnd.base.chall_le, hbnd.base.honest_le,
              hbnd.base.comp_u, hbnd.base.chainsA_le, hbnd.base.chainsB_le⟩,
              hbnd.sent_le, hbnd.snaps_le⟩
          have hextraAmb : SanSnapExtra C K sCAmb := by
            dsimp only [sCAmb]
            cases amb <;> exact hextra
          have hev1 : (fwdEvictedE C K Dh encPt encT decT lam
              (.snd (.snd (.snd (.snd (.snd .v1))))) (scBase (.fst (.fst .v1)))
              (.fst (.snd .v1))).eval ρ1 = evicted :=
            fwdEvictedE_eval C K Dh encPt encT decT lam _ _ _ ρ1 honestC sC.base Q rfl rfl rfl
          have hscAmb1 := fwdScAmbE_eval C K Dh encPt encT decT lam
            (.fst (.fst .v1)) (.fst (.snd .v1)) ρ1 sC Q rfl rfl (sanSnapExtra_chains C K hextra Q).1
          have hstAmb1 : (ReductionDsl.Expr.pair (O := AOps)
              (fwdScAmbE C K Dh encPt encT decT lam (.fst (.fst .v1)) (.fst (.snd .v1)))
              (.snd (.fst .v1))).eval ρ1 = dfStepEnc (sCAmb, ex) := by
            dsimp only [ReductionDsl.Expr.eval, dfStepEnc]; rw [hscAmb1]; rfl
          have hnextEp : (ReductionDsl.Expr.add (O := AOps)
              (pGet (mEpoch (ssMir (scBase (.fst (.fst .v1))))) (.fst (.snd .v1)))
              (.nat 1)).eval ρ1 = sC.base.mir.epoch Q + 1 := by
            cases Q <;> rfl
          rw [eval_ite_comp _ _ _ _ evicted hev1]
          by_cases hevB : evicted = true
          · simp only [hevB, ↓reduceIte]
            refine fwdEvictC_eval C K idA idB Dh encPt encT decT lam qep q hℓ
              _ _ _ _ _ _ _ ρ1 sCAmb ex Q w isDel pk pq'
              ((sC.base.mir.epoch Q + 1, some T₀), lct)
              hstAmb1 rfl rfl rfl rfl rfl ?_ hbndAmb hex hextraAmb
            cases Q <;> rfl
          · simp only [Bool.eq_false_iff.mpr hevB, Bool.false_eq_true, ↓reduceIte]
            refine fwdHookC_eval C K idA idB Dh encPt encT decT lam qep q hℓ
              _ _ _ _ _ _ _ _ _ ρ1 sCAmb ex Q w isDel none pk pq' honestC _
              hstAmb1 rfl rfl rfl rfl rfl rfl rfl ?_ hbndAmb hex hextraAmb
            exact fwdMkCE_eval C K Dh encPt encT decT lam _ _ _ _ ρ1 honestC
              (sC.base.mir.epoch Q + 1) (some T₀) lct rfl hnextEp rfl rfl

theorem fwdRecvSameC_eval (qep q : ℕ) (hℓ : ℓ < 10 ^ 6)
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ) (ex : List (Fig8C Pt))
    (Q : Party) (w : Bytes) (isDel : Bool)
    (pq' : Bytes) (i : ℕ) (pk : PublicKey) (T? : Option Pt)
    (lct : ℕ × LibsignalCiphertextWithSalt32)
    (honestC : Option (Fig8C Pt)) (ci : ℕ)
    (hbnd : SimCStateBounded q sC) (hex : ex.length ≤ q) (hextra : SanSnapExtra C K sC) :
    (dfRecvOutDec <$>
      (fwdRecvSameC C K idA idB Dh encPt encT decT lam qep q).eval
        (.cons (dfStepEnc (sC, ex), (partyEnc Q, (w, (isDel,
          (parseOutV (pq', (i, (pk, (T?, lct)))), (honestC.map fig8CtV, ci)))))) .nil)) =
    semRecvSameBranchDF C K idA idB Dh encPt encT lam qep (2 ^ 32) (50000 * q) (25001 * q + 25000)
      sC ex Q w isDel pq' i pk T? lct honestC ci := by
  let ρ0 : Env [dfRecvSameInT ℓ Pt] :=
    .cons (dfStepEnc (sC, ex), (partyEnc Q, (w, (isDel,
      (parseOutV (pq', (i, (pk, (T?, lct)))), (honestC.map fig8CtV, ci)))))) .nil
  let g := (sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩
  dsimp only [fwdRecvSameC, semRecvSameBranchDF]
  have hg0 : (getChainDE (O' := AOps)
      (pGet (ssChains (scBase (.fst (.fst .v0)))) (.fst (.snd .v0)))
      (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))).eval ρ0 = ghostChainEnc g :=
    eval_getChainDE _ _ ρ0 (sC.base.chains Q) (by cases Q <;> rfl)
      (sanSnapExtra_chains C K hextra Q).1
  have hsk : g.skipped.length ≤ 2000 := by
    change (((sC.base.chains Q)[ci]?).getD ⟨none, 0, 0, []⟩).skipped.length ≤ 2000
    rcases hget : (sC.base.chains Q)[ci]? with _ | gc
    · decide
    · exact (sanSnapExtra_chains C K hextra Q).2 gc (List.mem_of_getElem? hget)
  have hrej : (ghostRejectsE (O' := AOps)
      (getChainDE (pGet (ssChains (scBase (.fst (.fst .v0)))) (.fst (.snd .v0)))
        (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))))
      (.fst (.snd (.fst (.snd (.snd (.snd (.snd .v0)))))))).eval ρ0 = g.rejects i :=
    eval_ghostRejectsE _ _ ρ0 g hg0 hsk
  rw [eval_ite_comp _ _ _ _ (g.rejects i) hrej]
  by_cases hr : g.rejects i = true
  · change _ = if g.rejects i = true then _ else _
    simp only [hr, ↓reduceIte]
    exact eval_ret_rej C K Dh encPt encT decT lam (sC, ex) (dfStepDec_dfStepEnc (sC, ex))
  · change _ = if g.rejects i = true then _ else _
    simp only [Bool.eq_false_iff.mpr hr, Bool.false_eq_true, ↓reduceIte]
    have hep : (ReductionDsl.Expr.fst (O := AOps) (.snd
        (getChainDE (pGet (ssChains (scBase (.fst (.fst .v0)))) (.fst (.snd .v0)))
          (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))))).eval ρ0 = g.epoch := by
      dsimp only [ReductionDsl.Expr.eval]; rw [hg0]; rfl
    refine fwdHookC_eval C K idA idB Dh encPt encT decT lam qep q hℓ
      _ _ _ _ _ _ _ _ _ ρ0 sC ex Q w isDel (some ci) pk pq' honestC _
      rfl rfl rfl rfl rfl rfl rfl rfl ?_ hbnd hex hextra
    exact fwdMkCE_eval C K Dh encPt encT decT lam _ _ _ _ ρ0 honestC g.epoch T? lct rfl hep rfl rfl

theorem dfRecvHookC_eval (qep q : ℕ) (hℓ : ℓ < 10 ^ 6)
    (s_raw : (dfStepT ℓ Pt).denote) (Q : Party) (w : Bytes) (isDel : Bool)
    (hbnd : SimCStateBounded q (dfStepDec s_raw).1)
    (hex : (dfStepDec s_raw).2.length ≤ q)
    (hextra : SanSnapExtra C K (dfStepDec s_raw).1) :
    (dfRecvOutDec <$>
      (dfRecvHookC C K idA idB Dh encPt encT decT lam qep q).eval
        (.cons (s_raw, (partyEnc Q, (w, isDel))) .nil)) =
    semRecvHookS (paramsV1 C K idA idB) Dh encPt encT decT lam
      (50000 * q) (25001 * q + 25000)
      (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ))
      qep (2 ^ 32) (dfStepDec s_raw).1 (dfStepDec s_raw).2 Q w isDel := by
  let sC := (dfStepDec s_raw).1
  let ex := (dfStepDec s_raw).2
  have hs_raw : s_raw = dfStepEnc (sC, ex) := (dfStepEnc_dfStepDec s_raw).symm
  rw [hs_raw, dfStepDec_dfStepEnc (sC, ex)]
  let ρ0 : Env [dfRecvInT ℓ Pt] := .cons (dfStepEnc (sC, ex), (partyEnc Q, (w, isDel))) .nil
  change (dfRecvOutDec <$>
      (dfRecvHookC C K idA idB Dh encPt encT decT lam qep q).eval ρ0) =
    semRecvHookS (paramsV1 C K idA idB) Dh encPt encT decT lam
      (50000 * q) (25001 * q + 25000)
      (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ))
      qep (2 ^ 32) sC ex Q w isDel
  dsimp only [dfRecvHookC, fwdRecvDispatchC, semRecvHookS]
  let refuseB : Bool :=
    sC.base.stopped || sC.base.mir.win ||
      (isDel && (sC.base.mir.inTransit Q.other w).isNone) ||
      (!isDel && ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
        !(CryptoGames.Ratchet.LibsignalInst.ratchetKeyAdmissible
          (paramsV1 C K idA idB).codec decT encT w)))
  have hrefuse : (fwdRefuseE C K Dh encPt encT decT lam q
      (scBase (.fst (.fst .v0))) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))).eval ρ0 =
      refuseB :=
    fwdRefuseE_eval C K Dh encPt encT decT lam q
      (scBase (.fst (.fst .v0))) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))
      ρ0 sC.base Q w isDel rfl rfl rfl rfl hbnd.base.trans_le
  rw [eval_ite_comp _ _ _ _ refuseB hrefuse]
  by_cases href : refuseB = true
  · simp only [refuseB, href, ↓reduceIte]
    exact eval_ret_none C K Dh encPt encT decT lam (sC, ex) (dfStepDec_dfStepEnc (sC, ex))
  · have hrf : refuseB = false := Bool.eq_false_iff.mpr href
    simp only [refuseB, hrf, Bool.false_eq_true, ↓reduceIte, eval_bind_comp]
    have hp := parseRecvAtomicC_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) IDF idA idB (2 ^ 32)
      (.fst (.snd .v0)) (pGet (ssPq (scBase (.fst (.fst .v0)))) (.fst (.snd .v0)))
      (.fst (.snd (.snd .v0))) ρ0 (partyEnc Q) (sC.base.pq Q) w
      rfl (by cases Q <;> rfl) rfl (hextra.1 Q)
    rw [hp, pure_bind]
    rcases hpr : simParseRecvC (paramsV1 C K idA idB) decT (2 ^ 32)
        (partyEnc Q) (sC.base.pq Q) w with _ | ⟨pq', i, pk, T?, lct⟩
    · simp only [Option.map]
      rw [eval_caseOpt_none _ _ _ _ rfl]
      exact eval_ret_rej C K Dh encPt encT decT lam (sC, ex) (dfStepDec_dfStepEnc (sC, ex))
    · simp only [Option.map]
      let pv : (parseOutT ℓ Pt).denote := parseOutV (ℓ := ℓ) (Pt := Pt) (pq', (i, (pk, (T?, lct))))
      rw [eval_caseOpt_some _ _ _ _ pv rfl]
      let ρ2 := ReductionDsl.Env.cons (t := parseOutT ℓ Pt) pv
        (ReductionDsl.Env.cons (t := .opt (parseOutT ℓ Pt)) (some pv) ρ0)
      have hf := eval_findChainIdxE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam)
        (pGet (ssChains (scBase (.fst (.fst .v2)))) (.fst (.snd .v2)))
        (.fst (.snd (.snd .v0))) ρ2 (sC.base.chains Q) (by cases Q <;> rfl)
        (sanSnapExtra_chains C K hextra Q).1
      change _ = (sC.base.chains Q).findIdx? (fun g => g.key == some pk) at hf
      let honestC := (sC.base.honest.find? fun wc =>
        wc.1 == w && CryptoGames.Party.senderOf wc.2.1.1 == Q.other).map (·.2)
      rcases hci : (sC.base.chains Q).findIdx? (fun g => g.key == some pk) with _ | ci
      · simp only [hci]
        rw [hci] at hf
        rw [eval_caseOpt_none _ _ _ _ hf]
        have hhc2 := fwdHonestCE_eval C K Dh encPt encT decT lam q
          (scBase (.fst (.fst .v2))) (.fst (.snd .v2)) (.fst (.snd (.snd .v2)))
          ρ2 sC.base Q w rfl rfl rfl hbnd.base.honest_le
        rw [eval_bind_ret _ _ _
          (dfStepEnc (sC, ex), (partyEnc Q, (w, (isDel, (pv, honestC.map fig8CtV)))))
          (by dsimp only [ReductionDsl.Expr.eval]; rw [hhc2]; rfl)]
        rw [Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.renComp_eval]
        exact fwdRecvNewC_eval C K idA idB Dh encPt encT decT lam qep q hℓ
          sC ex Q w isDel pq' i pk T? lct honestC hbnd hex hextra
      · simp only [hci]
        rw [hci] at hf
        rw [eval_caseOpt_some (a := .nat) _ _ _ _ ci hf]
        let ρ3 := ReductionDsl.Env.cons (t := .nat) ci ρ2
        have hhc3 := fwdHonestCE_eval C K Dh encPt encT decT lam q
          (scBase (.fst (.fst .v3))) (.fst (.snd .v3)) (.fst (.snd (.snd .v3)))
          ρ3 sC.base Q w rfl rfl rfl hbnd.base.honest_le
        rw [eval_bind_ret _ _ _
          (dfStepEnc (sC, ex), (partyEnc Q, (w, (isDel, (pv, (honestC.map fig8CtV, ci))))))
          (by dsimp only [ReductionDsl.Expr.eval]; rw [hhc3]; rfl)]
        rw [Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.renComp_eval]
        exact fwdRecvSameC_eval C K idA idB Dh encPt encT decT lam qep q hℓ
          sC ex Q w isDel pq' i pk T? lct honestC ci hbnd hex hextra

end RecvFwdProofs

end

end Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStepRecvFwd

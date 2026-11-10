/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfSharedEval
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfCost
import VCVio.EvalDist.Monad.Basic

/-!
# Evaluation Equivalence and Wiring for `prfCkRedProg`

Proves list-length preservation and semantic evaluation equivalence between the `ReductionDsl`
`PrfChainKey` reduction `prfCkRedProg` and the shallow reduction `prfCkReductionAuthFixed`,
and shows both reductions have identical `PrfChainKey` advantage.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 100000
namespace SignalPqxdh.Security.ReductionDsl.AuthPrf

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh
open SignalPqxdh.LegacyCosted
open SignalPqxdh.Security
open SignalPqxdh.Security.AuthSubHops1to3
open RoKem
open FgGapDh
open OracleSpec OracleComp

@[simp] theorem authCodec_rdec_authRespToVal {S : Setup} (q : AuthQuery S) (r : AuthResponse) :
    (authCodec S).rdec q (authRespToVal r) = r :=
  authRdec_authRenc r

/-- Bounded state-representation simulation between `simulateQ (handlerImpl h)` over `pqPrimIface`
    and `runWithPrimStep`. -/
theorem simulateQ_prim_map_state_bounded {S : Setup} {σ : PT} {St α : Type}
    (f : St → σ.denote) (Inv : Nat → St → Prop)
    (hMono : ∀ {n m st}, n ≤ m → Inv n st → Inv m st)
    (step : (q : AuthQuery S) → St → OracleComp PrimBaseSpec ((authSpec S).Range q × St))
    (h : Comp pqxdhOps pqPrimIface [σ, authQueryTy] (.prod authRespTy σ))
    (K : Nat)
    (hStepEq : ∀ q st, Inv K st →
      h.eval (.cons (f st) (.cons (authQueryToVal q) .nil)) =
        Prod.map authRespToVal f <$> step q st)
    (hStepInv : ∀ n q st, Inv n st → HoldsOnLeaves (fun x => Inv (n + 1) x.2) (step q st))
    (mx : OracleComp (unifSpec + authSpec S) α) (rem : Nat)
    (hMx : IsQueryBoundP mx (fun q : ℕ ⊕ AuthQuery S => q.isRight = true) rem)
    (n : Nat) (st : St) (hInv : Inv n st) (hBound : n + rem ≤ K) :
    HoldsOnLeaves (fun x => Inv (n + rem) x.2) (runWithPrimStep step mx st) ∧
      (simulateQ (handlerImpl (C := authCodec S) h) mx).run (f st) =
        Prod.map id f <$> runWithPrimStep step mx st := by
  induction mx using OracleComp.inductionOn generalizing rem n st with
  | pure a =>
    refine ⟨HoldsOnLeaves.pure (hMono (by omega) hInv), ?_⟩
    rfl
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at hMx
    rcases q with uq | gq
    · have hCont : ∀ u, IsQueryBoundP (k u) (fun q : ℕ ⊕ AuthQuery S => q.isRight = true) rem := by
        intro u; simpa using hMx.2 u
      change HoldsOnLeaves (fun x => Inv (n + rem) x.2)
          (embedUnif (liftM (OracleSpec.query (spec := unifSpec) uq)) >>= fun u =>
            runWithPrimStep step (k u) st) ∧
        ((do let a ← pqPrimIface.fwdU uq; pure (a, f st)) >>= fun x =>
          (simulateQ (handlerImpl (C := authCodec S) h) (k x.1)).run x.2) =
        Prod.map id f <$>
          (embedUnif (liftM (OracleSpec.query (spec := unifSpec) uq)) >>= fun u =>
            runWithPrimStep step (k u) st)
      refine ⟨HoldsOnLeaves.bind_const _ (fun u => (ih u rem (hCont u) n st hInv hBound).1), ?_⟩
      simp only [pqPrimIface, embedUnif, bind_assoc, pure_bind, map_bind]
      congr 1; funext u
      exact (ih u rem (hCont u) n st hInv hBound).2
    · have hPos : 0 < rem := hMx.1.resolve_left (by simp)
      have hCont :
          ∀ r, IsQueryBoundP (k r) (fun q : ℕ ⊕ AuthQuery S => q.isRight = true) (rem - 1) := by
        intro r; simpa using hMx.2 r
      have hBound' : (n + 1) + (rem - 1) ≤ K := by omega
      have hAddEq : (n + 1) + (rem - 1) = n + rem := by omega
      have hInvK : Inv K st := hMono (by omega) hInv
      have hLeaves := hStepInv n gq st hInv
      change HoldsOnLeaves (fun x => Inv (n + rem) x.2)
          (step gq st >>= fun x => runWithPrimStep step (k x.1) x.2) ∧
        ((do let p ← h.eval (.cons (f st) (.cons (authQueryToVal gq) .nil))
             pure ((authCodec S).rdec gq p.1, p.2)) >>= fun x' =>
          (simulateQ (handlerImpl (C := authCodec S) h) (k x'.1)).run x'.2) =
        Prod.map id f <$> (step gq st >>= fun x => runWithPrimStep step (k x.1) x.2)
      refine ⟨HoldsOnLeaves.bind hLeaves (fun x hx => ?_), ?_⟩
      · rw [← hAddEq]
        exact (ih x.1 (rem - 1) (hCont x.1) (n + 1) x.2 hx hBound').1
      · rw [hStepEq gq st hInvK]
        simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, Prod.map,
          authCodec_rdec_authRespToVal]
        exact hLeaves.bind_congr _ _
          (fun x hx => by
            simpa [map_eq_bind_pure_comp] using
              (ih x.1 (rem - 1) (hCont x.1) (n + 1) x.2 hx hBound').2)

section PrfCkEval

variable (S : Setup) (K : Nat) {Γ Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}

theorem sampCkPairC_eval (ideal : Expr pqxdhOps Δ .bool) (env : Env Δ) :
    (sampCkPairC ideal).eval env = AuthSubHops1to3.sampCkPairPrim (ideal.eval env) := by
  cases h : ideal.eval env <;>
    simp [sampCkPairC, AuthSubHops1to3.sampCkPairPrim, letV, bindV, v, h,
      Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
      queryPrim_eval, evalPrimQ]

theorem caseOptV_eval_eq {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {τ υ : PT}
    (e : Expr pqxdhOps Γ (.opt τ)) (kNone : Comp pqxdhOps I Γ υ)
    (kSome : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) υ) (env : Env Γ)
    (val : Option τ.denote) :
    e.eval env = val →
    (caseOptV e kNone kSome).eval env =
      match val with
      | none => kNone.eval env
      | some a => (kSome .zero).eval (.cons a env) := by
  rintro rfl; exact caseOptV_eval e kNone kSome env

theorem iteC_eval_eq {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {υ : PT}
    (c : Expr pqxdhOps Γ .bool) (t e : Comp pqxdhOps I Γ υ) (env : Env Γ)
    (b : Bool) (h : c.eval env = b) :
    (Comp.ite c t e).eval env = (if b then t.eval env else e.eval env) := by
  simp only [Comp.eval, h]

theorem queryPrim_eval_eq {Γ : List PT} {t : PTag}
    (arg : Expr pqxdhOps Γ t.dom) (env : Env Γ) (val : t.dom.denote) (h : arg.eval env = val) :
    (queryPrim t arg).eval env = evalPrimOp t val := by
  simp only [queryPrim_eval, h, evalPrimQ]

theorem sampAtCkC_eval (idx : Expr pqxdhOps Δ .nat) (chalP : Expr pqxdhOps Δ (.prod (B 32) (B 32)))
    (s : Expr pqxdhOps Δ .nat) (env : Env Δ) :
    (sampAtCkC idx chalP s).eval env =
      AuthSubHops1to3.sampAtCkPrim (idx.eval env) (chalP.eval env) (s.eval env) := by
  simp only [sampAtCkC, AuthSubHops1to3.sampAtCkPrim, letV_eval, Comp.eval, v,
    Expr.eval, Ext.refl_wk, Env.get_zero, natEq_eval, sampCkPairC_eval, natLt_expr_eval]
  congr 1

theorem sampAtCkC_eval_eq (idx : Expr pqxdhOps Δ .nat) (chalP : Expr pqxdhOps Δ (.prod (B 32) (B 32)))
    (s : Expr pqxdhOps Δ .nat) (env : Env Δ) (idxv : Nat) (pv : Bytes × Bytes) (sv : Nat)
    (hidx : idx.eval env = idxv) (hchal : chalP.eval env = pv) (hs : s.eval env = sv) :
    (sampAtCkC idx chalP s).eval env =
      AuthSubHops1to3.sampAtCkPrim idxv pv sv := by
  rw [← hidx, ← hchal, ← hs]; exact sampAtCkC_eval idx chalP s env

theorem findHonestC_eval_eq (st : Var Γ authStateTy) [h : Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32))
    (env : Env Δ) (s : AuthState S) (ikv : Bytes)
    (hst : Env.get env (h.wk st) = authStateToVal s) (hik : ik.eval env = ikv)
    (hPrin : s.principals.length ≤ K) :
    (findHonestC S K st ik).eval env =
      Option.map (Prod.map id principalEntryToVal) <$>
        findHonestPrincipalPrim S s.principals ikv := by
  rw [← hik]; exact findHonestC_eval S st ik env s hst hPrin

theorem resolveSigPkC_eval_eq (st : Var Γ authStateTy) [h : Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32))
    (env : Env Δ) (s : AuthState S) (ikv : Bytes)
    (hst : Env.get env (h.wk st) = authStateToVal s) (hik : ik.eval env = ikv)
    (hPrin : s.principals.length ≤ K) :
    (resolveSigPkC S K st ik).eval env = resolveSigPkPrim S s.principals ikv := by
  rw [← hik]; exact resolveSigPkC_eval S st ik env s hst hPrin

theorem hkdfRoC_eval_eq (st : Var Γ authStateTy) [h : Ext Γ Δ] (sec : Expr pqxdhOps Δ (B 192))
    (env : Env Δ) (s : AuthState S) (secv : Bytes)
    (hst : Env.get env (h.wk st) = authStateToVal s) (hsec : sec.eval env = secv)
    (hRo : s.roCache.length ≤ K) :
    (hkdfRoC K st sec).eval env =
      Prod.map drKeyToVal (List.map (Prod.map id drKeyToVal)) <$>
        embedUnif (AuthSubHops1to3.evalHkdfRoPure s.roCache secv) := by
  rw [← hsec]; exact hkdfRoC_eval S K st sec env s hst hRo

theorem rootRoC_eval_eq (st : Var Γ authStateTy) [h : Ext Γ Δ] (rk dh : Expr pqxdhOps Δ (B 32))
    (env : Env Δ) (s : AuthState S) (rkv dhv : Bytes)
    (hst : Env.get env (h.wk st) = authStateToVal s)
    (hrk : rk.eval env = rkv) (hdh : dh.eval env = dhv)
    (hRoot : s.rootRoCache.length ≤ K) :
    (rootRoC K st rk dh).eval env =
      embedUnif (AuthSubHops1to3.evalRootKdfRoPure s.rootRoCache rkv dhv) := by
  rw [← hrk, ← hdh]; exact rootRoC_eval S K st rk dh env s hst hRoot

theorem finishAuthRecvCkC_eval (msg : Var Γ₁ preKeyMsgTy) (prep : Var Γ₂ preparedAuthRecvTy)
    (drKey : Expr pqxdhOps Δ drKeyTy) (rk1 : Expr pqxdhOps Δ (B 32)) (spqrSalt? : Expr pqxdhOps Δ (.opt (B 32)))
    (rc' : Expr pqxdhOps Δ .nat) (p : Expr pqxdhOps Δ (.prod (B 32) (B 32)))
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (env : Env Δ)
    (msgv : PreKeyMsg) (prepv : PreparedAuthRecvPrim S)
    (drKeyv : DRKey) (rk1v : Bytes) (spqrSaltv? : Option Bytes)
    (rcv' : Nat) (pv : Bytes × Bytes)
    (hmsg : Env.get env (h₁.wk msg) = preKeyMsgToVal msgv)
    (hprep : Env.get env (h₂.wk prep) = preparedAuthRecvToVal prepv)
    (hdrKey : drKey.eval env = drKeyToVal drKeyv)
    (hrk1 : rk1.eval env = rk1v)
    (hspqr : spqrSalt?.eval env = spqrSaltv?)
    (hrc : rc'.eval env = rcv')
    (hp : p.eval env = pv)
    (hOpk : prepv.finishTag.hstDec.base.opkEntries.length ≤ K)
    (hPrin : prepv.finishTag.hstDec.base.principals.length ≤ K)
    (hSentO : prepv.finishTag.hstDec.base.sentOPKEvents.length ≤ K := by
      first
      | exact (‹PreparedRecvBounded _ _›).tag_bounded.sentOPKEvents_le
      | exact (‹RecvTagBounded _ _›).sentOPKEvents_le
      | assumption)
    (hSentN : prepv.finishTag.hstDec.base.sentNoOPKEvents.length ≤ K := by
      first
      | exact (‹PreparedRecvBounded _ _›).tag_bounded.sentNoOPKEvents_le
      | exact (‹RecvTagBounded _ _›).sentNoOPKEvents_le
      | assumption) :
    (finishAuthRecvCkC S K msg prep drKey rk1 spqrSalt? rc' p).eval env =
      Prod.map authRespToVal authHybridStateFixedToVal <$>
        AuthSubHops1to3.finishAuthRecvCkPrim S msgv prepv drKeyv rk1v spqrSaltv? rcv' pv := by
  unfold finishAuthRecvCkC AuthSubHops1to3.finishAuthRecvCkPrim
    AuthSubHops1to3.finishAuthRecvCkSlotsPrim
  repeat' (rw [letV_eval]; simp only [v, ahsBase, parHstDec, parFinishTag,
    Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
    hprep, hdrKey, hrk1, hspqr, hrc, hp, preparedAuthRecvToVal, authHybridStateToVal])
  rw [bindV_eval]
  simp only [Expr.eval, queryPrim_eval, evalPrimQ,
    Env.get_succ, Env.get_zero, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  apply bind_congr; intro deriveMessageKeys
  rw [letV_eval]
  simp only [firstMsgADE_eval, pkmHdr, hdrIkAPk, parKEntry, peIkAPk, pkmEphAPk, pkmPqRatchetMsg,
    Expr.eval, Env.get_succ,
    hmsg, hprep, preKeyMsgToVal, preKeyMsgV, hdrV,
    preparedAuthRecvToVal, principalEntryToVal]
  rw [bindV_eval]
  simp only [Expr.eval, queryPrim_eval, evalPrimQ, pkmAeadCt,
    Env.get_succ, Env.get_zero]
  rw [hmsg]
  simp only [preKeyMsgToVal, preKeyMsgV]
  apply bind_congr; intro pt?
  rw [letV_eval, bindV_eval]
  rw [recvFinishTagRunC_eval S K _ _ _ prepv.finishTag
    (pt?.map fun pt =>
      (drKeyv, rk1v, pv.2, pt, prepv.hstDec.base.roCache, prepv.hstDec.base.rootRoCache))
    rfl ?_ hOpk hPrin (fun _ => hSentO) (fun _ => hSentN)]
  · simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, Prod.map]
    apply bind_congr; intro ⟨resp, hst'⟩
    simp only [Comp.eval, Expr.eval, Env.get_succ, Env.get_zero,
      authHybridStateFixedToVal, authHybridStateFixedWithSlotsToVal, authSlotStateToVal]
    rfl
  · cases pt? <;> simp [eCaseOpt, asRoCache, asRootRoCache, Expr.eval,
      authStateToVal, recvFinishResToVal]

theorem sendGuardE_eval {Γ : List PT} (opk : Bool) (x : Expr pqxdhOps Γ sendQTy) (env : Env Γ)
    (u i : Nat) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hx : x.eval env = (u, (i, (preKeyBundleToVal bundle, (m0, m1))))) :
    (sendGuardE opk x).eval env = (if opk then bundle.opkB?.isNone else bundle.opkB?.isSome) := by
  cases opk <;> cases h : bundle.opkB? <;>
    simp [sendGuardE, pkbOpkB?, Expr.eval, hx, preKeyBundleToVal, bundleV, h]

theorem eAny_usedSendSessions_eval (st : Var Γ₁ authStateTy) (sid : Var Γ₂ sessionIdTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (env : Env Δ)
    (baseSt : AuthState S) (sidv : SessionId S)
    (hst : Env.get env (h₁.wk st) = authStateToVal baseSt)
    (hsid : Env.get env (h₂.wk sid) = sessionIdToVal sidv)
    (hLen : baseSt.usedSendSessions.length ≤ K) :
    (eAny K (asUsedSendSessions (v st)) fun e => sidEq (v e) (v sid)).eval env =
      baseSt.usedSendSessions.contains sidv := by
  have hTake : (baseSt.usedSendSessions.map sessionIdToVal).take K =
      baseSt.usedSendSessions.map sessionIdToVal := by
    apply List.take_of_length_le; simpa using hLen
  simp only [eAny, asUsedSendSessions, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
    hst, authStateToVal, hTake, List.any_map]
  rw [Bool.eq_iff_iff, List.any_eq_true, List.contains_iff_exists_mem_beq]
  refine exists_congr (fun s => and_congr_right' ?_)
  have hEq := sidEq_eval (.var .zero) (.var (.succ (h₂.wk sid)))
    (.cons (sessionIdToVal s) env) s sidv rfl
    (by simp [Expr.eval, Env.get_succ, hsid, sessionIdToVal])
  change (sidEq (.var .zero) (.var (.succ (h₂.wk sid)))).eval
    (.cons (sessionIdToVal s) env) = true ↔ (sidv == s) = true
  rw [hEq, BEq.comm]

theorem isFreshE_eval (pp : Var Γ₁ (.opt (.prod .nat principalEntryTy)))
    [h₁ : Ext Γ₁ Δ] (env : Env Δ)
    (peerPrincipal? : Option (Nat × PrincipalEntry)) :
    Env.get env (h₁.wk pp) = peerPrincipal?.map (Prod.map id principalEntryToVal) →
    (eCaseOpt (v pp) (.bool false) fun p => .not (peCorrupted (.snd (v p)))).eval env =
      match peerPrincipal? with
      | some (_, pEntry) => !pEntry.corrupted
      | none             => false := by
  intro hpp
  cases peerPrincipal? with
  | none => simp [eCaseOpt, v, Expr.eval, hpp]
  | some pP =>
    rcases pP with ⟨pIdx, pEntry⟩
    simp [eCaseOpt, peCorrupted, v, Expr.eval, Ext.refl_wk, hpp,
      Prod.map, principalEntryToVal]

theorem pqspkHonE_eval (pp : Var Γ₁ (.opt (.prod .nat principalEntryTy)))
    (st : Var Γ₂ authStateTy) (bu : Var Γ₃ preKeyBundleTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] (env : Env Δ)
    (peerPrincipal? : Option (Nat × PrincipalEntry))
    (baseSt : AuthState S) (bundle : PreKeyBundleInput)
    (hpp : Env.get env (h₁.wk pp) = peerPrincipal?.map (Prod.map id principalEntryToVal))
    (hst : Env.get env (h₂.wk st) = authStateToVal baseSt)
    (hbu : Env.get env (h₃.wk bu) = preKeyBundleToVal bundle)
    (hSpk : baseSt.spkBundles.length ≤ K) :
    (eCaseOpt (v pp) (.bool false) fun p =>
      eAny K (asSpkBundles (v st)) fun b =>
        .and (natEq (.fst (.fst (v b))) (.fst (v p)))
          (bytesBeq 1568 (sbPqspkPk (.snd (v b))) (pkbPqspkB (v bu)))).eval env =
      (peerPrincipal?.map (fun p =>
        baseSt.spkBundles.any
          (fun ((u, _), b) => u == p.1 && b.pqspkPk == bundle.pqspkB))).getD false := by
  have hTakeS : (baseSt.spkBundles.map (Prod.map id spkBundleEntryToVal)).take K =
      baseSt.spkBundles.map (Prod.map id spkBundleEntryToVal) := by
    apply List.take_of_length_le; simpa using hSpk
  cases peerPrincipal? with
  | none =>
    simp [eCaseOpt, v, Expr.eval, hpp]
  | some pP =>
    rcases pP with ⟨pIdx, pEntry⟩
    simp [eCaseOpt, eAny, asSpkBundles, sbPqspkPk, pkbPqspkB, natEq_eval, bytesBeq_eval, v,
      Expr.eval, Ext.step_wk, Ext.refl_wk,
      hpp, hst, hbu, authStateToVal, hTakeS, List.any_map, Function.comp_def,
      Prod.map, spkBundleEntryToVal, preKeyBundleToVal, bundleV]

theorem sendSidE_eval {Γ : List PT} (opk : Bool) (x : Expr pqxdhOps Γ sendQTy) (env : Env Γ)
    (u i : Nat) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hx : x.eval env = (u, (i, (preKeyBundleToVal bundle, (m0, m1))))) :
    (if opk then Expr.inl (.pair (.fst x) (.fst (.snd x)))
      else .inr (.inl (.pair (.fst x) (.fst (.snd x)))) : Expr pqxdhOps Γ sessionIdTy).eval env =
    (if opk then Sum.inl (u, i) else Sum.inr (Sum.inl (u, i))) := by
  cases opk <;> simp [Expr.eval, hx]

theorem dh4OptC_eval (bu : Var Γ₁ preKeyBundleTy) (ekASk : Var Γ₂ (B 32))
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (env : Env Δ)
    (bundle : PreKeyBundleInput) (ekv : Bytes)
    (hbu : Env.get env (h₁.wk bu) = preKeyBundleToVal bundle)
    (hek : Env.get env (h₂.wk ekASk) = ekv) :
    (caseOptV (pkbOpkB? (v bu)) (.ret .none) fun oP =>
      bindV (queryPrim .x25519 (.pair (v ekASk) (.snd (v oP)))) fun d4 =>
      .ret (.some (v d4)) : Comp pqxdhOps pqPrimIface Δ (.opt (B 32))).eval env =
    Option.casesOn bundle.opkB? (pure none) (fun (_, opkPk) => do
      let d4 ← primQ (.x25519 ekv opkPk)
      pure (some d4)) := by
  cases hOpkB : bundle.opkB? with
  | none =>
    simp [caseOptV, pkbOpkB?, v, Comp.eval, Expr.eval, hbu, preKeyBundleToVal, bundleV, hOpkB]
  | some oP =>
    rcases oP with ⟨opkId, opkPk⟩
    simp only [caseOptV, bindV, pkbOpkB?, v, Comp.eval, Expr.eval, queryPrim_eval, evalPrimQ,
      Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
      hbu, hek, preKeyBundleToVal, bundleV, hOpkB]

private theorem allocSendSlotE_eval {Γ : List PT}
    (ss : Expr pqxdhOps Γ authSlotStateTy) (sid : Expr pqxdhOps Γ sessionIdTy)
    (env : Env Γ) (ssv : AuthSlotState) (sidv : SessionId S)
    (hss : ss.eval env = authSlotStateToVal ssv)
    (hsid : sid.eval env = sessionIdToVal sidv) :
    (allocSendSlotE ss sid).eval env =
      Prod.map id authSlotStateToVal (ssv.allocSend sidv) := by
  cases sidv with
  | sendOPK u i =>
    simp only [allocSendSlotE, AuthSlotState.allocSend, eLet2, eLet, eCaseSum, eCaseOpt,
      assNext, assSendOpk, assSendNoOpk, assRecv, assMk, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
      Env.get_succ, Env.get_zero, hss, hsid, authSlotStateToVal, sessionIdToVal, sidV]
    cases ssv.sendOpkTbl u.1 i.1 <;> rfl
  | sendNoOPK u i =>
    simp only [allocSendSlotE, AuthSlotState.allocSend, eLet2, eLet, eCaseSum, eCaseOpt,
      assNext, assSendOpk, assSendNoOpk, assRecv, assMk, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
      Env.get_succ, Env.get_zero, hss, hsid, authSlotStateToVal, sessionIdToVal, sidV]
    cases ssv.sendNoOpkTbl u.1 i.1 <;> rfl
  | recvOPK _ _ _ =>
    simp only [allocSendSlotE, AuthSlotState.allocSend, eLet2, eLet, eCaseSum, v, Expr.eval,
      Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, hss, hsid,
      authSlotStateToVal, sessionIdToVal, sidV, Prod.map, id_eq]
  | recvNoOPK _ _ _ =>
    simp only [allocSendSlotE, AuthSlotState.allocSend, eLet2, eLet, eCaseSum, v, Expr.eval,
      Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, hss, hsid,
      authSlotStateToVal, sessionIdToVal, sidV, Prod.map, id_eq]

private theorem allocRecvSlotE_eval {Γ : List PT}
    (ss : Expr pqxdhOps Γ authSlotStateTy) (rc : Expr pqxdhOps Γ .nat)
    (env : Env Γ) (ssv : AuthSlotState) (rcv : Nat)
    (hss : ss.eval env = authSlotStateToVal ssv)
    (hrc : rc.eval env = rcv) :
    (allocRecvSlotE ss rc).eval env =
      Prod.map id authSlotStateToVal (ssv.allocRecv rcv) := by
  simp only [allocRecvSlotE, AuthSlotState.allocRecv, eLet2, eLet, eCaseOpt,
    assNext, assSendOpk, assSendNoOpk, assRecv, assMk, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
    Env.get_succ, Env.get_zero, hss, hrc, authSlotStateToVal]
  cases ssv.recvTbl rcv <;> rfl

private def ckFreshPeer (peerPrincipal? : Option (Nat × PrincipalEntry)) : Bool :=
  match peerPrincipal? with
  | some (_, pEntry) => !pEntry.corrupted
  | none => false

private theorem ck_ite_bind {m : Type → Type} [Monad m] {α β : Type} {c : Prop} [Decidable c]
    (x y : m α) (f : α → m β) :
    ((if c then x else y) >>= f) = if c then x >>= f else y >>= f := by
  split <;> rfl

private theorem ck_ite_eq {α : Type _} {c₁ c₂ : Prop} [Decidable c₁] [Decidable c₂]
    {t₁ e₁ t₂ e₂ : α} (hc : c₁ ↔ c₂) (ht : c₁ → t₁ = t₂) (he : ¬ c₁ → e₁ = e₂) :
    (if c₁ then t₁ else e₁) = (if c₂ then t₂ else e₂) := by
  by_cases h : c₁
  · simp only [h, hc.mp h, ↓reduceIte]; exact ht h
  · have h₂ : ¬ c₂ := fun h' => h (hc.mpr h')
    simp only [h, h₂, ↓reduceIte]; exact he h

syntax "ck_eval" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| ck_eval [$extra,*]) =>
    `(tactic| simp only [v, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk,
      Env.get_succ, Env.get_zero, drKeyToVal, drKeyV, preKeyBundleToVal, bundleV,
      principalEntryToVal, authStateToVal, authHybridStateFixedToVal,
      authHybridStateFixedWithSlotsToVal, authSlotStateToVal,
      authRespToVal, authRenc, aNone, ahsfMk, ahsfMkSlots, ahsfUpd, ahsfUpdSlots,
      ahsfRecvCount, ahsfSlots, asRoCache, asRootRoCache,
      finishSendArgsToVal, litB_eval, List.map_nil,
      firstMsgADE_eval, peIkAPk, pkbIkB, pkbSpkB, natEq_eval, bytesBeq_eval,
      boolOr_eval, isSomeE_eval, Option.isSome_map, Prod.map, id_eq, pure_bind, map_pure, bne, $extra,*])

private theorem authCkSendB_ideal_eval
    {Γ₀ Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Γ₇ Γ₈ Γ₉ Γ₁₀ Γ₁₁ Γ₁₂ Γ₁₃ Γ₁₄ Γ₁₅ Γ₁₆ Γ₁₇ Δ : List PT}
    {noneDone : Var Γ₀ RSF}
    {idx : Var Γ₁ .nat} {chalP : Var Γ₂ (.prod (B 32) (B 32))}
    {fhst : Var Γ₃ authHybridStateFixedTy} {hst : Var Γ₄ authHybridStateTy}
    {st : Var Γ₅ authStateTy} {bu : Var Γ₆ preKeyBundleTy}
    {m0 : Var Γ₇ (B 32)} {m1 : Var Γ₈ (B 32)}
    {sid : Var Γ₉ sessionIdTy} {uE : Var Γ₁₀ principalEntryTy}
    {pp : Var Γ₁₁ (.opt (.prod .nat principalEntryTy))} {isFresh : Var Γ₁₂ .bool}
    {msgPlain : Var Γ₁₃ (B 32)} {spqrCoins : Var Γ₁₄ (B 32)}
    {ephAPk : Var Γ₁₅ (B 32)} {keys6 : Var Γ₁₆ keys6Ty}
    {ss : Var Γ₁₇ authSlotStateTy}
    [h₀ : Ext Γ₀ Δ]
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] [h₄ : Ext Γ₄ Δ]
    [h₅ : Ext Γ₅ Δ] [h₆ : Ext Γ₆ Δ] [h₇ : Ext Γ₇ Δ] [h₈ : Ext Γ₈ Δ]
    [h₉ : Ext Γ₉ Δ] [h₁₀ : Ext Γ₁₀ Δ] [h₁₁ : Ext Γ₁₁ Δ] [h₁₂ : Ext Γ₁₂ Δ]
    [h₁₃ : Ext Γ₁₃ Δ] [h₁₄ : Ext Γ₁₄ Δ] [h₁₅ : Ext Γ₁₅ Δ] [h₁₆ : Ext Γ₁₆ Δ]
    [h₁₇ : Ext Γ₁₇ Δ]
    {env : Env Δ}
    (idxv : Nat) (pv : Bytes × Bytes) (s : AuthHybridStateFixed S)
    (sidv : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry))
    (bundle : PreKeyBundleInput) (m0v m1v msgPlainv spqrCoinsv : Bytes)
    (ekASk ekAPk ssKem kemCt ephASk ephAPkv : Bytes)
    (hnd : Env.get env (h₀.wk noneDone) = (authRespToVal .noneResp, authHybridStateFixedToVal s))
    (hidx : Env.get env (h₁.wk idx) = idxv)
    (hchal : Env.get env (h₂.wk chalP) = pv)
    (hfhst : Env.get env (h₃.wk fhst) = authHybridStateFixedToVal s)
    (hhst : Env.get env (h₄.wk hst) = authHybridStateToVal s.toAuthHybridState)
    (hstV : Env.get env (h₅.wk st) = authStateToVal s.toAuthHybridState.base)
    (hbu : Env.get env (h₆.wk bu) = preKeyBundleToVal bundle)
    (hm0 : Env.get env (h₇.wk m0) = m0v)
    (hm1 : Env.get env (h₈.wk m1) = m1v)
    (hsid : Env.get env (h₉.wk sid) = sessionIdToVal sidv)
    (huE : Env.get env (h₁₀.wk uE) = principalEntryToVal uEntry)
    (hpp : Env.get env (h₁₁.wk pp) = peerPrincipal?.map (Prod.map id principalEntryToVal))
    (hfr : Env.get env (h₁₂.wk isFresh) = ckFreshPeer peerPrincipal?)
    (hpl : Env.get env (h₁₃.wk msgPlain) = msgPlainv)
    (hspqr : Env.get env (h₁₄.wk spqrCoins) = spqrCoinsv)
    (hephPk : Env.get env (h₁₅.wk ephAPk) = ephAPkv)
    (hk6 : Env.get env (h₁₆.wk keys6) = (ekASk, (ekAPk, (ssKem, (kemCt, (ephASk, ephAPkv))))))
    (hss : Env.get env (h₁₇.wk ss) = authSlotStateToVal s.slots)
    (hSpk : s.toAuthHybridState.base.spkBundles.length ≤ K)
    (hPrin : s.toAuthHybridState.base.principals.length ≤ K)
    (hOpk : s.toAuthHybridState.base.opkEntries.length ≤ K) :
    (bindV (samplePrim .drKey96) fun drKey =>
     bindV (samplePrim .bytes32) fun rk1 =>
     bindV (queryPrim (.spqrInitSend 32 32)
       (.pair (.snd (.snd (v drKey))) (v spqrCoins))) fun sp? =>
     caseOptV (v sp?) (.ret (v noneDone)) fun sp =>
     letV (.fst (.snd (v sp))) fun spqrSalt? =>
     letV (.snd (.snd (v sp))) fun pqMsg =>
     letV (allocSendSlotE (v ss) (v sid)) fun sa =>
     bindV (sampAtCkC (v idx) (v chalP) (.fst (v sa))) fun p =>
     letV (.fst (v p)) fun mkSeed =>
     letV (.snd (v p)) fun ck1_1 =>
     bindV (queryPrim (.deriveMsgKeys 32) (.pair (v mkSeed) (v spqrSalt?))) fun mks =>
     letV (firstMsgADE (peIkAPk (v uE)) (pkbIkB (v bu)) (v ephAPk) (v pqMsg)) fun ad =>
     bindV (queryPrim (.aeadEnc 158 32 32)
       (.pair (v mks) (.pair (v ad) (v msgPlain)))) fun aeadCt =>
     bindV (finishAuthHybridSendC S K hst
       (.pair (v sid) (.pair (v uE) (.pair (v pp) (.pair (v isFresh) (.pair (v bu)
         (.pair (.pair (v m0) (v m1)) (.pair (v keys6)
           (.pair (v drKey) (.pair (.pair (v rk1) (.pair (litB 32 [])
             (.pair (v mkSeed) (v ck1_1))))
             (.pair (v spqrSalt?) (.pair (v pqMsg) (.pair (v mks)
               (.pair (v ad) (.pair (v aeadCt) (.pair (v msgPlain)
                 (.pair (asRoCache (v st)) (asRootRoCache (v st))))))))))))))))))) fun out =>
     .ret (.pair (.fst (v out))
       (ahsfMkSlots (.snd (v out)) (ahsfRecvCount (v fhst)) .nil (.snd (v sa))))).eval env =
    ((do
        let drKey ← embedUnif sampleDRKey96
        let rk1 ← embedUnif sampleBytes32
        match ← primQ (.spqrInitSend drKey.pqrKey spqrCoinsv) with
        | none => return (AuthResponse.noneResp, s)
        | some (_pqrStA, spqrSalt?, pqRatchetMsg) =>
          let (sIdx, slots') := s.slots.allocSend sidv
          let p ← AuthSubHops1to3.sampAtCkPrim idxv pv sIdx
          AuthSubHops1to3.finishAuthSendCkPrim S sidv uEntry peerPrincipal? bundle m0v m1v
            ekASk ekAPk ssKem kemCt ephASk ephAPkv drKey rk1 spqrSalt?
            pqRatchetMsg msgPlainv { s with slots := slots' } p) >>=
      fun x => pure (Prod.map authRespToVal authHybridStateFixedToVal x)) := by
  simp only [bind_assoc]
  rw [bindV_eval, samplePrim_drKey96_eval]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  apply bind_congr; intro drKey
  rw [bindV_eval, samplePrim_bytes32_eval]; try simp only [bind_assoc]
  apply bind_congr; intro rk1
  rw [bindV_eval, queryPrim_eval_eq _ _ (drKey.pqrKey, spqrCoinsv)
    (by ck_eval [hspqr])]
  dsimp only [evalPrimOp]; try simp only [bind_assoc]
  apply bind_congr; intro sp?
  rw [caseOptV_eval_eq _ _ _ _ sp? rfl]
  cases sp? with
  | none =>
    ck_eval [hnd]
  | some sp =>
    rcases sp with ⟨pqrStA, spqrSalt?, pqRatchetMsg⟩
    dsimp only
    rw [letV_eval_eq _ _ _ spqrSalt? rfl]
    rw [letV_eval_eq _ _ _ pqRatchetMsg rfl]
    let saVal := s.slots.allocSend sidv
    rw [letV_eval_eq _ _ _ (Prod.map id authSlotStateToVal saVal)
      (by exact allocSendSlotE_eval S _ _ _ s.slots sidv (by ck_eval [hss]) (by ck_eval [hsid]))]
    rw [bindV_eval, sampAtCkC_eval_eq _ _ _ _ idxv pv saVal.1
      (by ck_eval [hidx])
      (by ck_eval [hchal])
      (by ck_eval [])]
    try simp only [bind_assoc]
    apply bind_congr; intro p
    rcases p with ⟨mkSeed, ck1_1⟩
    unfold AuthSubHops1to3.finishAuthSendCkPrim
    dsimp only
    rw [letV_eval_eq _ _ _ mkSeed rfl]
    rw [letV_eval_eq _ _ _ ck1_1 rfl]
    rw [bindV_eval, queryPrim_eval_eq _ _ (mkSeed, spqrSalt?) rfl]
    dsimp only [evalPrimOp]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
    apply bind_congr; intro mks
    rw [letV_eval_eq _ _ _
      (firstMsgAD uEntry.ikAPk bundle.ikB ephAPkv pqRatchetMsg)
      (by ck_eval [huE, hbu, hephPk])]
    rw [bindV_eval, queryPrim_eval_eq _ _
      (msgKeysToVal mks,
        (firstMsgAD uEntry.ikAPk bundle.ikB ephAPkv pqRatchetMsg, msgPlainv))
      (by ck_eval [hpl])]
    dsimp only [evalPrimOp]
    rw [valToMsgKeys_msgKeysToVal]; try simp only [bind_assoc]
    apply bind_congr; intro aeadCt
    rw [bindV_eval]
    rw [finishAuthHybridSendC_eval S K _ _ _ sidv uEntry peerPrincipal?
      (ckFreshPeer peerPrincipal?)
      bundle m0v m1v ekASk ekAPk ssKem kemCt ephASk ephAPkv
      drKey rk1 [] mkSeed ck1_1 spqrSalt? pqRatchetMsg mks
      (firstMsgAD uEntry.ikAPk bundle.ikB ephAPkv pqRatchetMsg)
      aeadCt msgPlainv s.toAuthHybridState.base.roCache
      s.toAuthHybridState.base.rootRoCache s.toAuthHybridState
      (by simp [Ext.step_wk, hhst])
      (by ck_eval [hsid, huE, hpp, hfr, hbu, hm0, hm1, hk6, hpl, hstV])
      hSpk hPrin hOpk]
    dsimp only [ckFreshPeer]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, Prod.map]
    apply bind_congr; intro ⟨resp, hst'⟩
    ck_eval [hfhst, saVal]

private theorem authCkSendB_real_eval
    {Γ₀ Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Γ₇ Γ₈ Γ₉ Γ₁₀ Γ₁₁ Γ₁₂ Γ₁₃ Γ₁₄ Γ₁₅ Γ₁₆ Γ₁₇ Γ₁₈ Δ : List PT}
    {noneDone : Var Γ₀ RSF}
    {fhst : Var Γ₁ authHybridStateFixedTy} {hst : Var Γ₂ authHybridStateTy}
    {st : Var Γ₃ authStateTy} {bu : Var Γ₄ preKeyBundleTy}
    {m0 : Var Γ₅ (B 32)} {m1 : Var Γ₆ (B 32)}
    {sid : Var Γ₇ sessionIdTy} {uE : Var Γ₈ principalEntryTy}
    {pp : Var Γ₉ (.opt (.prod .nat principalEntryTy))} {isFresh : Var Γ₁₀ .bool}
    {msgPlain : Var Γ₁₁ (B 32)} {ekASk : Var Γ₁₂ (B 32)}
    {ephASk : Var Γ₁₃ (B 32)} {spqrCoins : Var Γ₁₄ (B 32)}
    {ssKem : Var Γ₁₅ (B 32)} {ephAPk : Var Γ₁₆ (B 32)} {keys6 : Var Γ₁₇ keys6Ty}
    {ss : Var Γ₁₈ authSlotStateTy}
    [h₀ : Ext Γ₀ Δ]
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] [h₄ : Ext Γ₄ Δ]
    [h₅ : Ext Γ₅ Δ] [h₆ : Ext Γ₆ Δ] [h₇ : Ext Γ₇ Δ] [h₈ : Ext Γ₈ Δ]
    [h₉ : Ext Γ₉ Δ] [h₁₀ : Ext Γ₁₀ Δ] [h₁₁ : Ext Γ₁₁ Δ] [h₁₂ : Ext Γ₁₂ Δ]
    [h₁₃ : Ext Γ₁₃ Δ] [h₁₄ : Ext Γ₁₄ Δ] [h₁₅ : Ext Γ₁₅ Δ] [h₁₆ : Ext Γ₁₆ Δ]
    [h₁₇ : Ext Γ₁₇ Δ] [h₁₈ : Ext Γ₁₈ Δ]
    {env : Env Δ}
    (s : AuthHybridStateFixed S)
    (sidv : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry)) (isFreshPeer : Bool)
    (bundle : PreKeyBundleInput) (m0v m1v msgPlainv : Bytes)
    (ekASkv ekAPkv ssv kemCtv ephASkv ephAPkv spqrCoinsv : Bytes)
    (hnd : Env.get env (h₀.wk noneDone) = (authRespToVal .noneResp, authHybridStateFixedToVal s))
    (hfhst : Env.get env (h₁.wk fhst) = authHybridStateFixedToVal s)
    (hhst : Env.get env (h₂.wk hst) = authHybridStateToVal s.toAuthHybridState)
    (hstV : Env.get env (h₃.wk st) = authStateToVal s.toAuthHybridState.base)
    (hbu : Env.get env (h₄.wk bu) = preKeyBundleToVal bundle)
    (hm0 : Env.get env (h₅.wk m0) = m0v)
    (hm1 : Env.get env (h₆.wk m1) = m1v)
    (hsid : Env.get env (h₇.wk sid) = sessionIdToVal sidv)
    (huE : Env.get env (h₈.wk uE) = principalEntryToVal uEntry)
    (hpp : Env.get env (h₉.wk pp) = peerPrincipal?.map (Prod.map id principalEntryToVal))
    (hfr : Env.get env (h₁₀.wk isFresh) = isFreshPeer)
    (hpl : Env.get env (h₁₁.wk msgPlain) = msgPlainv)
    (hekSk : Env.get env (h₁₂.wk ekASk) = ekASkv)
    (hephSk : Env.get env (h₁₃.wk ephASk) = ephASkv)
    (hspqr : Env.get env (h₁₄.wk spqrCoins) = spqrCoinsv)
    (hssKem : Env.get env (h₁₅.wk ssKem) = ssv)
    (hephPk : Env.get env (h₁₆.wk ephAPk) = ephAPkv)
    (hk6 : Env.get env (h₁₇.wk keys6) =
      (ekASkv, (ekAPkv, (ssv, (kemCtv, (ephASkv, ephAPkv))))))
    (hss : Env.get env (h₁₈.wk ss) = authSlotStateToVal s.slots)
    (hB : AuthListsBounded K s) :
    (bindV (queryPrim .x25519 (.pair (peSecIKA0 (v uE)) (pkbSpkB (v bu)))) fun dh1 =>
     bindV (queryPrim .x25519 (.pair (v ekASk) (pkbIkB (v bu)))) fun dh2 =>
     bindV (queryPrim .x25519 (.pair (v ekASk) (pkbSpkB (v bu)))) fun dh3 =>
     bindV (caseOptV (pkbOpkB? (v bu)) (.ret .none) fun oP =>
       bindV (queryPrim .x25519 (.pair (v ekASk) (.snd (v oP)))) fun d4 =>
       .ret (.some (v d4))) fun dh4? =>
     letV (buildSecretsE (v dh1) (v dh2) (v dh3) (v dh4?) (v ssKem)) fun secrets =>
     bindV (hkdfRoC K st (v secrets)) fun drOut =>
     letV (.fst (v drOut)) fun drKey =>
     letV (.snd (v drOut)) fun roC' =>
     bindV (queryPrim .x25519 (.pair (v ephASk) (pkbSpkB (v bu)))) fun dhR =>
     bindV (rootRoC K st (.fst (v drKey)) (v dhR)) fun rkOut =>
     letV (.fst (.fst (v rkOut))) fun rk1 =>
     letV (.snd (.fst (v rkOut))) fun ck1_0 =>
     letV (.snd (v rkOut)) fun rootC' =>
     bindV (queryPrim .chainKdfSeed (v ck1_0)) fun mkSeed =>
     bindV (queryPrim .chainKdfNext (v ck1_0)) fun ck1_1 =>
     bindV (queryPrim (.spqrInitSend 32 32)
       (.pair (.snd (.snd (v drKey))) (v spqrCoins))) fun sp? =>
     caseOptV (v sp?) (.ret (v noneDone)) fun sp =>
     letV (.fst (.snd (v sp))) fun spqrSalt? =>
     letV (.snd (.snd (v sp))) fun pqMsg =>
     bindV (queryPrim (.deriveMsgKeys 32) (.pair (v mkSeed) (v spqrSalt?))) fun mks =>
     letV (firstMsgADE (peIkAPk (v uE)) (pkbIkB (v bu)) (v ephAPk) (v pqMsg)) fun ad =>
     bindV (queryPrim (.aeadEnc 158 32 32)
       (.pair (v mks) (.pair (v ad) (v msgPlain)))) fun aeadCt =>
     bindV (finishAuthHybridSendC S K hst
       (.pair (v sid) (.pair (v uE) (.pair (v pp) (.pair (v isFresh) (.pair (v bu)
         (.pair (.pair (v m0) (v m1)) (.pair (v keys6)
           (.pair (v drKey) (.pair (.pair (v rk1) (.pair (v ck1_0) (.pair (v mkSeed) (v ck1_1))))
             (.pair (v spqrSalt?) (.pair (v pqMsg) (.pair (v mks)
               (.pair (v ad) (.pair (v aeadCt) (.pair (v msgPlain)
                 (.pair (v roC') (v rootC')))))))))))))))))) fun out =>
     .ret (.pair (.fst (v out))
       (ahsfMkSlots (.snd (v out)) (ahsfRecvCount (v fhst)) .nil (v ss)))).eval env =
    ((do
        let dh1 ← primQ (.x25519 uEntry.secIKA0 bundle.spkB)
        let dh2 ← primQ (.x25519 ekASkv bundle.ikB)
        let dh3 ← primQ (.x25519 ekASkv bundle.spkB)
        let dh4? ←
          Option.casesOn bundle.opkB? (pure none) (fun (_, opkPk) => do
            let d4 ← primQ (.x25519 ekASkv opkPk)
            pure (some d4))
        let secrets := buildSecrets dh1 dh2 dh3 dh4? ssv
        let (drKey, roCache') ←
          embedUnif (AuthSubHops1to3.evalHkdfRoPure s.toAuthHybridState.base.roCache secrets)
        let dhRatchet ← primQ (.x25519 ephASkv bundle.spkB)
        let ((rk1, ck1_0), rootRoCache') ←
          embedUnif (AuthSubHops1to3.evalRootKdfRoPure s.toAuthHybridState.base.rootRoCache
            drKey.rootKey dhRatchet)
        let mkSeed ← primQ (.chainKdfSeed ck1_0)
        let ck1_1 ← primQ (.chainKdfNext ck1_0)
        match ← primQ (.spqrInitSend drKey.pqrKey spqrCoinsv) with
        | none => return (AuthResponse.noneResp, s)
        | some (_pqrStA, spqrSalt?, pqRatchetMsg) =>
          let deriveMessageKeys ← primQ (.deriveMsgKeys mkSeed spqrSalt?)
          let ad := firstMsgAD uEntry.ikAPk bundle.ikB ephAPkv pqRatchetMsg
          let aeadCt ← primQ (.aeadEnc deriveMessageKeys ad msgPlainv)
          let (resp, hst') ←
            AuthSubHops1to3.finishAuthHybridSendPrim S sidv uEntry peerPrincipal? isFreshPeer
              bundle m0v m1v ekASkv ekAPkv ssv kemCtv ephASkv ephAPkv drKey rk1 ck1_0 mkSeed ck1_1
              spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlainv roCache' rootRoCache'
              s.toAuthHybridState
          return (resp, { toAuthHybridState := hst', recvCount := s.recvCount,
                          slots := s.slots })) >>=
      fun x => pure (Prod.map authRespToVal authHybridStateFixedToVal x)) := by
  simp only [bind_assoc]
  rw [bindV_eval, queryPrim_eval_eq _ _ (uEntry.secIKA0, bundle.spkB)
    (by simp [v, peSecIKA0, pkbSpkB, Expr.eval, huE, hbu, principalEntryToVal, preKeyBundleToVal,
      bundleV])]
  dsimp only [evalPrimOp]; try simp only [bind_assoc]
  apply bind_congr; intro dh1
  rw [bindV_eval, queryPrim_eval_eq _ _ (ekASkv, bundle.ikB)
    (by simp [v, pkbIkB, Expr.eval, Ext.step_wk, hekSk, hbu, preKeyBundleToVal, bundleV])]
  dsimp only [evalPrimOp]; try simp only [bind_assoc]
  apply bind_congr; intro dh2
  rw [bindV_eval, queryPrim_eval_eq _ _ (ekASkv, bundle.spkB)
    (by simp [v, pkbSpkB, Expr.eval, Ext.step_wk, hekSk, hbu, preKeyBundleToVal, bundleV])]
  dsimp only [evalPrimOp]; try simp only [bind_assoc]
  apply bind_congr; intro dh3
  rw [bindV_eval, dh4OptC_eval _ _ _ bundle ekASkv
    (by simp [Ext.step_wk, hbu]) (by simp [Ext.step_wk, hekSk])]
  apply bind_congr; intro dh4?
  let secrets := buildSecrets dh1 dh2 dh3 dh4? ssv
  rw [letV_eval_eq _ _ _ secrets
    (by simp [secrets, v, buildSecretsE_eval, Expr.eval, Ext.step_wk, Ext.refl_wk, hssKem])]
  rw [bindV_eval,
    hkdfRoC_eval_eq S K _ _ _ s.toAuthHybridState.base secrets
      (by simp [Ext.step_wk, hstV]) rfl hB.roCache_le]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, Prod.map]
  apply bind_congr; intro ⟨drKey, roCache'⟩
  rw [letV_eval_eq _ _ _ (drKeyToVal drKey) rfl]
  rw [letV_eval_eq _ _ _ (roCache'.map (Prod.map id drKeyToVal)) rfl]
  rw [bindV_eval, queryPrim_eval_eq _ _ (ephASkv, bundle.spkB)
    (by ck_eval [hephSk, hbu])]
  dsimp only [evalPrimOp]; try simp only [bind_assoc]
  apply bind_congr; intro dhRatchet
  rw [bindV_eval,
    rootRoC_eval_eq S K _ _ _ _ s.toAuthHybridState.base drKey.rootKey dhRatchet
      (by simp [Ext.step_wk, hstV])
      (by ck_eval []) rfl hB.rootRoCache_le]
  try simp only [bind_assoc]
  apply bind_congr; intro ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
  rw [letV_eval_eq _ _ _ rk1 rfl]
  rw [letV_eval_eq _ _ _ ck1_0 rfl]
  rw [letV_eval_eq _ _ _ rootRoCache' rfl]
  rw [bindV_eval, queryPrim_eval_eq _ _ ck1_0 rfl]
  dsimp only [evalPrimOp]; try simp only [bind_assoc]
  apply bind_congr; intro mkSeed
  rw [bindV_eval, queryPrim_eval_eq _ _ ck1_0 rfl]
  dsimp only [evalPrimOp]; try simp only [bind_assoc]
  apply bind_congr; intro ck1_1
  rw [bindV_eval, queryPrim_eval_eq _ _ (drKey.pqrKey, spqrCoinsv)
    (by ck_eval [hspqr])]
  dsimp only [evalPrimOp]; try simp only [bind_assoc]
  apply bind_congr; intro sp?
  rw [caseOptV_eval_eq _ _ _ _ sp? rfl]
  cases sp? with
  | none =>
    ck_eval [hnd]
  | some sp =>
    rcases sp with ⟨pqrStA, spqrSalt?, pqRatchetMsg⟩
    dsimp only
    rw [letV_eval_eq _ _ _ spqrSalt? rfl]
    rw [letV_eval_eq _ _ _ pqRatchetMsg rfl]
    rw [bindV_eval, queryPrim_eval_eq _ _ (mkSeed, spqrSalt?) rfl]
    dsimp only [evalPrimOp]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
    apply bind_congr; intro mks
    rw [letV_eval_eq _ _ _
      (firstMsgAD uEntry.ikAPk bundle.ikB ephAPkv pqRatchetMsg)
      (by ck_eval [huE, hbu, hephPk])]
    rw [bindV_eval, queryPrim_eval_eq _ _
      (msgKeysToVal mks,
        (firstMsgAD uEntry.ikAPk bundle.ikB ephAPkv pqRatchetMsg, msgPlainv))
      (by ck_eval [hpl])]
    dsimp only [evalPrimOp]
    rw [valToMsgKeys_msgKeysToVal]; try simp only [bind_assoc]
    apply bind_congr; intro aeadCt
    rw [bindV_eval]
    rw [finishAuthHybridSendC_eval S K _ _ _ sidv uEntry peerPrincipal?
      isFreshPeer bundle m0v m1v ekASkv ekAPkv ssv kemCtv ephASkv ephAPkv
      drKey rk1 ck1_0 mkSeed ck1_1 spqrSalt? pqRatchetMsg mks
      (firstMsgAD uEntry.ikAPk bundle.ikB ephAPkv pqRatchetMsg)
      aeadCt msgPlainv roCache' rootRoCache' s.toAuthHybridState
      (by simp [Ext.step_wk, hhst])
      (by ck_eval [hsid, huE, hpp, hfr, hbu, hm0, hm1, hk6, hpl])
      hB.spkBundles_le hB.principals_le hB.opkEntries_le]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, Prod.map]
    apply bind_congr; intro ⟨resp, hst'⟩
    ck_eval [hfhst, hss]

private theorem authCkSendB_afterKem_eval
    {Γ₀ Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Γ₇ Γ₈ Γ₉ Γ₁₀ Γ₁₁ Γ₁₂ Γ₁₃ Γ₁₄ Γ₁₅ Γ₁₆ Γ₁₇ Γ₁₈ Δ : List PT}
    {noneDone : Var Γ₀ RSF}
    {idx : Var Γ₁ .nat} {chalP : Var Γ₂ (.prod (B 32) (B 32))}
    {fhst : Var Γ₃ authHybridStateFixedTy} {hst : Var Γ₄ authHybridStateTy}
    {st : Var Γ₅ authStateTy} {bu : Var Γ₆ preKeyBundleTy}
    {m0 : Var Γ₇ (B 32)} {m1 : Var Γ₈ (B 32)}
    {sid : Var Γ₉ sessionIdTy} {uE : Var Γ₁₀ principalEntryTy}
    {pp : Var Γ₁₁ (.opt (.prod .nat principalEntryTy))} {isFresh : Var Γ₁₂ .bool}
    {msgPlain : Var Γ₁₃ (B 32)} {ekASk : Var Γ₁₄ (B 32)}
    {ephASk : Var Γ₁₅ (B 32)} {spqrCoins : Var Γ₁₆ (B 32)}
    {sc : Var Γ₁₇ (.prod (B 32) (B 1568))}
    {ss : Var Γ₁₈ authSlotStateTy}
    [h₀ : Ext Γ₀ Δ]
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] [h₄ : Ext Γ₄ Δ]
    [h₅ : Ext Γ₅ Δ] [h₆ : Ext Γ₆ Δ] [h₇ : Ext Γ₇ Δ] [h₈ : Ext Γ₈ Δ]
    [h₉ : Ext Γ₉ Δ] [h₁₀ : Ext Γ₁₀ Δ] [h₁₁ : Ext Γ₁₁ Δ] [h₁₂ : Ext Γ₁₂ Δ]
    [h₁₃ : Ext Γ₁₃ Δ] [h₁₄ : Ext Γ₁₄ Δ] [h₁₅ : Ext Γ₁₅ Δ] [h₁₆ : Ext Γ₁₆ Δ]
    [h₁₇ : Ext Γ₁₇ Δ] [h₁₈ : Ext Γ₁₈ Δ]
    {env : Env Δ}
    (idxv : Nat) (pv : Bytes × Bytes) (s : AuthHybridStateFixed S)
    (sidv : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry))
    (bundle : PreKeyBundleInput) (m0v m1v msgPlainv : Bytes)
    (ekASkv ephASkv spqrCoinsv ssv kemCtv : Bytes)
    (hnd : Env.get env (h₀.wk noneDone) = (authRespToVal .noneResp, authHybridStateFixedToVal s))
    (hidx : Env.get env (h₁.wk idx) = idxv)
    (hchal : Env.get env (h₂.wk chalP) = pv)
    (hfhst : Env.get env (h₃.wk fhst) = authHybridStateFixedToVal s)
    (hhst : Env.get env (h₄.wk hst) = authHybridStateToVal s.toAuthHybridState)
    (hstV : Env.get env (h₅.wk st) = authStateToVal s.toAuthHybridState.base)
    (hbu : Env.get env (h₆.wk bu) = preKeyBundleToVal bundle)
    (hm0 : Env.get env (h₇.wk m0) = m0v)
    (hm1 : Env.get env (h₈.wk m1) = m1v)
    (hsid : Env.get env (h₉.wk sid) = sessionIdToVal sidv)
    (huE : Env.get env (h₁₀.wk uE) = principalEntryToVal uEntry)
    (hpp : Env.get env (h₁₁.wk pp) = peerPrincipal?.map (Prod.map id principalEntryToVal))
    (hfr : Env.get env (h₁₂.wk isFresh) = ckFreshPeer peerPrincipal?)
    (hpl : Env.get env (h₁₃.wk msgPlain) = msgPlainv)
    (hekSk : Env.get env (h₁₄.wk ekASk) = ekASkv)
    (hephSk : Env.get env (h₁₅.wk ephASk) = ephASkv)
    (hspqr : Env.get env (h₁₆.wk spqrCoins) = spqrCoinsv)
    (hsc : Env.get env (h₁₇.wk sc) = (ssv, kemCtv))
    (hss : Env.get env (h₁₈.wk ss) = authSlotStateToVal s.slots)
    (hB : AuthListsBounded K s) :
    (letV (.fst (v sc)) fun ssKem =>
     letV (.snd (v sc)) fun kemCt =>
     bindV (queryPrim .x25519Base (v ekASk)) fun ekAPk =>
     bindV (queryPrim .x25519Base (v ephASk)) fun ephAPk =>
     bindV (checkBundleSpkHonIdealC S K st bu) fun spkHonIdeal =>
     letV (eCaseOpt (v pp) (.bool false) fun p =>
       eAny K (asSpkBundles (v st)) fun b =>
         .and (natEq (.fst (.fst (v b))) (.fst (v p)))
           (bytesBeq 1568 (sbPqspkPk (.snd (v b))) (pkbPqspkB (v bu)))) fun pqspkHon =>
     letV (boolOr (v isFresh) (.and (.and (isSomeE (v pp)) (v spkHonIdeal)) (v pqspkHon)))
       fun isIdealSend =>
     letV (.pair (v ekASk) (.pair (v ekAPk) (.pair (v ssKem) (.pair (v kemCt)
         (.pair (v ephASk) (v ephAPk)))))) fun keys6 =>
     .ite (v isIdealSend)
       (bindV (samplePrim .drKey96) fun drKey =>
        bindV (samplePrim .bytes32) fun rk1 =>
        bindV (queryPrim (.spqrInitSend 32 32)
          (.pair (.snd (.snd (v drKey))) (v spqrCoins))) fun sp? =>
        caseOptV (v sp?) (.ret (v noneDone)) fun sp =>
        letV (.fst (.snd (v sp))) fun spqrSalt? =>
        letV (.snd (.snd (v sp))) fun pqMsg =>
        letV (allocSendSlotE (v ss) (v sid)) fun sa =>
        bindV (sampAtCkC (v idx) (v chalP) (.fst (v sa))) fun p =>
        letV (.fst (v p)) fun mkSeed =>
        letV (.snd (v p)) fun ck1_1 =>
        bindV (queryPrim (.deriveMsgKeys 32) (.pair (v mkSeed) (v spqrSalt?))) fun mks =>
        letV (firstMsgADE (peIkAPk (v uE)) (pkbIkB (v bu)) (v ephAPk) (v pqMsg)) fun ad =>
        bindV (queryPrim (.aeadEnc 158 32 32)
          (.pair (v mks) (.pair (v ad) (v msgPlain)))) fun aeadCt =>
        bindV (finishAuthHybridSendC S K hst
          (.pair (v sid) (.pair (v uE) (.pair (v pp) (.pair (v isFresh) (.pair (v bu)
            (.pair (.pair (v m0) (v m1)) (.pair (v keys6)
              (.pair (v drKey) (.pair (.pair (v rk1) (.pair (litB 32 [])
                (.pair (v mkSeed) (v ck1_1))))
                (.pair (v spqrSalt?) (.pair (v pqMsg) (.pair (v mks)
                  (.pair (v ad) (.pair (v aeadCt) (.pair (v msgPlain)
                    (.pair (asRoCache (v st)) (asRootRoCache (v st))))))))))))))))))) fun out =>
        .ret (.pair (.fst (v out))
          (ahsfMkSlots (.snd (v out)) (ahsfRecvCount (v fhst)) .nil (.snd (v sa)))))
       (bindV (queryPrim .x25519 (.pair (peSecIKA0 (v uE)) (pkbSpkB (v bu)))) fun dh1 =>
        bindV (queryPrim .x25519 (.pair (v ekASk) (pkbIkB (v bu)))) fun dh2 =>
        bindV (queryPrim .x25519 (.pair (v ekASk) (pkbSpkB (v bu)))) fun dh3 =>
        bindV (caseOptV (pkbOpkB? (v bu)) (.ret .none) fun oP =>
          bindV (queryPrim .x25519 (.pair (v ekASk) (.snd (v oP)))) fun d4 =>
          .ret (.some (v d4))) fun dh4? =>
        letV (buildSecretsE (v dh1) (v dh2) (v dh3) (v dh4?) (v ssKem)) fun secrets =>
        bindV (hkdfRoC K st (v secrets)) fun drOut =>
        letV (.fst (v drOut)) fun drKey =>
        letV (.snd (v drOut)) fun roC' =>
        bindV (queryPrim .x25519 (.pair (v ephASk) (pkbSpkB (v bu)))) fun dhR =>
        bindV (rootRoC K st (.fst (v drKey)) (v dhR)) fun rkOut =>
        letV (.fst (.fst (v rkOut))) fun rk1 =>
        letV (.snd (.fst (v rkOut))) fun ck1_0 =>
        letV (.snd (v rkOut)) fun rootC' =>
        bindV (queryPrim .chainKdfSeed (v ck1_0)) fun mkSeed =>
        bindV (queryPrim .chainKdfNext (v ck1_0)) fun ck1_1 =>
        bindV (queryPrim (.spqrInitSend 32 32)
          (.pair (.snd (.snd (v drKey))) (v spqrCoins))) fun sp? =>
        caseOptV (v sp?) (.ret (v noneDone)) fun sp =>
        letV (.fst (.snd (v sp))) fun spqrSalt? =>
        letV (.snd (.snd (v sp))) fun pqMsg =>
        bindV (queryPrim (.deriveMsgKeys 32) (.pair (v mkSeed) (v spqrSalt?))) fun mks =>
        letV (firstMsgADE (peIkAPk (v uE)) (pkbIkB (v bu)) (v ephAPk) (v pqMsg)) fun ad =>
        bindV (queryPrim (.aeadEnc 158 32 32)
          (.pair (v mks) (.pair (v ad) (v msgPlain)))) fun aeadCt =>
        bindV (finishAuthHybridSendC S K hst
          (.pair (v sid) (.pair (v uE) (.pair (v pp) (.pair (v isFresh) (.pair (v bu)
            (.pair (.pair (v m0) (v m1)) (.pair (v keys6)
              (.pair (v drKey) (.pair (.pair (v rk1) (.pair (v ck1_0) (.pair (v mkSeed) (v ck1_1))))
                (.pair (v spqrSalt?) (.pair (v pqMsg) (.pair (v mks)
                  (.pair (v ad) (.pair (v aeadCt) (.pair (v msgPlain)
                    (.pair (v roC') (v rootC')))))))))))))))))) fun out =>
        .ret (.pair (.fst (v out))
          (ahsfMkSlots (.snd (v out)) (ahsfRecvCount (v fhst)) .nil (v ss))))).eval env =
    ((let isFreshPeer : Bool := ckFreshPeer peerPrincipal?
      do
        let ekAPk ← primQ (.x25519Base ekASkv)
        let ephAPk ← primQ (.x25519Base ephASkv)
        let spkHonIdeal ← checkBundleSpkHonIdealPrim S s.toAuthHybridState.base.principals
          s.toAuthHybridState.base.spkBundles bundle
        let pqspkHon : Bool :=
          (peerPrincipal?.map (fun p =>
            s.toAuthHybridState.base.spkBundles.any
              (fun ((u, _), b) => u == p.1 && b.pqspkPk == bundle.pqspkB))).getD false
        let isIdealSend : Bool :=
          isFreshPeer || (peerPrincipal?.isSome && spkHonIdeal && pqspkHon)
        if isIdealSend then
          let drKey ← embedUnif sampleDRKey96
          let rk1 ← embedUnif sampleBytes32
          match ← primQ (.spqrInitSend drKey.pqrKey spqrCoinsv) with
          | none => return (AuthResponse.noneResp, s)
          | some (_pqrStA, spqrSalt?, pqRatchetMsg) =>
            let (sIdx, slots') := s.slots.allocSend sidv
            let p ← AuthSubHops1to3.sampAtCkPrim idxv pv sIdx
            AuthSubHops1to3.finishAuthSendCkPrim S sidv uEntry peerPrincipal? bundle m0v m1v
              ekASkv ekAPk ssv kemCtv ephASkv ephAPk drKey rk1 spqrSalt?
              pqRatchetMsg msgPlainv { s with slots := slots' } p
        else
          let dh1 ← primQ (.x25519 uEntry.secIKA0 bundle.spkB)
          let dh2 ← primQ (.x25519 ekASkv bundle.ikB)
          let dh3 ← primQ (.x25519 ekASkv bundle.spkB)
          let dh4? ←
            Option.casesOn bundle.opkB? (pure none) (fun (_, opkPk) => do
              let d4 ← primQ (.x25519 ekASkv opkPk)
              pure (some d4))
          let secrets := buildSecrets dh1 dh2 dh3 dh4? ssv
          let (drKey, roCache') ←
            embedUnif (AuthSubHops1to3.evalHkdfRoPure s.toAuthHybridState.base.roCache secrets)
          let dhRatchet ← primQ (.x25519 ephASkv bundle.spkB)
          let ((rk1, ck1_0), rootRoCache') ←
            embedUnif (AuthSubHops1to3.evalRootKdfRoPure s.toAuthHybridState.base.rootRoCache
              drKey.rootKey dhRatchet)
          let mkSeed ← primQ (.chainKdfSeed ck1_0)
          let ck1_1 ← primQ (.chainKdfNext ck1_0)
          match ← primQ (.spqrInitSend drKey.pqrKey spqrCoinsv) with
          | none => return (AuthResponse.noneResp, s)
          | some (_pqrStA, spqrSalt?, pqRatchetMsg) =>
            let deriveMessageKeys ← primQ (.deriveMsgKeys mkSeed spqrSalt?)
            let ad := firstMsgAD uEntry.ikAPk bundle.ikB ephAPk pqRatchetMsg
            let aeadCt ← primQ (.aeadEnc deriveMessageKeys ad msgPlainv)
            let (resp, hst') ←
              AuthSubHops1to3.finishAuthHybridSendPrim S sidv uEntry peerPrincipal? isFreshPeer
                bundle m0v m1v ekASkv ekAPk ssv kemCtv ephASkv ephAPk drKey rk1 ck1_0 mkSeed ck1_1
                spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlainv roCache' rootRoCache'
                s.toAuthHybridState
            return (resp, { toAuthHybridState := hst', recvCount := s.recvCount,
                            slots := s.slots })) >>=
      fun x => pure (Prod.map authRespToVal authHybridStateFixedToVal x)) := by
  dsimp only
  rw [letV_eval_eq _ _ _ ssv (by simp [v, Expr.eval, hsc])]
  rw [letV_eval_eq _ _ _ kemCtv (by simp [v, Expr.eval, Ext.step_wk, hsc])]
  rw [bindV_eval, queryPrim_eval_eq _ _ ekASkv (by simp [v, Expr.eval, Ext.step_wk, hekSk])]
  dsimp only [evalPrimOp]; try simp only [bind_assoc]
  apply bind_congr; intro ekAPk
  rw [bindV_eval, queryPrim_eval_eq _ _ ephASkv (by simp [v, Expr.eval, Ext.step_wk, hephSk])]
  dsimp only [evalPrimOp]; try simp only [bind_assoc]
  apply bind_congr; intro ephAPk
  rw [bindV_eval, checkBundleSpkHonIdealC_eval S _ _ _ s.toAuthHybridState.base bundle
    (by simp [Ext.step_wk, hstV]) (by simp [Ext.step_wk, hbu]) hB.principals_le hB.spkBundles_le]
  try simp only [bind_assoc]
  apply bind_congr; intro spkHonIdeal
  let pqspkHon : Bool :=
    (peerPrincipal?.map (fun p =>
      s.toAuthHybridState.base.spkBundles.any
        (fun ((u, _), b) => u == p.1 && b.pqspkPk == bundle.pqspkB))).getD false
  rw [letV_eval_eq _ _ _ pqspkHon
    (by exact pqspkHonE_eval S K _ _ _ _
          peerPrincipal? s.toAuthHybridState.base bundle
          (by simp [Ext.step_wk, hpp]) (by simp [Ext.step_wk, hstV])
          (by simp [Ext.step_wk, hbu]) hB.spkBundles_le)]
  let isFreshPeer : Bool := ckFreshPeer peerPrincipal?
  let isIdealSend : Bool :=
    isFreshPeer || (peerPrincipal?.isSome && spkHonIdeal && pqspkHon)
  rw [letV_eval_eq _ _ _ isIdealSend
    (by dsimp only [isIdealSend, isFreshPeer]; ck_eval [hfr, hpp])]
  rw [letV_eval_eq _ _ _ (ekASkv, (ekAPk, (ssv, (kemCtv, (ephASkv, ephAPk)))))
    (by ck_eval [hekSk, hephSk])]
  rw [iteC_eval_eq _ _ _ _ isIdealSend rfl]
  change _ = ((if isIdealSend = true then (_ : OracleComp PrimBaseSpec _) else _)
    >>= fun x => pure (Prod.map authRespToVal authHybridStateFixedToVal x))
  cases hIdeal : isIdealSend with
  | true =>
    simp only [↓reduceIte]
    apply authCkSendB_ideal_eval S K idxv pv s sidv uEntry peerPrincipal? bundle
      m0v m1v msgPlainv spqrCoinsv ekASkv ekAPk ssv kemCtv ephASkv ephAPk
    all_goals simp [Ext.step_wk, hnd, hidx, hchal, hfhst, hhst, hstV, hbu, hm0, hm1,
      hsid, huE, hpp, hfr, hpl, hspqr, hss, hB.spkBundles_le,
      hB.principals_le, hB.opkEntries_le]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    apply authCkSendB_real_eval S K s sidv uEntry peerPrincipal? isFreshPeer bundle
      m0v m1v msgPlainv ekASkv ekAPk ssv kemCtv ephASkv ephAPk spqrCoinsv
    all_goals simp [isFreshPeer, Ext.step_wk, hnd, hfhst, hhst, hstV, hbu, hm0, hm1,
      hsid, huE, hpp, hfr, hpl, hekSk, hephSk, hspqr, hss, hB]

theorem authCkSendB_eval (opk : Bool)
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ sendQTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] [h₄ : Ext Γ₄ Δ] (env : Env Δ)
    (idxv : Nat) (pv : Bytes × Bytes) (s : AuthHybridStateFixed S)
    (uv : Fin S.N_id) (iv_nat : Nat) (sidv : SessionId S)
    (bundle : PreKeyBundleInput) (m0v m1v : Bytes)
    (hidx : Env.get env (h₁.wk idx) = idxv)
    (hchal : Env.get env (h₂.wk chalP) = pv)
    (hfhst : Env.get env (h₃.wk fhst) = authHybridStateFixedToVal s)
    (hx : Env.get env (h₄.wk x) = (uv.val, (iv_nat, (preKeyBundleToVal bundle, (m0v, m1v)))))
    (hSid : (if opk then Sum.inl (uv.val, iv_nat) else Sum.inr (Sum.inl (uv.val, iv_nat))) =
      sessionIdToVal sidv)
    (hB : AuthListsBounded K s) :
    (authCkSendB S K opk idx chalP fhst x).eval env =
      Prod.map authRespToVal authHybridStateFixedToVal <$>
        (if (if opk then bundle.opkB?.isNone else bundle.opkB?.isSome) then
          pure (.noneResp, s)
        else
          AuthSubHops1to3.authCkSendWithPrim S (AuthSubHops1to3.sampAtCkPrim idxv pv)
            sidv uv bundle m0v m1v s) := by
  have hTakeP :
      (s.toAuthHybridState.base.principals.map (Prod.map id principalEntryToVal)).take K =
      s.toAuthHybridState.base.principals.map (Prod.map id principalEntryToVal) := by
    apply List.take_of_length_le; simpa using hB.principals_le
  unfold authCkSendB
  rw [letV_eval_eq _ _ _ (authRespToVal .noneResp, authHybridStateFixedToVal s)
    (by simp [v, aNone, Expr.eval, hfhst, authRespToVal, authRenc])]
  rw [iteC_eval_eq _ _ _ _ (if opk then bundle.opkB?.isNone else bundle.opkB?.isSome)
    (sendGuardE_eval opk (v x) _ uv.val iv_nat bundle m0v m1v
      (by simp [v, Expr.eval, Ext.step_wk, hx]))]
  cases hGuard : (if opk then bundle.opkB?.isNone else bundle.opkB?.isSome) with
  | true =>
    simp [v, Comp.eval, Expr.eval, Prod.map]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold AuthSubHops1to3.authCkSendWithPrim
    dsimp only
    rw [letV_eval_eq _ _ _ (authHybridStateToVal s.toAuthHybridState)
      (by simp [v, ahsfHybrid, Expr.eval, Ext.step_wk, hfhst, authHybridStateFixedToVal])]
    rw [letV_eval_eq _ _ _ (authSlotStateToVal s.slots)
      (by simp [v, Expr.eval, Ext.step_wk, hfhst, authHybridStateFixedToVal])]
    rw [letV_eval_eq _ _ _ (authStateToVal s.toAuthHybridState.base) rfl]
    rw [iteC_eval_eq _ _ _ _ s.toAuthHybridState.base.hasWonAuth rfl]
    cases hWon : s.toAuthHybridState.base.hasWonAuth with
    | true => simp [v, Comp.eval, Expr.eval, Ext.step_wk, Prod.map]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [letV_eval_eq _ _ _ (preKeyBundleToVal bundle)
        (by simp [v, Expr.eval, Ext.step_wk, hx])]
      rw [letV_eval_eq _ _ _ m0v
        (by simp [v, Expr.eval, Ext.step_wk, hx])]
      rw [letV_eval_eq _ _ _ m1v
        (by simp [v, Expr.eval, Ext.step_wk, hx])]
      rw [letV_eval_eq _ _ _ (sessionIdToVal sidv)
        (by rw [sendSidE_eval opk _ _ uv.val iv_nat bundle m0v m1v
              (by simp [v, Expr.eval, Ext.step_wk, hx]), hSid])]
      rw [iteC_eval_eq _ _ _ _ (m0v.length != m1v.length)
        (by simp [v, natEq_eval, bytesLen_eval, Expr.eval, bne])]
      cases hLen : (m0v.length != m1v.length) with
      | true => simp [v, Comp.eval, Expr.eval, Ext.step_wk, Prod.map]
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [iteC_eval_eq _ _ _ _ (s.toAuthHybridState.base.usedSendSessions.contains sidv)
          (eAny_usedSendSessions_eval S K _ _ _ s.toAuthHybridState.base sidv rfl rfl
            hB.usedSendSessions_le)]
        cases hUsed : s.toAuthHybridState.base.usedSendSessions.contains sidv with
        | true =>
          simp [v, Comp.eval, Expr.eval, Ext.step_wk, Prod.map]
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [caseOptV_eval_eq _ _ _ _
            ((s.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == uv.val)).map
              (Prod.map id principalEntryToVal))
            (by simp [eFind, asPrincipals, natEq_eval, v, Expr.eval, Ext.step_wk,
              hx, authStateToVal, hTakeP, List.find?_map, Prod.map])]
          cases hFindU :
              s.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == uv.val) with
          | none => simp [v, Comp.eval, Expr.eval, Ext.step_wk, Prod.map]
          | some uP =>
            rcases uP with ⟨uIdx, uEntry⟩
            dsimp only [Option.map, Prod.map, id_eq]
            rw [letV_eval_eq _ _ _ (principalEntryToVal uEntry) rfl]
            rw [bindV_eval, findHonestC_eval_eq S _ _ _ _ s.toAuthHybridState.base bundle.ikB rfl rfl
              hB.principals_le]
            simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
            apply bind_congr; intro peerPrincipal?
            let isFreshPeer : Bool := ckFreshPeer peerPrincipal?
            rw [letV_eval_eq _ _ _ isFreshPeer
              (by exact isFreshE_eval _ _ peerPrincipal? rfl)]
            rw [iteC_eval_eq _ _ _ _ (!isFreshPeer && (m0v != m1v))
              (by ck_eval [])]
            rw [ck_ite_bind]
            refine ck_ite_eq Iff.rfl (fun _ => ?_) (fun _ => ?_)
            · ck_eval []
            · let msgPlain : Bytes :=
                if isFreshPeer then (if s.toAuthHybridState.base.secb then m1v else m0v) else m0v
              rw [letV_eval_eq _ _ _ msgPlain rfl]
              rw [bindV_eval, koskBundleOkC_eval S K _ _ _ s.toAuthHybridState.base bundle rfl rfl
                hB.advKeys_le hB.principals_le
        hB.spkBundles_le hB.opkEntries_le]
              simp only [bind_assoc]
              apply bind_congr; intro koskOk
              rw [iteC_eval_eq _ _ _ _ (!koskOk) rfl]
              cases koskOk with
              | false =>
                simp [v, Comp.eval, Expr.eval, Ext.step_wk, Prod.map]
              | true =>
                simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                rw [bindV_eval, samplePrim_bytes32_eval]; try simp only [bind_assoc]
                apply bind_congr; intro ekASk
                rw [bindV_eval, samplePrim_bytes32_eval]; try simp only [bind_assoc]
                apply bind_congr; intro kemCoins
                rw [bindV_eval, samplePrim_bytes32_eval]; try simp only [bind_assoc]
                apply bind_congr; intro ephASk
                rw [bindV_eval, samplePrim_bytes32_eval]; try simp only [bind_assoc]
                apply bind_congr; intro spqrCoins
                rw [bindV_eval,
                  resolveSigPkC_eval_eq S _ _ _ _ s.toAuthHybridState.base bundle.ikB rfl rfl
                  hB.principals_le]
                try simp only [bind_assoc]
                apply bind_congr; intro sigPkB
                rw [bindV_eval,
                  queryPrim_eval_eq _ _ (sigPkB, (encodeEC bundle.spkB, bundle.spkSig))
                  (by simp [encEC_eval, v, pkbSpkB, pkbSpkSig, Expr.eval,
                    preKeyBundleToVal, bundleV])]
                dsimp only [evalPrimOp]; try simp only [bind_assoc]
                apply bind_congr; intro v1
                rw [bindV_eval,
                  queryPrim_eval_eq _ _ (sigPkB, (encodeKEM bundle.pqspkB, bundle.pqspkSig))
                  (by simp [encKEM_eval, v, pkbPqspkB, pkbPqspkSig, Expr.eval,
                    preKeyBundleToVal, bundleV])]
                dsimp only [evalPrimOp]; try simp only [bind_assoc]
                apply bind_congr; intro v2
                rw [iteC_eval_eq _ _ _ _ (!(v1 && v2)) rfl]
                cases hv : (v1 && v2) with
                | false => simp [v, Comp.eval, Expr.eval, Ext.step_wk, Prod.map]
                | true =>
                  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                  rw [bindV_eval, queryPrim_eval_eq _ _ (bundle.pqspkB, kemCoins) rfl]
                  dsimp only [evalPrimOp]; try simp only [bind_assoc]
                  apply bind_congr; intro enc?
                  rw [caseOptV_eval_eq _ _ _ _ enc? rfl]
                  cases enc? with
                  | none => simp [v, Comp.eval, Expr.eval, Ext.step_wk, Prod.map]
                  | some sc =>
                    rcases sc with ⟨ssKem, kemCt⟩
                    dsimp only [isFreshPeer]
                    apply authCkSendB_afterKem_eval S K idxv pv s sidv uEntry peerPrincipal?
                      bundle m0v m1v msgPlain ekASk ephASk spqrCoins ssKem kemCt
                    all_goals first | exact hB |
                      simp only [Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
                        hidx, hchal, hfhst]

private theorem finishAuthRecvCkSlotsPrim_eq_map
    (msg : PreKeyMsg) (prep : PreparedAuthRecvPrim S)
    (drKey : DRKey) (rk1 : Bytes) (spqrSalt? : Option Bytes)
    (rcv' : Nat) (p : Bytes × Bytes) (slots' : AuthSlotState) :
    AuthSubHops1to3.finishAuthRecvCkSlotsPrim S msg prep drKey rk1 spqrSalt? rcv' p slots' =
      Prod.map id (fun x => { x with slots := slots' }) <$>
        AuthSubHops1to3.finishAuthRecvCkPrim S msg prep drKey rk1 spqrSalt? rcv' p := by
  unfold AuthSubHops1to3.finishAuthRecvCkPrim AuthSubHops1to3.finishAuthRecvCkSlotsPrim
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, Prod.map, id_eq]

theorem authCkRecvB_of_prepare (opk : Bool)
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ recvQTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] [h₄ : Ext Γ₄ Δ] (env : Env Δ)
    (idxv : Nat) (pv : Bytes × Bytes) (s : AuthHybridStateFixed S)
    (msgv : PreKeyMsg)
    (mPrep : OracleComp PrimBaseSpec (Option (PreparedAuthRecvPrim S)))
    (hidx : Env.get env (h₁.wk idx) = idxv)
    (hchal : Env.get env (h₂.wk chalP) = pv)
    (hfhst : Env.get env (h₃.wk fhst) = authHybridStateFixedToVal s)
    (hmsg : (Env.get env (h₄.wk x)).2.2.2 = preKeyMsgToVal msgv)
    (hPrepEval :
      (prepareAuthHybridRecvC S K opk (.zero : Var (authHybridStateTy :: Δ) authHybridStateTy) x :
        Comp pqxdhOps pqPrimIface
          (.nat :: preKeyMsgTy :: authSlotStateTy :: .nat :: authHybridStateTy :: Δ)
          (.opt preparedAuthRecvTy)).eval
        (.cons (s.recvCount + 1)
          (.cons (preKeyMsgToVal msgv)
            (.cons (authSlotStateToVal s.slots)
              (.cons s.recvCount
                (.cons (authHybridStateToVal s.toAuthHybridState) env))))) =
      Option.map preparedAuthRecvToVal <$> mPrep)
    (hPrepBounded : AllLeaves
      (fun prep? => ∀ prep, prep? = some prep → PreparedRecvBounded K prep) mPrep) :
    (authCkRecvB S K opk idx chalP fhst x).eval env =
      Prod.map authRespToVal authHybridStateFixedToVal <$>
        (mPrep >>= fun prep? =>
          AuthSubHops1to3.authCkRecvWithPrim S (AuthSubHops1to3.sampAtCkPrim idxv pv)
            msgv prep? s) := by
  unfold authCkRecvB
  rw [letV_eval_eq _ _ _ (authHybridStateToVal s.toAuthHybridState)
    (by simp [v, ahsfHybrid, Expr.eval, hfhst, authHybridStateFixedToVal])]
  rw [letV_eval_eq _ _ _ s.recvCount
    (by simp [v, ahsfRecvCount, Expr.eval, Ext.step_wk, hfhst, authHybridStateFixedToVal])]
  rw [letV_eval_eq _ _ _ (authSlotStateToVal s.slots)
    (by simp [v, Expr.eval, Ext.step_wk, hfhst, authHybridStateFixedToVal])]
  rw [letV_eval_eq _ _ _ (preKeyMsgToVal msgv)
    (by simp [v, Expr.eval, Ext.step_wk, hmsg])]
  rw [letV_eval_eq _ _ _ (s.recvCount + 1)
    (by simp [v, Expr.eval, Ext.step_wk])]
  rw [bindV_eval, hPrepEval]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  refine hPrepBounded.toHoldsOnLeaves.bind_congr _ _ (fun prep? hPrep => ?_)
  rw [caseOptV_eval_eq _ _ _ _ (prep?.map preparedAuthRecvToVal) rfl]
  cases prep? with
  | none =>
    simp [AuthSubHops1to3.authCkRecvWithPrim, aNone,
      ahsfHybrid, ahsfMkSaltCache,
      v, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk,
      hfhst, authHybridStateFixedToVal, authHybridStateFixedWithSlotsToVal,
      authRespToVal, authRenc, Prod.map]
  | some prep =>
    have hP : PreparedRecvBounded K prep := hPrep prep rfl
    unfold AuthSubHops1to3.authCkRecvWithPrim
    dsimp only [Option.map]
    rw [letV_eval_eq _ _ _ (authStateToVal prep.hstDec.base) rfl]
    rw [letV_eval_eq _ _ _ (recvFinishTagToVal prep.finishTag) rfl]
    rw [letV_eval_eq _ _ _ (prep.matchedSess?.isSome || prep.isUncorruptedHonestSender)
      (by simp [v, boolOr_eval, isSomeE_eval, parMatchedSess?, Expr.eval,
        preparedAuthRecvToVal, Option.isSome_map])]
    rw [iteC_eval_eq _ _ _ _ (prep.matchedSess?.isSome || prep.isUncorruptedHonestSender) rfl]
    cases hUseIdeal : (prep.matchedSess?.isSome || prep.isUncorruptedHonestSender) with
    | true =>
      simp only [↓reduceIte]
      rw [caseOptV_eval_eq _ _ _ _ (prep.matchedSess?.map idealAuthSessionToVal) rfl]
      cases hMatch : prep.matchedSess? with
      | none =>
        dsimp only [Option.map]
        rw [bindV_eval, samplePrim_drKey96_eval]
        simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
        apply bind_congr; intro drKey
        rw [bindV_eval, samplePrim_bytes32_eval]
        apply bind_congr; intro rk1
        rw [bindV_eval, queryPrim_eval_eq _ _ (drKey.pqrKey, msgv.pqRatchetMsg) rfl]
        dsimp only [evalPrimOp]; try simp only [bind_assoc]
        apply bind_congr; intro sp?
        rw [caseOptV_eval_eq _ _ _ _ sp? rfl]
        cases sp? with
        | none =>
          dsimp only
          rw [bindV_eval, recvFinishTagRunC_eval S K _ _ _ prep.finishTag none rfl rfl
            hP.tag_bounded.opkEntries_le
            hP.tag_bounded.principals_le]
          simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, Prod.map]
          apply bind_congr; intro ⟨resp, hst'⟩
          simp [v, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk,
            authHybridStateFixedToVal, authHybridStateFixedWithSlotsToVal]
        | some sp =>
          rcases sp with ⟨pqrStB, spqrSalt?⟩
          dsimp only
          let raVal := s.slots.allocRecv s.recvCount
          rw [letV_eval_eq _ _ _ (Prod.map id authSlotStateToVal raVal)
            (by exact allocRecvSlotE_eval _ _ _ s.slots s.recvCount rfl rfl)]
          rw [bindV_eval, sampAtCkC_eval]
          simp only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
            Prod.map, id_eq]
          rw [hidx, hchal]; try simp only [bind_assoc]
          apply bind_congr; intro p
          rw [bindV_eval, finishAuthRecvCkC_eval S K _ _ _ _ _ _ _ _ msgv prep drKey rk1 spqrSalt?
            (s.recvCount + 1) p rfl rfl rfl rfl rfl rfl rfl hP.tag_bounded.opkEntries_le
            hP.tag_bounded.principals_le,
            finishAuthRecvCkSlotsPrim_eq_map]
          simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, Prod.map]
          apply bind_congr; intro ⟨resp, fhstOut⟩
          simp [Comp.eval, Expr.eval, raVal,
            ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, authHybridStateFixedToVal,
            authHybridStateFixedWithSlotsToVal]
      | some sess =>
        dsimp only [Option.map]
        rw [iteC_eval_eq _ _ _ _ prep.sameEph rfl]
        cases hSame : prep.sameEph with
        | true =>
          simp only [↓reduceIte]
          rw [bindV_eval, queryPrim_eval_eq _ _ (sess.drKey.pqrKey, msgv.pqRatchetMsg) rfl]
          dsimp only [evalPrimOp]; try simp only [bind_assoc]
          apply bind_congr; intro sp?
          rw [caseOptV_eval_eq _ _ _ _ sp? rfl]
          cases sp? with
          | none =>
            dsimp only
            rw [bindV_eval, recvFinishTagRunC_eval S K _ _ _ prep.finishTag none rfl rfl
              hP.tag_bounded.opkEntries_le
            hP.tag_bounded.principals_le]
            simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, Prod.map]
            apply bind_congr; intro ⟨resp, hst'⟩
            simp [v, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk,
              authHybridStateFixedToVal, authHybridStateFixedWithSlotsToVal]
          | some sp =>
            rcases sp with ⟨pqrStB, spqrSalt?⟩
            dsimp only
            rw [bindV_eval, finishAuthRecvCkC_eval S K _ _ _ _ _ _ _ _ msgv prep sess.drKey sess.rk1 spqrSalt?
              (s.recvCount + 1) (sess.mkSeed, sess.ck1_1) rfl rfl rfl rfl rfl rfl rfl
              hP.tag_bounded.opkEntries_le
            hP.tag_bounded.principals_le,
              finishAuthRecvCkSlotsPrim_eq_map]
            simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, Prod.map]
            apply bind_congr; intro ⟨resp, fhstOut⟩
            simp [v, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk,
              ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, authHybridStateFixedToVal,
              authHybridStateFixedWithSlotsToVal]
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [bindV_eval, samplePrim_bytes32_eval]; try simp only [bind_assoc]
          apply bind_congr; intro rk1
          rw [bindV_eval, queryPrim_eval_eq _ _ (sess.drKey.pqrKey, msgv.pqRatchetMsg) rfl]
          dsimp only [evalPrimOp]; try simp only [bind_assoc]
          apply bind_congr; intro sp?
          rw [caseOptV_eval_eq _ _ _ _ sp? rfl]
          cases sp? with
          | none =>
            dsimp only
            rw [bindV_eval, recvFinishTagRunC_eval S K _ _ _ prep.finishTag none rfl rfl
              hP.tag_bounded.opkEntries_le
            hP.tag_bounded.principals_le]
            simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, Prod.map]
            apply bind_congr; intro ⟨resp, hst'⟩
            simp [v, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk,
              authHybridStateFixedToVal, authHybridStateFixedWithSlotsToVal]
          | some sp =>
            rcases sp with ⟨pqrStB, spqrSalt?⟩
            dsimp only
            let raVal := s.slots.allocRecv s.recvCount
            rw [letV_eval_eq _ _ _ (Prod.map id authSlotStateToVal raVal)
              (by exact allocRecvSlotE_eval _ _ _ s.slots s.recvCount rfl rfl)]
            rw [bindV_eval, sampAtCkC_eval]
            simp only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
              Prod.map, id_eq]
            rw [hidx, hchal]; try simp only [bind_assoc]
            apply bind_congr; intro p
            rw [bindV_eval, finishAuthRecvCkC_eval S K _ _ _ _ _ _ _ _ msgv prep sess.drKey rk1 spqrSalt?
              (s.recvCount + 1) p rfl rfl rfl rfl rfl rfl rfl hP.tag_bounded.opkEntries_le
            hP.tag_bounded.principals_le,
              finishAuthRecvCkSlotsPrim_eq_map]
            simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, Prod.map]
            apply bind_congr; intro ⟨resp, fhstOut⟩
            simp [Comp.eval, Expr.eval, raVal,
              ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, authHybridStateFixedToVal,
              authHybridStateFixedWithSlotsToVal]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [bindV_eval, hkdfRoC_eval S K _ _ _ prep.hstDec.base rfl hP.roCache_le]
      dsimp only [parSecrets, v, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
        preparedAuthRecvToVal]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, Prod.map]
      apply bind_congr; intro ⟨drKey, roCache'⟩
      rw [letV_eval_eq _ _ _ (drKeyToVal drKey) rfl]
      rw [letV_eval_eq _ _ _ (roCache'.map (Prod.map id drKeyToVal)) rfl]
      rw [bindV_eval, rootRoC_eval S K _ _ _ _ prep.hstDec.base rfl hP.rootRoCache_le]
      dsimp only [parDhRatchet, v, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
        preparedAuthRecvToVal, drKeyToVal, drKeyV]
      try simp only [bind_assoc]
      apply bind_congr; intro ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
      rw [letV_eval_eq _ _ _ rk1 rfl]
      rw [letV_eval_eq _ _ _ ck1_0 rfl]
      rw [letV_eval_eq _ _ _ rootRoCache' rfl]
      rw [bindV_eval, queryPrim_eval_eq _ _ ck1_0 rfl]
      dsimp only [evalPrimOp]; try simp only [bind_assoc]
      apply bind_congr; intro mkSeed
      rw [bindV_eval, queryPrim_eval_eq _ _ ck1_0 rfl]
      dsimp only [evalPrimOp]; try simp only [bind_assoc]
      apply bind_congr; intro ck1_1
      rw [bindV_eval, queryPrim_eval_eq _ _ (drKey.pqrKey, msgv.pqRatchetMsg) rfl]
      dsimp only [evalPrimOp]; try simp only [bind_assoc]
      apply bind_congr; intro sp?
      rw [caseOptV_eval_eq _ _ _ _ sp? rfl]
      cases sp? with
      | none =>
        dsimp only
        rw [bindV_eval, recvFinishTagRunC_eval S K _ _ _ prep.finishTag none rfl rfl
          hP.tag_bounded.opkEntries_le
            hP.tag_bounded.principals_le]
        simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, Prod.map]
        apply bind_congr; intro ⟨resp, hst'⟩
        simp [Comp.eval, Expr.eval,
          authHybridStateFixedToVal, authHybridStateFixedWithSlotsToVal]
      | some sp =>
        rcases sp with ⟨pqrStB, spqrSalt?⟩
        dsimp only
        rw [bindV_eval, queryPrim_eval_eq _ _ (mkSeed, spqrSalt?) rfl]
        dsimp only [evalPrimOp]
        simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
        apply bind_congr; intro mks
        rw [letV_eval_eq _ _ _
          (firstMsgAD msgv.hdr.ikAPk prep.kEntry.ikAPk msgv.ephAPk msgv.pqRatchetMsg)
          (by simp [firstMsgADE_eval, pkmHdr, hdrIkAPk, parKEntry, peIkAPk,
            pkmEphAPk, pkmPqRatchetMsg, Expr.eval, preKeyMsgToVal, preKeyMsgV,
            hdrV, principalEntryToVal])]
        rw [bindV_eval, queryPrim_eval_eq _ _
          (msgKeysToVal mks,
            (firstMsgAD msgv.hdr.ikAPk prep.kEntry.ikAPk msgv.ephAPk msgv.pqRatchetMsg,
              msgv.aeadCt))
          rfl]
        dsimp only [evalPrimOp]; rw [valToMsgKeys_msgKeysToVal]; try simp only [bind_assoc]
        apply bind_congr; intro pt?
        rw [letV_eval, bindV_eval]
        rw [recvFinishTagRunC_eval S K _ _ _ prep.finishTag
          (pt?.map fun pt => (drKey, rk1, ck1_1, pt, roCache', rootRoCache'))
          rfl ?_ hP.tag_bounded.opkEntries_le
            hP.tag_bounded.principals_le
            (fun _ => hP.tag_bounded.sentOPKEvents_le)
            (fun _ => hP.tag_bounded.sentNoOPKEvents_le)]
        · simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, Prod.map]
          apply bind_congr; intro ⟨resp, hst'⟩
          simp [Comp.eval, Expr.eval,
            authHybridStateFixedToVal, authHybridStateFixedWithSlotsToVal]
        · cases pt? <;> simp [eCaseOpt, Expr.eval, recvFinishResToVal, drKeyToVal, drKeyV]

theorem authCkRecvOPKB_eval
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ recvQTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] [h₄ : Ext Γ₄ Δ] (env : Env Δ)
    (idxv : Nat) (pv : Bytes × Bytes) (s : AuthHybridStateFixed S)
    (kv : Fin S.N_id) (jv : Fin S.N_recv) (ov : Fin S.N_opk) (msgv : PreKeyMsg)
    (hidx : Env.get env (h₁.wk idx) = idxv)
    (hchal : Env.get env (h₂.wk chalP) = pv)
    (hfhst : Env.get env (h₃.wk fhst) = authHybridStateFixedToVal s)
    (hx : Env.get env (h₄.wk x) = (kv.val, (jv.val, (ov.val, preKeyMsgToVal msgv))))
    (hB : AuthListsBounded K s) :
    (authCkRecvB S K true idx chalP fhst x).eval env =
      Prod.map authRespToVal authHybridStateFixedToVal <$>
        (prepareAuthHybridRecvOPKPrim S kv jv ov msgv s.toAuthHybridState >>= fun prep? =>
          AuthSubHops1to3.authCkRecvWithPrim S (AuthSubHops1to3.sampAtCkPrim idxv pv)
            msgv prep? s) := by
  refine authCkRecvB_of_prepare S K true idx chalP fhst x env idxv pv s msgv
    (prepareAuthHybridRecvOPKPrim S kv jv ov msgv s.toAuthHybridState)
    hidx hchal hfhst (by simp [hx]) ?_
    (prepareAuthHybridRecvOPKPrim_bounded kv jv ov msgv s.toAuthHybridState
      hB.toAuthHybridListsBounded)
  exact prepareAuthHybridRecvOPKC_eval S K
    (.zero : Var (authHybridStateTy :: Δ) authHybridStateTy) x _
    s.toAuthHybridState kv jv ov msgv rfl
    (by simp [Ext.step_wk, hx])
    hB.toAuthHybridListsBounded

theorem authCkRecvNoOPKB_eval
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ recvQTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] [h₄ : Ext Γ₄ Δ] (env : Env Δ)
    (idxv : Nat) (pv : Bytes × Bytes) (s : AuthHybridStateFixed S)
    (kv : Fin S.N_id) (jv : Fin S.N_recv) (lv : Fin S.N_no_opk) (msgv : PreKeyMsg)
    (hidx : Env.get env (h₁.wk idx) = idxv)
    (hchal : Env.get env (h₂.wk chalP) = pv)
    (hfhst : Env.get env (h₃.wk fhst) = authHybridStateFixedToVal s)
    (hx : Env.get env (h₄.wk x) = (kv.val, (jv.val, (lv.val, preKeyMsgToVal msgv))))
    (hB : AuthListsBounded K s) :
    (authCkRecvB S K false idx chalP fhst x).eval env =
      Prod.map authRespToVal authHybridStateFixedToVal <$>
        (prepareAuthHybridRecvNoOPKPrim S kv jv lv msgv s.toAuthHybridState >>= fun prep? =>
          AuthSubHops1to3.authCkRecvWithPrim S (AuthSubHops1to3.sampAtCkPrim idxv pv)
            msgv prep? s) := by
  refine authCkRecvB_of_prepare S K false idx chalP fhst x env idxv pv s msgv
    (prepareAuthHybridRecvNoOPKPrim S kv jv lv msgv s.toAuthHybridState)
    hidx hchal hfhst (by simp [hx]) ?_
    (prepareAuthHybridRecvNoOPKPrim_bounded kv jv lv msgv s.toAuthHybridState
      hB.toAuthHybridListsBounded)
  exact prepareAuthHybridRecvNoOPKC_eval S K
    (.zero : Var (authHybridStateTy :: Δ) authHybridStateTy) x _
    s.toAuthHybridState kv jv lv msgv rfl
    (by simp [Ext.step_wk, hx])
    hB.toAuthHybridListsBounded

theorem authCkStepC_eval
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (q : Var Γ₄ authQueryTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] [h₄ : Ext Γ₄ Δ] (env : Env Δ)
    (idxv : Nat) (pv : Bytes × Bytes) (s : AuthHybridStateFixed S) (qv : AuthQuery S)
    (hidx : Env.get env (h₁.wk idx) = idxv)
    (hchal : Env.get env (h₂.wk chalP) = pv)
    (hfhst : Env.get env (h₃.wk fhst) = authHybridStateFixedToVal s)
    (hq : Env.get env (h₄.wk q) = authQueryToVal qv)
    (hB : AuthListsBounded K s) :
    (authCkStepC S K idx chalP fhst q).eval env =
      Prod.map authRespToVal authHybridStateFixedToVal <$>
        AuthSubHops1to3.authCkStepWithPrim S (AuthSubHops1to3.sampAtCkPrim idxv pv) qv s := by
  cases qv with
  | initPrin u =>
    unfold authCkStepC AuthSubHops1to3.authCkStepWithPrim
    simp only [caseSumV, v, Comp.eval, Expr.eval, hq, authQueryToVal, authQenc]
    exact initPrinFixedB_eval S K fhst .zero _ s u
      (by simp [Ext.step_wk, hfhst]) rfl hB
  | corruptIK u =>
    unfold authCkStepC AuthSubHops1to3.authCkStepWithPrim
    simp only [caseSumV, v, Comp.eval, Expr.eval, Ext.refl_wk, Env.get_zero,
      hq, authQueryToVal, authQenc]
    exact corruptFixedB_eval S K fhst .zero _ s u
      (by simp [Ext.step_wk, hfhst]) rfl hB
  | genSPK u j =>
    unfold authCkStepC AuthSubHops1to3.authCkStepWithPrim
    simp only [caseSumV, v, Comp.eval, Expr.eval, Ext.refl_wk, Env.get_zero,
      hq, authQueryToVal, authQenc]
    exact genSpkFixedB_eval S K fhst .zero _ s u j
      (by simp [Ext.step_wk, hfhst]) rfl hB
  | genOPK u j o =>
    unfold authCkStepC AuthSubHops1to3.authCkStepWithPrim
    simp only [caseSumV, v, Comp.eval, Expr.eval, Ext.refl_wk, Env.get_zero,
      hq, authQueryToVal, authQenc]
    exact genOpkFixedB_eval S K fhst .zero _ s u j o
      (by simp [Ext.step_wk, hfhst]) rfl hB
  | sendOPK u i bundle m0 m1 =>
    unfold authCkStepC AuthSubHops1to3.authCkStepWithPrim
    simp only [caseSumV, v, Comp.eval, Expr.eval, Ext.refl_wk, Env.get_zero,
      hq, authQueryToVal, authQenc]
    exact authCkSendB_eval S K true idx chalP fhst .zero _ idxv pv s u i.val (.sendOPK u i)
      bundle m0 m1
      (by simp [Ext.step_wk, hidx])
      (by simp [Ext.step_wk, hchal])
      (by simp [Ext.step_wk, hfhst])
      rfl rfl hB
  | sendNoOPK u i bundle m0 m1 =>
    unfold authCkStepC AuthSubHops1to3.authCkStepWithPrim
    simp only [caseSumV, v, Comp.eval, Expr.eval, Ext.refl_wk, Env.get_zero,
      hq, authQueryToVal, authQenc]
    exact authCkSendB_eval S K false idx chalP fhst .zero _ idxv pv s u i.val (.sendNoOPK u i)
      bundle m0 m1
      (by simp [Ext.step_wk, hidx])
      (by simp [Ext.step_wk, hchal])
      (by simp [Ext.step_wk, hfhst])
      rfl rfl hB
  | recvOPK k j o msg =>
    unfold authCkStepC AuthSubHops1to3.authCkStepWithPrim
    simp only [caseSumV, v, Comp.eval, Expr.eval, Ext.refl_wk, Env.get_zero,
      hq, authQueryToVal, authQenc]
    exact authCkRecvOPKB_eval S K idx chalP fhst .zero _ idxv pv s k j o msg
      (by simp [Ext.step_wk, hidx])
      (by simp [Ext.step_wk, hchal])
      (by simp [Ext.step_wk, hfhst])
      rfl hB
  | recvNoOPK k j l msg =>
    unfold authCkStepC AuthSubHops1to3.authCkStepWithPrim
    simp only [caseSumV, v, Comp.eval, Expr.eval, Ext.refl_wk, Env.get_zero,
      hq, authQueryToVal, authQenc]
    exact authCkRecvNoOPKB_eval S K idx chalP fhst .zero _ idxv pv s k j l msg
      (by simp [Ext.step_wk, hidx])
      (by simp [Ext.step_wk, hchal])
      (by simp [Ext.step_wk, hfhst])
      rfl hB
  | roQuery sec =>
    unfold authCkStepC AuthSubHops1to3.authCkStepWithPrim
    simp only [caseSumV, v, Comp.eval, Expr.eval, Ext.refl_wk, Env.get_zero,
      hq, authQueryToVal, authQenc]
    exact roFixedB_eval S K fhst .zero _ s sec
      (by simp [Ext.step_wk, hfhst]) rfl hB
  | roRootQuery rk dh =>
    unfold authCkStepC AuthSubHops1to3.authCkStepWithPrim
    simp only [caseSumV, v, Comp.eval, Expr.eval, Ext.refl_wk, Env.get_zero,
      hq, authQueryToVal, authQenc]
    exact roRootFixedB_eval S K fhst .zero _ s rk dh
      (by simp [Ext.step_wk, hfhst]) rfl hB
  | revealDhSecrets =>
    unfold authCkStepC AuthSubHops1to3.authCkStepWithPrim AuthSubHops1to3.stepAuthOtherPrim
    simp only [caseSumV, v, aNone, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk,
      Env.get_succ, Env.get_zero, hfhst, hq, authQueryToVal, authQenc]
    cases s.toAuthHybridState.base.hasWonAuth <;> rfl
  | registerKey sk =>
    unfold authCkStepC AuthSubHops1to3.authCkStepWithPrim
    simp only [caseSumV, v, Comp.eval, Expr.eval, Ext.refl_wk, Env.get_zero,
      hq, authQueryToVal, authQenc]
    exact registerFixedB_eval S fhst .zero _ s sk
      (by simp [Ext.step_wk, hfhst]) rfl

@[simp] def prfCkStateToVal {S : Setup} (secb : Bool) (idx : Nat) (p : Bytes × Bytes)
    (hst : AuthHybridStateFixed S) : prfCkStTy.denote :=
  (secb, (idx, (p, authHybridStateFixedToVal hst)))

theorem prfCkHandleDsl_eval (secb : Bool) (idx : Nat) (p : Bytes × Bytes)
    (s : AuthHybridStateFixed S) (q : AuthQuery S) (hB : AuthListsBounded K s) :
    (prfCkHandleDsl S K).eval
      (.cons (prfCkStateToVal secb idx p s) (.cons (authQueryToVal q) .nil)) =
      Prod.map authRespToVal (prfCkStateToVal secb idx p) <$>
        AuthSubHops1to3.authCkStepWithPrim S (AuthSubHops1to3.sampAtCkPrim idx p) q s := by
  unfold prfCkHandleDsl
  repeat' (rw [letV_eval]; simp only [ckSecb, ckIdx, ckChal, ckFhst, v,
    Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, prfCkStateToVal])
  rw [bindV_eval]
  rw [authCkStepC_eval S K _ _ _ _ _ idx p s q rfl rfl rfl rfl hB]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, Prod.map]
  apply bind_congr; intro ⟨resp, s'⟩
  rfl

theorem finishAuthSendCkPrim_bounded {S : Setup} {n : Nat}
    (sid : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry))
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
    (drKey : DRKey) (rk1 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg msgPlain : Bytes)
    (hst : AuthHybridStateFixed S) (p : Bytes × Bytes)
    (hB : AuthListsBounded n hst) :
    AllLeaves (fun x => AuthListsBounded (n + 1) x.2)
      (AuthSubHops1to3.finishAuthSendCkPrim S sid uEntry peerPrincipal? bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt? pqRatchetMsg msgPlain hst p) := by
  unfold AuthSubHops1to3.finishAuthSendCkPrim
  refine AllLeaves.bind_const _ (fun deriveMessageKeys => ?_)
  refine AllLeaves.bind_const _ (fun aeadCt => ?_)
  refine AllLeaves.bind
    (finishAuthHybridSendPrim_bounded sid uEntry peerPrincipal? _ bundle m0 m1
      ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 [] p.1 p.2 spqrSalt?
      pqRatchetMsg deriveMessageKeys _ aeadCt msgPlain hst.toAuthHybridState.base.roCache
      hst.toAuthHybridState.base.rootRoCache hst.toAuthHybridState
      hB.toAuthHybridListsBounded
      (Nat.le_trans hB.roCache_le (Nat.le_succ n))
      (Nat.le_trans hB.rootRoCache_le (Nat.le_succ n))) ?_
  intro ⟨resp, hst'⟩ hB'
  exact AllLeaves.pure ⟨hB', Nat.zero_le _⟩

theorem authCkSendWithPrim_bounded {S : Setup} {n : Nat}
    (sampAt : Nat → OracleComp PrimBaseSpec (Bytes × Bytes))
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) (hB : AuthListsBounded n hst) :
    AllLeaves (fun x => AuthListsBounded (n + 1) x.2)
      (AuthSubHops1to3.authCkSendWithPrim S sampAt sid u bundle m0 m1 hst) := by
  have hB' : AuthListsBounded (n + 1) hst := hB.mono (Nat.le_succ n)
  unfold AuthSubHops1to3.authCkSendWithPrim
  refine AllLeaves.ite _ (fun _ => AllLeaves.pure hB') (fun _ => ?_)
  refine AllLeaves.ite _ (fun _ => AllLeaves.pure hB') (fun _ => ?_)
  refine AllLeaves.ite _ (fun _ => AllLeaves.pure hB') (fun _ => ?_)
  cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
  | none => exact AllLeaves.pure hB'
  | some uP =>
    rcases uP with ⟨_, uEntry⟩
    refine AllLeaves.bind_const _ (fun peerPrincipal? => ?_)
    refine AllLeaves.ite _ (fun _ => AllLeaves.pure hB') (fun _ => ?_)
    refine AllLeaves.bind_const _ (fun koskOk => ?_)
    refine AllLeaves.ite _ (fun _ => AllLeaves.pure hB') (fun _ => ?_)
    refine AllLeaves.bind_const _ (fun ekASk => ?_)
    refine AllLeaves.bind_const _ (fun kemCoins => ?_)
    refine AllLeaves.bind_const _ (fun ephASk => ?_)
    refine AllLeaves.bind_const _ (fun spqrCoins => ?_)
    refine AllLeaves.bind_const _ (fun sigPkB => ?_)
    refine AllLeaves.bind_const _ (fun v1 => ?_)
    refine AllLeaves.bind_const _ (fun v2 => ?_)
    refine AllLeaves.ite _ (fun _ => AllLeaves.pure hB') (fun _ => ?_)
    refine AllLeaves.bind_const _ (fun enc? => ?_)
    cases enc? with
    | none => exact AllLeaves.pure hB'
    | some sc =>
      rcases sc with ⟨ss, kemCt⟩
      refine AllLeaves.bind_const _ (fun ekAPk => ?_)
      refine AllLeaves.bind_const _ (fun ephAPk => ?_)
      refine AllLeaves.bind_const _ (fun spkHonIdeal => ?_)
      refine AllLeaves.ite _ (fun _ => ?_) (fun _ => ?_)
      · refine AllLeaves.bind_const _ (fun drKey => ?_)
        refine AllLeaves.bind_const _ (fun rk1 => ?_)
        refine AllLeaves.bind_const _ (fun sp? => ?_)
        cases sp? with
        | none => exact AllLeaves.pure hB'
        | some sp =>
          rcases sp with ⟨pqrStA, spqrSalt?, pqRatchetMsg⟩
          refine AllLeaves.bind_const _ (fun p => ?_)
          exact finishAuthSendCkPrim_bounded sid uEntry peerPrincipal? bundle m0 m1
            ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt? pqRatchetMsg _
            { hst with slots := (hst.slots.allocSend sid).2 } p
            ⟨hB.toAuthHybridListsBounded, hB.mkSaltCache_le⟩
      · refine AllLeaves.bind_const _ (fun dh1 => ?_)
        refine AllLeaves.bind_const _ (fun dh2 => ?_)
        refine AllLeaves.bind_const _ (fun dh3 => ?_)
        refine AllLeaves.bind_const _ (fun dh4? => ?_)
        refine AllLeaves.bind
          (AllLeaves.embedUnif (evalHkdfRoPure_length_le _ _ hB.roCache_le)) ?_
        intro ⟨drKey, roCache'⟩ hRo
        refine AllLeaves.bind_const _ (fun dhRatchet => ?_)
        refine AllLeaves.bind
          (AllLeaves.embedUnif (evalRootKdfRoPure_length_le _ _ _ hB.rootRoCache_le)) ?_
        intro ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ hRoot
        refine AllLeaves.bind_const _ (fun mkSeed => ?_)
        refine AllLeaves.bind_const _ (fun ck1_1 => ?_)
        refine AllLeaves.bind_const _ (fun sp? => ?_)
        cases sp? with
        | none => exact AllLeaves.pure hB'
        | some sp =>
          rcases sp with ⟨pqrStA, spqrSalt?, pqRatchetMsg⟩
          refine AllLeaves.bind_const _ (fun deriveMessageKeys => ?_)
          refine AllLeaves.bind_const _ (fun aeadCt => ?_)
          refine AllLeaves.bind
            (finishAuthHybridSendPrim_bounded sid uEntry peerPrincipal? _ bundle m0 m1
              ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 ck1_0 mkSeed ck1_1 spqrSalt?
              pqRatchetMsg deriveMessageKeys _ aeadCt _ roCache' rootRoCache' hst.toAuthHybridState
              hB.toAuthHybridListsBounded hRo hRoot) ?_
          intro ⟨resp, hst'⟩ hOut
          exact AllLeaves.pure ⟨hOut, Nat.zero_le _⟩

private theorem finishAuthRecvCkSlotsPrim_bounded {S : Setup} {n : Nat}
    (msg : PreKeyMsg) (prep : PreparedAuthRecvPrim S)
    (drKey : DRKey) (rk1 : Bytes) (spqrSalt? : Option Bytes)
    (recvCount' : Nat) (p : Bytes × Bytes) (slots' : AuthSlotState)
    (hP : PreparedRecvBounded n prep) :
    AllLeaves (fun x => AuthListsBounded (n + 1) x.2)
      (AuthSubHops1to3.finishAuthRecvCkSlotsPrim S msg prep drKey rk1 spqrSalt? recvCount' p slots') := by
  unfold AuthSubHops1to3.finishAuthRecvCkSlotsPrim
  refine AllLeaves.bind_const _ (fun deriveMessageKeys => ?_)
  refine AllLeaves.bind_const _ (fun pt? => ?_)
  refine AllLeaves.bind
    (recvFinishTagRunPrim_bounded true prep.finishTag _ hP.tag_bounded ?_) ?_
  · intro dk rk ck pt roC rootC hEq
    cases pt? with
    | none => cases hEq
    | some pt0 =>
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hEq
      rcases hEq with ⟨_, _, _, _, rfl, rfl⟩
      exact ⟨Nat.le_trans hP.roCache_le (Nat.le_succ n),
        Nat.le_trans hP.rootRoCache_le (Nat.le_succ n)⟩
  · intro ⟨resp, hst'⟩ hOut
    exact AllLeaves.pure ⟨hOut, Nat.zero_le _⟩

theorem finishAuthRecvCkPrim_bounded {S : Setup} {n : Nat}
    (msg : PreKeyMsg) (prep : PreparedAuthRecvPrim S)
    (drKey : DRKey) (rk1 : Bytes) (spqrSalt? : Option Bytes)
    (recvCount' : Nat) (p : Bytes × Bytes)
    (hP : PreparedRecvBounded n prep) :
    AllLeaves (fun x => AuthListsBounded (n + 1) x.2)
      (AuthSubHops1to3.finishAuthRecvCkPrim S msg prep drKey rk1 spqrSalt? recvCount' p) :=
  finishAuthRecvCkSlotsPrim_bounded msg prep drKey rk1 spqrSalt? recvCount' p {} hP

theorem authCkRecvWithPrim_bounded {S : Setup} {n : Nat}
    (sampAt : Nat → OracleComp PrimBaseSpec (Bytes × Bytes))
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecvPrim S))
    (hst : AuthHybridStateFixed S)
    (hB : AuthListsBounded n hst)
    (hPrep : ∀ prep, prep? = some prep → PreparedRecvBounded n prep) :
    AllLeaves (fun x => AuthListsBounded (n + 1) x.2)
      (AuthSubHops1to3.authCkRecvWithPrim S sampAt msg prep? hst) := by
  unfold AuthSubHops1to3.authCkRecvWithPrim
  cases prep? with
  | none =>
    exact AllLeaves.pure ⟨hB.toAuthHybridListsBounded.mono (Nat.le_succ n),
      Nat.le_trans hB.mkSaltCache_le (Nat.le_succ n)⟩
  | some prep =>
    have hP : PreparedRecvBounded n prep := hPrep prep rfl
    have hRunNone :
        AllLeaves (fun x : AuthResponse × AuthHybridStateFixed S => AuthListsBounded (n + 1) x.2)
          ( do
              let (resp, hst') ← prep.finishTag.runPrim S true none
              return (resp, { toAuthHybridState := hst', recvCount := hst.recvCount + 1,
                              slots := hst.slots }) ) := by
      refine AllLeaves.bind
        (recvFinishTagRunPrim_bounded true prep.finishTag none hP.tag_bounded
          (by intro _ _ _ _ _ _ h; cases h)) ?_
      intro ⟨resp, hst'⟩ hOut
      exact AllLeaves.pure ⟨hOut, Nat.zero_le _⟩
    refine AllLeaves.ite _ (fun _ => ?_) (fun _ => ?_)
    · cases prep.matchedSess? with
      | none =>
        refine AllLeaves.bind_const _ (fun drKey => ?_)
        refine AllLeaves.bind_const _ (fun rk1 => ?_)
        refine AllLeaves.bind_const _ (fun sp? => ?_)
        cases sp? with
        | none => exact hRunNone
        | some sp =>
          rcases sp with ⟨pqrStB, spqrSalt?⟩
          refine AllLeaves.bind_const _ (fun p => ?_)
          exact finishAuthRecvCkSlotsPrim_bounded msg prep drKey rk1 spqrSalt? _ p _ hP
      | some s =>
        refine AllLeaves.ite _ (fun _ => ?_) (fun _ => ?_)
        · refine AllLeaves.bind_const _ (fun sp? => ?_)
          cases sp? with
          | none => exact hRunNone
          | some sp =>
            rcases sp with ⟨pqrStB, spqrSalt?⟩
            exact finishAuthRecvCkSlotsPrim_bounded msg prep s.drKey s.rk1 spqrSalt? _ _ _ hP
        · refine AllLeaves.bind_const _ (fun rk1 => ?_)
          refine AllLeaves.bind_const _ (fun sp? => ?_)
          cases sp? with
          | none => exact hRunNone
          | some sp =>
            rcases sp with ⟨pqrStB, spqrSalt?⟩
            refine AllLeaves.bind_const _ (fun p => ?_)
            exact finishAuthRecvCkSlotsPrim_bounded msg prep s.drKey rk1 spqrSalt? _ p _ hP
    · refine AllLeaves.bind
        (AllLeaves.embedUnif (evalHkdfRoPure_length_le _ _ hP.roCache_le)) ?_
      intro ⟨drKey, roCache'⟩ hRo
      refine AllLeaves.bind
        (AllLeaves.embedUnif (evalRootKdfRoPure_length_le _ _ _ hP.rootRoCache_le)) ?_
      intro ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ hRoot
      refine AllLeaves.bind_const _ (fun mkSeed => ?_)
      refine AllLeaves.bind_const _ (fun ck1_1 => ?_)
      refine AllLeaves.bind_const _ (fun sp? => ?_)
      cases sp? with
      | none => exact hRunNone
      | some sp =>
        rcases sp with ⟨pqrStB, spqrSalt?⟩
        refine AllLeaves.bind_const _ (fun deriveMessageKeys => ?_)
        refine AllLeaves.bind_const _ (fun pt? => ?_)
        refine AllLeaves.bind
          (recvFinishTagRunPrim_bounded true prep.finishTag _ hP.tag_bounded ?_) ?_
        · intro dk rk ck pt roC rootC hEq
          cases pt? with
          | none => cases hEq
          | some pt0 =>
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hEq
            rcases hEq with ⟨_, _, _, _, rfl, rfl⟩
            exact ⟨hRo, hRoot⟩
        · intro ⟨resp, hst'⟩ hOut
          exact AllLeaves.pure ⟨hOut, Nat.zero_le _⟩

theorem authCkStepWithPrim_bounded {S : Setup} {n : Nat}
    (sampAt : Nat → OracleComp PrimBaseSpec (Bytes × Bytes))
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) (hB : AuthListsBounded n hst) :
    HoldsOnLeaves (fun x => AuthListsBounded (n + 1) x.2)
      (AuthSubHops1to3.authCkStepWithPrim S sampAt q hst) := by
  apply AllLeaves.toHoldsOnLeaves
  have hB' : AuthListsBounded (n + 1) hst := hB.mono (Nat.le_succ n)
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold AuthSubHops1to3.authCkStepWithPrim
    exact AllLeaves.ite bundle.opkB?.isNone
      (fun _ => AllLeaves.pure hB')
      (fun _ => authCkSendWithPrim_bounded sampAt (.sendOPK u i) u bundle m0 m1 hst hB)
  | sendNoOPK u i bundle m0 m1 =>
    unfold AuthSubHops1to3.authCkStepWithPrim
    exact AllLeaves.ite bundle.opkB?.isSome
      (fun _ => AllLeaves.pure hB')
      (fun _ => authCkSendWithPrim_bounded sampAt (.sendNoOPK u i) u bundle m0 m1 hst hB)
  | recvOPK k j o msg =>
    unfold AuthSubHops1to3.authCkStepWithPrim
    refine AllLeaves.bind
      (prepareAuthHybridRecvOPKPrim_bounded k j o msg hst.toAuthHybridState
        hB.toAuthHybridListsBounded) ?_
    intro prep? hPrep
    exact authCkRecvWithPrim_bounded sampAt msg prep? hst hB hPrep
  | recvNoOPK k j l msg =>
    unfold AuthSubHops1to3.authCkStepWithPrim
    refine AllLeaves.bind
      (prepareAuthHybridRecvNoOPKPrim_bounded k j l msg hst.toAuthHybridState
        hB.toAuthHybridListsBounded) ?_
    intro prep? hPrep
    exact authCkRecvWithPrim_bounded sampAt msg prep? hst hB hPrep
  | initPrin u => exact stepAuthOtherPrim_bounded (.initPrin u) hst hB
  | corruptIK u => exact stepAuthOtherPrim_bounded (.corruptIK u) hst hB
  | genSPK u j => exact stepAuthOtherPrim_bounded (.genSPK u j) hst hB
  | genOPK u j o => exact stepAuthOtherPrim_bounded (.genOPK u j o) hst hB
  | roQuery sec => exact stepAuthOtherPrim_bounded (.roQuery sec) hst hB
  | roRootQuery rk dh => exact stepAuthOtherPrim_bounded (.roRootQuery rk dh) hst hB
  | revealDhSecrets => exact stepAuthOtherPrim_bounded .revealDhSecrets hst hB
  | registerKey sk => exact stepAuthOtherPrim_bounded (.registerKey sk) hst hB

/-- Evaluation equivalence for `prfCkRedProg S K` on any adversary making at most `rem ≤ K` game
    queries. -/
theorem prfCkRedProg_eval_eq_of_bound (S : Setup) (K : Nat)
    (A : AuthAdversary S) (mkSeedChal ck1_1Chal : Bytes)
    (rem : Nat) (hA : IsQueryBoundP A.run (fun q : ℕ ⊕ AuthQuery S => q.isRight = true) rem)
    (hK : rem ≤ K) :
    (prfCkRedProg S K).eval (fun _ => A.run) (mkSeedChal, ck1_1Chal) =
    ( do
        let idx ← embedUnif (RoKem.sampleIndexRange (min K S.N_sess_tot))
        AuthSubHops1to3.authCkPreSampleRunPrim S idx (mkSeedChal, ck1_1Chal) A ) := by
  have hInit :
      (prfCkInitDslK S K).eval (.cons (mkSeedChal, ck1_1Chal) .nil) =
      ( do
          let idx ← embedUnif (RoKem.sampleIndexRange (min K S.N_sess_tot))
          let secb ← embedUnif ($ᵗ Bool)
          pure ((), prfCkStateToVal secb idx (mkSeedChal, ck1_1Chal)
            (AuthHybridStateFixed.empty S secb)) ) := by
    simp only [prfCkInitDslK, bindV, v, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk,
      Env.get_succ, Env.get_zero, samplePrim_index_eval, samplePrim_bool_eval]
    rfl
  unfold CostedReduction.eval CostedReduction.impl prfCkRedProg AuthSubHops1to3.authCkPreSampleRunPrim
  dsimp only [id_eq]
  rw [hInit]
  simp only [bind_assoc, pure_bind]
  apply bind_congr; intro idx
  apply bind_congr; intro secb
  let p := (mkSeedChal, ck1_1Chal)
  have hSim := simulateQ_prim_map_state_bounded
    (prfCkStateToVal secb idx p)
    AuthListsBounded
    (fun h hB => hB.mono h)
    (AuthSubHops1to3.authCkStepWithPrim S (AuthSubHops1to3.sampAtCkPrim idx p))
    (prfCkHandleDsl S K)
    K
    (fun q s hB => prfCkHandleDsl_eval S K secb idx p s q hB)
    (fun n q s hB => authCkStepWithPrim_bounded (AuthSubHops1to3.sampAtCkPrim idx p) q s hB)
    A.run rem hA 0 (AuthHybridStateFixed.empty S secb)
    (authListsBounded_empty S secb) (by omega)
  rw [hSim.2, bind_map_left]
  refine hSim.1.bind_congr _ _ (fun ⟨b', finalSt⟩ hFinB => ?_)
  have hFinK : AuthListsBounded K finalSt := hFinB.mono (by omega)
  simp only [prfCkFinishDsl, letV_eval, ckSecb, ckFhst, ahsfHybrid, Expr.eval,
    Env.get_succ, Env.get_zero, prfCkStateToVal, authHybridStateFixedToVal,
    Prod.map, id_eq]
  exact finalizeAuthFixedDsl_eval S K secb b' finalSt.toAuthHybridState _
    hFinK.toAuthHybridListsBounded

/-- Evaluating `prfCkRedProg S b.q_total` agrees with `(prfCkReductionAuthFixed S b A).dist`. -/
theorem prfCkRedProg_eval_eq (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) (mkSeedChal ck1_1Chal : Bytes) :
    (prfCkRedProg S b.q_total).eval (fun _ => A.1.run) (mkSeedChal, ck1_1Chal) =
    (prfCkReductionAuthFixed S b A).dist mkSeedChal ck1_1Chal := by
  have hA : IsQueryBoundP A.1.run (fun q : ℕ ⊕ AuthQuery S => q.isRight = true) b.q_total := by
    have h := SignalPqxdh.QueryBounded.auth_total A.2
    convert h using 1; funext q; cases q <;> rfl
  exact prfCkRedProg_eval_eq_of_bound S b.q_total A.1 mkSeedChal ck1_1Chal b.q_total hA le_rfl

/-- The `PrfChainKey` adversary obtained by running the `ReductionDsl` program `prfCkRedProg S b.q_total`. -/
def prfCkReductionAuthFixedDslAdv (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) : PrfCkAdv where
  dist mkSeedChal ck1_1Chal :=
    (prfCkRedProg S b.q_total).eval (fun _ => A.1.run) (mkSeedChal, ck1_1Chal)
  q_prf  := (prfCkReductionAuthFixed S b A).q_prf
  q_prim := (prfCkReductionAuthFixed S b A).q_prim

theorem prfCkReductionAuthFixedDslAdv_eq (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    prfCkReductionAuthFixedDslAdv S b A = prfCkReductionAuthFixed S b A := by
  unfold prfCkReductionAuthFixedDslAdv
  congr 1
  funext mkSeedChal ck1_1Chal
  exact prfCkRedProg_eval_eq S b A mkSeedChal ck1_1Chal

/-- For every `S`, `prfCkReductionAuthFixedDslAdv` and `prfCkReductionAuthFixed` have the same
    `PrfChainKey` advantage. -/
theorem prfCkRedProg_prfCk_eq (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    PrfChainKey P (prfCkReductionAuthFixedDslAdv S b A) =
      PrfChainKey P (prfCkReductionAuthFixed S b A) := by
  rw [prfCkReductionAuthFixedDslAdv_eq]

end PrfCkEval

end SignalPqxdh.Security.ReductionDsl.AuthPrf

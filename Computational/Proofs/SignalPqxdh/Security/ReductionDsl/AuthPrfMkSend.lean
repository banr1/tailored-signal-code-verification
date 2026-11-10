/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfMkShallow
import VCVio.EvalDist.Monad.Basic

/-!
# Send Branch of the `PrfMsgKeys` Evaluation Equivalence

Proves that `finishAuthSendMkC` and `authMkSendPreB` evaluate to `finishAuthSendMkPrim` and the
send cases of `mkPre`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthPrf

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh
open SignalPqxdh.LegacyCosted
open SignalPqxdh.Security
open SignalPqxdh.Security.AuthSubHops1to3
open RoKem
open FgGapDh
open OracleSpec OracleComp

section Iface

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List PT}

theorem mkS_peel {m : Type → Type} [Monad m] [LawfulMonad m] {α α' γ δ : Type}
    (F : γ → δ) {x : m α} {x' : m α'} (h : α' → α) {g : α → m δ} {g' : α' → m γ}
    (hx : x = h <$> x') (hg : ∀ a, g (h a) = F <$> g' a) :
    x >>= g = F <$> (x' >>= g') := by
  subst hx; simp only [bind_map_left, map_bind, hg]

theorem mkS_peelS {m : Type → Type} [Monad m] [LawfulMonad m] {α γ δ : Type}
    (F : γ → δ) {x x' : m α} {g : α → m δ} {g' : α → m γ}
    (hx : x = x') (hg : ∀ a, g a = F <$> g' a) :
    x >>= g = F <$> (x' >>= g') := by
  subst hx; rw [map_bind]; exact congrArg _ (funext hg)

theorem mkS_ite {m : Type → Type} [Functor m] {γ δ : Type} (F : γ → δ) {c c' : Prop}
    [Decidable c] [Decidable c'] {a b : m δ} {a' b' : m γ} (hc : c ↔ c')
    (h1 : c' → a = F <$> a') (h2 : ¬ c' → b = F <$> b') :
    (if c then a else b) = F <$> (if c' then a' else b') := by
  by_cases h : c'
  · simp only [hc.mpr h, h, ↓reduceIte]; exact h1 h
  · have h' : ¬ c := fun h' => h (hc.mp h')
    simp only [h, h', ↓reduceIte]; exact h2 h

theorem mkS_pure {m : Type → Type} [Monad m] [LawfulMonad m] {γ δ : Type} (F : γ → δ)
    {a : δ} {a' : γ} (h : a = F a') : (pure a : m δ) = F <$> pure a' := by
  rw [map_pure, h]

theorem mkS_ite_bind {m : Type → Type} [Monad m] {α β : Type} {c : Prop} [Decidable c]
    (x y : m α) (f : α → m β) :
    ((if c then x else y) >>= f) = if c then x >>= f else y >>= f := by
  split <;> rfl

theorem mkS_if_pos {α : Sort _} {c : Prop} [Decidable c] (hc : c) {a b : α} :
    (if c then a else b) = a := by simp [hc]

theorem mkS_if_neg {α : Sort _} {c : Prop} [Decidable c] (hc : ¬ c) {a b : α} :
    (if c then a else b) = b := by simp [hc]

theorem prfMk_take_map_of_le {α β : Type} {K : Nat} (f : α → β) (l : List α) (h : l.length ≤ K) :
    List.take K (List.map f l) = List.map f l := List.take_of_length_le (by simpa using h)

theorem prfMk_any_sid_iff {S : Setup} (l : List (SessionId S)) (P : sessionIdTy.denote → Bool)
    (sid : SessionId S) (hP : ∀ x, P (sessionIdToVal x) = (sid == x)) :
    (l.map sessionIdToVal).any P = l.contains sid := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.any_cons, hP, ih, List.contains_cons]

theorem finishAuthSendMkC_eval (fhst : Var Γ₁ authHybridStateFixedTy)
    (sid : Expr pqxdhOps Δ sessionIdTy) (uE : Expr pqxdhOps Δ principalEntryTy)
    (pp : Expr pqxdhOps Δ (.opt (.prod .nat principalEntryTy))) (isFresh : Expr pqxdhOps Δ .bool)
    (bu : Expr pqxdhOps Δ preKeyBundleTy) (m01 : Expr pqxdhOps Δ (.prod (B 32) (B 32)))
    (keys6 : Expr pqxdhOps Δ keys6Ty)
    (drKey : Expr pqxdhOps Δ drKeyTy) (rk1 mkSeed ck1_1 : Expr pqxdhOps Δ (B 32))
    (spqrSalt? : Expr pqxdhOps Δ (.opt (B 32))) (pqMsg msgPlain : Expr pqxdhOps Δ (B 32))
    (mks : Expr pqxdhOps Δ msgKeysTy) [h₁ : Ext Γ₁ Δ] (env : Env Δ)
    (hst : AuthHybridStateFixed S) (sidv : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry)) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes) (drKeyv : DRKey) (rk1v mkSeedv ck1_1v : Bytes)
    (spqrSaltv? : Option Bytes) (pqMsgv msgPlainv : Bytes) (mk : MessageKeys)
    (hhst : Env.get env (h₁.wk fhst) = authHybridStateFixedToVal hst)
    (hsid : sid.eval env = sessionIdToVal sidv) (huE : uE.eval env = principalEntryToVal uEntry)
    (hpp : pp.eval env = peerPrincipal?.map (Prod.map id principalEntryToVal))
    (hfr : isFresh.eval env = mkFreshPeer peerPrincipal?)
    (hbu : bu.eval env = preKeyBundleToVal bundle) (hm : m01.eval env = (m0, m1))
    (hk : keys6.eval env = (ekASk, (ekAPk, (ss, (kemCt, (ephASk, ephAPk))))))
    (hdr : drKey.eval env = drKeyToVal drKeyv) (hrk : rk1.eval env = rk1v)
    (hms : mkSeed.eval env = mkSeedv) (hck : ck1_1.eval env = ck1_1v)
    (hsa : spqrSalt?.eval env = spqrSaltv?) (hpq : pqMsg.eval env = pqMsgv)
    (hpl : msgPlain.eval env = msgPlainv) (hmk : mks.eval env = msgKeysToVal mk)
    (hB : AuthListsBounded K hst) :
    (finishAuthSendMkC S K fhst sid uE pp isFresh bu m01 keys6 drKey rk1 mkSeed ck1_1
        spqrSalt? pqMsg msgPlain mks).eval env =
      Prod.map authRespToVal authHybridStateFixedToVal <$>
        finishAuthSendMkPrim S sidv uEntry peerPrincipal? bundle m0 m1 ekASk ekAPk ss kemCt
          ephASk ephAPk drKeyv rk1v mkSeedv ck1_1v spqrSaltv? pqMsgv msgPlainv hst mk := by
  unfold finishAuthSendMkC finishAuthSendMkPrim
  repeat' (rw [letV_eval]; simp only [v, ahsfHybrid, ahsBase, peIkAPk, pkbIkB, firstMsgADE_eval,
    Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
    hhst, hsid, huE, hpp, hfr, hbu, hm, hk, hdr, hrk, hms, hck, hsa, hpq, hpl, hmk])
  simp only [bindV, Comp.eval, Expr.eval, Env.get_succ, Env.get_zero,
    queryPrim_eval, evalPrimQ, evalPrimOp]
  simp only [valToMsgKeys_msgKeysToVal, principalEntryToVal, preKeyBundleToVal, bundleV,
    map_eq_bind_pure_comp, bind_assoc]
  apply bind_congr; intro ct
  rw [finishAuthHybridSendC_eval S K _ _ _ sidv uEntry peerPrincipal? (mkFreshPeer peerPrincipal?)
    bundle m0 m1 ekASk ekAPk ss kemCt ephASk ephAPk drKeyv rk1v [] mkSeedv ck1_1v spqrSaltv?
    pqMsgv mk (firstMsgAD uEntry.ikAPk bundle.ikB ephAPk pqMsgv) ct msgPlainv
    hst.toAuthHybridState.base.roCache hst.toAuthHybridState.base.rootRoCache hst.toAuthHybridState
    (by simp) (by simp [Expr.eval, asRoCache, asRootRoCache, principalEntryToVal,
      preKeyBundleToVal, bundleV]) hB.spkBundles_le hB.principals_le hB.opkEntries_le]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  apply bind_congr; intro r
  simp [ahsfRecvCount, ahsfMkSaltCache, Expr.eval, hhst]

private theorem mkS_caseOptV_eq {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {τ υ : PT}
    (e : Expr pqxdhOps Γ (.opt τ)) (kNone : Comp pqxdhOps I Γ υ)
    (kSome : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) υ) (env : Env Γ)
    (val : Option τ.denote) :
    e.eval env = val →
    (caseOptV e kNone kSome).eval env =
      match val with
      | none => kNone.eval env
      | some a => (kSome .zero).eval (.cons a env) := by
  intro h; subst h; exact caseOptV_eval e kNone kSome env

private theorem mkS_iteC_eq {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {υ : PT}
    (c : Expr pqxdhOps Γ .bool) (t e : Comp pqxdhOps I Γ υ) (env : Env Γ)
    (b : Bool) (h : c.eval env = b) :
    (Comp.ite c t e).eval env = (if b then t.eval env else e.eval env) := by
  simp only [Comp.eval, h]

private theorem mkS_queryPrim_eq {Γ : List PT} {t : PTag}
    (arg : Expr pqxdhOps Γ t.dom) (env : Env Γ) (val : t.dom.denote) (h : arg.eval env = val) :
    (queryPrim t arg).eval env = evalPrimOp t val := by
  simp only [queryPrim_eval, h, evalPrimQ]

private theorem mkS_sendGuardE_eval {Γ : List PT} (opk : Bool) (x : Expr pqxdhOps Γ sendQTy)
    (env : Env Γ) (u i : Nat) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hx : x.eval env = (u, (i, (preKeyBundleToVal bundle, (m0, m1))))) :
    (sendGuardE opk x).eval env = (if opk then bundle.opkB?.isNone else bundle.opkB?.isSome) := by
  cases opk <;> cases h : bundle.opkB? <;>
    simp [sendGuardE, pkbOpkB?, Expr.eval, hx, preKeyBundleToVal, bundleV, h]

private theorem mkS_sendSidE_eval {Γ : List PT} (opk : Bool) (x : Expr pqxdhOps Γ sendQTy)
    (env : Env Γ) (u i : Nat) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hx : x.eval env = (u, (i, (preKeyBundleToVal bundle, (m0, m1))))) :
    (if opk then Expr.inl (.pair (.fst x) (.fst (.snd x)))
      else .inr (.inl (.pair (.fst x) (.fst (.snd x)))) : Expr pqxdhOps Γ sessionIdTy).eval env =
    (if opk then Sum.inl (u, i) else Sum.inr (Sum.inl (u, i))) := by
  cases opk <;> simp [Expr.eval, hx]

private theorem mkS_usedSend_eval {Γ₁' Γ₂' Δ' : List PT}
    (st : Var Γ₁' authStateTy) (sid : Var Γ₂' sessionIdTy)
    [h₁' : Ext Γ₁' Δ'] [h₂' : Ext Γ₂' Δ'] (env : Env Δ')
    (baseSt : AuthState S) (sidv : SessionId S)
    (hst : Env.get env (h₁'.wk st) = authStateToVal baseSt)
    (hsid : Env.get env (h₂'.wk sid) = sessionIdToVal sidv)
    (hLen : baseSt.usedSendSessions.length ≤ K) :
    (eAny K (asUsedSendSessions (v st)) fun e => sidEq (v e) (v sid)).eval env =
      baseSt.usedSendSessions.contains sidv := by
  have hTake := prfMk_take_map_of_le sessionIdToVal baseSt.usedSendSessions hLen
  simp only [eAny, asUsedSendSessions, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
    hst, authStateToVal, hTake]
  apply prfMk_any_sid_iff
  intro y
  have hEq := sidEq_eval (.var .zero) (.var (.succ (h₂'.wk sid)))
    (.cons (sessionIdToVal y) env) y sidv rfl
    (by simp [Expr.eval, Env.get_succ, hsid])
  change (sidEq (.var .zero) (.var (.succ (h₂'.wk sid)))).eval
    (.cons (sessionIdToVal y) env) = (sidv == y)
  rw [hEq, BEq.comm]

private theorem mkS_isFreshE_eval {Γ₁' Δ' : List PT}
    (pp : Var Γ₁' (.opt (.prod .nat principalEntryTy)))
    [h₁' : Ext Γ₁' Δ'] (env : Env Δ')
    (peerPrincipal? : Option (Nat × PrincipalEntry))
    (hpp : Env.get env (h₁'.wk pp) = peerPrincipal?.map (Prod.map id principalEntryToVal)) :
    (eCaseOpt (v pp) (.bool false) fun p => .not (peCorrupted (.snd (v p)))).eval env =
      mkFreshPeer peerPrincipal? := by
  cases peerPrincipal? with
  | none => simp [eCaseOpt, mkFreshPeer, v, Expr.eval, hpp]
  | some pP =>
    rcases pP with ⟨pIdx, pEntry⟩
    simp [eCaseOpt, mkFreshPeer, peCorrupted, v, Expr.eval, Ext.refl_wk, hpp,
      Prod.map, principalEntryToVal]

private theorem mkS_pqspkHonE_eval {Γ₁' Γ₂' Γ₃' Δ' : List PT}
    (pp : Var Γ₁' (.opt (.prod .nat principalEntryTy)))
    (st : Var Γ₂' authStateTy) (bu : Var Γ₃' preKeyBundleTy)
    [h₁' : Ext Γ₁' Δ'] [h₂' : Ext Γ₂' Δ'] [h₃' : Ext Γ₃' Δ'] (env : Env Δ')
    (peerPrincipal? : Option (Nat × PrincipalEntry))
    (baseSt : AuthState S) (bundle : PreKeyBundleInput)
    (hpp : Env.get env (h₁'.wk pp) = peerPrincipal?.map (Prod.map id principalEntryToVal))
    (hst : Env.get env (h₂'.wk st) = authStateToVal baseSt)
    (hbu : Env.get env (h₃'.wk bu) = preKeyBundleToVal bundle)
    (hSpk : baseSt.spkBundles.length ≤ K) :
    (eCaseOpt (v pp) (.bool false) fun p =>
      eAny K (asSpkBundles (v st)) fun b =>
        .and (natEq (.fst (.fst (v b))) (.fst (v p)))
          (bytesBeq 1568 (sbPqspkPk (.snd (v b))) (pkbPqspkB (v bu)))).eval env =
      (peerPrincipal?.map (fun p =>
        baseSt.spkBundles.any
          (fun ((u, _), b) => u == p.1 && b.pqspkPk == bundle.pqspkB))).getD false := by
  have hTakeS := prfMk_take_map_of_le (Prod.map id spkBundleEntryToVal) baseSt.spkBundles hSpk
  cases peerPrincipal? with
  | none => simp [eCaseOpt, v, Expr.eval, hpp]
  | some pP =>
    rcases pP with ⟨pIdx, pEntry⟩
    simp [eCaseOpt, eAny, asSpkBundles, sbPqspkPk, pkbPqspkB, natEq_eval, bytesBeq_eval, v,
      Expr.eval, Ext.step_wk, Ext.refl_wk,
      hpp, hst, hbu, authStateToVal, hTakeS, List.any_map, Function.comp_def,
      Prod.map, spkBundleEntryToVal, preKeyBundleToVal, bundleV]

private theorem mkS_dh4OptC_eval {Γ₁' Γ₂' Δ' : List PT}
    (bu : Var Γ₁' preKeyBundleTy) (ekASk : Var Γ₂' (B 32))
    [h₁' : Ext Γ₁' Δ'] [h₂' : Ext Γ₂' Δ'] (env : Env Δ')
    (bundle : PreKeyBundleInput) (ekv : Bytes)
    (hbu : Env.get env (h₁'.wk bu) = preKeyBundleToVal bundle)
    (hek : Env.get env (h₂'.wk ekASk) = ekv) :
    (caseOptV (pkbOpkB? (v bu)) (.ret .none) fun oP =>
      bindV (queryPrim .x25519 (.pair (v ekASk) (.snd (v oP)))) fun d4 =>
      .ret (.some (v d4)) : Comp pqxdhOps pqPrimIface Δ' (.opt (B 32))).eval env =
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
    (env : Env Γ) (ssv : AuthSlotState) (s : SessionId S)
    (hss : ss.eval env = authSlotStateToVal ssv)
    (hsid : sid.eval env = sessionIdToVal s) :
    (allocSendSlotE ss sid).eval env =
      Prod.map id authSlotStateToVal (ssv.allocSend s) := by
  simp only [allocSendSlotE, eLet2, eLet, eCaseSum, eCaseOpt, assNext, assSendOpk,
    assSendNoOpk, assRecv, assMk, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
    Env.get_succ, Env.get_zero, hss, hsid, authSlotStateToVal, AuthSlotState.allocSend]
  cases s with
  | sendOPK u i =>
    simp only [sessionIdToVal, sidV]
    cases ssv.sendOpkTbl u.1 i.1 <;> rfl
  | sendNoOPK u i =>
    simp only [sessionIdToVal, sidV]
    cases ssv.sendNoOpkTbl u.1 i.1 <;> rfl
  | recvOPK _ _ _ => rfl
  | recvNoOPK _ _ _ => rfl

private def mkSendCont (secb : Bool) (idx : Nat) (sc : Bool)
    (sid : SessionId S) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) :
    PreparedAuthSend S → OracleComp PrimBaseSpec prfMkStepPreTy.denote
  | .done resp hst' => pure (mkPreToVal secb idx sc (.inl (resp, hst')))
  | .idealMk uEntry peerPrincipal? ekASk ekAPk ss kemCt ephASk ephAPk
      drKey rk1 spqrSalt? pqRatchetMsg msgPlain =>
    mkPreToVal secb idx sc <$> (do
      let (sIdx, slots') := hst.slots.allocSend sid
      let hst' := { hst with slots := slots' }
      if !sc && (sIdx == idx) then
        let ck1_1 ← embedUnif sampleBytes32
        return .inr (spqrSalt?, .send hst' sid uEntry peerPrincipal? bundle m0 m1 ekASk ekAPk ss
          kemCt ephASk ephAPk drKey rk1 ck1_1 spqrSalt? pqRatchetMsg msgPlain)
      else if decide (sIdx < idx) then
        let ck1_1 ← embedUnif sampleBytes32
        let deriveMessageKeys ← embedUnif sampleMessageKeys80
        let res ← finishAuthSendMkPrim S sid uEntry peerPrincipal? bundle m0 m1
          ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 [] ck1_1
          spqrSalt? pqRatchetMsg msgPlain hst' deriveMessageKeys
        return .inl res
      else
        let mkSeed ← embedUnif sampleBytes32
        let ck1_1 ← embedUnif sampleBytes32
        let deriveMessageKeys ← primQ (.deriveMsgKeys mkSeed spqrSalt?)
        let res ← finishAuthSendMkPrim S sid uEntry peerPrincipal? bundle m0 m1
          ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1
          spqrSalt? pqRatchetMsg msgPlain hst' deriveMessageKeys
        return .inl res)

private theorem mkSendPre_map_eq (secb : Bool) (idx : Nat) (sc : Bool)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) :
    mkPreToVal secb idx sc <$> mkSendPre S idx sid u bundle m0 m1 hst sc =
      (prepareAuthSendMkPrim S sid u bundle m0 m1 hst >>=
        mkSendCont S secb idx sc sid bundle m0 m1 hst) := by
  unfold mkSendPre
  rw [map_bind]
  refine congrArg _ (funext fun r => ?_)
  cases r <;> simp [mkSendCont]

private theorem mkS_ite_eq {α : Type _} {c₁ c₂ : Prop} [Decidable c₁] [Decidable c₂]
    {t₁ e₁ t₂ e₂ : α} (hc : c₁ ↔ c₂) (ht : c₁ → t₁ = t₂) (he : ¬ c₁ → e₁ = e₂) :
    (if c₁ then t₁ else e₁) = (if c₂ then t₂ else e₂) := by
  by_cases h : c₁
  · simp only [h, hc.mp h, ↓reduceIte]; exact ht h
  · have h₂ : ¬ c₂ := fun h' => h (hc.mpr h')
    simp only [h, h₂, ↓reduceIte]; exact he h

syntax "mks_eval" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| mks_eval [$extra,*]) =>
    `(tactic| simp only [v, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk,
      Env.get_succ, Env.get_zero, drKeyToVal, drKeyV, preKeyBundleToVal, bundleV,
      principalEntryToVal, authStateToVal, authHybridStateFixedToVal,
      authHybridStateFixedWithSlotsToVal,
      mkSendCont, mkPreToVal, mkCoreToVal, MkCont.toVal, mkcMk, ahsfMk,
      ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots, finishSendArgsToVal, litB_eval,
      List.map_nil, firstMsgADE_eval, peIkAPk, pkbIkB, pkbSpkB,
      natEq_eval, natLt_expr_eval, bytesBeq_eval, boolOr_eval, isSomeE_eval,
      Option.isSome_map, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      mkS_ite_bind, pure_bind, map_pure, bne, $extra,*])

private theorem authMkSendPreB_ideal_eval
    {Γ₀ Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Γ₇ Γ₈ Γ₉ Γ₁₀ Γ₁₁ Γ₁₂ Γ₁₃ Γ₁₄ Γ₁₅ Δ' : List PT}
    {slotSt : Var Γ₀ authSlotStateTy}
    {secb : Var Γ₁ .bool} {idx : Var Γ₂ .nat} {sentChal : Var Γ₃ .bool}
    {fhst : Var Γ₄ authHybridStateFixedTy} {noneDone : Var Γ₅ prfMkStepPreTy}
    {bu : Var Γ₆ preKeyBundleTy} {m0 : Var Γ₇ (B 32)} {m1 : Var Γ₈ (B 32)}
    {sid : Var Γ₉ sessionIdTy} {uE : Var Γ₁₀ principalEntryTy}
    {pp : Var Γ₁₁ (.opt (.prod .nat principalEntryTy))} {isFresh : Var Γ₁₂ .bool}
    {msgPlain : Var Γ₁₃ (B 32)} {spqrCoins : Var Γ₁₄ (B 32)} {keys6 : Var Γ₁₅ keys6Ty}
    [h₀ : Ext Γ₀ Δ'] [h₁ : Ext Γ₁ Δ'] [h₂ : Ext Γ₂ Δ'] [h₃ : Ext Γ₃ Δ'] [h₄ : Ext Γ₄ Δ']
    [h₅ : Ext Γ₅ Δ'] [h₆ : Ext Γ₆ Δ'] [h₇ : Ext Γ₇ Δ'] [h₈ : Ext Γ₈ Δ']
    [h₉ : Ext Γ₉ Δ'] [h₁₀ : Ext Γ₁₀ Δ'] [h₁₁ : Ext Γ₁₁ Δ'] [h₁₂ : Ext Γ₁₂ Δ']
    [h₁₃ : Ext Γ₁₃ Δ'] [h₁₄ : Ext Γ₁₄ Δ'] [h₁₅ : Ext Γ₁₅ Δ']
    {env : Env Δ'}
    (secbv : Bool) (idxv : Nat) (scv : Bool) (hst : AuthHybridStateFixed S)
    (sidv : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry))
    (bundle : PreKeyBundleInput) (m0v m1v msgPlainv spqrCoinsv : Bytes)
    (ekASkv ekAPkv ssv kemCtv ephASkv ephAPkv : Bytes)
    (hslot : Env.get env (h₀.wk slotSt) = authSlotStateToVal hst.slots)
    (hsecb : Env.get env (h₁.wk secb) = secbv)
    (hidx : Env.get env (h₂.wk idx) = idxv)
    (hsc : Env.get env (h₃.wk sentChal) = scv)
    (hfhst : Env.get env (h₄.wk fhst) = authHybridStateFixedToVal hst)
    (hnone : Env.get env (h₅.wk noneDone) =
      mkPreToVal secbv idxv scv (.inl (.noneResp, hst)))
    (hbu : Env.get env (h₆.wk bu) = preKeyBundleToVal bundle)
    (hm0 : Env.get env (h₇.wk m0) = m0v)
    (hm1 : Env.get env (h₈.wk m1) = m1v)
    (hsid : Env.get env (h₉.wk sid) = sessionIdToVal sidv)
    (huE : Env.get env (h₁₀.wk uE) = principalEntryToVal uEntry)
    (hpp : Env.get env (h₁₁.wk pp) = peerPrincipal?.map (Prod.map id principalEntryToVal))
    (hfr : Env.get env (h₁₂.wk isFresh) = mkFreshPeer peerPrincipal?)
    (hpl : Env.get env (h₁₃.wk msgPlain) = msgPlainv)
    (hspqr : Env.get env (h₁₄.wk spqrCoins) = spqrCoinsv)
    (hk6 : Env.get env (h₁₅.wk keys6) =
      (ekASkv, (ekAPkv, (ssv, (kemCtv, (ephASkv, ephAPkv))))))
    (hB : AuthListsBounded K hst) :
    (bindV (samplePrim .drKey96) fun drKey =>
     bindV (samplePrim .bytes32) fun rk1 =>
     bindV (queryPrim (.spqrInitSend 32 32)
       (.pair (.snd (.snd (v drKey))) (v spqrCoins))) fun sp? =>
     caseOptV (v sp?) (.ret (v noneDone)) fun sp =>
     letV (.fst (.snd (v sp))) fun spqrSalt? =>
     letV (.snd (.snd (v sp))) fun pqMsg =>
     letV (allocSendSlotE (v slotSt) (v sid)) fun sa =>
     letV (.fst (v sa)) fun sIdx =>
     letV (ahsfUpdSlots (v fhst) (slots := .snd (v sa))) fun fhst' =>
     .ite (.and (.not (v sentChal)) (natEq (v sIdx) (v idx)))
       (bindV (samplePrim .bytes32) fun ck1_1 =>
        .ret (.inr (.pair (v spqrSalt?)
          (.inl (.pair (v secb) (.pair (v idx) (.pair (v fhst')
            (.pair (v sid) (.pair (v uE) (.pair (v pp)
              (.pair (v isFresh) (.pair (v bu) (.pair (.pair (v m0) (v m1))
                (.pair (v keys6) (.pair (v drKey) (.pair (v rk1) (.pair (v ck1_1)
                  (.pair (v spqrSalt?) (.pair (v pqMsg) (v msgPlain))))))))))))))))))))
       (.ite (natLt (v sIdx) (v idx))
         (bindV (samplePrim .bytes32) fun ck1_1 =>
          bindV (samplePrim .msgKeys80) fun mks =>
          bindV (finishAuthSendMkC S K fhst' (v sid) (v uE) (v pp) (v isFresh) (v bu)
            (.pair (v m0) (v m1)) (v keys6) (v drKey) (v rk1) (litB 32 []) (v ck1_1)
            (v spqrSalt?) (v pqMsg) (v msgPlain) (v mks)) fun res =>
          .ret (.inl (.pair (.fst (v res))
            (mkcMk (v secb) (v idx) (v sentChal) (.snd (v res))))))
         (bindV (samplePrim .bytes32) fun mkSeed =>
          bindV (samplePrim .bytes32) fun ck1_1 =>
          bindV (queryPrim (.deriveMsgKeys 32) (.pair (v mkSeed) (v spqrSalt?))) fun mks =>
          bindV (finishAuthSendMkC S K fhst' (v sid) (v uE) (v pp) (v isFresh) (v bu)
            (.pair (v m0) (v m1)) (v keys6) (v drKey) (v rk1) (v mkSeed) (v ck1_1)
            (v spqrSalt?) (v pqMsg) (v msgPlain) (v mks)) fun res =>
          .ret (.inl (.pair (.fst (v res))
            (mkcMk (v secb) (v idx) (v sentChal) (.snd (v res)))))))).eval env =
    ((do
        let drKey ← embedUnif sampleDRKey96
        let rk1 ← embedUnif sampleBytes32
        match ← primQ (.spqrInitSend drKey.pqrKey spqrCoinsv) with
        | none => return PreparedAuthSend.done .noneResp hst
        | some (_pqrStA, spqrSalt?, pqRatchetMsg) =>
          return PreparedAuthSend.idealMk uEntry peerPrincipal? ekASkv ekAPkv ssv kemCtv
            ephASkv ephAPkv drKey rk1 spqrSalt? pqRatchetMsg msgPlainv) >>=
      mkSendCont S secbv idxv scv sidv bundle m0v m1v hst) := by
  simp only [bind_assoc]
  rw [bindV_eval, samplePrim_drKey96_eval]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  apply bind_congr; intro drKey
  rw [bindV_eval, samplePrim_bytes32_eval]; try simp only [bind_assoc]
  apply bind_congr; intro rk1
  rw [bindV_eval, mkS_queryPrim_eq _ _ (drKey.pqrKey, spqrCoinsv)
    (by mks_eval [hspqr])]
  dsimp only [evalPrimOp]; try simp only [bind_assoc]
  apply bind_congr; intro sp?
  rw [mkS_caseOptV_eq _ _ _ _ sp? rfl]
  cases sp? with
  | none =>
    mks_eval [hnone]
  | some sp =>
    rcases sp with ⟨pqrStA, spqrSalt?, pqRatchetMsg⟩
    simp only [pure_bind, mkSendCont]
    let sIdx := (hst.slots.allocSend sidv).1
    let slots' := (hst.slots.allocSend sidv).2
    let hst' : AuthHybridStateFixed S := { hst with slots := slots' }
    have hB' : AuthListsBounded K hst' := ⟨hB.toAuthHybridListsBounded, hB.mkSaltCache_le⟩
    rw [letV_eval_eq _ _ _ spqrSalt? rfl]
    rw [letV_eval_eq _ _ _ pqRatchetMsg rfl]
    rw [letV_eval_eq _ _ _ (sIdx, authSlotStateToVal slots')
      (allocSendSlotE_eval S _ _ _ hst.slots sidv
        (by simp only [v, Expr.eval, Ext.step_wk, Env.get_succ, hslot])
        (by simp only [v, Expr.eval, Ext.step_wk, Env.get_succ, hsid]))]
    rw [letV_eval_eq _ _ _ sIdx rfl]
    rw [letV_eval_eq _ _ _ (authHybridStateFixedToVal hst')
      (by simp [hst', v, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, Expr.eval, Ext.step_wk,
        hfhst])]
    rw [mkS_iteC_eq _ _ _ _ (!scv && (sIdx == idxv))
      (by mks_eval [hsc, hidx])]
    refine mkS_ite _ Iff.rfl (fun _ => ?_) (fun _ => ?_)
    · rw [bindV_eval, samplePrim_bytes32_eval]
      refine mkS_peelS _ rfl (fun ck1_1 => mkS_pure _ ?_)
      simp [hst', sIdx, slots', Expr.eval, v, Ext.step_wk, Ext.refl_wk,
        hsecb, hidx, hsid, huE, hpp, hfr, hbu, hm0, hm1, hk6, hpl,
        mkPreToVal, MkCont.toVal]
    · rw [mkS_iteC_eq _ _ _ _ (decide (sIdx < idxv))
        (by mks_eval [hidx])]
      refine mkS_ite _ Iff.rfl (fun _ => ?_) (fun _ => ?_)
      · rw [bindV_eval, samplePrim_bytes32_eval]
        refine mkS_peelS _ rfl (fun ck1_1 => ?_)
        rw [bindV_eval, samplePrim_msgKeys80_eval]
        refine mkS_peel _ msgKeysToVal rfl (fun mk => ?_)
        rw [bindV_eval]
        refine mkS_peel _ (Prod.map authRespToVal authHybridStateFixedToVal) ?_ (fun ⟨r, h'⟩ => ?_)
        · apply finishAuthSendMkC_eval S K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hst' sidv uEntry
            peerPrincipal? bundle m0v m1v ekASkv ekAPkv ssv kemCtv ephASkv ephAPkv
            drKey rk1 [] ck1_1 spqrSalt? pqRatchetMsg msgPlainv mk
          all_goals simp [v, Expr.eval, Ext.step_wk, Ext.refl_wk,
            hsid, huE, hpp, hfr, hbu, hm0, hm1, hk6, hpl, hB']
        · exact mkS_pure _ (by simp [Expr.eval, v, Ext.step_wk, Ext.refl_wk,
            hsecb, hidx, hsc, mkPreToVal, mkCoreToVal])
      · rw [bindV_eval, samplePrim_bytes32_eval]
        refine mkS_peelS _ rfl (fun mkSeed => ?_)
        rw [bindV_eval, samplePrim_bytes32_eval]
        refine mkS_peelS _ rfl (fun ck1_1 => ?_)
        rw [bindV_eval, mkS_queryPrim_eq _ _ (mkSeed, spqrSalt?) rfl]
        dsimp only [evalPrimOp]
        refine mkS_peel _ msgKeysToVal rfl (fun mk => ?_)
        rw [bindV_eval]
        refine mkS_peel _ (Prod.map authRespToVal authHybridStateFixedToVal) ?_ (fun ⟨r, h'⟩ => ?_)
        · apply finishAuthSendMkC_eval S K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hst' sidv uEntry
            peerPrincipal? bundle m0v m1v ekASkv ekAPkv ssv kemCtv ephASkv ephAPkv
            drKey rk1 mkSeed ck1_1 spqrSalt? pqRatchetMsg msgPlainv mk
          all_goals simp [v, Expr.eval, Ext.step_wk, Ext.refl_wk,
            hsid, huE, hpp, hfr, hbu, hm0, hm1, hk6, hpl, hB']
        · exact mkS_pure _ (by simp [Expr.eval, v, Ext.step_wk, Ext.refl_wk,
            hsecb, hidx, hsc, mkPreToVal, mkCoreToVal])

private theorem authMkSendPreB_real_eval
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Γ₇ Γ₈ Γ₉ Γ₁₀ Γ₁₁ Γ₁₂ Γ₁₃ Γ₁₄ Γ₁₅ Γ₁₆ Γ₁₇ Γ₁₈ Γ₁₉ Γ₂₀ Γ₂₁ Δ' : List PT}
    {secb : Var Γ₁ .bool} {idx : Var Γ₂ .nat} {sentChal : Var Γ₃ .bool}
    {fhst : Var Γ₄ authHybridStateFixedTy} {noneDone : Var Γ₅ prfMkStepPreTy}
    {hstV : Var Γ₆ authHybridStateTy} {st : Var Γ₇ authStateTy}
    {bu : Var Γ₈ preKeyBundleTy} {m0 : Var Γ₉ (B 32)} {m1 : Var Γ₁₀ (B 32)}
    {sid : Var Γ₁₁ sessionIdTy} {uE : Var Γ₁₂ principalEntryTy}
    {pp : Var Γ₁₃ (.opt (.prod .nat principalEntryTy))} {isFresh : Var Γ₁₄ .bool}
    {msgPlain : Var Γ₁₅ (B 32)} {ekASk : Var Γ₁₆ (B 32)} {ephASk : Var Γ₁₇ (B 32)}
    {spqrCoins : Var Γ₁₈ (B 32)} {ss : Var Γ₁₉ (B 32)} {ephAPk : Var Γ₂₀ (B 32)}
    {keys6 : Var Γ₂₁ keys6Ty}
    [h₁ : Ext Γ₁ Δ'] [h₂ : Ext Γ₂ Δ'] [h₃ : Ext Γ₃ Δ'] [h₄ : Ext Γ₄ Δ']
    [h₅ : Ext Γ₅ Δ'] [h₆ : Ext Γ₆ Δ'] [h₇ : Ext Γ₇ Δ'] [h₈ : Ext Γ₈ Δ']
    [h₉ : Ext Γ₉ Δ'] [h₁₀ : Ext Γ₁₀ Δ'] [h₁₁ : Ext Γ₁₁ Δ'] [h₁₂ : Ext Γ₁₂ Δ']
    [h₁₃ : Ext Γ₁₃ Δ'] [h₁₄ : Ext Γ₁₄ Δ'] [h₁₅ : Ext Γ₁₅ Δ'] [h₁₆ : Ext Γ₁₆ Δ']
    [h₁₇ : Ext Γ₁₇ Δ'] [h₁₈ : Ext Γ₁₈ Δ'] [h₁₉ : Ext Γ₁₉ Δ'] [h₂₀ : Ext Γ₂₀ Δ']
    [h₂₁ : Ext Γ₂₁ Δ']
    {env : Env Δ'}
    (secbv : Bool) (idxv : Nat) (scv : Bool) (hst : AuthHybridStateFixed S)
    (sidv : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry)) (isFreshPeer : Bool)
    (bundle : PreKeyBundleInput) (m0v m1v msgPlainv : Bytes)
    (ekASkv ekAPkv ssv kemCtv ephASkv ephAPkv spqrCoinsv : Bytes)
    (hsecb : Env.get env (h₁.wk secb) = secbv)
    (hidx : Env.get env (h₂.wk idx) = idxv)
    (hsc : Env.get env (h₃.wk sentChal) = scv)
    (hfhst : Env.get env (h₄.wk fhst) = authHybridStateFixedToVal hst)
    (hnone : Env.get env (h₅.wk noneDone) =
      mkPreToVal secbv idxv scv (.inl (.noneResp, hst)))
    (hhst : Env.get env (h₆.wk hstV) = authHybridStateToVal hst.toAuthHybridState)
    (hstV_eq : Env.get env (h₇.wk st) = authStateToVal hst.toAuthHybridState.base)
    (hbu : Env.get env (h₈.wk bu) = preKeyBundleToVal bundle)
    (hm0 : Env.get env (h₉.wk m0) = m0v)
    (hm1 : Env.get env (h₁₀.wk m1) = m1v)
    (hsid : Env.get env (h₁₁.wk sid) = sessionIdToVal sidv)
    (huE : Env.get env (h₁₂.wk uE) = principalEntryToVal uEntry)
    (hpp : Env.get env (h₁₃.wk pp) = peerPrincipal?.map (Prod.map id principalEntryToVal))
    (hfr : Env.get env (h₁₄.wk isFresh) = isFreshPeer)
    (hpl : Env.get env (h₁₅.wk msgPlain) = msgPlainv)
    (hekSk : Env.get env (h₁₆.wk ekASk) = ekASkv)
    (hephSk : Env.get env (h₁₇.wk ephASk) = ephASkv)
    (hspqr : Env.get env (h₁₈.wk spqrCoins) = spqrCoinsv)
    (hss : Env.get env (h₁₉.wk ss) = ssv)
    (hephPk : Env.get env (h₂₀.wk ephAPk) = ephAPkv)
    (hk6 : Env.get env (h₂₁.wk keys6) =
      (ekASkv, (ekAPkv, (ssv, (kemCtv, (ephASkv, ephAPkv))))))
    (hB : AuthListsBounded K hst) :
    (bindV (queryPrim .x25519 (.pair (peSecIKA0 (v uE)) (pkbSpkB (v bu)))) fun dh1 =>
     bindV (queryPrim .x25519 (.pair (v ekASk) (pkbIkB (v bu)))) fun dh2 =>
     bindV (queryPrim .x25519 (.pair (v ekASk) (pkbSpkB (v bu)))) fun dh3 =>
     bindV (caseOptV (pkbOpkB? (v bu)) (.ret .none) fun oP =>
       bindV (queryPrim .x25519 (.pair (v ekASk) (.snd (v oP)))) fun d4 =>
       .ret (.some (v d4))) fun dh4? =>
     letV (buildSecretsE (v dh1) (v dh2) (v dh3) (v dh4?) (v ss)) fun secrets =>
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
     bindV (finishAuthHybridSendC S K hstV
       (.pair (v sid) (.pair (v uE) (.pair (v pp) (.pair (v isFresh) (.pair (v bu)
         (.pair (.pair (v m0) (v m1)) (.pair (v keys6)
           (.pair (v drKey) (.pair (.pair (v rk1) (.pair (v ck1_0) (.pair (v mkSeed) (v ck1_1))))
             (.pair (v spqrSalt?) (.pair (v pqMsg) (.pair (v mks)
               (.pair (v ad) (.pair (v aeadCt) (.pair (v msgPlain)
                 (.pair (v roC') (v rootC')))))))))))))))))) fun out =>
     .ret (.inl (.pair (.fst (v out))
       (mkcMk (v secb) (v idx) (v sentChal)
         (ahsfUpd (v fhst) (hst := .snd (v out))))))).eval env =
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
          embedUnif (evalHkdfRoPure hst.toAuthHybridState.base.roCache secrets)
        let dhRatchet ← primQ (.x25519 ephASkv bundle.spkB)
        let ((rk1, ck1_0), rootRoCache') ←
          embedUnif (evalRootKdfRoPure hst.toAuthHybridState.base.rootRoCache
            drKey.rootKey dhRatchet)
        let mkSeed ← primQ (.chainKdfSeed ck1_0)
        let ck1_1 ← primQ (.chainKdfNext ck1_0)
        match ← primQ (.spqrInitSend drKey.pqrKey spqrCoinsv) with
        | none => return PreparedAuthSend.done .noneResp hst
        | some (_pqrStA, spqrSalt?, pqRatchetMsg) =>
          let deriveMessageKeys ← primQ (.deriveMsgKeys mkSeed spqrSalt?)
          let ad := firstMsgAD uEntry.ikAPk bundle.ikB ephAPkv pqRatchetMsg
          let aeadCt ← primQ (.aeadEnc deriveMessageKeys ad msgPlainv)
          let (resp, hst') ←
            finishAuthHybridSendPrim S sidv uEntry peerPrincipal? isFreshPeer
              bundle m0v m1v ekASkv ekAPkv ssv kemCtv ephASkv ephAPkv drKey rk1 ck1_0 mkSeed ck1_1
              spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlainv roCache' rootRoCache'
              hst.toAuthHybridState
          return PreparedAuthSend.done resp { toAuthHybridState := hst',
                                              recvCount := hst.recvCount,
                                              mkSaltCache := hst.mkSaltCache,
                                              slots := hst.slots }) >>=
      mkSendCont S secbv idxv scv sidv bundle m0v m1v hst) := by
  simp only [bind_assoc]
  rw [bindV_eval, mkS_queryPrim_eq _ _ (uEntry.secIKA0, bundle.spkB)
    (by simp [v, peSecIKA0, pkbSpkB, Expr.eval, huE, hbu, principalEntryToVal, preKeyBundleToVal,
      bundleV])]
  dsimp only [evalPrimOp]; try simp only [bind_assoc]
  apply bind_congr; intro dh1
  rw [bindV_eval, mkS_queryPrim_eq _ _ (ekASkv, bundle.ikB)
    (by simp [v, pkbIkB, Expr.eval, Ext.step_wk, hekSk, hbu, preKeyBundleToVal, bundleV])]
  dsimp only [evalPrimOp]; try simp only [bind_assoc]
  apply bind_congr; intro dh2
  rw [bindV_eval, mkS_queryPrim_eq _ _ (ekASkv, bundle.spkB)
    (by simp [v, pkbSpkB, Expr.eval, Ext.step_wk, hekSk, hbu, preKeyBundleToVal, bundleV])]
  dsimp only [evalPrimOp]; try simp only [bind_assoc]
  apply bind_congr; intro dh3
  rw [bindV_eval, mkS_dh4OptC_eval _ _ _ bundle ekASkv
    (by simp [Ext.step_wk, hbu]) (by simp [Ext.step_wk, hekSk])]
  apply bind_congr; intro dh4?
  let secrets := buildSecrets dh1 dh2 dh3 dh4? ssv
  rw [letV_eval_eq _ _ _ secrets
    (by simp [secrets, v, buildSecretsE_eval, Expr.eval, Ext.step_wk, Ext.refl_wk, hss])]
  rw [bindV_eval, hkdfRoC_eval S K _ _ _ hst.toAuthHybridState.base
    (by simp [Ext.step_wk, hstV_eq]) hB.roCache_le]
  simp only [v, Expr.eval, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_def, Prod.map]
  apply bind_congr; intro ⟨drKey, roCache'⟩
  rw [letV_eval_eq _ _ _ (drKeyToVal drKey) rfl]
  rw [letV_eval_eq _ _ _ (roCache'.map (Prod.map id drKeyToVal)) rfl]
  rw [bindV_eval, mkS_queryPrim_eq _ _ (ephASkv, bundle.spkB)
    (by simp [pkbSpkB, Expr.eval, Ext.step_wk, hephSk, hbu, preKeyBundleToVal, bundleV])]
  dsimp only [evalPrimOp]; try simp only [bind_assoc]
  apply bind_congr; intro dhRatchet
  rw [bindV_eval, rootRoC_eval S K _ _ _ _ hst.toAuthHybridState.base
    (by simp [Ext.step_wk, hstV_eq]) hB.rootRoCache_le]
  mks_eval []; try simp only [bind_assoc]
  apply bind_congr; intro ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
  rw [letV_eval_eq _ _ _ rk1 rfl]
  rw [letV_eval_eq _ _ _ ck1_0 rfl]
  rw [letV_eval_eq _ _ _ rootRoCache' rfl]
  rw [bindV_eval, mkS_queryPrim_eq _ _ ck1_0 rfl]
  dsimp only [evalPrimOp]; try simp only [bind_assoc]
  apply bind_congr; intro mkSeed
  rw [bindV_eval, mkS_queryPrim_eq _ _ ck1_0 rfl]
  dsimp only [evalPrimOp]; try simp only [bind_assoc]
  apply bind_congr; intro ck1_1
  rw [bindV_eval, mkS_queryPrim_eq _ _ (drKey.pqrKey, spqrCoinsv)
    (by mks_eval [hspqr])]
  dsimp only [evalPrimOp]; try simp only [bind_assoc]
  apply bind_congr; intro sp?
  rw [mkS_caseOptV_eq _ _ _ _ sp? rfl]
  cases sp? with
  | none =>
    mks_eval [hnone]
  | some sp =>
    rcases sp with ⟨pqrStA, spqrSalt?, pqRatchetMsg⟩
    dsimp only
    rw [letV_eval_eq _ _ _ spqrSalt? rfl]
    rw [letV_eval_eq _ _ _ pqRatchetMsg rfl]
    rw [bindV_eval, mkS_queryPrim_eq _ _ (mkSeed, spqrSalt?) rfl]
    dsimp only [evalPrimOp]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
    apply bind_congr; intro mks
    rw [letV_eval_eq _ _ _
      (firstMsgAD uEntry.ikAPk bundle.ikB ephAPkv pqRatchetMsg)
      (by mks_eval [huE, hbu, hephPk])]
    rw [bindV_eval, mkS_queryPrim_eq _ _
      (msgKeysToVal mks,
        (firstMsgAD uEntry.ikAPk bundle.ikB ephAPkv pqRatchetMsg, msgPlainv))
      (by mks_eval [hpl])]
    dsimp only [evalPrimOp]
    rw [valToMsgKeys_msgKeysToVal]; try simp only [bind_assoc]
    apply bind_congr; intro aeadCt
    rw [bindV_eval]
    rw [finishAuthHybridSendC_eval S K _ _ _ sidv uEntry peerPrincipal?
      isFreshPeer bundle m0v m1v ekASkv ekAPkv ssv kemCtv ephASkv ephAPkv
      drKey rk1 ck1_0 mkSeed ck1_1 spqrSalt? pqRatchetMsg mks
      (firstMsgAD uEntry.ikAPk bundle.ikB ephAPkv pqRatchetMsg)
      aeadCt msgPlainv roCache' rootRoCache' hst.toAuthHybridState
      (by simp [Ext.step_wk, hhst])
      (by mks_eval [hsid, huE, hpp, hfr, hbu, hm0, hm1, hk6, hpl])
      hB.spkBundles_le hB.principals_le hB.opkEntries_le]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, Prod.map]
    apply bind_congr; intro ⟨resp, hst'⟩
    mks_eval [hsecb, hidx, hsc, hfhst]

private theorem authMkSendPreB_afterKem_eval
    {Γ₀ Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Γ₇ Γ₈ Γ₉ Γ₁₀ Γ₁₁ Γ₁₂ Γ₁₃ Γ₁₄ Γ₁₅ Γ₁₆ Γ₁₇ Γ₁₈ Γ₁₉ Δ' : List PT}
    {slotSt : Var Γ₀ authSlotStateTy}
    {secb : Var Γ₁ .bool} {idx : Var Γ₂ .nat} {sentChal : Var Γ₃ .bool}
    {fhst : Var Γ₄ authHybridStateFixedTy} {noneDone : Var Γ₅ prfMkStepPreTy}
    {hstV : Var Γ₆ authHybridStateTy} {st : Var Γ₇ authStateTy}
    {bu : Var Γ₈ preKeyBundleTy} {m0 : Var Γ₉ (B 32)} {m1 : Var Γ₁₀ (B 32)}
    {sid : Var Γ₁₁ sessionIdTy} {uE : Var Γ₁₂ principalEntryTy}
    {pp : Var Γ₁₃ (.opt (.prod .nat principalEntryTy))} {isFresh : Var Γ₁₄ .bool}
    {msgPlain : Var Γ₁₅ (B 32)} {ekASk : Var Γ₁₆ (B 32)} {ephASk : Var Γ₁₇ (B 32)}
    {spqrCoins : Var Γ₁₈ (B 32)} {sc : Var Γ₁₉ (.prod (B 32) (B 1568))}
    [h₀ : Ext Γ₀ Δ'] [h₁ : Ext Γ₁ Δ'] [h₂ : Ext Γ₂ Δ'] [h₃ : Ext Γ₃ Δ'] [h₄ : Ext Γ₄ Δ']
    [h₅ : Ext Γ₅ Δ'] [h₆ : Ext Γ₆ Δ'] [h₇ : Ext Γ₇ Δ'] [h₈ : Ext Γ₈ Δ']
    [h₉ : Ext Γ₉ Δ'] [h₁₀ : Ext Γ₁₀ Δ'] [h₁₁ : Ext Γ₁₁ Δ'] [h₁₂ : Ext Γ₁₂ Δ']
    [h₁₃ : Ext Γ₁₃ Δ'] [h₁₄ : Ext Γ₁₄ Δ'] [h₁₅ : Ext Γ₁₅ Δ'] [h₁₆ : Ext Γ₁₆ Δ']
    [h₁₇ : Ext Γ₁₇ Δ'] [h₁₈ : Ext Γ₁₈ Δ'] [h₁₉ : Ext Γ₁₉ Δ']
    {env : Env Δ'}
    (secbv : Bool) (idxv : Nat) (scv : Bool) (hst : AuthHybridStateFixed S)
    (sidv : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry))
    (bundle : PreKeyBundleInput) (m0v m1v msgPlainv : Bytes)
    (ekASkv ephASkv spqrCoinsv ssv kemCtv : Bytes)
    (hslot : Env.get env (h₀.wk slotSt) = authSlotStateToVal hst.slots)
    (hsecb : Env.get env (h₁.wk secb) = secbv)
    (hidx : Env.get env (h₂.wk idx) = idxv)
    (hsc : Env.get env (h₃.wk sentChal) = scv)
    (hfhst : Env.get env (h₄.wk fhst) = authHybridStateFixedToVal hst)
    (hnone : Env.get env (h₅.wk noneDone) =
      mkPreToVal secbv idxv scv (.inl (.noneResp, hst)))
    (hhst : Env.get env (h₆.wk hstV) = authHybridStateToVal hst.toAuthHybridState)
    (hstV_eq : Env.get env (h₇.wk st) = authStateToVal hst.toAuthHybridState.base)
    (hbu : Env.get env (h₈.wk bu) = preKeyBundleToVal bundle)
    (hm0 : Env.get env (h₉.wk m0) = m0v)
    (hm1 : Env.get env (h₁₀.wk m1) = m1v)
    (hsid : Env.get env (h₁₁.wk sid) = sessionIdToVal sidv)
    (huE : Env.get env (h₁₂.wk uE) = principalEntryToVal uEntry)
    (hpp : Env.get env (h₁₃.wk pp) = peerPrincipal?.map (Prod.map id principalEntryToVal))
    (hfr : Env.get env (h₁₄.wk isFresh) = mkFreshPeer peerPrincipal?)
    (hpl : Env.get env (h₁₅.wk msgPlain) = msgPlainv)
    (hekSk : Env.get env (h₁₆.wk ekASk) = ekASkv)
    (hephSk : Env.get env (h₁₇.wk ephASk) = ephASkv)
    (hspqr : Env.get env (h₁₈.wk spqrCoins) = spqrCoinsv)
    (hscP : Env.get env (h₁₉.wk sc) = (ssv, kemCtv))
    (hB : AuthListsBounded K hst) :
    (letV (.fst (v sc)) fun ss =>
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
     letV (.pair (v ekASk) (.pair (v ekAPk) (.pair (v ss) (.pair (v kemCt)
         (.pair (v ephASk) (v ephAPk)))))) fun keys6 =>
     .ite (v isIdealSend)
       (bindV (samplePrim .drKey96) fun drKey =>
        bindV (samplePrim .bytes32) fun rk1 =>
        bindV (queryPrim (.spqrInitSend 32 32)
          (.pair (.snd (.snd (v drKey))) (v spqrCoins))) fun sp? =>
        caseOptV (v sp?) (.ret (v noneDone)) fun sp =>
        letV (.fst (.snd (v sp))) fun spqrSalt? =>
        letV (.snd (.snd (v sp))) fun pqMsg =>
        letV (allocSendSlotE (v slotSt) (v sid)) fun sa =>
        letV (.fst (v sa)) fun sIdx =>
        letV (ahsfUpdSlots (v fhst) (slots := .snd (v sa))) fun fhst' =>
        .ite (.and (.not (v sentChal)) (natEq (v sIdx) (v idx)))
          (bindV (samplePrim .bytes32) fun ck1_1 =>
           .ret (.inr (.pair (v spqrSalt?)
             (.inl (.pair (v secb) (.pair (v idx) (.pair (v fhst')
               (.pair (v sid) (.pair (v uE) (.pair (v pp)
                 (.pair (v isFresh) (.pair (v bu) (.pair (.pair (v m0) (v m1))
                   (.pair (v keys6) (.pair (v drKey) (.pair (v rk1) (.pair (v ck1_1)
                     (.pair (v spqrSalt?) (.pair (v pqMsg) (v msgPlain))))))))))))))))))))
          (.ite (natLt (v sIdx) (v idx))
            (bindV (samplePrim .bytes32) fun ck1_1 =>
             bindV (samplePrim .msgKeys80) fun mks =>
             bindV (finishAuthSendMkC S K fhst' (v sid) (v uE) (v pp) (v isFresh) (v bu)
               (.pair (v m0) (v m1)) (v keys6) (v drKey) (v rk1) (litB 32 []) (v ck1_1)
               (v spqrSalt?) (v pqMsg) (v msgPlain) (v mks)) fun res =>
             .ret (.inl (.pair (.fst (v res))
               (mkcMk (v secb) (v idx) (v sentChal) (.snd (v res))))))
            (bindV (samplePrim .bytes32) fun mkSeed =>
             bindV (samplePrim .bytes32) fun ck1_1 =>
             bindV (queryPrim (.deriveMsgKeys 32) (.pair (v mkSeed) (v spqrSalt?))) fun mks =>
             bindV (finishAuthSendMkC S K fhst' (v sid) (v uE) (v pp) (v isFresh) (v bu)
               (.pair (v m0) (v m1)) (v keys6) (v drKey) (v rk1) (v mkSeed) (v ck1_1)
               (v spqrSalt?) (v pqMsg) (v msgPlain) (v mks)) fun res =>
             .ret (.inl (.pair (.fst (v res))
               (mkcMk (v secb) (v idx) (v sentChal) (.snd (v res))))))))
       (bindV (queryPrim .x25519 (.pair (peSecIKA0 (v uE)) (pkbSpkB (v bu)))) fun dh1 =>
        bindV (queryPrim .x25519 (.pair (v ekASk) (pkbIkB (v bu)))) fun dh2 =>
        bindV (queryPrim .x25519 (.pair (v ekASk) (pkbSpkB (v bu)))) fun dh3 =>
        bindV (caseOptV (pkbOpkB? (v bu)) (.ret .none) fun oP =>
          bindV (queryPrim .x25519 (.pair (v ekASk) (.snd (v oP)))) fun d4 =>
          .ret (.some (v d4))) fun dh4? =>
        letV (buildSecretsE (v dh1) (v dh2) (v dh3) (v dh4?) (v ss)) fun secrets =>
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
        bindV (finishAuthHybridSendC S K hstV
          (.pair (v sid) (.pair (v uE) (.pair (v pp) (.pair (v isFresh) (.pair (v bu)
            (.pair (.pair (v m0) (v m1)) (.pair (v keys6)
              (.pair (v drKey) (.pair (.pair (v rk1) (.pair (v ck1_0) (.pair (v mkSeed) (v ck1_1))))
                (.pair (v spqrSalt?) (.pair (v pqMsg) (.pair (v mks)
                  (.pair (v ad) (.pair (v aeadCt) (.pair (v msgPlain)
                    (.pair (v roC') (v rootC')))))))))))))))))) fun out =>
        .ret (.inl (.pair (.fst (v out))
          (mkcMk (v secb) (v idx) (v sentChal)
            (ahsfUpd (v fhst) (hst := .snd (v out)))))))).eval
      env =
    ((let isFreshPeer := mkFreshPeer peerPrincipal?
      do
        let ekAPk ← primQ (.x25519Base ekASkv)
        let ephAPk ← primQ (.x25519Base ephASkv)
        let spkHonIdeal ← checkBundleSpkHonIdealPrim S hst.toAuthHybridState.base.principals
          hst.toAuthHybridState.base.spkBundles bundle
        let pqspkHon : Bool :=
          (peerPrincipal?.map (fun p =>
            hst.toAuthHybridState.base.spkBundles.any
              (fun ((u, _), b) => u == p.1 && b.pqspkPk == bundle.pqspkB))).getD false
        let isIdealSend : Bool :=
          isFreshPeer || (peerPrincipal?.isSome && spkHonIdeal && pqspkHon)
        if isIdealSend then
          let drKey ← embedUnif sampleDRKey96
          let rk1 ← embedUnif sampleBytes32
          match ← primQ (.spqrInitSend drKey.pqrKey spqrCoinsv) with
          | none => return PreparedAuthSend.done .noneResp hst
          | some (_pqrStA, spqrSalt?, pqRatchetMsg) =>
            return PreparedAuthSend.idealMk uEntry peerPrincipal? ekASkv ekAPk ssv kemCtv
              ephASkv ephAPk drKey rk1 spqrSalt? pqRatchetMsg msgPlainv
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
            embedUnif (evalHkdfRoPure hst.toAuthHybridState.base.roCache secrets)
          let dhRatchet ← primQ (.x25519 ephASkv bundle.spkB)
          let ((rk1, ck1_0), rootRoCache') ←
            embedUnif (evalRootKdfRoPure hst.toAuthHybridState.base.rootRoCache
              drKey.rootKey dhRatchet)
          let mkSeed ← primQ (.chainKdfSeed ck1_0)
          let ck1_1 ← primQ (.chainKdfNext ck1_0)
          match ← primQ (.spqrInitSend drKey.pqrKey spqrCoinsv) with
          | none => return PreparedAuthSend.done .noneResp hst
          | some (_pqrStA, spqrSalt?, pqRatchetMsg) =>
            let deriveMessageKeys ← primQ (.deriveMsgKeys mkSeed spqrSalt?)
            let ad := firstMsgAD uEntry.ikAPk bundle.ikB ephAPk pqRatchetMsg
            let aeadCt ← primQ (.aeadEnc deriveMessageKeys ad msgPlainv)
            let (resp, hst') ←
              finishAuthHybridSendPrim S sidv uEntry peerPrincipal? isFreshPeer
                bundle m0v m1v ekASkv ekAPk ssv kemCtv ephASkv ephAPk drKey rk1 ck1_0 mkSeed ck1_1
                spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlainv roCache' rootRoCache'
                hst.toAuthHybridState
            return PreparedAuthSend.done resp { toAuthHybridState := hst',
                                                recvCount := hst.recvCount,
                                                mkSaltCache := hst.mkSaltCache,
                                                slots := hst.slots }) >>=
      mkSendCont S secbv idxv scv sidv bundle m0v m1v hst) := by
  dsimp only
  rw [letV_eval_eq _ _ _ ssv (by simp [v, Expr.eval, hscP])]
  rw [letV_eval_eq _ _ _ kemCtv (by simp [v, Expr.eval, Ext.step_wk, hscP])]
  rw [bindV_eval, mkS_queryPrim_eq _ _ ekASkv (by simp [v, Expr.eval, Ext.step_wk, hekSk])]
  dsimp only [evalPrimOp]; try simp only [bind_assoc]
  apply bind_congr; intro ekAPk
  rw [bindV_eval, mkS_queryPrim_eq _ _ ephASkv (by simp [v, Expr.eval, Ext.step_wk, hephSk])]
  dsimp only [evalPrimOp]; try simp only [bind_assoc]
  apply bind_congr; intro ephAPk
  rw [bindV_eval, checkBundleSpkHonIdealC_eval S _ _ _ hst.toAuthHybridState.base bundle
    (by simp [Ext.step_wk, hstV_eq]) (by simp [Ext.step_wk, hbu]) hB.principals_le
    hB.spkBundles_le]
  try simp only [bind_assoc]
  apply bind_congr; intro spkHonIdeal
  let pqspkHon : Bool :=
    (peerPrincipal?.map (fun p =>
      hst.toAuthHybridState.base.spkBundles.any
        (fun ((u, _), b) => u == p.1 && b.pqspkPk == bundle.pqspkB))).getD false
  rw [letV_eval_eq _ _ _ pqspkHon
    (by exact mkS_pqspkHonE_eval S K _ _ _ _
          peerPrincipal? hst.toAuthHybridState.base bundle
          (by simp [Ext.step_wk, hpp]) (by simp [Ext.step_wk, hstV_eq])
          (by simp [Ext.step_wk, hbu]) hB.spkBundles_le)]
  let isFreshPeer := mkFreshPeer peerPrincipal?
  let isIdealSend : Bool :=
    isFreshPeer || (peerPrincipal?.isSome && spkHonIdeal && pqspkHon)
  rw [letV_eval_eq _ _ _ isIdealSend
    (by simp [isIdealSend, isFreshPeer, v, boolOr_eval, isSomeE_eval, Expr.eval,
      Ext.step_wk, Ext.refl_wk, hfr, hpp, Option.isSome_map])]
  rw [letV_eval_eq _ _ _ (ekASkv, (ekAPk, (ssv, (kemCtv, (ephASkv, ephAPk)))))
    (by simp [v, Expr.eval, Ext.step_wk, Ext.refl_wk, hekSk, hephSk])]
  rw [mkS_iteC_eq _ _ _ _ isIdealSend rfl]
  change _ = ((if isIdealSend = true then (_ : OracleComp PrimBaseSpec _) else _)
    >>= mkSendCont S secbv idxv scv sidv bundle m0v m1v hst)
  cases hIdeal : isIdealSend with
  | true =>
    simp only [↓reduceIte]
    apply authMkSendPreB_ideal_eval S K secbv idxv scv hst sidv uEntry peerPrincipal? bundle
      m0v m1v msgPlainv spqrCoinsv ekASkv ekAPk ssv kemCtv ephASkv ephAPk
    all_goals simp [Ext.step_wk, hslot, hsecb, hidx, hsc, hfhst, hnone, hbu, hm0, hm1,
      hsid, huE, hpp, hfr, hpl, hspqr, hB]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    apply authMkSendPreB_real_eval S K secbv idxv scv hst sidv uEntry peerPrincipal? isFreshPeer
      bundle m0v m1v msgPlainv ekASkv ekAPk ssv kemCtv ephASkv ephAPk spqrCoinsv
    all_goals simp [isFreshPeer, Ext.step_wk, hsecb, hidx, hsc, hfhst, hnone, hhst, hstV_eq,
      hbu, hm0, hm1, hsid, huE, hpp, hfr, hpl, hekSk, hephSk, hspqr, hB]

private theorem authMkSendPreB_afterKosk_eval
    {Γ₀ Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Γ₇ Γ₈ Γ₉ Γ₁₀ Γ₁₁ Γ₁₂ Γ₁₃ Γ₁₄ Γ₁₅ Δ' : List PT}
    {slotSt : Var Γ₀ authSlotStateTy}
    {secb : Var Γ₁ .bool} {idx : Var Γ₂ .nat} {sentChal : Var Γ₃ .bool}
    {fhst : Var Γ₄ authHybridStateFixedTy} {noneDone : Var Γ₅ prfMkStepPreTy}
    {hstV : Var Γ₆ authHybridStateTy} {st : Var Γ₇ authStateTy}
    {bu : Var Γ₈ preKeyBundleTy} {m0 : Var Γ₉ (B 32)} {m1 : Var Γ₁₀ (B 32)}
    {sid : Var Γ₁₁ sessionIdTy} {uE : Var Γ₁₂ principalEntryTy}
    {pp : Var Γ₁₃ (.opt (.prod .nat principalEntryTy))} {isFresh : Var Γ₁₄ .bool}
    {msgPlain : Var Γ₁₅ (B 32)}
    [h₀ : Ext Γ₀ Δ'] [h₁ : Ext Γ₁ Δ'] [h₂ : Ext Γ₂ Δ'] [h₃ : Ext Γ₃ Δ'] [h₄ : Ext Γ₄ Δ']
    [h₅ : Ext Γ₅ Δ'] [h₆ : Ext Γ₆ Δ'] [h₇ : Ext Γ₇ Δ'] [h₈ : Ext Γ₈ Δ']
    [h₉ : Ext Γ₉ Δ'] [h₁₀ : Ext Γ₁₀ Δ'] [h₁₁ : Ext Γ₁₁ Δ'] [h₁₂ : Ext Γ₁₂ Δ']
    [h₁₃ : Ext Γ₁₃ Δ'] [h₁₄ : Ext Γ₁₄ Δ'] [h₁₅ : Ext Γ₁₅ Δ']
    {env : Env Δ'}
    (secbv : Bool) (idxv : Nat) (scv : Bool) (hst : AuthHybridStateFixed S)
    (sidv : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry))
    (bundle : PreKeyBundleInput) (m0v m1v msgPlainv : Bytes)
    (hslot : Env.get env (h₀.wk slotSt) = authSlotStateToVal hst.slots)
    (hsecb : Env.get env (h₁.wk secb) = secbv)
    (hidx : Env.get env (h₂.wk idx) = idxv)
    (hsc : Env.get env (h₃.wk sentChal) = scv)
    (hfhst : Env.get env (h₄.wk fhst) = authHybridStateFixedToVal hst)
    (hnone : Env.get env (h₅.wk noneDone) =
      mkPreToVal secbv idxv scv (.inl (.noneResp, hst)))
    (hhst : Env.get env (h₆.wk hstV) = authHybridStateToVal hst.toAuthHybridState)
    (hstV_eq : Env.get env (h₇.wk st) = authStateToVal hst.toAuthHybridState.base)
    (hbu : Env.get env (h₈.wk bu) = preKeyBundleToVal bundle)
    (hm0 : Env.get env (h₉.wk m0) = m0v)
    (hm1 : Env.get env (h₁₀.wk m1) = m1v)
    (hsid : Env.get env (h₁₁.wk sid) = sessionIdToVal sidv)
    (huE : Env.get env (h₁₂.wk uE) = principalEntryToVal uEntry)
    (hpp : Env.get env (h₁₃.wk pp) = peerPrincipal?.map (Prod.map id principalEntryToVal))
    (hfr : Env.get env (h₁₄.wk isFresh) = mkFreshPeer peerPrincipal?)
    (hpl : Env.get env (h₁₅.wk msgPlain) = msgPlainv)
    (hB : AuthListsBounded K hst) :
    (bindV (samplePrim .bytes32) fun ekASk =>
     bindV (samplePrim .bytes32) fun kemCoins =>
     bindV (samplePrim .bytes32) fun ephASk =>
     bindV (samplePrim .bytes32) fun spqrCoins =>
     bindV (resolveSigPkC S K st (pkbIkB (v bu))) fun sigPkB =>
     bindV (queryPrim (.sigVerify 33)
       (.pair (v sigPkB) (.pair (encEC (pkbSpkB (v bu))) (pkbSpkSig (v bu))))) fun v1 =>
     bindV (queryPrim (.sigVerify 1569)
       (.pair (v sigPkB) (.pair (encKEM (pkbPqspkB (v bu))) (pkbPqspkSig (v bu))))) fun v2 =>
     .ite (.not (.and (v v1) (v v2))) (.ret (v noneDone)) <|
     bindV (queryPrim .kemEncaps (.pair (pkbPqspkB (v bu)) (v kemCoins))) fun enc? =>
     caseOptV (v enc?) (.ret (v noneDone)) fun sc =>
     letV (.fst (v sc)) fun ss =>
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
     letV (.pair (v ekASk) (.pair (v ekAPk) (.pair (v ss) (.pair (v kemCt)
         (.pair (v ephASk) (v ephAPk)))))) fun keys6 =>
     .ite (v isIdealSend)
       (bindV (samplePrim .drKey96) fun drKey =>
        bindV (samplePrim .bytes32) fun rk1 =>
        bindV (queryPrim (.spqrInitSend 32 32)
          (.pair (.snd (.snd (v drKey))) (v spqrCoins))) fun sp? =>
        caseOptV (v sp?) (.ret (v noneDone)) fun sp =>
        letV (.fst (.snd (v sp))) fun spqrSalt? =>
        letV (.snd (.snd (v sp))) fun pqMsg =>
        letV (allocSendSlotE (v slotSt) (v sid)) fun sa =>
        letV (.fst (v sa)) fun sIdx =>
        letV (ahsfUpdSlots (v fhst) (slots := .snd (v sa))) fun fhst' =>
        .ite (.and (.not (v sentChal)) (natEq (v sIdx) (v idx)))
          (bindV (samplePrim .bytes32) fun ck1_1 =>
           .ret (.inr (.pair (v spqrSalt?)
             (.inl (.pair (v secb) (.pair (v idx) (.pair (v fhst')
               (.pair (v sid) (.pair (v uE) (.pair (v pp)
                 (.pair (v isFresh) (.pair (v bu) (.pair (.pair (v m0) (v m1))
                   (.pair (v keys6) (.pair (v drKey) (.pair (v rk1) (.pair (v ck1_1)
                     (.pair (v spqrSalt?) (.pair (v pqMsg) (v msgPlain))))))))))))))))))))
          (.ite (natLt (v sIdx) (v idx))
            (bindV (samplePrim .bytes32) fun ck1_1 =>
             bindV (samplePrim .msgKeys80) fun mks =>
             bindV (finishAuthSendMkC S K fhst' (v sid) (v uE) (v pp) (v isFresh) (v bu)
               (.pair (v m0) (v m1)) (v keys6) (v drKey) (v rk1) (litB 32 []) (v ck1_1)
               (v spqrSalt?) (v pqMsg) (v msgPlain) (v mks)) fun res =>
             .ret (.inl (.pair (.fst (v res))
               (mkcMk (v secb) (v idx) (v sentChal) (.snd (v res))))))
            (bindV (samplePrim .bytes32) fun mkSeed =>
             bindV (samplePrim .bytes32) fun ck1_1 =>
             bindV (queryPrim (.deriveMsgKeys 32) (.pair (v mkSeed) (v spqrSalt?))) fun mks =>
             bindV (finishAuthSendMkC S K fhst' (v sid) (v uE) (v pp) (v isFresh) (v bu)
               (.pair (v m0) (v m1)) (v keys6) (v drKey) (v rk1) (v mkSeed) (v ck1_1)
               (v spqrSalt?) (v pqMsg) (v msgPlain) (v mks)) fun res =>
             .ret (.inl (.pair (.fst (v res))
               (mkcMk (v secb) (v idx) (v sentChal) (.snd (v res))))))))
       (bindV (queryPrim .x25519 (.pair (peSecIKA0 (v uE)) (pkbSpkB (v bu)))) fun dh1 =>
        bindV (queryPrim .x25519 (.pair (v ekASk) (pkbIkB (v bu)))) fun dh2 =>
        bindV (queryPrim .x25519 (.pair (v ekASk) (pkbSpkB (v bu)))) fun dh3 =>
        bindV (caseOptV (pkbOpkB? (v bu)) (.ret .none) fun oP =>
          bindV (queryPrim .x25519 (.pair (v ekASk) (.snd (v oP)))) fun d4 =>
          .ret (.some (v d4))) fun dh4? =>
        letV (buildSecretsE (v dh1) (v dh2) (v dh3) (v dh4?) (v ss)) fun secrets =>
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
        bindV (finishAuthHybridSendC S K hstV
          (.pair (v sid) (.pair (v uE) (.pair (v pp) (.pair (v isFresh) (.pair (v bu)
            (.pair (.pair (v m0) (v m1)) (.pair (v keys6)
              (.pair (v drKey) (.pair (.pair (v rk1) (.pair (v ck1_0) (.pair (v mkSeed) (v ck1_1))))
                (.pair (v spqrSalt?) (.pair (v pqMsg) (.pair (v mks)
                  (.pair (v ad) (.pair (v aeadCt) (.pair (v msgPlain)
                    (.pair (v roC') (v rootC')))))))))))))))))) fun out =>
        .ret (.inl (.pair (.fst (v out))
          (mkcMk (v secb) (v idx) (v sentChal)
            (ahsfUpd (v fhst) (hst := .snd (v out)))))))).eval
      env =
    ((let isFreshPeer := mkFreshPeer peerPrincipal?
      do
        let ekASk ← embedUnif sampleScalar32
        let kemCoins ← embedUnif sampleCoins32
        let ephASk ← embedUnif sampleScalar32
        let spqrCoins ← embedUnif sampleCoins32
        let sigPkB ← resolveSigPkPrim S hst.toAuthHybridState.base.principals bundle.ikB
        let v1 ← primQ (.sigVerify sigPkB (encodeEC bundle.spkB) bundle.spkSig)
        let v2 ← primQ (.sigVerify sigPkB (encodeKEM bundle.pqspkB) bundle.pqspkSig)
        if !(v1 && v2) then
          return PreparedAuthSend.done .noneResp hst
        else
          match ← primQ (.kemEncaps bundle.pqspkB kemCoins) with
          | none => return PreparedAuthSend.done .noneResp hst
          | some (ss, kemCt) =>
            let ekAPk ← primQ (.x25519Base ekASk)
            let ephAPk ← primQ (.x25519Base ephASk)
            let spkHonIdeal ← checkBundleSpkHonIdealPrim S hst.toAuthHybridState.base.principals
              hst.toAuthHybridState.base.spkBundles bundle
            let pqspkHon : Bool :=
              (peerPrincipal?.map (fun p =>
                hst.toAuthHybridState.base.spkBundles.any
                  (fun ((u, _), b) => u == p.1 && b.pqspkPk == bundle.pqspkB))).getD false
            let isIdealSend : Bool :=
              isFreshPeer || (peerPrincipal?.isSome && spkHonIdeal && pqspkHon)
            if isIdealSend then
              let drKey ← embedUnif sampleDRKey96
              let rk1 ← embedUnif sampleBytes32
              match ← primQ (.spqrInitSend drKey.pqrKey spqrCoins) with
              | none => return PreparedAuthSend.done .noneResp hst
              | some (_pqrStA, spqrSalt?, pqRatchetMsg) =>
                return PreparedAuthSend.idealMk uEntry peerPrincipal? ekASk ekAPk ss kemCt
                  ephASk ephAPk drKey rk1 spqrSalt? pqRatchetMsg msgPlainv
            else
              let dh1 ← primQ (.x25519 uEntry.secIKA0 bundle.spkB)
              let dh2 ← primQ (.x25519 ekASk bundle.ikB)
              let dh3 ← primQ (.x25519 ekASk bundle.spkB)
              let dh4? ←
                Option.casesOn bundle.opkB? (pure none) (fun (_, opkPk) => do
                  let d4 ← primQ (.x25519 ekASk opkPk)
                  pure (some d4))
              let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
              let (drKey, roCache') ←
                embedUnif (evalHkdfRoPure hst.toAuthHybridState.base.roCache secrets)
              let dhRatchet ← primQ (.x25519 ephASk bundle.spkB)
              let ((rk1, ck1_0), rootRoCache') ←
                embedUnif (evalRootKdfRoPure hst.toAuthHybridState.base.rootRoCache
                  drKey.rootKey dhRatchet)
              let mkSeed ← primQ (.chainKdfSeed ck1_0)
              let ck1_1 ← primQ (.chainKdfNext ck1_0)
              match ← primQ (.spqrInitSend drKey.pqrKey spqrCoins) with
              | none => return PreparedAuthSend.done .noneResp hst
              | some (_pqrStA, spqrSalt?, pqRatchetMsg) =>
                let deriveMessageKeys ← primQ (.deriveMsgKeys mkSeed spqrSalt?)
                let ad := firstMsgAD uEntry.ikAPk bundle.ikB ephAPk pqRatchetMsg
                let aeadCt ← primQ (.aeadEnc deriveMessageKeys ad msgPlainv)
                let (resp, hst') ←
                  finishAuthHybridSendPrim S sidv uEntry peerPrincipal? isFreshPeer
                    bundle m0v m1v ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 ck1_0 mkSeed ck1_1
                    spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlainv roCache'
                    rootRoCache' hst.toAuthHybridState
                return PreparedAuthSend.done resp { toAuthHybridState := hst',
                                                    recvCount := hst.recvCount,
                                                    mkSaltCache := hst.mkSaltCache,
                                                    slots := hst.slots }) >>=
      mkSendCont S secbv idxv scv sidv bundle m0v m1v hst) := by
  dsimp only
  rw [bindV_eval, samplePrim_bytes32_eval]; try simp only [bind_assoc]
  apply bind_congr; intro ekASk
  rw [bindV_eval, samplePrim_bytes32_eval]; try simp only [bind_assoc]
  apply bind_congr; intro kemCoins
  rw [bindV_eval, samplePrim_bytes32_eval]; try simp only [bind_assoc]
  apply bind_congr; intro ephASk
  rw [bindV_eval, samplePrim_bytes32_eval]; try simp only [bind_assoc]
  apply bind_congr; intro spqrCoins
  rw [bindV_eval, resolveSigPkC_eval S _ _ _ hst.toAuthHybridState.base
    (by simp [Ext.step_wk, hstV_eq]) hB.principals_le,
    show (pkbIkB (v bu)).eval _ = bundle.ikB by
      simp [v, pkbIkB, Expr.eval, Ext.step_wk, hbu, preKeyBundleToVal, bundleV]]
  try simp only [bind_assoc]
  apply bind_congr; intro sigPkB
  rw [bindV_eval,
    mkS_queryPrim_eq _ _ (sigPkB, (encodeEC bundle.spkB, bundle.spkSig))
    (by simp [v, encEC_eval, pkbSpkB, pkbSpkSig, Expr.eval, Ext.step_wk, hbu,
      preKeyBundleToVal, bundleV])]
  dsimp only [evalPrimOp]; try simp only [bind_assoc]
  apply bind_congr; intro v1
  rw [bindV_eval,
    mkS_queryPrim_eq _ _ (sigPkB, (encodeKEM bundle.pqspkB, bundle.pqspkSig))
    (by simp [v, encKEM_eval, pkbPqspkB, pkbPqspkSig, Expr.eval, Ext.step_wk, hbu,
      preKeyBundleToVal, bundleV])]
  dsimp only [evalPrimOp]; try simp only [bind_assoc]
  apply bind_congr; intro v2
  rw [mkS_iteC_eq _ _ _ _ (!(v1 && v2)) (by simp [v, Expr.eval, Ext.step_wk])]
  cases hv : (v1 && v2) with
  | false =>
    simp [mkSendCont, v, Comp.eval, Expr.eval, Ext.step_wk, hnone]
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [bindV_eval, mkS_queryPrim_eq _ _ (bundle.pqspkB, kemCoins)
      (by simp [v, pkbPqspkB, Expr.eval, Ext.step_wk, hbu, preKeyBundleToVal, bundleV])]
    dsimp only [evalPrimOp]; try simp only [bind_assoc]
    apply bind_congr; intro enc?
    rw [mkS_caseOptV_eq _ _ _ _ enc? rfl]
    cases enc? with
    | none =>
      simp [mkSendCont, v, Comp.eval, Expr.eval, Ext.step_wk, hnone]
    | some scP =>
      rcases scP with ⟨ss, kemCt⟩
      dsimp only
      apply authMkSendPreB_afterKem_eval S K secbv idxv scv hst sidv uEntry
        peerPrincipal? bundle m0v m1v msgPlainv ekASk ephASk spqrCoins ss kemCt
      all_goals simp [Ext.step_wk, hslot, hsecb, hidx, hsc, hfhst, hnone, hhst, hstV_eq,
        hbu, hm0, hm1, hsid, huE, hpp, hfr, hpl, hB]

private theorem authMkSendPreB_eval_gen (opk : Bool) (core : Var Γ₁ prfMkCoreTy) (x : Var Γ₂ sendQTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (env : Env Δ)
    (secb : Bool) (idx : Nat) (sc : Bool) (hst : AuthHybridStateFixed S)
    (u : Fin S.N_id) (i_nat : Nat) (sidv : SessionId S) (b : PreKeyBundleInput) (m0 m1 : Bytes)
    (hcore : Env.get env (h₁.wk core) = mkCoreToVal secb idx sc hst)
    (hx : Env.get env (h₂.wk x) = (u.val, (i_nat, (preKeyBundleToVal b, (m0, m1)))))
    (hSid : (if opk then Sum.inl (u.val, i_nat) else Sum.inr (Sum.inl (u.val, i_nat))) =
      sessionIdToVal sidv)
    (hB : AuthListsBounded K hst) :
    (authMkSendPreB S K opk core x).eval env =
      mkPreToVal secb idx sc <$>
        (if (if opk then b.opkB?.isNone else b.opkB?.isSome) then
          pure (.inl (.noneResp, hst))
        else
          mkSendPre S idx sidv u b m0 m1 hst sc) := by
  have hTakeP := prfMk_take_map_of_le (Prod.map id principalEntryToVal)
    hst.toAuthHybridState.base.principals hB.principals_le
  unfold authMkSendPreB
  rw [letV_eval_eq _ _ _ secb (by simp [v, Expr.eval, hcore, mkCoreToVal])]
  rw [letV_eval_eq _ _ _ idx (by simp [v, Expr.eval, Ext.step_wk, hcore, mkCoreToVal])]
  rw [letV_eval_eq _ _ _ sc (by simp [v, Expr.eval, Ext.step_wk, hcore, mkCoreToVal])]
  rw [letV_eval_eq _ _ _ (authHybridStateFixedToVal hst)
    (by simp [v, Expr.eval, Ext.step_wk, hcore, mkCoreToVal])]
  rw [letV_eval_eq _ _ _ (authSlotStateToVal hst.slots) rfl]
  let noneDoneV : prfMkStepPreTy.denote := mkPreToVal secb idx sc (.inl (.noneResp, hst))
  rw [letV_eval_eq _ _ _ noneDoneV
    (by simp [noneDoneV, v, aNone, Expr.eval, Ext.step_wk, hcore, mkPreToVal, authRespToVal,
      authRenc])]
  rw [mkS_iteC_eq _ _ _ _ (if opk then b.opkB?.isNone else b.opkB?.isSome)
    (mkS_sendGuardE_eval opk _ _ u.val i_nat b m0 m1 (by simp [v, Expr.eval, Ext.step_wk, hx]))]
  cases hGuard : (if opk then b.opkB?.isNone else b.opkB?.isSome) with
  | true =>
    simp [noneDoneV, v, Comp.eval, Expr.eval]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [mkSendPre_map_eq]
    unfold prepareAuthSendMkPrim
    dsimp only
    rw [letV_eval_eq _ _ _ (authHybridStateToVal hst.toAuthHybridState) rfl]
    rw [letV_eval_eq _ _ _ (authStateToVal hst.toAuthHybridState.base) rfl]
    rw [mkS_iteC_eq _ _ _ _ hst.toAuthHybridState.base.hasWonAuth rfl]
    cases hWon : hst.toAuthHybridState.base.hasWonAuth with
    | true =>
      simp [noneDoneV, mkSendCont, v, Comp.eval, Expr.eval, Ext.step_wk]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [letV_eval_eq _ _ _ (preKeyBundleToVal b)
        (by simp [v, Expr.eval, Ext.step_wk, hx])]
      rw [letV_eval_eq _ _ _ m0 (by simp [v, Expr.eval, Ext.step_wk, hx])]
      rw [letV_eval_eq _ _ _ m1 (by simp [v, Expr.eval, Ext.step_wk, hx])]
      rw [letV_eval_eq _ _ _ (sessionIdToVal sidv)
        (by rw [mkS_sendSidE_eval opk _ _ u.val i_nat b m0 m1
              (by simp [v, Expr.eval, Ext.step_wk, hx]), hSid])]
      rw [mkS_iteC_eq _ _ _ _ (m0.length != m1.length)
        (by simp [v, natEq_eval, bytesLen_eval, Expr.eval, bne])]
      cases hLen : (m0.length != m1.length) with
      | true =>
        simp [noneDoneV, mkSendCont, v, Comp.eval, Expr.eval, Ext.step_wk]
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [mkS_iteC_eq _ _ _ _ (hst.toAuthHybridState.base.usedSendSessions.contains sidv)
          (mkS_usedSend_eval S K _ _ _ hst.toAuthHybridState.base sidv rfl rfl
            hB.usedSendSessions_le)]
        cases hUsed : hst.toAuthHybridState.base.usedSendSessions.contains sidv with
        | true =>
          simp [noneDoneV, mkSendCont, v, Comp.eval, Expr.eval, Ext.step_wk]
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [mkS_caseOptV_eq _ _ _ _
            ((hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val)).map
              (Prod.map id principalEntryToVal))
            (by simp [eFind, asPrincipals, natEq_eval, v, Expr.eval, Ext.step_wk,
              hx, authStateToVal, hTakeP, List.find?_map, Prod.map])]
          cases hFindU :
              hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
          | none =>
            simp [noneDoneV, mkSendCont, v, Comp.eval, Expr.eval, Ext.step_wk]
          | some uP =>
            rcases uP with ⟨uIdx, uEntry⟩
            dsimp only [Option.map, Prod.map, id_eq]
            rw [letV_eval_eq _ _ _ (principalEntryToVal uEntry) rfl]
            rw [bindV_eval, findHonestC_eval S _ _ _ hst.toAuthHybridState.base rfl hB.principals_le,
              show (pkbIkB (v _)).eval _ = b.ikB by
                simp [v, pkbIkB, Expr.eval, Ext.step_wk, preKeyBundleToVal, bundleV]]
            simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
            apply bind_congr; intro peerPrincipal?
            rw [letV_eval_eq _ _ _ (mkFreshPeer peerPrincipal?)
              (mkS_isFreshE_eval _ _ peerPrincipal? rfl)]
            rw [mkS_iteC_eq _ _ _ _ (!mkFreshPeer peerPrincipal? && (m0 != m1))
              (by mks_eval [])]
            rw [mkS_ite_bind]
            refine mkS_ite_eq Iff.rfl (fun _ => ?_) (fun _ => ?_)
            · dsimp only [noneDoneV]; mks_eval []
            · let msgPlain : Bytes :=
                if mkFreshPeer peerPrincipal? then
                  (if hst.toAuthHybridState.base.secb then m1 else m0)
                else m0
              rw [letV_eval_eq _ _ _ msgPlain rfl]
              rw [bindV_eval, koskBundleOkC_eval S K _ _ _ hst.toAuthHybridState.base b rfl rfl
                hB.advKeys_le hB.principals_le hB.spkBundles_le hB.opkEntries_le]
              simp only [bind_assoc]
              apply bind_congr; intro koskOk
              rw [mkS_iteC_eq _ _ _ _ (!koskOk) rfl]
              cases koskOk with
              | false =>
                dsimp only [noneDoneV]; mks_eval []
              | true =>
                simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                apply authMkSendPreB_afterKosk_eval S K secb idx sc hst sidv uEntry
                  peerPrincipal? b m0 m1 msgPlain
                all_goals first | rfl | exact hB

theorem authMkSendPreB_eval_opk (core : Var Γ₁ prfMkCoreTy) (x : Var Γ₂ sendQTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (env : Env Δ)
    (secb : Bool) (idx : Nat) (sc : Bool) (hst : AuthHybridStateFixed S)
    (u : Fin S.N_id) (i : Fin S.N_send_opk) (b : PreKeyBundleInput) (m0 m1 : Bytes)
    (hcore : Env.get env (h₁.wk core) = mkCoreToVal secb idx sc hst)
    (hx : Env.get env (h₂.wk x) = (u.val, (i.val, (preKeyBundleToVal b, (m0, m1)))))
    (hB : AuthListsBounded K hst) :
    (authMkSendPreB S K true core x).eval env =
      mkPreToVal secb idx sc <$> mkPre S idx (.sendOPK u i b m0 m1) hst sc := by
  simpa [mkPre] using
    authMkSendPreB_eval_gen S K true core x env secb idx sc hst u i.val (.sendOPK u i) b m0 m1
      hcore hx rfl hB

theorem authMkSendPreB_eval_noopk (core : Var Γ₁ prfMkCoreTy) (x : Var Γ₂ sendQTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (env : Env Δ)
    (secb : Bool) (idx : Nat) (sc : Bool) (hst : AuthHybridStateFixed S)
    (u : Fin S.N_id) (i : Fin S.N_send_no_opk) (b : PreKeyBundleInput) (m0 m1 : Bytes)
    (hcore : Env.get env (h₁.wk core) = mkCoreToVal secb idx sc hst)
    (hx : Env.get env (h₂.wk x) = (u.val, (i.val, (preKeyBundleToVal b, (m0, m1)))))
    (hB : AuthListsBounded K hst) :
    (authMkSendPreB S K false core x).eval env =
      mkPreToVal secb idx sc <$> mkPre S idx (.sendNoOPK u i b m0 m1) hst sc := by
  simpa [mkPre] using
    authMkSendPreB_eval_gen S K false core x env secb idx sc hst u i.val (.sendNoOPK u i) b m0 m1
      hcore hx rfl hB

end Iface

end SignalPqxdh.Security.ReductionDsl.AuthPrf

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
# Receiver Branch of the `PrfMsgKeys` Evaluation Equivalence

Proves that `finishAuthRecvMkC` and `authMkRecvPreB` evaluate to `finishAuthRecvMkPrim` and the
receiver cases of `mkPre`.
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

section Helpers

theorem mkR_peel {m : Type → Type} [Monad m] [LawfulMonad m] {α α' γ δ : Type}
    (F : γ → δ) {x : m α} {x' : m α'} (h : α' → α) {g : α → m δ} {g' : α' → m γ}
    (hx : x = h <$> x') (hg : ∀ a, g (h a) = F <$> g' a) :
    x >>= g = F <$> (x' >>= g') := by
  subst hx; simp only [bind_map_left, map_bind, hg]

theorem mkR_peelS {m : Type → Type} [Monad m] [LawfulMonad m] {α γ δ : Type}
    (F : γ → δ) {x x' : m α} {g : α → m δ} {g' : α → m γ}
    (hx : x = x') (hg : ∀ a, g a = F <$> g' a) :
    x >>= g = F <$> (x' >>= g') := by
  subst hx; rw [map_bind]; exact congrArg _ (funext hg)

theorem mkR_ite {m : Type → Type} [Functor m] {γ δ : Type} (F : γ → δ) {c c' : Prop}
    [Decidable c] [Decidable c'] {a b : m δ} {a' b' : m γ} (hc : c ↔ c')
    (h1 : c' → a = F <$> a') (h2 : ¬ c' → b = F <$> b') :
    (if c then a else b) = F <$> (if c' then a' else b') := by
  by_cases h : c'
  · simp only [hc.mpr h, h, ↓reduceIte]; exact h1 h
  · have h' : ¬ c := fun h' => h (hc.mp h')
    simp only [h, h', ↓reduceIte]; exact h2 h

theorem mkR_pure {m : Type → Type} [Monad m] [LawfulMonad m] {γ δ : Type} (F : γ → δ)
    {a : δ} {a' : γ} (h : a = F a') : (pure a : m δ) = F <$> pure a' := by
  rw [map_pure, h]

theorem mkR_aeadDec_congr {mk mk' : MessageKeys} {ad ad' ct ct' : Bytes} (h1 : mk = mk')
    (h2 : ad = ad') (h3 : ct = ct') :
    primQ (PrimQuery.aeadDec mk ad ct) = primQ (PrimQuery.aeadDec mk' ad' ct') := by
  subst h1 h2 h3; rfl

theorem mkR_bind_congr_leaves {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    {P : α → Prop} {m : OracleComp spec α} {f g : α → OracleComp spec β}
    (hm : AllLeaves P m) (hfg : ∀ a, P a → f a = g a) : m >>= f = m >>= g := by
  induction m using OracleComp.inductionOn with
  | pure a => simp only [pure_bind]; exact hfg a hm
  | query_bind q k ih =>
    simp only [bind_assoc]
    congr 1
    funext u
    exact ih u (hm u)

theorem mkR_peelL {ι : Type} {spec : OracleSpec.{0, 0} ι} {α α' γ δ : Type} {P : α' → Prop}
    (F : γ → δ) {x : OracleComp spec α} {x' : OracleComp spec α'} (h : α' → α)
    {g : α → OracleComp spec δ} {g' : α' → OracleComp spec γ}
    (hL : AllLeaves P x') (hx : x = h <$> x') (hg : ∀ a, P a → g (h a) = F <$> g' a) :
    x >>= g = F <$> (x' >>= g') := by
  subst hx
  rw [bind_map_left, map_bind]
  exact mkR_bind_congr_leaves hL hg

end Helpers

section Iface

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List PT}

private theorem finishAuthRecvMkSlotsPrim_eq_map {S : Setup} (msg : PreKeyMsg)
    (prep : PreparedAuthRecvPrim S) (drKey : DRKey) (rk1 ck1_1 : Bytes) (recvCount' : Nat)
    (mkSaltCache' : List ((SessionId S × Option Bytes) × (Nat × MessageKeys)))
    (slots' : AuthSlotState) (deriveMessageKeys : MessageKeys) :
    finishAuthRecvMkSlotsPrim S msg prep drKey rk1 ck1_1 recvCount' mkSaltCache' slots'
        deriveMessageKeys =
      (fun p => (p.1, { p.2 with slots := slots' })) <$>
        finishAuthRecvMkPrim S msg prep drKey rk1 ck1_1 recvCount' mkSaltCache'
          deriveMessageKeys := by
  unfold finishAuthRecvMkPrim finishAuthRecvMkSlotsPrim
  simp only [map_bind, map_pure]

theorem finishAuthRecvMkC_eval (msg : Var Γ₁ preKeyMsgTy) (prep : Var Γ₂ preparedAuthRecvTy)
    (drKey : Expr pqxdhOps Δ drKeyTy) (rk1 ck1_1 : Expr pqxdhOps Δ (B 32)) (rc' : Expr pqxdhOps Δ .nat)
    (cache' : Expr pqxdhOps Δ authMkSaltCacheTy) (mks : Expr pqxdhOps Δ msgKeysTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (env : Env Δ)
    (msgv : PreKeyMsg) (prepv : PreparedAuthRecvPrim S) (drKeyv : DRKey) (rk1v ck1_1v : Bytes)
    (rcv : Nat) (cachev : AuthMkSaltCache S) (mk : MessageKeys)
    (hmsg : Env.get env (h₁.wk msg) = preKeyMsgToVal msgv)
    (hprep : Env.get env (h₂.wk prep) = preparedAuthRecvToVal prepv)
    (hdr : drKey.eval env = drKeyToVal drKeyv) (hrk : rk1.eval env = rk1v)
    (hck : ck1_1.eval env = ck1_1v) (hrc : rc'.eval env = rcv)
    (hc : cache'.eval env = mkCacheToVal cachev) (hmk : mks.eval env = msgKeysToVal mk)
    (hB : PreparedRecvBounded K prepv) :
    (finishAuthRecvMkC S K msg prep drKey rk1 ck1_1 rc' cache' mks).eval env =
      Prod.map authRespToVal authHybridStateFixedToVal <$>
        finishAuthRecvMkPrim S msgv prepv drKeyv rk1v ck1_1v rcv cachev mk := by
  unfold finishAuthRecvMkPrim finishAuthRecvMkSlotsPrim
  simp only [finishAuthRecvMkC, letV, eval_letC, bindV, v, eCaseOpt, ahsBase, parHstDec,
    parFinishTag, parKEntry, pkmHdr, hdrIkAPk, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt, peIkAPk,
    asRoCache, asRootRoCache, ahsfMk, Comp.eval, Expr.eval, queryPrim_eval, evalPrimQ, evalPrimOp,
    Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, hprep, hdr, hrk, hck, hrc, hc, hmk,
    preparedAuthRecvToVal, principalEntryToVal]
  refine mkR_peelS _ ?_ (fun pt? => ?_)
  · apply mkR_aeadDec_congr <;>
      simp only [firstMsgADE_eval, Expr.eval, Env.get_succ, hmsg, hprep,
        valToMsgKeys_msgKeysToVal, preparedAuthRecvToVal, preKeyMsgToVal, preKeyMsgV,
        hdrV, principalEntryToVal]
  rw [recvFinishTagRunC_eval (S := S) (K := K) (tagv := prepv.finishTag)
    (resv? := pt?.map (fun pt => (drKeyv, rk1v, ck1_1v, pt, prepv.hstDec.base.roCache,
      prepv.hstDec.base.rootRoCache))) (htag := ?_) (hres := ?_) (hOpk := ?_)
      (hPrin := hB.tag_bounded.principals_le)
      (hSentO := fun _ => hB.tag_bounded.sentOPKEvents_le)
      (hSentN := fun _ => hB.tag_bounded.sentNoOPKEvents_le)]
  · simp only [map_bind, bind_map_left, map_pure, Prod.map]
    rfl
  · rfl
  · cases pt? <;> rfl
  · exact hB.tag_bounded.opkEntries_le

theorem finishRecvUnmatchedMkPreC_eval (core : Var Γ₁ prfMkCoreTy) (msg : Var Γ₂ preKeyMsgTy)
    (prep : Var Γ₃ preparedAuthRecvTy) (drKey : Expr pqxdhOps Δ drKeyTy) (rk1 : Expr pqxdhOps Δ (B 32))
    (spqrSalt? : Expr pqxdhOps Δ (.opt (B 32))) (rSlot rc' : Expr pqxdhOps Δ .nat)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] (env : Env Δ)
    (secb : Bool) (idx : Nat) (sc : Bool) (hst : AuthHybridStateFixed S)
    (msgv : PreKeyMsg) (prepv : PreparedAuthRecvPrim S) (drKeyv : DRKey) (rk1v : Bytes)
    (saltv : Option Bytes) (rSlotv rcv : Nat)
    (hcore : Env.get env (h₁.wk core) = mkCoreToVal secb idx sc hst)
    (hmsg : Env.get env (h₂.wk msg) = preKeyMsgToVal msgv)
    (hprep : Env.get env (h₃.wk prep) = preparedAuthRecvToVal prepv)
    (hdr : drKey.eval env = drKeyToVal drKeyv) (hrk : rk1.eval env = rk1v)
    (hsa : spqrSalt?.eval env = saltv) (hrs : rSlot.eval env = rSlotv)
    (hrc : rc'.eval env = rcv)
    (hB : PreparedRecvBounded K prepv) :
    (finishRecvUnmatchedMkPreC S K core msg prep drKey rk1 spqrSalt? rSlot rc').eval env =
      mkPreToVal secb idx sc <$>
        mkUnmatchedSlotsPre S idx msgv prepv drKeyv rk1v saltv rSlotv rcv hst.mkSaltCache
          hst.slots sc := by
  unfold mkUnmatchedSlotsPre
  simp only [finishRecvUnmatchedMkPreC, letV, eval_letC, bindV, v, mkcSecb, mkcIdx, mkcSentChal,
    mkcFhst, ahsfMkSaltCache, ahsfHybrid, ahsfRecvCount, mkcMk, Comp.eval, Expr.eval,
    samplePrim_bytes32_eval, samplePrim_msgKeys80_eval, queryPrim_eval, evalPrimQ, evalPrimOp,
    Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, hcore, hdr, hrk, hsa,
    hrs, hrc, mkCoreToVal, authHybridStateFixedToVal, authHybridStateFixedWithSlotsToVal,
    natEq_eval, natLt_expr_eval]
  have hc : List.map (fun x => ((sessionIdToVal x.1.1, x.1.2), x.2.1, msgKeysToVal x.2.2))
      hst.mkSaltCache = mkCacheToVal hst.mkSaltCache := rfl
  rw [hc]
  apply mkR_ite _ Iff.rfl
  · intro _
    refine mkR_peelS _ rfl (fun ck => ?_)
    apply mkR_ite _ Iff.rfl
    · intro _
      refine mkR_pure _ ?_
      simp only [mkPreToVal, MkCont.toVal, hmsg, hprep, Option.map_none]
    · intro _
      refine mkR_peel _ msgKeysToVal rfl (fun mk => ?_)
      rw [finishAuthRecvMkSlotsPrim_eq_map, finishAuthRecvMkC_eval (S := S) (K := K) (msgv := msgv)
        (prepv := prepv) (drKeyv := drKeyv) (rk1v := rk1v) (ck1_1v := ck) (rcv := rcv)
        (cachev := hst.mkSaltCache) (mk := mk) (hmsg := by simpa using hmsg)
        (hprep := by simpa using hprep) (hdr := rfl) (hrk := rfl) (hck := rfl) (hrc := rfl)
        (hc := rfl) (hmk := rfl) (hB := hB)]
      simp only [map_bind, bind_map_left, map_pure, mkPreToVal, mkCoreToVal]
      rfl
  · intro _
    apply mkR_ite _ Iff.rfl
    · intro _
      refine mkR_peelS _ rfl (fun ck => ?_)
      refine mkR_peel _ msgKeysToVal rfl (fun mk => ?_)
      rw [finishAuthRecvMkSlotsPrim_eq_map, finishAuthRecvMkC_eval (S := S) (K := K) (msgv := msgv)
        (prepv := prepv) (drKeyv := drKeyv) (rk1v := rk1v) (ck1_1v := ck) (rcv := rcv)
        (cachev := hst.mkSaltCache) (mk := mk) (hmsg := by simpa using hmsg)
        (hprep := by simpa using hprep) (hdr := rfl) (hrk := rfl) (hck := rfl) (hrc := rfl)
        (hc := rfl) (hmk := rfl) (hB := hB)]
      simp only [map_bind, bind_map_left, map_pure, mkPreToVal, mkCoreToVal]
      rfl
    · intro _
      refine mkR_peelS _ rfl (fun seed => ?_)
      refine mkR_peelS _ rfl (fun ck => ?_)
      refine mkR_peel _ msgKeysToVal rfl (fun mk => ?_)
      rw [finishAuthRecvMkSlotsPrim_eq_map, finishAuthRecvMkC_eval (S := S) (K := K) (msgv := msgv)
        (prepv := prepv) (drKeyv := drKeyv) (rk1v := rk1v) (ck1_1v := ck) (rcv := rcv)
        (cachev := hst.mkSaltCache) (mk := mk) (hmsg := by simpa using hmsg)
        (hprep := by simpa using hprep) (hdr := rfl) (hrk := rfl) (hck := rfl) (hrc := rfl)
        (hc := rfl) (hmk := rfl) (hB := hB)]
      simp only [map_bind, bind_map_left, map_pure, mkPreToVal, mkCoreToVal]
      rfl

section Proj

variable {S : Setup}

@[simp] theorem mkR_par_k (p : PreparedAuthRecvPrim S) :
    (preparedAuthRecvToVal p).1 = principalEntryToVal p.kEntry := rfl
@[simp] theorem mkR_par_sec (p : PreparedAuthRecvPrim S) :
    (preparedAuthRecvToVal p).2.2.2.1 = p.secrets := rfl
@[simp] theorem mkR_par_dh (p : PreparedAuthRecvPrim S) :
    (preparedAuthRecvToVal p).2.2.2.2.1 = p.dhRatchet := rfl
@[simp] theorem mkR_par_unc (p : PreparedAuthRecvPrim S) :
    (preparedAuthRecvToVal p).2.2.2.2.2.1 = p.isUncorruptedHonestSender := rfl
@[simp] theorem mkR_par_ms (p : PreparedAuthRecvPrim S) :
    (preparedAuthRecvToVal p).2.2.2.2.2.2.1 = p.matchedSess?.map idealAuthSessionToVal := rfl
@[simp] theorem mkR_par_se (p : PreparedAuthRecvPrim S) :
    (preparedAuthRecvToVal p).2.2.2.2.2.2.2.1 = p.sameEph := rfl
@[simp] theorem mkR_par_hd (p : PreparedAuthRecvPrim S) :
    (preparedAuthRecvToVal p).2.2.2.2.2.2.2.2.1 = authHybridStateToVal p.hstDec := rfl
@[simp] theorem mkR_par_ft (p : PreparedAuthRecvPrim S) :
    (preparedAuthRecvToVal p).2.2.2.2.2.2.2.2.2 = recvFinishTagToVal p.finishTag := rfl
@[simp] theorem mkR_pe_ik (e : PrincipalEntry) : (principalEntryToVal e).2.1 = e.ikAPk := rfl
@[simp] theorem mkR_ahs_base (h : AuthHybridState S) :
    (authHybridStateToVal h).1 = authStateToVal h.base := rfl
@[simp] theorem mkR_dr_root (d : DRKey) : (drKeyToVal d).1 = d.rootKey := rfl
@[simp] theorem mkR_dr_pqr (d : DRKey) : (drKeyToVal d).2.2 = d.pqrKey := rfl
@[simp] theorem mkR_ias_sid (s : IdealAuthSession S) :
    (idealAuthSessionToVal s).1 = sessionIdToVal s.sid := rfl
@[simp] theorem mkR_ias_salt (s : IdealAuthSession S) :
    (idealAuthSessionToVal s).2.2.2.2.2.2.2.2.2.1 = s.spqrSalt? := rfl
@[simp] theorem mkR_ias_dr (s : IdealAuthSession S) :
    (idealAuthSessionToVal s).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 = drKeyToVal s.drKey := rfl
@[simp] theorem mkR_ias_rk1 (s : IdealAuthSession S) :
    (idealAuthSessionToVal s).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 = s.rk1 := rfl
@[simp] theorem mkR_ias_seed (s : IdealAuthSession S) :
    (idealAuthSessionToVal s).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 = s.mkSeed := rfl
@[simp] theorem mkR_ias_ck (s : IdealAuthSession S) :
    (idealAuthSessionToVal s).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 = s.ck1_1 := rfl
@[simp] theorem mkR_ias_mk (s : IdealAuthSession S) :
    (idealAuthSessionToVal s).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 =
      msgKeysToVal s.deriveMessageKeys := rfl

theorem mkR_sidx {Γ : List PT} (e : Expr pqxdhOps Γ sessionIdTy) (env : Env Γ) (s : SessionId S)
    (h : e.eval env = sessionIdToVal s) :
    (sessionSlotIndexE S e).eval env = sessionSlotIndex s :=
  sessionSlotIndexE_eval e env s h

private theorem lookupSendSlotOrZeroE_eval {Γ : List PT}
    (ss : Expr pqxdhOps Γ authSlotStateTy) (sid : Expr pqxdhOps Γ sessionIdTy)
    (env : Env Γ) (ssv : AuthSlotState) (s : SessionId S)
    (hss : ss.eval env = authSlotStateToVal ssv)
    (hsid : sid.eval env = sessionIdToVal s) :
    (lookupSendSlotOrZeroE ss sid).eval env = ssv.lookupSendOrZero s := by
  simp only [lookupSendSlotOrZeroE, lookupSendSlotE, eCaseOpt, eLet2, eLet, eCaseSum,
    assSendOpk, assSendNoOpk, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
    Env.get_succ, Env.get_zero, hss, hsid, authSlotStateToVal,
    AuthSlotState.lookupSendOrZero, AuthSlotState.lookupSend]
  cases s with
  | sendOPK u i =>
    simp only [sessionIdToVal, sidV]
    cases ssv.sendOpkTbl u.1 i.1 <;> rfl
  | sendNoOPK u i =>
    simp only [sessionIdToVal, sidV]
    cases ssv.sendNoOpkTbl u.1 i.1 <;> rfl
  | recvOPK _ _ _ => rfl
  | recvNoOPK _ _ _ => rfl

private theorem allocRecvSlotE_eval {Γ : List PT}
    (ss : Expr pqxdhOps Γ authSlotStateTy) (rc : Expr pqxdhOps Γ .nat)
    (env : Env Γ) (ssv : AuthSlotState) (rcv : Nat)
    (hss : ss.eval env = authSlotStateToVal ssv)
    (hrc : rc.eval env = rcv) :
    (allocRecvSlotE ss rc).eval env =
      Prod.map id authSlotStateToVal (ssv.allocRecv rcv) := by
  simp only [allocRecvSlotE, eLet2, eLet, eCaseOpt, assRecv, assNext, assSendOpk,
    assSendNoOpk, assMk, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
    Env.get_succ, Env.get_zero, hss, hrc, authSlotStateToVal, AuthSlotState.allocRecv]
  cases ssv.recvTbl rcv <;> rfl

theorem mkR_find (K : Nat) (cache : AuthMkSaltCache S)
    (L : List ((sessionIdTy.denote × Option Bytes) × Nat × msgKeysTy.denote))
    (hL : L = mkCacheToVal cache) (hK : cache.length ≤ K)
    (sid : SessionId S) (salt : Option Bytes)
    (p : ((sessionIdTy.denote × Option Bytes) × Nat × msgKeysTy.denote) → Bool)
    (hp : ∀ (s' : SessionId S) (o : Option Bytes) (rc : Nat) (mk : MessageKeys),
      p ((sessionIdToVal s', o), (rc, msgKeysToVal mk)) = mkSaltKeyMatch (s', o) sid salt) :
    (L.take K).find? p = (cache.find? (fun (k, _) => mkSaltKeyMatch k sid salt)).map
      (fun ((sid, salt?), (rc, mk)) => ((sessionIdToVal sid, salt?), (rc, msgKeysToVal mk))) := by
  subst hL
  rw [List.take_of_length_le (by simpa [mkCacheToVal] using hK)]
  unfold mkCacheToVal
  rw [List.find?_map]
  congr 2
  funext ⟨⟨s', o⟩, rc, mk⟩
  simp only [Function.comp_apply, hp]

end Proj

syntax "mkr_simp" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| mkr_simp [$extra,*]) =>
    `(tactic| simp only [caseOptV, eCaseOpt, letV, eval_letC, bindV, v, Comp.eval, Expr.eval,
      samplePrim_bytes32_eval, samplePrim_drKey96_eval, samplePrim_msgKeys80_eval,
      queryPrim_eval, evalPrimQ, evalPrimOp, boolOr_eval,
      Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
      Option.map_some, Option.map_none, parMatchedSess?, parIsUncorrSender,
      parSameEph, parHstDec, parFinishTag, parKEntry, parSecrets, parDhRatchet, isSomeE_eval,
      mkcMk, ahsfMk, ahsfUpd, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache,
      ahsBase, aNone, natEq_eval, natLt_expr_eval,
      pkmPqRatchetMsg, pkmHdr, hdrIkAPk, pkmEphAPk, pkmAeadCt, peIkAPk, firstMsgADE_eval,
      iasDrKey, iasRk1, iasCk1_1, iasMsgKeys, iasMkSeed, iasSid, iasSpqrSalt?,
      preKeyMsgToVal, preKeyMsgV, handshakeHdrToVal, hdrV, valToMsgKeys_msgKeysToVal,
      sameSaltKeyE_eval,
      mkR_par_k, mkR_par_sec, mkR_par_dh, mkR_par_unc, mkR_par_ms, mkR_par_se, mkR_par_hd,
      mkR_par_ft, mkR_pe_ik, mkR_ahs_base, mkR_dr_root, mkR_dr_pqr, mkR_ias_sid, mkR_ias_salt,
      mkR_ias_dr, mkR_ias_rk1, mkR_ias_seed, mkR_ias_ck, mkR_ias_mk, $extra,*])

macro "mkr_fin" : tactic => `(tactic| (
  rw [finishAuthRecvMkSlotsPrim_eq_map, bind_map_left]
  refine mkR_peel _ (Prod.map authRespToVal authHybridStateFixedToVal) ?_ (fun ⟨r, h'⟩ => ?_)
  · apply finishAuthRecvMkC_eval
    all_goals first | rfl | assumption
  · exact mkR_pure _ rfl))

macro "mkr_unm" hst':term : tactic => `(tactic| (
  apply finishRecvUnmatchedMkPreC_eval (hst := $hst')
  all_goals first | rfl | assumption))

macro "mkr_tag0" : tactic => `(tactic| (
  rw [recvFinishTagRunC_eval (resv? := none) (htag := rfl) (hres := rfl)
    (hOpk := (‹PreparedRecvBounded _ _›).tag_bounded.opkEntries_le)
    (hPrin := (‹PreparedRecvBounded _ _›).tag_bounded.principals_le)]
  simp only [map_bind, bind_map_left, map_pure]
  rfl))

theorem authMkRecvPreB_eval_gen (opk : Bool) (core : Var Γ₁ prfMkCoreTy) (x : Var Γ₂ recvQTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (env : Env Δ)
    (secb : Bool) (idx : Nat) (sc : Bool) (hst : AuthHybridStateFixed S) (msg : PreKeyMsg)
    (P : OracleComp PrimBaseSpec (Option (PreparedAuthRecvPrim S)))
    (hcore : Env.get env (h₁.wk core) = mkCoreToVal secb idx sc hst)
    (hxm : (Env.get env (h₂.wk x)).2.2.2 = preKeyMsgToVal msg)
    (hPeval : ∀ {Γ₁' Γ₂' Δ' : List PT} (hv : Var Γ₁' authHybridStateTy) (xv : Var Γ₂' recvQTy)
      [h₁' : Ext Γ₁' Δ'] [h₂' : Ext Γ₂' Δ'] (env' : Env Δ'),
      Env.get env' (h₁'.wk hv) = authHybridStateToVal hst.toAuthHybridState →
      Env.get env' (h₂'.wk xv) = Env.get env (h₂.wk x) →
      (prepareAuthHybridRecvC S K opk hv xv).eval env' = Option.map preparedAuthRecvToVal <$> P)
    (hPL : AllLeaves (fun prep? => ∀ prep, prep? = some prep → PreparedRecvBounded K prep) P)
    (hB : AuthListsBounded K hst) :
    (authMkRecvPreB S K opk core x).eval env =
      mkPreToVal secb idx sc <$> (P >>= fun prep? => mkRecvPre S idx msg prep? hst sc) := by
  unfold authMkRecvPreB
  rw [letV_eval_eq _ _ _ secb (by simp [v, Expr.eval, hcore, mkCoreToVal])]
  rw [letV_eval_eq _ _ _ idx (by simp [v, Expr.eval, Ext.step_wk, hcore, mkCoreToVal])]
  rw [letV_eval_eq _ _ _ sc (by simp [v, Expr.eval, Ext.step_wk, hcore, mkCoreToVal])]
  rw [letV_eval_eq _ _ _ (authHybridStateFixedToVal hst)
    (by simp [v, Expr.eval, Ext.step_wk, hcore, mkCoreToVal])]
  rw [letV_eval_eq _ _ _ (authSlotStateToVal hst.slots) rfl]
  rw [letV_eval_eq _ _ _ (authHybridStateToVal hst.toAuthHybridState) rfl]
  rw [letV_eval_eq _ _ _ hst.recvCount rfl]
  rw [letV_eval_eq _ _ _ (mkCacheToVal hst.mkSaltCache) rfl]
  rw [letV_eval_eq _ _ _ (preKeyMsgToVal msg) (by simp [v, Expr.eval, Ext.step_wk, hxm])]
  rw [letV_eval_eq _ _ _ (hst.recvCount + 1) rfl]
  rw [bindV_eval]
  refine mkR_peelL _ (Option.map preparedAuthRecvToVal) hPL
    (hPeval _ _ _ rfl (by simp [Ext.step_wk])) (fun prep? hprepB => ?_)
  rcases prep? with _ | prepv
  · rw [caseOptV_eval]
    mkr_simp [mkRecvPre, map_pure, mkPreToVal, mkCoreToVal, authHybridStateFixedToVal,
      authHybridStateFixedWithSlotsToVal, authRespToVal, authRenc]
  · have hPB := hprepB prepv rfl
    rw [caseOptV_eval]
    dsimp only [Option.map, v, Expr.eval, Ext.refl_wk, Env.get_zero]
    rw [letV_eval_eq _ _ _ (authStateToVal prepv.hstDec.base) rfl]
    rw [letV_eval_eq _ _ _ (recvFinishTagToVal prepv.finishTag) rfl]
    rw [letV_eval_eq _ _ _ (prepv.matchedSess?.isSome || prepv.isUncorruptedHonestSender)
      (by simp [boolOr_eval, isSomeE_eval, parMatchedSess?, parIsUncorrSender, Expr.eval,
        Option.isSome_map])]
    rw [Comp.eval]
    dsimp only [v, Expr.eval, Ext.refl_wk, Env.get_zero]
    unfold mkRecvPre
    dsimp only
    rcases hm : prepv.matchedSess? with _ | sess
    · cases hu : prepv.isUncorruptedHonestSender
      ·
        simp only [Option.isSome_none, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
        mkr_simp [hxm]
        rw [hkdfRoC_eval (S := S) (K := K) (s := prepv.hstDec.base) (hst := rfl)
          (hRo := hPB.roCache_le)]
        refine mkR_peel _ (Prod.map drKeyToVal (List.map (Prod.map id drKeyToVal))) rfl
          (fun ⟨dk, roC'⟩ => ?_)
        rw [rootRoC_eval (S := S) (K := K) (s := prepv.hstDec.base) (hst := rfl)
          (hRoot := hPB.rootRoCache_le)]
        mkr_simp [hxm, Prod.map, id_eq]
        refine mkR_peelS _ rfl (fun ⟨⟨rk1, ck0⟩, rootC'⟩ => ?_)
        refine mkR_peelS _ rfl (fun seed => ?_)
        refine mkR_peelS _ rfl (fun ck1 => ?_)
        refine mkR_peelS _ rfl (fun sp? => ?_)
        rcases sp? with _ | ⟨pqrSt, salt?⟩
        · rw [recvFinishTagRunC_eval (S := S) (K := K) (tagv := prepv.finishTag) (resv? := none)
            (htag := rfl) (hres := rfl) (hOpk := hPB.tag_bounded.opkEntries_le)
            (hPrin := hPB.tag_bounded.principals_le)]
          simp only [map_bind, bind_map_left, map_pure]
          rfl
        · simp only []
          refine mkR_peel _ msgKeysToVal rfl (fun mk => ?_)
          refine mkR_peelS _ rfl (fun pt? => ?_)
          rw [recvFinishTagRunC_eval (S := S) (K := K) (tagv := prepv.finishTag)
            (resv? := pt?.map (fun pt => (dk, rk1, ck1, pt, roC', rootC')))
            (htag := rfl) (hres := by cases pt? <;> rfl) (hOpk := hPB.tag_bounded.opkEntries_le)
            (hPrin := hPB.tag_bounded.principals_le)
            (hSentO := fun _ => hPB.tag_bounded.sentOPKEvents_le)
            (hSentN := fun _ => hPB.tag_bounded.sentNoOPKEvents_le)]
          simp only [map_bind, bind_map_left, map_pure]
          rfl
      ·
        simp only [Option.isSome_none, Bool.false_or, ↓reduceIte]
        rw [caseOptV_eval]
        simp only [Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
          mkR_par_ms, hm, Option.map_none]
        rw [bindV_eval, samplePrim_drKey96_eval]
        refine mkR_peel _ drKeyToVal rfl (fun dk => ?_)
        rw [bindV_eval, samplePrim_bytes32_eval]
        refine mkR_peelS _ rfl (fun rk1 => ?_)
        rw [bindV_eval, queryPrim_eval]
        simp only [evalPrimQ, evalPrimOp, Expr.eval,
          Env.get_succ, Env.get_zero, mkR_dr_pqr, pkmPqRatchetMsg, preKeyMsgToVal, preKeyMsgV]
        refine mkR_peelS _ rfl (fun sp? => ?_)
        rw [caseOptV_eval]
        rcases sp? with _ | ⟨pqrSt, salt?⟩
        · dsimp only [v, Expr.eval, Ext.refl_wk, Env.get_zero]
          mkr_simp []
          mkr_tag0
        · dsimp only [v, Expr.eval, Ext.refl_wk, Env.get_zero]
          rw [letV_eval_eq _ _ _ (Prod.map id authSlotStateToVal (hst.slots.allocRecv hst.recvCount))
            (allocRecvSlotE_eval _ _ _ hst.slots hst.recvCount rfl rfl)]
          rw [letV_eval_eq _ _ _
            (mkCoreToVal secb idx sc { hst with slots := (hst.slots.allocRecv hst.recvCount).2 })
            rfl]
          mkr_unm { hst with slots := (hst.slots.allocRecv hst.recvCount).2 }
    · simp only [Option.isSome_some, Bool.true_or, ↓reduceIte]
      rw [caseOptV_eval]
      simp only [Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
        mkR_par_ms, hm, Option.map_some]
      rw [Comp.eval]
      simp only [Expr.eval, Env.get_succ, Env.get_zero, mkR_par_se]
      by_cases he : prepv.sameEph = true
      ·
        simp only [he, ↓reduceIte]
        rw [bindV_eval, queryPrim_eval]
        simp only [evalPrimQ, evalPrimOp, Expr.eval,
          Env.get_succ, Env.get_zero, iasDrKey, mkR_ias_dr, mkR_dr_pqr,
          pkmPqRatchetMsg, preKeyMsgToVal, preKeyMsgV]
        refine mkR_peelS _ rfl (fun sp? => ?_)
        rw [caseOptV_eval]
        rcases sp? with _ | ⟨pqrSt, salt?⟩
        · dsimp only [v, Expr.eval, Ext.refl_wk, Env.get_zero]
          mkr_simp []
          mkr_tag0
        · dsimp only [v, Expr.eval, Ext.refl_wk, Env.get_zero]
          rw [letV_eval_eq _ _ _ salt? rfl]
          rw [letV_eval_eq _ _ _ (hst.slots.lookupSendOrZero sess.sid)
            (lookupSendSlotOrZeroE_eval _ _ _ hst.slots sess.sid rfl
              (by simp [iasSid, Expr.eval, Env.get_succ, Env.get_zero]))]
          mkr_simp [bind_assoc, pure_bind]
          unfold mkMatchedSameEphSlotsPre
          dsimp only
          simp only [eFind, Expr.eval, Env.get_succ, Env.get_zero]
          rw [mkR_find K hst.mkSaltCache _ rfl hB.mkSaltCache_le sess.sid salt?]
          rotate_left
          · intro s' o rc mk
            simp only [Expr.eval, Env.get_succ, Env.get_zero, sameSaltKeyE_eval, mkSaltKeyMatch]
            rw [sidEq_eval _ _ _ s' sess.sid rfl rfl]
          generalize List.find? _ hst.mkSaltCache = r
          apply mkR_ite _ Iff.rfl
          · intro _
            apply mkR_ite _ Iff.rfl
            · intro _
              mkr_fin
            · intro _
              rcases r with _ | ⟨⟨s', o⟩, rc, mk⟩
              · exact mkR_pure _ rfl
              · simp only [Option.map_some]
                mkr_fin
          · intro _
            apply mkR_ite _ Iff.rfl
            · intro _
              apply mkR_ite _ Iff.rfl
              · intro _
                mkr_fin
              · intro _
                rcases r with _ | ⟨⟨s', o⟩, rc, mk⟩
                · simp only [Option.map_none]
                  refine mkR_peel _ msgKeysToVal rfl (fun mk => ?_)
                  mkr_fin
                · simp only [Option.map_some]
                  mkr_fin
            · intro _
              refine mkR_peel _ msgKeysToVal rfl (fun mk => ?_)
              mkr_fin
      ·
        simp only [he, Bool.false_eq_true, ↓reduceIte]
        rw [bindV_eval, samplePrim_bytes32_eval]
        refine mkR_peelS _ rfl (fun rk1 => ?_)
        rw [bindV_eval, queryPrim_eval]
        simp only [evalPrimQ, evalPrimOp, Expr.eval,
          Env.get_succ, Env.get_zero, iasDrKey, mkR_ias_dr, mkR_dr_pqr,
          pkmPqRatchetMsg, preKeyMsgToVal, preKeyMsgV]
        refine mkR_peelS _ rfl (fun sp? => ?_)
        rw [caseOptV_eval]
        rcases sp? with _ | ⟨pqrSt, salt?⟩
        · dsimp only [v, Expr.eval, Ext.refl_wk, Env.get_zero]
          mkr_simp []
          mkr_tag0
        · dsimp only [v, Expr.eval, Ext.refl_wk, Env.get_zero]
          rw [letV_eval_eq _ _ _ (Prod.map id authSlotStateToVal (hst.slots.allocRecv hst.recvCount))
            (allocRecvSlotE_eval _ _ _ hst.slots hst.recvCount rfl rfl)]
          rw [letV_eval_eq _ _ _
            (mkCoreToVal secb idx sc { hst with slots := (hst.slots.allocRecv hst.recvCount).2 })
            rfl]
          mkr_unm { hst with slots := (hst.slots.allocRecv hst.recvCount).2 }

theorem authMkRecvPreB_eval_opk (core : Var Γ₁ prfMkCoreTy) (x : Var Γ₂ recvQTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (env : Env Δ)
    (secb : Bool) (idx : Nat) (sc : Bool) (hst : AuthHybridStateFixed S)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (hcore : Env.get env (h₁.wk core) = mkCoreToVal secb idx sc hst)
    (hx : Env.get env (h₂.wk x) = (k.val, (j.val, (o.val, preKeyMsgToVal msg))))
    (hB : AuthListsBounded K hst) :
    (authMkRecvPreB S K true core x).eval env =
      mkPreToVal secb idx sc <$> mkPre S idx (.recvOPK k j o msg) hst sc := by
  refine authMkRecvPreB_eval_gen S K true core x env secb idx sc hst msg _ hcore
    (by rw [hx]) ?_
    (prepareAuthHybridRecvOPKPrim_bounded k j o msg _ hB.toAuthHybridListsBounded) hB
  intro _ _ _ hv xv _ _ env' hhv hxv
  exact prepareAuthHybridRecvOPKC_eval S K hv xv env' _ k j o msg hhv (hxv.trans hx)
    hB.toAuthHybridListsBounded

theorem authMkRecvPreB_eval_noopk (core : Var Γ₁ prfMkCoreTy) (x : Var Γ₂ recvQTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (env : Env Δ)
    (secb : Bool) (idx : Nat) (sc : Bool) (hst : AuthHybridStateFixed S)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (hcore : Env.get env (h₁.wk core) = mkCoreToVal secb idx sc hst)
    (hx : Env.get env (h₂.wk x) = (k.val, (j.val, (l.val, preKeyMsgToVal msg))))
    (hB : AuthListsBounded K hst) :
    (authMkRecvPreB S K false core x).eval env =
      mkPreToVal secb idx sc <$> mkPre S idx (.recvNoOPK k j l msg) hst sc := by
  refine authMkRecvPreB_eval_gen S K false core x env secb idx sc hst msg _ hcore
    (by rw [hx]) ?_
    (prepareAuthHybridRecvNoOPKPrim_bounded k j l msg _ hB.toAuthHybridListsBounded) hB
  intro _ _ _ hv xv _ _ env' hhv hxv
  exact prepareAuthHybridRecvNoOPKC_eval S K hv xv env' _ k j l msg hhv (hxv.trans hx)
    hB.toAuthHybridListsBounded

end Iface

end SignalPqxdh.Security.ReductionDsl.AuthPrf

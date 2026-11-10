/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfHmacEnc
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfHmacMu
import Computational.Proofs.GameHop.ReductionDsl.PeelSim
import VCVio.EvalDist.Monad.Basic

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthPrfHmac

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open Computational.Proofs.GameHop.ReductionDsl
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security
open SignalPqxdh.Security.ReductionDsl SignalPqxdh.Security.ReductionDsl.AuthAead
open SignalPqxdh.Security.ReductionDsl.AuthPrf hiding queryPrim_eval
open OracleSpec OracleComp

section Helpers

theorem hmR_mapTail {m : Type → Type} [Monad m] [LawfulMonad m] {α β γ δ : Type}
    (F : γ → δ) (h : α → β) {x : m β} {x' : m α} {g : β → m δ} (G : α → γ)
    (hx : x = h <$> x') (hg : ∀ a, g (h a) = pure (F (G a))) :
    x >>= g = F <$> (G <$> x') := by
  subst hx; simp only [bind_map_left, hg, Functor.map_map]
  rw [map_eq_bind_pure_comp]; rfl

theorem hmR_peelL {ι : Type} {spec : OracleSpec.{0, 0} ι} {α α' γ δ : Type} {P : α' → Prop}
    (F : γ → δ) {x : OracleComp spec α} {x' : OracleComp spec α'} (h : α' → α)
    {g : α → OracleComp spec δ} {g' : α' → OracleComp spec γ}
    (hL : AllLeaves P x') (hx : x = h <$> x') (hg : ∀ a, P a → g (h a) = F <$> g' a) :
    x >>= g = F <$> (x' >>= g') := by
  subst hx
  rw [bind_map_left, map_bind]
  exact hL.toHoldsOnLeaves.bind_congr _ _ hg

end Helpers

section Recv

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}

theorem hmR_finErasedE_eval_opk {Γ : List PT} (kjo : Var Γ₁ (.prod .nat (.prod .nat .nat)))
    (usedT' : Var Γ₂ (.list (.prod .nat (.prod U32 (.prod U32 (B 32))))))
    (sndHon : Var Γ₃ .bool) (hstDec : Var Γ₄ authHybridStateTy) (res? : Var Γ₅ schedOutTy)
    [h₁ : Ext Γ₁ Γ] [h₂ : Ext Γ₂ Γ] [h₃ : Ext Γ₃ Γ] [h₄ : Ext Γ₄ Γ] [h₅ : Ext Γ₅ Γ] (env : Env Γ)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (ut : List (Nat × KeyId × KeyId × Bytes))
    (sh : Bool) (hd : AuthHybridState S) (res : HmSchedOut)
    (hk : Env.get env (h₁.wk kjo) = (k.val, (j.val, o.val)))
    (hu : Env.get env (h₂.wk usedT') = ut) (hsh : Env.get env (h₃.wk sndHon) = sh)
    (hh : Env.get env (h₄.wk hstDec) = authHybridStateToVal hd)
    (hr : Env.get env (h₅.wk res?) = schedOutToVal res)
    (hO : hd.base.opkEntries.length ≤ K) :
    (finErasedE K true kjo usedT' sndHon hstDec res?).eval env =
      Prod.map authRespToVal authHybridStateToVal (finishErasedRecvOPK k j o ut sh hd res) := by
  simp only [finErasedE, eCaseOpt, v, Expr.eval, hr]
  rcases res with _ | ⟨dk, rk1, ck, pt, ro, root⟩
  · simp [schedOutToVal, finishErasedRecvOPK, hh, aNone, Expr.eval, authRenc]
  · have hT : (hd.base.opkEntries.map
        (Prod.map (fun (u, j', o') => (u, (j', o'))) opkEntryToVal)).take K
        = hd.base.opkEntries.map (Prod.map (fun (u, j', o') => (u, (j', o'))) opkEntryToVal) := by
      apply List.take_of_length_le; simpa using hO
    simp only [schedOutToVal, Option.map_some, finishErasedRecvOPK]
    cases sh <;> simp only [Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, hsh,
      hh, hu, hk, eMap, nat3Eq_eval, ↓reduceIte, Bool.false_eq_true, Prod.map, authRespToVal,
      authRenc, aRecvHonest, aRecvUnfresh, authHybridStateToVal, authStateToVal, ahsBase,
      stUpd, stMk, oeUpd, oeMk, asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries,
      asSessions, asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK,
      asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
      asAdvKeys, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions, oeOpkSk,
      oeOpkPk, hT, List.map_map, Function.comp_def, List.map_cons, drKeyToVal,
      drKeyV]
    all_goals
      congr
      all_goals first
        | (funext x; rcases x with ⟨⟨a, b, c⟩, e⟩
           by_cases h : ((a, b, c) == (k.val, j.val, o.val)) = true <;> simp [h])
        | simp

theorem hmR_finErasedE_eval_noopk {Γ : List PT} (kjo : Var Γ₁ (.prod .nat (.prod .nat .nat)))
    (usedT' : Var Γ₂ (.list (.prod .nat (.prod U32 (.prod U32 (B 32))))))
    (sndHon : Var Γ₃ .bool) (hstDec : Var Γ₄ authHybridStateTy) (res? : Var Γ₅ schedOutTy)
    [h₁ : Ext Γ₁ Γ] [h₂ : Ext Γ₂ Γ] [h₃ : Ext Γ₃ Γ] [h₄ : Ext Γ₄ Γ] [h₅ : Ext Γ₅ Γ] (env : Env Γ)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (ut : List (Nat × KeyId × KeyId × Bytes))
    (sh : Bool) (hd : AuthHybridState S) (res : HmSchedOut)
    (hk : Env.get env (h₁.wk kjo) = (k.val, (j.val, l.val)))
    (hu : Env.get env (h₂.wk usedT') = ut) (hsh : Env.get env (h₃.wk sndHon) = sh)
    (hh : Env.get env (h₄.wk hstDec) = authHybridStateToVal hd)
    (hr : Env.get env (h₅.wk res?) = schedOutToVal res) :
    (finErasedE K false kjo usedT' sndHon hstDec res?).eval env =
      Prod.map authRespToVal authHybridStateToVal (finishErasedRecvNoOPK k j l ut sh hd res) := by
  simp only [finErasedE, eCaseOpt, v, Expr.eval, hr]
  rcases res with _ | ⟨dk, rk1, ck, pt, ro, root⟩
  · simp [schedOutToVal, finishErasedRecvNoOPK, hh, aNone, Expr.eval, authRenc]
  · simp only [schedOutToVal, Option.map_some, finishErasedRecvNoOPK]
    cases sh <;> simp only [Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, hsh,
      hh, hu, hk, ↓reduceIte, Bool.false_eq_true, Prod.map, authRespToVal, authRenc,
      aRecvHonest, aRecvUnfresh, authHybridStateToVal, authStateToVal, ahsBase,
      stUpd, stMk, asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries,
      asSessions, asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK,
      asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
      asAdvKeys, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
      List.map_cons, drKeyToVal, drKeyV]
    all_goals
      congr
      all_goals simp

theorem hmR_hmCacheFind (cache : AuthMkSaltCache S) (hC : cache.length ≤ K)
    (sid : SessionId S) (salt : Option Bytes)
    (p : ((sessionIdTy.denote × Option Bytes) × Nat × msgKeysTy.denote) → Bool)
    (hp : ∀ (s' : SessionId S) (o : Option Bytes) (rc : Nat) (mk : MessageKeys),
      p ((sessionIdToVal s', o), (rc, msgKeysToVal mk)) = mkSaltKeyMatch (s', o) sid salt) :
    ((hmCacheToVal cache).take K).find? p =
      (cache.find? (fun (k, _) => mkSaltKeyMatch k sid salt)).map
        (fun ((sid, salt?), (rc, mk)) => ((sessionIdToVal sid, salt?), (rc, msgKeysToVal mk))) := by
  rw [List.take_of_length_le (by simpa [hmCacheToVal] using hC)]
  unfold hmCacheToVal
  rw [List.find?_map]
  congr 2
  funext ⟨⟨s', o⟩, rc, mk⟩
  simp only [Function.comp_apply, hp]

private theorem hmR_initKeyIdE_eval {Γ : List PT} (e : Expr pqxdhOps Γ sessionIdTy) (env : Env Γ)
    (sid : SessionId S) (he : e.eval env = sessionIdToVal sid) :
    (initKeyIdE S e).eval env = natToMuKeyIdVal S (initSessionSlotIdx sid) := by
  simp only [initKeyIdE, eCaseSum, v, Expr.eval, Ext.refl_wk, Env.get_zero, he]
  cases sid with
  | sendOPK u i =>
    have hu : u.val < S.N_id := u.isLt
    have hi : i.val < S.N_send_opk := i.isLt
    have hlt : u.val * S.N_send_opk + i.val < S.N_send_opk_tot := by
      unfold Setup.N_send_opk_tot
      have h1 : (u.val + 1) * S.N_send_opk ≤ S.N_id * S.N_send_opk := Nat.mul_le_mul_right _ hu
      nlinarith
    have hdiv : (u.val * S.N_send_opk + i.val) / S.N_send_opk = u.val := by
      rw [Nat.mul_comm, Nat.mul_add_div (Nat.zero_lt_of_lt hi), Nat.div_eq_of_lt hi, Nat.add_zero]
    have hmod : (u.val * S.N_send_opk + i.val) % S.N_send_opk = i.val := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
    simp [sessionIdToVal, sidV, initSessionSlotIdx, natToMuKeyIdVal, hlt, hdiv, hmod]
  | sendNoOPK u i =>
    have hu : u.val < S.N_id := u.isLt
    have hi : i.val < S.N_send_no_opk := i.isLt
    have hlt0 : ¬ (S.N_send_opk_tot + (u.val * S.N_send_no_opk + i.val) < S.N_send_opk_tot) := by
      omega
    have hlt1 : S.N_send_opk_tot + (u.val * S.N_send_no_opk + i.val) < S.N_send_tot := by
      unfold Setup.N_send_tot Setup.N_send_no_opk_tot
      have h1 : (u.val + 1) * S.N_send_no_opk ≤ S.N_id * S.N_send_no_opk :=
        Nat.mul_le_mul_right _ hu
      nlinarith
    have hdiv : (u.val * S.N_send_no_opk + i.val) / S.N_send_no_opk = u.val := by
      rw [Nat.mul_comm, Nat.mul_add_div (Nat.zero_lt_of_lt hi), Nat.div_eq_of_lt hi, Nat.add_zero]
    have hmod : (u.val * S.N_send_no_opk + i.val) % S.N_send_no_opk = i.val := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
    simp [sessionIdToVal, sidV, initSessionSlotIdx, natToMuKeyIdVal, hlt0, hlt1, hdiv, hmod]
  | recvOPK _ _ _ =>
    have hLe : S.N_send_opk_tot ≤ S.N_send_tot := Nat.le_add_right _ _
    have h1 : ¬ (S.N_send_tot < S.N_send_opk_tot) := by omega
    simp [sessionIdToVal, sidV, initSessionSlotIdx, natToMuKeyIdVal, h1]
  | recvNoOPK _ _ _ =>
    have hLe : S.N_send_opk_tot ≤ S.N_send_tot := Nat.le_add_right _ _
    have h1 : ¬ (S.N_send_tot < S.N_send_opk_tot) := by omega
    simp [sessionIdToVal, sidV, initSessionSlotIdx, natToMuKeyIdVal, h1]

theorem hmR_forgeRetIdC_eval
    (fc : Var Γ₁ (.prod .nat (.prod (B 158) (.prod (B 32) muStTy)))) [h₁ : Ext Γ₁ Δ]
    (idx : Expr pqxdhOps Δ muKeyIdTy) (cache' : Expr pqxdhOps Δ authMkSaltCacheTy) (env : Env Δ)
    (jt i : Nat) (ad ct : Bytes) (ms : PrfHmacMuState) (cache : AuthMkSaltCache S)
    (hfc : Env.get env (h₁.wk fc) = (jt, (ad, (ct, muStToValS S ms))))
    (hi : idx.eval env = natToMuKeyIdVal S i) (hc : cache'.eval env = hmCacheToVal cache)
    (hM : MuBounded K ms) :
    (forgeRetIdC K fc idx cache').eval env =
      schedResToVal <$> (do
        let (_, mst') ← hmForgeP jt i ad ct ms
        return (((none : HmSchedOut), cache), mst')) := by
  simp only [forgeRetIdC, letV_eval, bindV_eval]
  refine PeelSim.peel_bind schedResToVal (fun r => muStToValS S r.2)
    (hmForgeIdC_eval S K _ _ jt i ad ct ms ?_ hM) (fun r => ?_)
  · simp [v, Expr.eval, hfc, hi]
  · rcases r with ⟨b, ms'⟩
    simp only [Comp.eval, Expr.eval, v, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, hc,
      map_pure, schedResToVal, schedOutToVal, Option.map_none]

theorem hmR_hmSchedFinC_eval_v2 (a : Expr pqxdhOps Δ schedFinArgsTy) (env : Env Δ) (jt : Nat)
    (kE : PrincipalEntry) (msg : PreKeyMsg) (rc : Nat) (cache : AuthMkSaltCache S)
    (sp : AuthIntRecvSchedPrep S) (ms : PrfHmacMuState)
    (ha : a.eval env = (jt, (principalEntryToVal kE, (preKeyMsgToVal msg, (rc,
      (hmCacheToVal cache, (schedPrepToVal sp, muStToValS S ms)))))))
    (hC : cache.length ≤ K) (hM : MuBounded K ms) :
    (hmSchedFinC S K a).eval env = schedResToVal <$> hmSchedFinP jt kE msg rc cache sp ms := by
  simp only [hmSchedFinC, letV_eval]
  unfold hmSchedFinP
  simp only [Comp.eval, Expr.eval, v, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, ha,
    schedPrepToVal, firstMsgADE_eval, pkmHdr, hdrIkAPk, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt,
    peIkAPk, preKeyMsgToVal, preKeyMsgV, hdrV, principalEntryToVal, eCaseOpt]
  by_cases hI : sp.useIdealBranch = true
  · simp only [hI, ↓reduceIte]
    rcases hm : sp.matchedSess? with _ | s
    · simp only [Option.map_none, caseOptV_eval, Expr.eval,
        Env.get_succ, Env.get_zero]
      exact hmR_forgeRetIdC_eval S K _ _ _ _ _ (S.N_send_tot + rc) _ _ _ _ rfl
        (natToMuKeyIdVal_add_send_tot S rc).symm rfl hM
    · simp only [Option.map_some, caseOptV_eval, Expr.eval,
        Env.get_succ, Env.get_zero, sameSaltKeyE_eval, iasSpqrSalt?, iasAdE, iasAeadCtE,
        iasMsgPlainE, idealAuthSessionToVal]
      simp only [Comp.eval, Expr.eval, Env.get_succ, Env.get_zero]
      by_cases h1 : (sp.sameEph && sameSaltKey sp.spqrSalt? s.spqrSalt?) = true
      · simp only [h1, ↓reduceIte]
        apply PeelSim.peel_ite _ Iff.rfl
        · intro _
          exact PeelSim.peel_pure _ rfl
        · intro _
          exact hmR_forgeRetIdC_eval S K _ _ _ _ _ (initSessionSlotIdx s.sid) _ _ _ _ rfl
            (hmR_initKeyIdE_eval S _ _ s.sid rfl) rfl hM
      · simp only [h1, Bool.false_eq_true, ↓reduceIte]
        apply PeelSim.peel_ite _ Iff.rfl
        · intro _
          simp only [caseOptV_eval, eFind, Expr.eval, Env.get_succ,
            Env.get_zero]
          rw [hmR_hmCacheFind S K cache hC s.sid sp.spqrSalt? _ ?_]
          swap
          · intro s' o rc' mk
            simp only [Expr.eval, Env.get_succ, Env.get_zero,
              sameSaltKeyE_eval, mkSaltKeyMatch]
            rw [sidEq_eval _ _ _ s' s.sid rfl rfl]
          generalize List.find? _ cache = r
          rcases r with _ | ⟨⟨s', o⟩, rc', mk⟩
          · simp only [Option.map_none]
            exact hmR_forgeRetIdC_eval S K _ _ _ _ _ (S.N_send_tot + rc) _ _ _ _ rfl
              (natToMuKeyIdVal_add_send_tot S rc).symm (by rfl) hM
          · simp only [Option.map_some]
            exact hmR_forgeRetIdC_eval S K _ _ _ _ _ (S.N_send_tot + rc') _ _ _ _ rfl
              (natToMuKeyIdVal_add_send_tot S rc').symm rfl hM
        · intro _
          exact hmR_forgeRetIdC_eval S K _ _ _ _ _ (S.N_send_tot + rc) _ _ _ _ rfl
            (natToMuKeyIdVal_add_send_tot S rc).symm rfl hM
  · simp only [hI, Bool.false_eq_true, ↓reduceIte, bindV_eval, queryPrim_eval,
      queryPrim_deriveMsgKeys_eval, queryPrim_aeadDec_eval, Expr.eval,
      Env.get_succ, Env.get_zero]
    refine PeelSim.peel_bind schedResToVal msgKeysToVal rfl (fun mk => ?_)
    refine PeelSim.peel_bind_same schedResToVal (primQ_aeadDec_args_eq (by simp; rfl) rfl rfl) (fun pt? => ?_)
    rcases pt? with _ | pt
    · simp only [caseOptV_eval, Comp.eval, Expr.eval, Env.get_succ,
        Env.get_zero, map_pure]
      rfl
    · simp only [caseOptV_eval, Comp.eval, Expr.eval, Env.get_succ,
        Env.get_zero, map_pure]
      rfl

set_option hygiene false in
local macro "sp_tail" : tactic => `(tactic| (
    refine PeelSim.peel_bind_same _ rfl (fun sp? => ?_)
    rcases sp? with _ | ⟨pq, salt?⟩
    all_goals (try simp only [Comp.eval, Expr.eval, v, Ext.step_wk, Ext.refl_wk, Env.get_succ,
      Env.get_zero, queryPrim_eval, queryPrim_spqrInitRecv_eval, bind_assoc, caseOptV_eval,
      pure_bind, bindV_eval, ↓reduceIte, pkmPqRatchetMsg, map_pure, Option.map_none,
      Option.map_some])
    all_goals rfl))

set_option hygiene false in
local macro "sp_matched" : tactic => `(tactic| (
    simp only [Comp.eval, Expr.eval, v, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
      queryPrim_eval, queryPrim_x25519_eval, queryPrim_pow8_eval, queryPrim_spqrInitRecv_eval,
      samplePrim_bytes32_eval, bytesBeq_eval, bind_assoc, caseOptV_eval, pure_bind, bindV_eval,
      ↓reduceIte, pkmPqRatchetMsg, map_pure, Option.map_none, Option.map_some, Option.isSome_some,
      Bool.true_or, iasDrKey, idealAuthSessionToVal]
    refine PeelSim.peel_bind_same _ rfl (fun dhR => ?_)
    try simp only [Comp.eval, Expr.eval, v, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
      queryPrim_eval, queryPrim_pow8_eval, samplePrim_bytes32_eval, bytesBeq_eval,
      bind_assoc, caseOptV_eval, pure_bind, bindV_eval, ↓reduceIte, pkmPqRatchetMsg,
      map_pure, Option.map_none, Option.map_some]
    refine PeelSim.peel_bind_same _ rfl (fun p1 => ?_)
    refine PeelSim.peel_bind_same _ rfl (fun p2 => ?_)
    try simp only [Comp.eval, Expr.eval, v, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
      samplePrim_bytes32_eval, bytesBeq_eval, bind_assoc, caseOptV_eval, pure_bind, bindV_eval,
      ↓reduceIte, pkmPqRatchetMsg, map_pure, Option.map_none, Option.map_some]
    by_cases hE : (p1 == p2) = true
    · simp only [hE, ↓reduceIte, pure_bind]
      try simp only [Comp.eval, Expr.eval, v, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
        queryPrim_eval, queryPrim_spqrInitRecv_eval, bind_assoc, caseOptV_eval, pure_bind,
        bindV_eval, ↓reduceIte, pkmPqRatchetMsg, map_pure, Option.map_none, Option.map_some]
      sp_tail
    · simp only [hE, Bool.false_eq_true, ↓reduceIte]
      try simp only [Comp.eval, Expr.eval, v, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
        samplePrim_bytes32_eval, queryPrim_eval, queryPrim_spqrInitRecv_eval, bind_assoc,
        caseOptV_eval, pure_bind, bindV_eval, ↓reduceIte, pkmPqRatchetMsg, map_pure,
        Option.map_none, Option.map_some]
      refine PeelSim.peel_bind_same _ rfl (fun r => ?_)
      refine PeelSim.peel_bind_same _ rfl (fun c => ?_)
      try simp only [Comp.eval, Expr.eval, v, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
        samplePrim_bytes32_eval, queryPrim_eval, queryPrim_spqrInitRecv_eval, bind_assoc,
        caseOptV_eval, pure_bind, bindV_eval, ↓reduceIte, pkmPqRatchetMsg, map_pure,
        Option.map_none, Option.map_some]
      refine PeelSim.peel_bind_same _ rfl (fun ms => ?_)
      refine PeelSim.peel_bind_same _ rfl (fun cn => ?_)
      try simp only [Comp.eval, Expr.eval, v, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
        queryPrim_eval, queryPrim_spqrInitRecv_eval, bind_assoc, caseOptV_eval, pure_bind,
        bindV_eval, ↓reduceIte, pkmPqRatchetMsg, map_pure, Option.map_none, Option.map_some]
      sp_tail))

set_option hygiene false in
local macro "sp_nonideal" : tactic => `(tactic| (
    refine PeelSim.peel_bind _ (Prod.map drKeyToVal (List.map (Prod.map id drKeyToVal)))
      (by rw [hkdfRoC_eval S K _ _ _ hd.base (by simp [authHybridStateToVal]) hRo]; rfl)
      (fun ⟨dk, roC'⟩ => ?_)
    simp only [Comp.eval, Expr.eval, v, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
      queryPrim_eval, queryPrim_x25519_eval, bind_assoc, Prod.map, caseOptV_eval, pure_bind,
      sbSpkSk, pkmEphAPk, spkBundleEntryToVal]
    refine PeelSim.peel_bind_same _ rfl (fun dhR => ?_)
    try simp only [Comp.eval, Expr.eval, v, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
      bind_assoc, Prod.map, caseOptV_eval, pure_bind, Option.isSome_none,
      Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    refine PeelSim.peel_bind_same _
      (by rw [rootRoC_eval S K _ _ _ _ hd.base (by simp [authHybridStateToVal]) hRoot]; rfl)
      (fun ⟨⟨rk1, ck0⟩, rootC'⟩ => ?_)
    simp only [Comp.eval, Expr.eval, v, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
      queryPrim_eval, queryPrim_chainKdfSeed_eval, queryPrim_chainKdfNext_eval,
      bind_assoc, bindV_eval, pure_bind]
    refine PeelSim.peel_bind_same _ rfl (fun ms => ?_)
    refine PeelSim.peel_bind_same _ rfl (fun cn => ?_)
    simp only [Comp.eval, Expr.eval, v, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
      queryPrim_eval, queryPrim_spqrInitRecv_eval, bind_assoc, bindV_eval, pure_bind,
      pkmPqRatchetMsg]
    refine PeelSim.peel_bind_same _ rfl (fun sp? => ?_)
    rcases sp? with _ | ⟨pq, salt?⟩
    · simp only [caseOptV_eval, Comp.eval, Expr.eval, v, Ext.step_wk, Ext.refl_wk, Env.get_succ,
        Env.get_zero, map_pure, Option.map_none]
    · simp only [caseOptV_eval, Comp.eval, Expr.eval, v, Ext.step_wk, Ext.refl_wk, Env.get_succ,
        Env.get_zero, map_pure, Option.map_some]
      rfl))

theorem hmR_hmSchedPrepC_eval_v2 (a : Expr pqxdhOps Δ schedPrepArgsTy) (env : Env Δ)
    (hd : AuthHybridState S) (kE : PrincipalEntry) (bE : SpkBundleEntry) (opk? : Option Bytes)
    (sec : Bytes) (msg : PreKeyMsg)
    (ha : a.eval env = (authHybridStateToVal hd, (principalEntryToVal kE, (spkBundleEntryToVal bE,
      (opk?, (sec, preKeyMsgToVal msg))))))
    (hRo : hd.base.roCache.length ≤ K) (hRoot : hd.base.rootRoCache.length ≤ K)
    (hPrin : hd.base.principals.length ≤ K) (hIdeal : hd.idealSessions.length ≤ K) :
    (hmSchedPrepC S K a).eval env =
      Option.map schedPrepToVal <$> prepAuthIntRecvSchedPrim S hd kE bE opk? sec msg := by
  have hTakeI : hd.idealSessions.take (min K S.N_sess_tot) = hd.idealSessions.take S.N_sess_tot := by
    by_cases hKS : K ≤ S.N_sess_tot
    · rw [Nat.min_eq_left hKS, List.take_of_length_le hIdeal,
        List.take_of_length_le (hIdeal.trans hKS)]
    · rw [Nat.min_eq_right (by omega)]
  simp only [hmSchedPrepC, letV_eval, bindV_eval]
  unfold prepAuthIntRecvSchedPrim
  refine PeelSim.peel_bind _ (Option.map (Prod.map id principalEntryToVal))
    ((findHonestC_eval S _ _ _ hd.base
      (by simp [v, Expr.eval, ahsBase, ha, authHybridStateToVal]) hPrin).trans
      (by simp [v, Expr.eval, ha, hdrIkAPk, pkmHdr, preKeyMsgToVal, preKeyMsgV, hdrV]))
    (fun snd? => ?_)
  simp only [Expr.eval, v, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, ha, eCaseOpt,
    peCorrupted, peIkAPk, sbSpkPk, sbPqspkPk, findMV, Comp.eval, findML_eq_findMPrim,
    ← List.map_take, ahsIdealSessions, authHybridStateToVal, hTakeI, pkmHdr, ahsBase, preKeyMsgToVal,
    preKeyMsgV, spkBundleEntryToVal, principalEntryToVal, boolOr_eval]
  rcases snd? with _ | ⟨_, sE⟩ <;> simp only [Option.map_none, Option.map_some, Prod.map, id_eq]
  all_goals
    rw [findMPrim_map_congr idealAuthSessionToVal _
      (matchIdealAuthHandshakePrim kE.ikAPk bE.spkPk opk? bE.pqspkPk msg.hdr)]
    swap
    · intro s
      exact matchIdealAuthHandshakeC_eval S _ _ _ _ _ .zero _
        kE.ikAPk bE.spkPk opk? bE.pqspkPk msg.hdr s rfl rfl rfl rfl rfl rfl
    refine PeelSim.peel_bind _ (Option.map idealAuthSessionToVal) rfl (fun m? => ?_)
    simp only [Expr.eval, Env.get_zero, isSomeE_eval,
      Option.isSome_map, principalEntryToVal]
  · rcases m? with _ | sm
    · simp only [Option.isSome_none, Bool.or_false, Bool.false_eq_true, ↓reduceIte, Option.map_none,
        bind_assoc]
      sp_nonideal
    · simp only [Option.isSome_some, Bool.true_or, ↓reduceIte, Option.map_some,
        Comp.eval, Expr.eval, Env.get_succ, Env.get_zero, bind_assoc,
        caseOptV_eval, pure_bind]
      sp_matched
  · by_cases hc : sE.corrupted = false
    · simp only [hc, Bool.not_false, Bool.or_true, ↓reduceIte]
      rcases m? with _ | sm
      · simp only [Option.map_none, Comp.eval, Expr.eval, Env.get_succ,
          Env.get_zero, bind_assoc, caseOptV_eval, pure_bind, bindV_eval, samplePrim_drKey96_eval]
        refine PeelSim.peel_bind _ drKeyToVal rfl (fun dk => ?_)
        simp only [Expr.eval, Env.get_succ, Env.get_zero,
          queryPrim_eval, queryPrim_x25519_eval, sbSpkSk, pkmEphAPk,
          asRoCache, authStateToVal]
        refine PeelSim.peel_bind_same _ rfl (fun dhR => ?_)
        simp only [samplePrim_bytes32_eval]
        refine PeelSim.peel_bind_same _ rfl (fun r => ?_)
        refine PeelSim.peel_bind_same _ rfl (fun c => ?_)
        try simp only [Comp.eval, Expr.eval, v, Ext.step_wk, Ext.refl_wk, Env.get_succ,
          Env.get_zero, samplePrim_bytes32_eval, bind_assoc, caseOptV_eval, pure_bind, bindV_eval,
          ↓reduceIte]
        refine PeelSim.peel_bind_same _ rfl (fun ms => ?_)
        refine PeelSim.peel_bind_same _ rfl (fun cn => ?_)
        simp only [Expr.eval, Env.get_succ, Env.get_zero, queryPrim_spqrInitRecv_eval,
          pkmPqRatchetMsg]
        sp_tail
      · sp_matched
    · simp only [Bool.not_eq_false] at hc
      simp only [hc, Bool.not_true, Bool.or_false]
      rcases m? with _ | sm
      · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Option.map_none,
          bind_assoc]
        sp_nonideal
      · sp_matched

theorem hmR_hmSchedC_eval_v2 (a : Expr pqxdhOps Δ schedArgsTy) (env : Env Δ) (jt rc : Nat)
    (cache : AuthMkSaltCache S) (hd : AuthHybridState S)
    (kE : PrincipalEntry) (bE : SpkBundleEntry) (opk? : Option Bytes) (sec : Bytes)
    (msg : PreKeyMsg) (ms : PrfHmacMuState)
    (ha : a.eval env = (jt, (rc, (hmCacheToVal cache, ((authHybridStateToVal hd,
      (principalEntryToVal kE, (spkBundleEntryToVal bE, (opk?, (sec, preKeyMsgToVal msg))))),
        muStToValS S ms)))))
    (hRo : hd.base.roCache.length ≤ K) (hRoot : hd.base.rootRoCache.length ≤ K)
    (hC : cache.length ≤ K) (hM : MuBounded K ms) (hPrin : hd.base.principals.length ≤ K)
    (hIdeal : hd.idealSessions.length ≤ K) :
    (hmSchedC S K a).eval env =
      schedResToVal <$> hmSchedP S jt hd rc cache kE bE opk? sec msg ms := by
  simp only [hmSchedC, hmSchedP, letV_eval, bindV_eval]
  refine PeelSim.peel_bind schedResToVal (Option.map schedPrepToVal)
    (hmR_hmSchedPrepC_eval_v2 S K _ _ hd kE bE opk? sec msg ?_ hRo hRoot hPrin hIdeal)
    (fun sp? => ?_)
  · simp [v, Expr.eval, ha]
  rcases sp? with _ | sp
  · simp only [caseOptV_eval, v, Expr.eval, Ext.refl_wk, Ext.step_wk, Env.get_zero, Env.get_succ,
      Option.map_none, Comp.eval, map_pure, ha]
    rfl
  · simp only [caseOptV_eval, v, Expr.eval, Ext.refl_wk, Env.get_zero, Option.map_some]
    exact hmR_hmSchedFinC_eval_v2 S K _ _ jt kE msg rc cache sp ms (by simp [Expr.eval, ha]) hC hM

theorem hmR_hmRecvTailC_eval_v2 (opk : Bool) (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ recvQTy) (d : Var Γ₅ hmRecvDataTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] [h₄ : Ext Γ₄ Δ] [h₅ : Ext Γ₅ Δ] (env : Env Δ)
    (jtv : Nat) (hst : AuthHybridStateFixed S) (ms : PrfHmacMuState) (msg : PreKeyMsg)
    (dv : HmRecvData S) (fin : HmSchedOut → AuthResponse × AuthHybridState S)
    (hj : Env.get env (h₁.wk jt) = jtv)
    (hs : Env.get env (h₂.wk fhst) = authHybridStateFixedToVal hst)
    (hm : Env.get env (h₃.wk mst) = muStToValS S ms)
    (hxm : (Env.get env (h₄.wk x)).2.2.2 = preKeyMsgToVal msg)
    (hd : Env.get env (h₅.wk d) = hmRecvDataToVal dv)
    (hfin : ∀ {Γ Γ₁' Γ₂' Γ₃' Γ₄' Γ₅' : List PT} (kjo : Var Γ₁' (.prod .nat (.prod .nat .nat)))
      (usedT' : Var Γ₂' (.list (.prod .nat (.prod U32 (.prod U32 (B 32))))))
      (sndHon : Var Γ₃' .bool) (hstDec : Var Γ₄' authHybridStateTy) (res? : Var Γ₅' schedOutTy)
      {h₁' : Ext Γ₁' Γ} {h₂' : Ext Γ₂' Γ} {h₃' : Ext Γ₃' Γ} {h₄' : Ext Γ₄' Γ} {h₅' : Ext Γ₅' Γ}
      (env' : Env Γ) (res : HmSchedOut),
      Env.get env' (h₁'.wk kjo) = ((Env.get env (h₄.wk x)).1, ((Env.get env (h₄.wk x)).2.1,
        (Env.get env (h₄.wk x)).2.2.1)) →
      Env.get env' (h₂'.wk usedT') = dv.usedTriples' →
      Env.get env' (h₃'.wk sndHon) = dv.senderIsHonest →
      Env.get env' (h₄'.wk hstDec) = authHybridStateToVal dv.hstDec →
      Env.get env' (h₅'.wk res?) = schedOutToVal res →
      (finErasedE K opk kjo usedT' sndHon hstDec res?).eval env' =
        Prod.map authRespToVal authHybridStateToVal (fin res))
    (hRo : dv.hstDec.base.roCache.length ≤ K) (hRoot : dv.hstDec.base.rootRoCache.length ≤ K)
    (hC : hst.mkSaltCache.length ≤ K) (hM : MuBounded K ms)
    (hPrin : dv.hstDec.base.principals.length ≤ K)
    (hIdeal : dv.hstDec.idealSessions.length ≤ K) :
    (hmRecvTailC S K opk jt fhst mst x d).eval env =
      hmResToVal <$> hmRecvTail S jtv msg hst ms dv fin := by
  simp only [hmRecvTailC, letV_eval, bindV_eval]
  refine PeelSim.peel_bind hmResToVal schedResToVal
    (hmR_hmSchedC_eval_v2 S K _ _ jtv hst.recvCount hst.mkSaltCache dv.hstDec dv.kEntry dv.bEntry
      dv.opkPk? dv.secrets msg ms ?_ hRo hRoot hC hM hPrin hIdeal) (fun ⟨⟨res, cache'⟩, mst'⟩ => ?_)
  · simp only [Expr.eval, v, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, hj, hs, hm, hd,
      hxm, ahsfRecvCount, ahsfMkSaltCache, authHybridStateFixedToVal,
      authHybridStateFixedWithSlotsToVal, hmRecvDataToVal]
    rfl
  · rw [hfin (res := res)]
    rotate_left
    · simp [v, Expr.eval]
    · simp [v, Expr.eval, hd, hmRecvDataToVal]
    · simp [v, Expr.eval, hd, hmRecvDataToVal]
    · simp [v, Expr.eval, hd, hmRecvDataToVal]
    · simp [v, Expr.eval, schedResToVal]
    simp only [Comp.eval, Expr.eval, v, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, hs,
      ahsfRecvCount, authHybridStateFixedToVal,
      authHybridStateFixedWithSlotsToVal, authSlotStateToVal, schedResToVal, map_pure, hmResToVal]
    rfl

theorem hmR_hmFinishPrepP_leaves (kVal jVal : Nat) (kEntry : PrincipalEntry)
    (bEntry : SpkBundleEntry) (opkSk? opkPk? : Option Bytes) (msg : PreKeyMsg)
    (hst : AuthHybridState S) :
    AllLeaves (fun d? => ∀ d : HmRecvData S, d? = some d → d.hstDec.base = hst.base)
      (hmFinishPrepP S kVal jVal kEntry bEntry opkSk? opkPk? msg hst) := by
  unfold hmFinishPrepP
  refine AllLeaves.bind_const _ fun _ => AllLeaves.bind_const _ fun _ => ?_
  split
  · exact AllLeaves.pure (by simp)
  refine AllLeaves.bind_const _ fun ss? => ?_
  rcases ss? with _ | ss
  · exact AllLeaves.pure (by simp)
  refine AllLeaves.bind_const _ fun _ => AllLeaves.bind_const _ fun _ =>
    AllLeaves.bind_const _ fun _ => AllLeaves.bind_const _ fun _ =>
    AllLeaves.bind_const _ fun _ => AllLeaves.pure ?_
  rintro d ⟨⟩
  rfl

theorem hmR_hmRecvOPKPrepP_leaves (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (msg : PreKeyMsg) (hst : AuthHybridState S) :
    AllLeaves (fun d? => ∀ d : HmRecvData S, d? = some d → d.hstDec.base = hst.base)
      (hmRecvOPKPrepP S k j o msg hst) := by
  unfold hmRecvOPKPrepP
  try dsimp only
  split
  · exact AllLeaves.pure (by simp)
  try dsimp only
  split
  · exact AllLeaves.pure (by simp)
  refine AllLeaves.bind_const _ fun _ => ?_
  try dsimp only
  split
  · exact AllLeaves.pure (by simp)
  try dsimp only
  split
  · split
    · exact AllLeaves.pure (by simp)
    · exact hmR_hmFinishPrepP_leaves S _ _ _ _ _ _ _ _
  · exact AllLeaves.pure (by simp)

theorem hmR_hmRecvNoOPKPrepP_leaves (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (msg : PreKeyMsg) (hst : AuthHybridState S) :
    AllLeaves (fun d? => ∀ d : HmRecvData S, d? = some d → d.hstDec.base = hst.base)
      (hmRecvNoOPKPrepP S k j l msg hst) := by
  unfold hmRecvNoOPKPrepP
  try dsimp only
  split
  · exact AllLeaves.pure (by simp)
  try dsimp only
  split
  · exact AllLeaves.pure (by simp)
  refine AllLeaves.bind_const _ fun _ => ?_
  try dsimp only
  split
  · exact AllLeaves.pure (by simp)
  try dsimp only
  split
  · exact hmR_hmFinishPrepP_leaves S _ _ _ _ _ _ _ _
  · exact AllLeaves.pure (by simp)

theorem hmR_any_usedRecv (xs : List (Nat × Nat × Nat)) (k j o : Nat) :
    (xs.map (fun (u, j', o') => (u, (j', o')))).any (fun e => e == (k, (j, o))) =
    xs.contains (k, j, o) := by
  rw [Bool.eq_iff_iff, List.any_map, List.any_eq_true, List.contains_iff_exists_mem_beq]
  refine exists_congr (fun ⟨u, j', o'⟩ => and_congr_right' ?_)
  by_cases h1 : u = k <;> by_cases h2 : j' = j <;> by_cases h3 : o' = o <;>
    simp [h1, h2, h3] <;> omega

theorem hmR_hmRecvPrepC_eval_opk (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ recvQTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (env : Env Δ) (hst : AuthHybridStateFixed S)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (hs : Env.get env (h₁.wk fhst) = authHybridStateFixedToVal hst)
    (hx : Env.get env (h₂.wk x) = (k.val, (j.val, (o.val, preKeyMsgToVal msg))))
    (hB : AuthListsBounded K hst) :
    (hmRecvPrepC S K true fhst x).eval env =
      Option.map hmRecvDataToVal <$> hmRecvOPKPrepP S k j o msg hst.toAuthHybridState := by
  have hB' := hB.toAuthHybridListsBounded
  have hTakeUsedO : (hst.toAuthHybridState.base.usedRecvOPK.map
      (fun (u, j', o') => (u, (j', o')))).take K =
      hst.toAuthHybridState.base.usedRecvOPK.map (fun (u, j', o') => (u, (j', o'))) := by
    apply List.take_of_length_le; simpa using hB'.usedRecvOPK_le
  have hTakeP : (hst.toAuthHybridState.base.principals.map
      (Prod.map id principalEntryToVal)).take K =
      hst.toAuthHybridState.base.principals.map (Prod.map id principalEntryToVal) := by
    apply List.take_of_length_le; simpa using hB'.principals_le
  have hTakeS : (hst.toAuthHybridState.base.spkBundles.map
      (Prod.map id spkBundleEntryToVal)).take K =
      hst.toAuthHybridState.base.spkBundles.map (Prod.map id spkBundleEntryToVal) := by
    apply List.take_of_length_le; simpa using hB'.spkBundles_le
  have hTakeO : (hst.toAuthHybridState.base.opkEntries.map
      (Prod.map (fun (u, j', o') => (u, (j', o'))) opkEntryToVal)).take K =
      hst.toAuthHybridState.base.opkEntries.map
      (Prod.map (fun (u, j', o') => (u, (j', o'))) opkEntryToVal) := by
    apply List.take_of_length_le; simpa using hB'.opkEntries_le
  have hhs : Env.get env (h₁.wk fhst) = authHybridStateFixedToVal hst := hs
  unfold hmRecvPrepC hmRecvOPKPrepP
  simp only [letV_eval, Comp.eval, Expr.eval, v, Ext.step_wk, Ext.refl_wk, Env.get_succ,
    Env.get_zero, hs, hx, ahsfHybrid, ahsBase, pkmHdr, authHybridStateFixedToVal,
    authHybridStateFixedWithSlotsToVal, preKeyMsgToVal,
    preKeyMsgV, hdrV, hdrSpkId, hdrPqspkId, hdrOpkId?, hdrIkAPk, hdrEkAPk,
    pkmEphAPk, optU32Eq_eval, natEq_eval, u32Beq_eval, u32OfNat_eval, bytesLen_eval, ↓reduceIte]
  refine PeelSim.peel_ite _ Iff.rfl (fun _ => PeelSim.peel_pure _ (a' := none) rfl) (fun _ => ?_)
  simp only [eAny, Expr.eval, asUsedRecvOPK, nat3Eq_eval, Env.get_succ, Env.get_zero]
  refine PeelSim.peel_ite _ (by simp only [authHybridStateToVal, authStateToVal, hTakeUsedO,
    hmR_any_usedRecv]) (fun _ => PeelSim.peel_pure _ (a' := none) rfl) (fun _ => ?_)
  simp only [bindV_eval]
  refine PeelSim.peel_bind_same _
    ((koskSenderOkC_eval S K _ _ _ hst.toAuthHybridState.base
      (by simp [authStateToVal]) hB'.advKeys_le hB'.principals_le).trans (by simp [Expr.eval])) (fun ok => ?_)
  simp only [Comp.eval, Expr.eval, Env.get_zero]
  refine PeelSim.peel_ite _ Iff.rfl (fun _ => PeelSim.peel_pure _ (a' := none) rfl) (fun _ => ?_)
  simp only [caseOptV_eval, eFind, asPrincipals, asSpkBundles, natEq_eval, nat2Eq_eval, Comp.eval,
    Expr.eval, Env.get_succ, Env.get_zero, hx, authStateToVal, hTakeP,
    hTakeS, List.find?_map, Function.comp_def, Prod.map, id_eq, authHybridStateToVal]
  cases hFindP : hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == k.val) with
  | none => simp only [Option.map_none]; exact PeelSim.peel_pure _ rfl
  | some kP =>
    rcases kP with ⟨kIdx, kEntry⟩
    cases hFindS : hst.toAuthHybridState.base.spkBundles.find?
        (fun (idx, _) => idx == (k.val, j.val)) with
    | none => simp only [Option.map_none, Option.map_some]; exact PeelSim.peel_pure _ rfl
    | some bP =>
      rcases bP with ⟨bIdx, bEntry⟩
      simp only [Option.map_some, letV_eval, bindV_eval, caseOptV_eval, Comp.eval, Expr.eval,
        Env.get_succ, Env.get_zero, asOpkEntries, nat3Eq_eval, hTakeO,
        List.find?_map, Function.comp_def, Prod.map, id_eq]
      have hO' : List.find? (fun x : (Nat × Nat × Nat) × OpkEntry =>
          (x.1.1, x.1.2.1, x.1.2.2) == (k.val, j.val, o.val)) hst.base.opkEntries =
          hst.toAuthHybridState.base.opkEntries.find?
            (fun (idx, _) => idx == (k.val, j.val, o.val)) := rfl
      rw [hO']
      cases hFindO : hst.toAuthHybridState.base.opkEntries.find?
          (fun (idx, _) => idx == (k.val, j.val, o.val)) with
      | none =>
        simp only [Option.map_none, pure_bind, caseSumV, Comp.eval, Expr.eval, Env.get_zero]
        exact PeelSim.peel_pure _ rfl
      | some oP =>
        rcases oP with ⟨oIdx, oEntry⟩
        simp only [Option.map_some, oeConsumed, Expr.eval, Env.get_zero, opkEntryToVal, Prod.map]
        cases hCons : oEntry.consumed
        · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, caseSumV, Comp.eval, Expr.eval,
            Env.get_zero]
          unfold hmFinishPrepP
          rw [letV_eval, kyberCheckE_eval K _ _ _ (by simp [asUsedKyberTriples, Expr.eval,
            hB'.usedKyberTriples_le])]
          simp only [asUsedKyberTriples, Expr.eval, Env.get_succ, Env.get_zero, hx,
            Prod.mk.eta, List.map_id']
          generalize checkAndMarkKyberBaseKeySeen _ _ _ _ _ = kcv
          rcases kcv with ⟨ok, ut⟩
          simp only [bindV_eval, queryPrim_eval, queryPrim_isCanonical_eval,
            queryPrim_kemDecaps_eval, boolOr_eval, Comp.eval, Expr.eval, Env.get_succ, Env.get_zero]
          refine PeelSim.peel_bind_same _ rfl (fun can => ?_)
          refine PeelSim.peel_bind_same _ rfl (fun canE => ?_)
          refine PeelSim.peel_ite _ Iff.rfl (fun _ => PeelSim.peel_pure _ (a' := none) rfl) (fun _ => ?_)
          refine PeelSim.peel_bind_same _ rfl (fun ss? => ?_)
          rcases ss? with _ | ss
          · simp only [caseOptV_eval, Expr.eval, Env.get_zero, Comp.eval]
            exact PeelSim.peel_pure _ rfl
          · simp only [caseOptV_eval, letV_eval, bindV_eval, queryPrim_eval, queryPrim_x25519_eval,
              Expr.eval, Env.get_zero, Env.get_succ, Comp.eval]
            refine PeelSim.peel_bind_same _ rfl (fun dh1 => ?_)
            refine PeelSim.peel_bind_same _ rfl (fun dh2 => ?_)
            refine PeelSim.peel_bind_same _ rfl (fun dh3 => ?_)
            refine PeelSim.peel_bind_same _ rfl (fun dh4? => ?_)
            refine PeelSim.peel_bind _ (Option.map (Prod.map id principalEntryToVal))
              ((findHonestC_eval S _ _ _ hst.toAuthHybridState.base
                (by first | rfl | simp [authStateToVal]) hB'.principals_le).trans rfl)
              (fun sp => ?_)
            simp only [Expr.eval, Env.get_succ, Env.get_zero, buildSecretsE_eval,
              isSomeE_eval, Option.isSome_map, hx]
            refine PeelSim.peel_pure _ ?_
            rcases sp with _ | ⟨_, _⟩ <;> rcases dh4? with _ | _ <;>
              simp only [hmRecvDataToVal, Option.map_some, Option.some.injEq, Prod.mk.injEq] <;>
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try rfl) <;>
              simp only [Expr.eval, Env.get_succ, Env.get_zero, ahsInitKemRecs, ahsRecvKemRecs,
                ahsIdealSessions, sbPqspkPk, sbPqspkSk, hdrKemCt, spkBundleEntryToVal,
                authHybridStateToVal, authStateToVal, recvKemRecordToVal, List.map_cons,
                Prod.mk.injEq] <;>
              simp []
        · simp only [↓reduceIte, pure_bind, caseSumV, Comp.eval, Expr.eval, Env.get_zero]
          exact PeelSim.peel_pure _ rfl

theorem hmR_hmRecvPrepC_eval_noopk (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ recvQTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (env : Env Δ) (hst : AuthHybridStateFixed S)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (hs : Env.get env (h₁.wk fhst) = authHybridStateFixedToVal hst)
    (hx : Env.get env (h₂.wk x) = (k.val, (j.val, (l.val, preKeyMsgToVal msg))))
    (hB : AuthListsBounded K hst) :
    (hmRecvPrepC S K false fhst x).eval env =
      Option.map hmRecvDataToVal <$> hmRecvNoOPKPrepP S k j l msg hst.toAuthHybridState := by
  have hB' := hB.toAuthHybridListsBounded
  have hTakeUsedN : (hst.toAuthHybridState.base.usedRecvNoOPK.map
      (fun (u, j', o') => (u, (j', o')))).take K =
      hst.toAuthHybridState.base.usedRecvNoOPK.map (fun (u, j', o') => (u, (j', o'))) := by
    apply List.take_of_length_le; simpa using hB'.usedRecvNoOPK_le
  have hTakeP : (hst.toAuthHybridState.base.principals.map
      (Prod.map id principalEntryToVal)).take K =
      hst.toAuthHybridState.base.principals.map (Prod.map id principalEntryToVal) := by
    apply List.take_of_length_le; simpa using hB'.principals_le
  have hTakeS : (hst.toAuthHybridState.base.spkBundles.map
      (Prod.map id spkBundleEntryToVal)).take K =
      hst.toAuthHybridState.base.spkBundles.map (Prod.map id spkBundleEntryToVal) := by
    apply List.take_of_length_le; simpa using hB'.spkBundles_le
  unfold hmRecvPrepC hmRecvNoOPKPrepP
  simp only [letV_eval, Comp.eval, Expr.eval, v, Ext.step_wk, Ext.refl_wk, Env.get_succ,
    Env.get_zero, hs, hx, ahsfHybrid, ahsBase, pkmHdr, authHybridStateFixedToVal,
    authHybridStateFixedWithSlotsToVal, preKeyMsgToVal,
    preKeyMsgV, hdrV, hdrSpkId, hdrPqspkId, hdrOpkId?, hdrIkAPk, hdrEkAPk,
    pkmEphAPk, optU32Eq_eval, natEq_eval, u32Beq_eval, u32OfNat_eval, bytesLen_eval,
    Bool.false_eq_true, ↓reduceIte]
  refine PeelSim.peel_ite _ Iff.rfl (fun _ => PeelSim.peel_pure _ (a' := none) rfl) (fun _ => ?_)
  simp only [eAny, Expr.eval, asUsedRecvNoOPK, nat3Eq_eval, Env.get_succ, Env.get_zero]
  refine PeelSim.peel_ite _ (by simp only [authHybridStateToVal, authStateToVal, hTakeUsedN,
    hmR_any_usedRecv]) (fun _ => PeelSim.peel_pure _ (a' := none) rfl) (fun _ => ?_)
  simp only [bindV_eval]
  refine PeelSim.peel_bind_same _
    ((koskSenderOkC_eval S K _ _ _ hst.toAuthHybridState.base
      (by simp [authStateToVal]) hB'.advKeys_le hB'.principals_le).trans (by simp [Expr.eval])) (fun ok => ?_)
  simp only [Comp.eval, Expr.eval, Env.get_zero]
  refine PeelSim.peel_ite _ Iff.rfl (fun _ => PeelSim.peel_pure _ (a' := none) rfl) (fun _ => ?_)
  simp only [caseOptV_eval, eFind, asPrincipals, asSpkBundles, natEq_eval, nat2Eq_eval, Comp.eval,
    Expr.eval, Env.get_succ, Env.get_zero, hx, authStateToVal, hTakeP,
    hTakeS, List.find?_map, Function.comp_def, Prod.map, id_eq, authHybridStateToVal]
  cases hFindP : hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == k.val) with
  | none => simp only [Option.map_none]; exact PeelSim.peel_pure _ rfl
  | some kP =>
    rcases kP with ⟨kIdx, kEntry⟩
    cases hFindS : hst.toAuthHybridState.base.spkBundles.find?
        (fun (idx, _) => idx == (k.val, j.val)) with
    | none => simp only [Option.map_none, Option.map_some]; exact PeelSim.peel_pure _ rfl
    | some bP =>
      rcases bP with ⟨bIdx, bEntry⟩
      simp only [Option.map_some, letV_eval, bindV_eval, Comp.eval, Expr.eval, Env.get_succ,
        Env.get_zero, pure_bind, caseSumV]
      unfold hmFinishPrepP
      rw [kyberCheckE_eval K _ _ _ (by simp [asUsedKyberTriples, Expr.eval,
        hB'.usedKyberTriples_le])]
      simp only [asUsedKyberTriples, Expr.eval, Env.get_succ, Env.get_zero, hx,
        Prod.mk.eta, List.map_id']
      generalize checkAndMarkKyberBaseKeySeen _ _ _ _ _ = kcv
      rcases kcv with ⟨ok, ut⟩
      simp only [queryPrim_eval, queryPrim_isCanonical_eval, queryPrim_kemDecaps_eval,
        boolOr_eval, Expr.eval, Env.get_succ, Env.get_zero]
      refine PeelSim.peel_bind_same _ rfl (fun can => ?_)
      refine PeelSim.peel_bind_same _ rfl (fun canE => ?_)
      refine PeelSim.peel_ite _ Iff.rfl (fun _ => PeelSim.peel_pure _ (a' := none) rfl) (fun _ => ?_)
      refine PeelSim.peel_bind_same _ rfl (fun ss? => ?_)
      rcases ss? with _ | ss
      · simp only [caseOptV_eval, Expr.eval, Env.get_zero, Comp.eval]
        exact PeelSim.peel_pure _ rfl
      · simp only [caseOptV_eval, letV_eval, bindV_eval, queryPrim_eval, queryPrim_x25519_eval,
          Expr.eval, Env.get_zero, Env.get_succ, Comp.eval]
        refine PeelSim.peel_bind_same _ rfl (fun dh1 => ?_)
        refine PeelSim.peel_bind_same _ rfl (fun dh2 => ?_)
        refine PeelSim.peel_bind_same _ rfl (fun dh3 => ?_)
        simp only [pure_bind]
        refine PeelSim.peel_bind _ (Option.map (Prod.map id principalEntryToVal))
          ((findHonestC_eval S _ _ _ hst.toAuthHybridState.base
            (by first | rfl | simp [authStateToVal]) hB'.principals_le).trans rfl)
          (fun sp => ?_)
        simp only [Expr.eval, Env.get_succ, Env.get_zero, buildSecretsE_eval,
          isSomeE_eval, Option.isSome_map, hx]
        refine PeelSim.peel_pure _ ?_
        rcases sp with _ | ⟨_, _⟩ <;>
          simp only [hmRecvDataToVal, Option.map_some, Option.some.injEq, Prod.mk.injEq] <;>
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try rfl) <;>
          simp only [Expr.eval, Env.get_succ, Env.get_zero, ahsInitKemRecs, ahsRecvKemRecs,
            ahsIdealSessions, sbPqspkPk, sbPqspkSk, hdrKemCt,
            authHybridStateToVal, authStateToVal, recvKemRecordToVal, List.map_cons,
            Prod.mk.injEq] <;>
          simp []

private theorem hmR_hmFinishPrepP_ideal (kVal jVal : Nat) (kEntry : PrincipalEntry)
    (bEntry : SpkBundleEntry) (opkSk? opkPk? : Option Bytes) (msg : PreKeyMsg)
    (hst : AuthHybridState S) :
    AllLeaves (fun d? => ∀ d : HmRecvData S, d? = some d →
        d.hstDec.base = hst.base ∧ d.hstDec.idealSessions = hst.idealSessions)
      (hmFinishPrepP S kVal jVal kEntry bEntry opkSk? opkPk? msg hst) := by
  unfold hmFinishPrepP
  refine AllLeaves.bind_const _ fun _ => AllLeaves.bind_const _ fun _ => ?_
  split
  · exact AllLeaves.pure (by simp)
  refine AllLeaves.bind_const _ fun ss? => ?_
  rcases ss? with _ | ss
  · exact AllLeaves.pure (by simp)
  refine AllLeaves.bind_const _ fun _ => AllLeaves.bind_const _ fun _ =>
    AllLeaves.bind_const _ fun _ => AllLeaves.bind_const _ fun _ =>
    AllLeaves.bind_const _ fun _ => AllLeaves.pure ?_
  rintro d ⟨⟩
  exact ⟨rfl, rfl⟩

private theorem hmR_hmRecvOPKPrepP_ideal (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (msg : PreKeyMsg) (hst : AuthHybridState S) :
    AllLeaves (fun d? => ∀ d : HmRecvData S, d? = some d →
        d.hstDec.base = hst.base ∧ d.hstDec.idealSessions = hst.idealSessions)
      (hmRecvOPKPrepP S k j o msg hst) := by
  unfold hmRecvOPKPrepP
  try dsimp only
  split
  · exact AllLeaves.pure (by simp)
  try dsimp only
  split
  · exact AllLeaves.pure (by simp)
  refine AllLeaves.bind_const _ fun _ => ?_
  try dsimp only
  split
  · exact AllLeaves.pure (by simp)
  try dsimp only
  split
  · split
    · exact AllLeaves.pure (by simp)
    · exact hmR_hmFinishPrepP_ideal S _ _ _ _ _ _ _ _
  · exact AllLeaves.pure (by simp)

private theorem hmR_hmRecvNoOPKPrepP_ideal (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (msg : PreKeyMsg) (hst : AuthHybridState S) :
    AllLeaves (fun d? => ∀ d : HmRecvData S, d? = some d →
        d.hstDec.base = hst.base ∧ d.hstDec.idealSessions = hst.idealSessions)
      (hmRecvNoOPKPrepP S k j l msg hst) := by
  unfold hmRecvNoOPKPrepP
  try dsimp only
  split
  · exact AllLeaves.pure (by simp)
  try dsimp only
  split
  · exact AllLeaves.pure (by simp)
  refine AllLeaves.bind_const _ fun _ => ?_
  try dsimp only
  split
  · exact AllLeaves.pure (by simp)
  try dsimp only
  split
  · exact hmR_hmFinishPrepP_ideal S _ _ _ _ _ _ _ _
  · exact AllLeaves.pure (by simp)

theorem hmRecvC_eval_opk_v2 (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ recvQTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] [h₄ : Ext Γ₄ Δ] (env : Env Δ)
    (jtv : Nat) (hst : AuthHybridStateFixed S) (ms : PrfHmacMuState)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (hj : Env.get env (h₁.wk jt) = jtv)
    (hs : Env.get env (h₂.wk fhst) = authHybridStateFixedToVal hst)
    (hm : Env.get env (h₃.wk mst) = muStToValS S ms)
    (hx : Env.get env (h₄.wk x) = (k.val, (j.val, (o.val, preKeyMsgToVal msg))))
    (hB : AuthListsBounded K hst) (hM : MuBounded K ms) :
    (hmRecvC S K true jt fhst mst x).eval env =
      hmPreToVal <$> hmPre S jtv (.recvOPK k j o msg) hst ms := by
  simp only [hmRecvC, bindV_eval]
  rw [hmR_hmRecvPrepC_eval_opk S K fhst x env hst k j o msg hs hx hB]
  simp only [hmPre]
  refine hmR_peelL hmPreToVal (Option.map hmRecvDataToVal)
    (hmR_hmRecvOPKPrepP_ideal S k j o msg _) rfl (fun d? hd => ?_)
  rcases d? with _ | dv
  · simp only [caseOptV_eval, v, Expr.eval, Ext.refl_wk, Env.get_zero, Option.map_none, Comp.eval,
      map_pure]
    simp only [aNone, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache,
      Expr.eval, Ext.step_wk, Env.get_succ, hs, hm, hmPreToVal, hmResToVal,
      authHybridStateFixedToVal, authHybridStateFixedWithSlotsToVal, authSlotStateToVal]
    rfl
  · obtain ⟨hbase, hideal⟩ := hd dv rfl
    simp only [caseOptV_eval, v, Expr.eval, Ext.refl_wk, Env.get_zero, Option.map_some, bindV_eval]
    refine hmR_mapTail hmPreToVal hmResToVal Sum.inl
      (hmR_hmRecvTailC_eval_v2 S K true jt fhst mst x .zero _ jtv hst ms msg dv _
        (by simpa using hj) (by simpa using hs) (by simpa using hm) (by simp [hx]) rfl ?_
        (by rw [hbase]; exact hB.roCache_le) (by rw [hbase]; exact hB.rootRoCache_le)
        hB.mkSaltCache_le hM (by rw [hbase]; exact hB.principals_le)
        (by rw [hideal]; exact hB.idealSessions_le)) (fun r => rfl)
    · intro _ _ _ _ _ _ kjo usedT' sndHon hstDec res? _ _ _ _ _ env' res hk hu hsh hh hr
      exact hmR_finErasedE_eval_opk S K kjo usedT' sndHon hstDec res? env' k j o _ _ _ res
        (by rw [hk]; simp [hx]) hu hsh hh hr (by rw [hbase]; exact hB.opkEntries_le)

theorem hmRecvC_eval_noopk_v2 (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ recvQTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] [h₄ : Ext Γ₄ Δ] (env : Env Δ)
    (jtv : Nat) (hst : AuthHybridStateFixed S) (ms : PrfHmacMuState)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (hj : Env.get env (h₁.wk jt) = jtv)
    (hs : Env.get env (h₂.wk fhst) = authHybridStateFixedToVal hst)
    (hm : Env.get env (h₃.wk mst) = muStToValS S ms)
    (hx : Env.get env (h₄.wk x) = (k.val, (j.val, (l.val, preKeyMsgToVal msg))))
    (hB : AuthListsBounded K hst) (hM : MuBounded K ms) :
    (hmRecvC S K false jt fhst mst x).eval env =
      hmPreToVal <$> hmPre S jtv (.recvNoOPK k j l msg) hst ms := by
  simp only [hmRecvC, bindV_eval]
  rw [hmR_hmRecvPrepC_eval_noopk S K fhst x env hst k j l msg hs hx hB]
  simp only [hmPre]
  refine hmR_peelL hmPreToVal (Option.map hmRecvDataToVal)
    (hmR_hmRecvNoOPKPrepP_ideal S k j l msg _) rfl (fun d? hd => ?_)
  rcases d? with _ | dv
  · simp only [caseOptV_eval, v, Expr.eval, Ext.refl_wk, Env.get_zero, Option.map_none, Comp.eval,
      map_pure]
    simp only [aNone, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache,
      Expr.eval, Ext.step_wk, Env.get_succ, hs, hm, hmPreToVal, hmResToVal,
      authHybridStateFixedToVal, authHybridStateFixedWithSlotsToVal, authSlotStateToVal]
    rfl
  · obtain ⟨hbase, hideal⟩ := hd dv rfl
    simp only [caseOptV_eval, v, Expr.eval, Ext.refl_wk, Env.get_zero, Option.map_some, bindV_eval]
    refine hmR_mapTail hmPreToVal hmResToVal Sum.inl
      (hmR_hmRecvTailC_eval_v2 S K false jt fhst mst x .zero _ jtv hst ms msg dv _
        (by simpa using hj) (by simpa using hs) (by simpa using hm) (by simp [hx]) rfl ?_
        (by rw [hbase]; exact hB.roCache_le) (by rw [hbase]; exact hB.rootRoCache_le)
        hB.mkSaltCache_le hM (by rw [hbase]; exact hB.principals_le)
        (by rw [hideal]; exact hB.idealSessions_le)) (fun r => rfl)
    · intro _ _ _ _ _ _ kjo usedT' sndHon hstDec res? _ _ _ _ _ env' res hk hu hsh hh hr
      exact hmR_finErasedE_eval_noopk S K kjo usedT' sndHon hstDec res? env' k j l _ _ _ res
        (by rw [hk]; simp [hx]) hu hsh hh hr

end Recv

end SignalPqxdh.Security.ReductionDsl.AuthPrfHmac

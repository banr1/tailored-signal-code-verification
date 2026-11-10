/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthAeadCpa
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfSharedEval
import Computational.Proofs.GameHop.ReductionDsl.PeelSim
import VCVio.EvalDist.Monad.Basic

/-!
# Receive Branch of the `Auth` `AeadIndCpa` Reduction

Proves evaluation equivalence (`cpaRecvC_slot_eval_opk`, `cpaRecvC_slot_eval_noopk`) between
`cpaRecvC` and `stepAuthCpaNonSendPrim`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthAead

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open Computational.Proofs.GameHop.ReductionDsl
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open SignalPqxdh.Security.ReductionDsl.AuthPrf hiding queryPrim_eval
open OracleSpec OracleComp

attribute [local simp] Expr.eval

section Helpers

theorem cpR_any_map3 (xs : List (Nat × Nat × Nat)) (a : Nat × Nat × Nat) :
    (xs.map (fun x => (x.1, x.2.1, x.2.2))).any (fun x => x == a) = xs.contains a := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    rw [List.map_cons, List.any_cons, List.contains_cons, ih]
    congr 1
    exact Bool.eq_iff_iff.mpr (by simp only [beq_iff_eq]; exact eq_comm)

theorem cpR_any_take3 (K : Nat) (xs : List (Nat × Nat × Nat)) (hK : xs.length ≤ K)
    (a : Nat × Nat × Nat) :
    ((xs.map (fun x => (x.1, x.2.1, x.2.2))).take K).any (fun x => x == a) = xs.contains a := by
  rw [List.take_of_length_le (by simpa using hK), cpR_any_map3]

theorem cpR_optCases2 {α β : Type} {P : Prop} (o : Option (α × β)) (h1 : o = none → P)
    (h2 : ∀ a b, o = some (a, b) → P) : P := by
  rcases o with _ | ⟨a, b⟩
  · exact h1 rfl
  · exact h2 _ _ rfl

theorem cpR_optCases {α : Type} {P : Prop} (o : Option α) (h1 : o = none → P)
    (h2 : ∀ a, o = some a → P) : P := by
  cases o
  · exact h1 rfl
  · exact h2 _ rfl

theorem cpR_ret {Γ : List PT} {τ : PT} (e : Expr pqxdhOps Γ τ) (env : Env Γ) :
    (Comp.ret (I := pqPrimIface) e).eval env = pure (e.eval env) := rfl

theorem cpR_iteC {Γ : List PT} {τ : PT} (c : Expr pqxdhOps Γ .bool)
    (t e : Comp pqxdhOps pqPrimIface Γ τ) (env : Env Γ) :
    (Comp.ite c t e).eval env = if c.eval env = true then t.eval env else e.eval env := rfl

theorem cpR_caseOpt_none {Γ : List PT} {τ₁ τ₂ : PT} (o : Expr pqxdhOps Γ (.opt τ₁))
    (kn : Comp pqxdhOps pqPrimIface Γ τ₂)
    (ks : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqPrimIface (τ₁ :: Γ) τ₂) (env : Env Γ)
    (h : o.eval env = none) : (caseOptV o kn ks).eval env = kn.eval env := by
  rw [caseOptV_eval, h]

theorem cpR_caseOpt_some {Γ : List PT} {τ₁ τ₂ : PT} (o : Expr pqxdhOps Γ (.opt τ₁))
    (kn : Comp pqxdhOps pqPrimIface Γ τ₂)
    (ks : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqPrimIface (τ₁ :: Γ) τ₂) (env : Env Γ)
    (a : τ₁.denote) (h : o.eval env = some a) :
    (caseOptV o kn ks).eval env = (ks .zero).eval (.cons a env) := by
  rw [caseOptV_eval, h]

theorem cpR_caseSum_inl {Γ : List PT} {τ₁ τ₂ τ : PT} (s : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (kl : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqPrimIface (τ₁ :: Γ) τ)
    (kr : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps pqPrimIface (τ₂ :: Γ) τ)
    (env : Env Γ) (a : τ₁.denote) (h : s.eval env = .inl a) :
    (caseSumV s kl kr).eval env = (kl .zero).eval (.cons a env) := by
  simp only [caseSumV, Comp.eval, h]

theorem cpR_caseSum_inr {Γ : List PT} {τ₁ τ₂ τ : PT} (s : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (kl : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqPrimIface (τ₁ :: Γ) τ)
    (kr : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps pqPrimIface (τ₂ :: Γ) τ)
    (env : Env Γ) (b : τ₂.denote) (h : s.eval env = .inr b) :
    (caseSumV s kl kr).eval env = (kr .zero).eval (.cons b env) := by
  simp only [caseSumV, Comp.eval, h]

macro "cpR_close" : tactic => `(tactic| first
  | rfl
  | (simp only [Expr.eval, Env.get_zero, Env.get_succ, Prod.map, authHybridStateFixedToVal,
      authHybridStateFixedWithSlotsToVal, authSlotStateToVal,
      authHybridStateToVal, authStateToVal, authRespToVal, authRenc, drKeyToVal, drKeyV,
      Prod.mk.eta, List.map_id', List.map_cons, recvKemRecordToVal]; done))

theorem cpR_pairCases {α β : Type} {P : α × β → Prop} (h : ∀ a b, P (a, b)) (p : α × β) : P p :=
  h p.1 p.2

theorem cpR_iteEq {α : Type} {c c' : Prop} [Decidable c] [Decidable c'] {a b a' b' : α}
    (hc : c ↔ c') (h1 : c' → a = a') (h2 : ¬ c' → b = b') :
    (if c then a else b) = (if c' then a' else b') := by
  by_cases h : c'
  · simp only [hc.mpr h, h, ↓reduceIte]; exact h1 h
  · have h' : ¬ c := fun h' => h (hc.mp h')
    simp only [h, h', ↓reduceIte]; exact h2 h

theorem cpR_opkMap (L : List ((Nat × Nat × Nat) × OpkEntry)) (key : Nat × Nat × Nat) :
    List.map ((fun x => if (x.1 == key) = true then (x.1, x.2.1, x.2.2.1, true) else x) ∘
        Prod.map (fun x : Nat × Nat × Nat => (x.1, x.2.1, x.2.2)) opkEntryToVal) L =
      List.map (Prod.map (fun x : Nat × Nat × Nat => (x.1, x.2.1, x.2.2)) opkEntryToVal ∘ fun x =>
        if (x.1 == key) = true then
          (x.1, { opkSk := x.2.opkSk, opkPk := x.2.opkPk, consumed := true })
        else (x.1, x.2)) L := by
  apply List.map_congr_left
  intro ⟨i, e⟩ _
  by_cases h : i = key <;> simp [h, Prod.map, opkEntryToVal]

theorem cpR_mkFind {S : Setup} (K : Nat) (cache : AuthMkSaltCache S) (hK : cache.length ≤ K)
    (sid : SessionId S) (salt : Option Bytes)
    (p : ((sessionIdTy.denote × Option Bytes) × Nat × msgKeysTy.denote) → Bool)
    (hp : ∀ (s' : SessionId S) (o : Option Bytes) (rc : Nat) (mk : MessageKeys),
      p ((sessionIdToVal s', o), (rc, msgKeysToVal mk)) = mkSaltKeyMatch (s', o) sid salt) :
    ((cache.map (fun x =>
      ((sessionIdToVal x.1.1, x.1.2), x.2.1, msgKeysToVal x.2.2))).take K).find? p =
      (cache.find? (fun x => mkSaltKeyMatch x.1 sid salt)).map
        (fun x => ((sessionIdToVal x.1.1, x.1.2), x.2.1, msgKeysToVal x.2.2)) := by
  rw [List.take_of_length_le (by simpa using hK), List.find?_map]
  congr 2
  funext ⟨⟨s', o⟩, rc, mk⟩
  simp only [Function.comp_apply, hp]

theorem cpR_iteMapBind {m : Type → Type} [Monad m] {α β γ : Type}
    (F : β → γ) (c : Prop) [Decidable c] (a b : m α) (f : α → m β) :
    F <$> ((if c then a else b) >>= f) = if c then F <$> (a >>= f) else F <$> (b >>= f) := by
  split <;> rfl

theorem cpR_eIte {Γ : List PT} {τ : PT} (c : Expr pqxdhOps Γ .bool) (t e : Expr pqxdhOps Γ τ)
    (env : Env Γ) :
    (Expr.ite c t e).eval env = cond (c.eval env) (t.eval env) (e.eval env) := by
  show (if c.eval env = true then t.eval env else e.eval env) = _
  cases c.eval env <;> rfl

theorem cpR_bindPure {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type} (x : m α) (a : α)
    (g : α → m β) (h : x = pure a) : x >>= g = g a := by
  rw [h, pure_bind]

end Helpers

section Recv

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List PT}

private theorem cpR_take_min_of_le {α : Type*} (n m : Nat) (xs : List α) (h : xs.length ≤ n) :
    xs.take (min n m) = xs.take m := by
  by_cases hnm : n ≤ m
  · rw [Nat.min_eq_left hnm, List.take_of_length_le h, List.take_of_length_le (Nat.le_trans h hnm)]
  · rw [Nat.min_eq_right (by omega)]

set_option maxHeartbeats 1000000 in
theorem cpaRecvC_slot_eval_opk (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ recvQTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (env : Env Δ) (hst : AuthHybridStateFixed S)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (hs : Env.get env (h₁.wk fhst) = authHybridStateFixedToVal hst)
    (hx : Env.get env (h₂.wk x) = (k.val, (j.val, (o.val, preKeyMsgToVal msg))))
    (hB : AuthListsBounded K hst)
    (hIdeal : hst.toAuthHybridState.idealSessions.length ≤ K) :
    (cpaRecvC S K true fhst x).eval env =
      Prod.map authRespToVal authHybridStateFixedToVal <$>
        stepAuthCpaNonSendPrim S (.recvOPK k j o msg) hst := by
  have hx' : @Env.get pqSig Δ (.prod .nat (.prod .nat (.prod .nat preKeyMsgTy))) env
      (@Ext.wk Γ₂ Δ h₂ (.prod .nat (.prod .nat (.prod .nat preKeyMsgTy))) x) =
      (k.val, (j.val, (o.val, preKeyMsgToVal msg))) := hx
  have hTakeP : (hst.base.principals.map (Prod.map id principalEntryToVal)).take K =
      hst.base.principals.map (Prod.map id principalEntryToVal) := by
    apply List.take_of_length_le; simpa using hB.principals_le
  have hTakeS : (hst.base.spkBundles.map (Prod.map id spkBundleEntryToVal)).take K =
      hst.base.spkBundles.map (Prod.map id spkBundleEntryToVal) := by
    apply List.take_of_length_le; simpa using hB.spkBundles_le
  have hTakeO : (hst.base.opkEntries.map
      (Prod.map (fun x => (x.1, x.2.1, x.2.2)) opkEntryToVal)).take K =
      hst.base.opkEntries.map (Prod.map (fun x => (x.1, x.2.1, x.2.2)) opkEntryToVal) := by
    apply List.take_of_length_le; simpa using hB.opkEntries_le
  unfold cpaRecvC stepAuthCpaNonSendPrim
  simp only [letV_eval, cpR_iteC, cpR_ret, bindV_eval, v, ahsfHybrid, ahsBase, ahsfRecvCount,
    ahsfUpd, ahsfMkSlots, ahsfSlots, ahsfMkSaltCache, aNone, pkmHdr, hdrSpkId, hdrPqspkId, hdrOpkId?, hdrIkAPk,
    hdrEkAPk, pkmEphAPk, optU32Eq_eval, natEq_eval, u32Beq_eval, u32OfNat_eval, bytesLen_eval,
    ↓reduceIte, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, hs, hx,
    authHybridStateFixedToVal, authHybridStateFixedWithSlotsToVal, authSlotStateToVal, preKeyMsgToVal, preKeyMsgV, hdrV]
  refine PeelSim.peel_ite _ Iff.rfl (fun _ => PeelSim.peel_pure _ rfl) (fun _ => ?_)
  refine PeelSim.peel_ite _ ?_ (fun _ => PeelSim.peel_pure _ rfl) (fun _ => ?_)
  · simp only [eAny, asUsedRecvOPK, nat3Eq_eval, Expr.eval, Env.get_zero, Env.get_succ,
      authHybridStateToVal, authStateToVal]
    rw [cpR_any_take3 K _ hB.usedRecvOPK_le]
  rw [koskSenderOkC_eval S K _ _ _ hst.base rfl hB.advKeys_le hB.principals_le]
  refine PeelSim.peel_bind_same _ (by simp only [Expr.eval, Env.get_zero, Env.get_succ]) (fun ok => ?_)
  refine PeelSim.peel_ite _ Iff.rfl (fun _ => PeelSim.peel_pure _ rfl) (fun hok => ?_)
  refine cpR_optCases2 (List.find? (fun x => x.1 == k.val) hst.base.principals)
    (fun hp => ?_) (fun kIdx kEntry hp => ?_)
  · rw [cpR_caseOpt_none _ _ _ _ (by
      simp only [eFind, asPrincipals, natEq_eval, Expr.eval, Env.get_zero, Env.get_succ,
        hx, authHybridStateToVal, authStateToVal, hTakeP, List.find?_map, Function.comp_def,
        Prod.map, id_eq, hp, Option.map_none])]
    simp only [hp]
    exact PeelSim.peel_pure _ rfl
  rw [cpR_caseOpt_some _ _ _ _ (kIdx, principalEntryToVal kEntry) (by
      simp only [eFind, asPrincipals, natEq_eval, Expr.eval, Env.get_zero, Env.get_succ,
        hx, authHybridStateToVal, authStateToVal, hTakeP, List.find?_map, Function.comp_def,
        Prod.map, id_eq, hp, Option.map_some])]
  simp only [hp]
  refine cpR_optCases2 (List.find? (fun x => x.1 == (k.val, j.val)) hst.base.spkBundles)
    (fun hb => ?_) (fun bIdx bEntry hb => ?_)
  · rw [cpR_caseOpt_none _ _ _ _ (by
      simp only [eFind, asSpkBundles, nat2Eq_eval, Expr.eval, Env.get_zero, Env.get_succ,
        hx, authHybridStateToVal, authStateToVal, hTakeS, List.find?_map, Function.comp_def,
        Prod.map, id_eq, hb, Option.map_none])]
    simp only [hb]
    exact PeelSim.peel_pure _ rfl
  rw [cpR_caseOpt_some _ _ _ _ (bIdx, spkBundleEntryToVal bEntry) (by
      simp only [eFind, asSpkBundles, nat2Eq_eval, Expr.eval, Env.get_zero, Env.get_succ,
        hx, authHybridStateToVal, authStateToVal, hTakeS, List.find?_map, Function.comp_def,
        Prod.map, id_eq, hb, Option.map_some])]
  simp only [hb, letV_eval, bindV_eval]
  refine cpR_optCases2 (List.find? (fun x => x.1 == (k.val, j.val, o.val)) hst.base.opkEntries)
    (fun ho => ?_) (fun oIdx oEntry ho => ?_)
  · rw [cpR_caseOpt_none _ _ _ _ (by
      simp only [eFind, asOpkEntries, nat3Eq_eval, Expr.eval, Env.get_zero, Env.get_succ,
        authHybridStateToVal, authStateToVal, hTakeO, List.find?_map, Function.comp_def,
        Prod.map, ho, Option.map_none])]
    simp only [ho, cpR_ret, pure_bind]
    rw [cpR_caseSum_inl _ _ _ _ () rfl]
    exact PeelSim.peel_pure _ rfl
  rw [cpR_caseOpt_some _ _ _ _ ((oIdx.1, oIdx.2.1, oIdx.2.2), opkEntryToVal oEntry) (by
      simp only [eFind, asOpkEntries, nat3Eq_eval, Expr.eval, Env.get_zero, Env.get_succ,
        authHybridStateToVal, authStateToVal, hTakeO, List.find?_map, Function.comp_def,
        Prod.map, ho, Option.map_some])]
  simp only [ho, cpR_iteC, Expr.eval, Env.get_zero, Env.get_succ, oeConsumed, opkEntryToVal]
  by_cases hc : oEntry.consumed = true
  · simp only [hc, ↓reduceIte, cpR_ret, pure_bind]
    rw [cpR_caseSum_inl _ _ _ _ () rfl]
    exact PeelSim.peel_pure _ rfl
  simp only [hc, Bool.false_eq_true, ↓reduceIte, cpR_ret, pure_bind]
  rw [cpR_caseSum_inr _ _ _ _ (some (oEntry.opkSk, oEntry.opkPk, false)) rfl]
  simp only [letV_eval]
  rw [kyberCheckE_eval K _ _ _ (by
    simp [asUsedKyberTriples, Expr.eval, authHybridStateToVal, authStateToVal,
      hB.usedKyberTriples_le])]
  simp only [bindV_eval, asUsedKyberTriples, Expr.eval, Env.get_zero, Env.get_succ, hx,
    authHybridStateToVal, authStateToVal, Prod.mk.eta, List.map_id']
  refine PeelSim.peel_bind_same _ (by rfl) (fun can => ?_)
  refine PeelSim.peel_bind_same _ (by rfl) (fun canE => ?_)
  rw [cpR_iteC]
  refine PeelSim.peel_ite _ (by simp only [boolOr_eval, Expr.eval, Env.get_zero, Env.get_succ])
    (fun _ => PeelSim.peel_pure _ (by cpR_close)) (fun hcan => ?_)
  rw [bindV_eval]
  refine PeelSim.peel_bind_same _ (by rfl) (fun ss? => ?_)
  refine cpR_optCases ss? (fun hn => ?_) (fun ss hss => ?_)
  · subst hn
    rw [cpR_caseOpt_none _ _ _ _ rfl]
    exact PeelSim.peel_pure _ (by cpR_close)
  subst hss
  rw [cpR_caseOpt_some _ _ _ _ ss rfl]
  simp only [letV_eval, bindV_eval]
  refine PeelSim.peel_bind_same _ (by rfl) (fun dh1 => ?_)
  refine PeelSim.peel_bind_same _ (by rfl) (fun dh2 => ?_)
  refine PeelSim.peel_bind_same _ (by rfl) (fun dh3 => ?_)
  refine PeelSim.peel_bind _ some (by
    rw [cpR_caseOpt_some _ _ _ _ _ rfl]
    simp only [bindV_eval, cpR_ret, Expr.eval, Env.get_zero, bind_pure_comp]
    rfl) (fun dh4 => ?_)
  simp only [Expr.eval, Env.get_zero, Env.get_succ, hs,
    hx', authHybridStateFixedToVal, authHybridStateFixedWithSlotsToVal, authSlotStateToVal, buildSecretsE_eval, eCaseOpt, oeOpkPk,
    ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions, ahsUpd,
    sbPqspkPk, sbPqspkSk, sbSpkSk, sbSpkPk, hdrKemCt, peIkAPk,
    spkBundleEntryToVal, principalEntryToVal, preKeyMsgToVal, preKeyMsgV, hdrV]
  unfold evalAuthRecvScheduleCpaFixedPrim
  simp only [bind_assoc]
  refine PeelSim.peel_bind _ (Option.map (Prod.map id principalEntryToVal))
    (findHonestC_eval S _ _ _ hst.base (by
      simp only [Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, authStateToVal,
        Prod.mk.eta, List.map_id']) hB.principals_le) (fun sP => ?_)
  simp only [Expr.eval, Env.get_zero, peCorrupted]
  refine PeelSim.peel_bind _ (Option.map idealAuthSessionToVal) ?_ (fun mt => ?_)
  · simp only [findMV, Comp.eval, Expr.eval, Env.get_succ, Env.get_zero, findML_eq_findMPrim,
      ← List.map_take, cpR_take_min_of_le K S.N_sess_tot _ hIdeal]
    rw [findMPrim_map_congr idealAuthSessionToVal _
      (matchIdealAuthHandshakePrim kEntry.ikAPk bEntry.spkPk (some oEntry.opkPk) bEntry.pqspkPk
        msg.hdr)]
    intro s
    exact matchIdealAuthHandshakeC_eval S _ _ _ _ _ .zero _ kEntry.ikAPk bEntry.spkPk
      (some oEntry.opkPk) bEntry.pqspkPk msg.hdr s rfl rfl rfl rfl rfl rfl
  refine cpR_optCases mt (fun hn => ?_) (fun sM hsM => ?_)
  · subst hn
    simp only [Option.map_none]
    rw [cpR_caseOpt_none _ _ _ _ rfl, cpR_iteC]
    refine PeelSim.peel_bind _ (Prod.map drKeyToVal (List.map (Prod.map id drKeyToVal))) ?_ (fun dro => ?_)
    · refine PeelSim.peel_ite _ ?_ (fun hu => ?_) (fun hu => ?_)
      · rcases sP with _ | ⟨_, e⟩ <;> simp
      · simp only [bindV_eval, samplePrim_drKey96_eval, cpR_ret, Expr.eval, Env.get_zero, map_bind,
          bind_map_left, map_pure]
        rfl
      · rw [hkdfRoC_eval S K _ _ _ hst.base (by
          simp only [Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, authStateToVal,
            Prod.mk.eta, List.map_id']) hB.roCache_le]
        rfl
    revert dro
    refine cpR_pairCases (fun dk roC => ?_)
    simp only [Prod.map]
    refine PeelSim.peel_bind_same _ (by rfl) (fun dhR => ?_)
    refine PeelSim.peel_bind_same _ (by rw [cpR_caseOpt_none _ _ _ _ rfl]; rfl) (fun se => ?_)
    refine PeelSim.peel_bind_same _ (by
      rw [cpR_caseOpt_none _ _ _ _ rfl, cpR_iteC]
      refine cpR_iteEq (by rcases sP with _ | ⟨_, e⟩ <;> simp) (fun _ => rfl) (fun _ => ?_)
      rw [rootRoC_eval S K _ _ _ _ hst.base (by
          simp only [Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, authStateToVal,
            Prod.mk.eta, List.map_id']) hB.rootRoCache_le]
      rfl) (fun rko => ?_)
    refine PeelSim.peel_bind_same _ (by
      rw [cpR_caseOpt_none _ _ _ _ rfl, cpR_iteC]
      exact cpR_iteEq (by rcases sP with _ | ⟨_, e⟩ <;> simp) (fun _ => rfl) (fun _ => rfl))
      (fun mkc => ?_)
    refine PeelSim.peel_bind_same _ (by rfl) (fun sp? => ?_)
    refine cpR_optCases2 sp? (fun hn => ?_) (fun pqr salt hsp => ?_)
    · subst hn
      rw [cpR_caseOpt_none _ _ _ _ rfl]
      simp only [pure_bind]
      exact PeelSim.peel_pure _ (by cpR_close)
    subst hsp
    rw [cpR_caseOpt_some _ _ _ _ _ rfl]
    simp only [bind_assoc, letV_eval, bindV_eval, Expr.eval, Env.get_zero, Env.get_succ]
    refine PeelSim.peel_bind _ (Prod.map msgKeysToVal
        (List.map (fun x => ((sessionIdToVal x.1.1, x.1.2), x.2.1, msgKeysToVal x.2.2))))
        ?_ (fun mko => ?_)
    · rw [cpR_caseOpt_none _ _ _ _ rfl, cpR_iteC]
      refine PeelSim.peel_ite _ (by rcases sP with _ | ⟨_, e⟩ <;> simp) (fun _ => ?_) (fun _ => ?_)
      · simp only [bindV_eval, samplePrim_msgKeys80_eval, cpR_ret, Expr.eval, Env.get_zero, Env.get_succ,
          map_bind, bind_map_left, map_pure]
        rfl
      · simp only [bindV_eval, queryPrim_eval, queryPrim_deriveMsgKeys_eval, cpR_ret, Expr.eval,
          Env.get_zero, Env.get_succ, map_bind, bind_map_left, map_pure]
        rfl
    revert mko
    refine cpR_pairCases (fun mk c' => ?_)
    simp only [Prod.map, Bool.false_eq_true, ↓reduceIte]
    rw [cpR_iteC, ite_eq_right (by simp only [Expr.eval, Env.get_zero, Env.get_succ,
      Bool.false_eq_true, not_false_eq_true]), cpR_iteC, PeelSim.ite_bind, PeelSim.ite_bind]
    refine PeelSim.peel_ite _ (by rcases sP with _ | ⟨_, e⟩ <;> simp) (fun _ => ?_) (fun _ => ?_)
    · simp only [cpR_ret, pure_bind, Expr.eval]
      rw [cpR_caseOpt_none _ _ _ _ rfl]
      exact PeelSim.peel_pure _ (by cpR_close)
    simp only [bind_assoc]
    refine PeelSim.peel_bind_same _ ?_ (fun pt? => ?_)
    · simp only [queryPrim_eval, Expr.eval, Env.get_zero, Env.get_succ, firstMsgADE_eval, PTag.evalPrim]
      rfl
    refine cpR_optCases pt? (fun hn => ?_) (fun pt hpt => ?_)
    · subst hn
      rw [cpR_caseOpt_none _ _ _ _ rfl]
      simp only [pure_bind]
      exact PeelSim.peel_pure _ (by cpR_close)
    subst hpt
    rw [cpR_caseOpt_some _ _ _ _ pt rfl]
    simp only [pure_bind, bindV_eval]
    refine PeelSim.peel_bind _ (Option.map (Prod.map id principalEntryToVal))
      (findHonestC_eval S _ _ _ hst.base (by
        simp only [Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, authStateToVal,
          Prod.mk.eta, List.map_id']) hB.principals_le) (fun sP2 => ?_)
    simp only [letV_eval, cpR_ret]
    refine PeelSim.peel_pure _ ?_
    rcases sP2 with _ | ⟨i2, e2⟩ <;>
    simp only [Expr.eval, Env.get_zero, Env.get_succ, Option.map, Prod.map,
      authHybridStateFixedToVal, authHybridStateFixedWithSlotsToVal, authSlotStateToVal,
      authHybridStateToVal, authStateToVal, authRespToVal, authRenc,
      drKeyToVal, drKeyV, Prod.mk.eta, List.map_id', List.map_cons, recvKemRecordToVal, hTakeO,
      aRecvUnfresh, aRecvHonest, List.map_map, nat3Eq_eval, Prod.mk.injEq, true_and, and_true, eMap,
      asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
      asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asSentOPKEvents, asSentNoOPKEvents,
      asRecvdOPKEvents, asRecvdNoOPKEvents, asAdvKeys, oeOpkSk, oeOpkPk] <;> exact cpR_opkMap _ _
  · subst hsM
    simp only [Option.map_some]
    rw [cpR_caseOpt_some _ _ _ _ _ rfl]
    simp only [cpR_ret, pure_bind, Expr.eval]
    refine PeelSim.peel_bind_same _ (by rfl) (fun dhR => ?_)
    refine PeelSim.peel_bind_same _ (by
      rw [cpR_caseOpt_some _ _ _ _ _ rfl]
      simp only [bindV_eval, queryPrim_eval, cpR_ret]
      rfl) (fun se => ?_)
    refine PeelSim.peel_bind_same _ (by
      rw [cpR_caseOpt_some _ _ _ _ _ rfl, cpR_iteC]
      exact cpR_iteEq Iff.rfl (fun _ => rfl) (fun _ => rfl)) (fun rko => ?_)
    refine PeelSim.peel_bind_same _ (by
      rw [cpR_caseOpt_some _ _ _ _ _ rfl, cpR_iteC]
      exact cpR_iteEq Iff.rfl (fun _ => rfl) (fun _ => rfl)) (fun mkc => ?_)
    refine PeelSim.peel_bind_same _ (by rfl) (fun sp? => ?_)
    refine cpR_optCases2 sp? (fun hn => ?_) (fun pqr salt hsp => ?_)
    · subst hn
      rw [cpR_caseOpt_none _ _ _ _ rfl]
      simp only [pure_bind]
      exact PeelSim.peel_pure _ (by cpR_close)
    subst hsp
    rw [cpR_caseOpt_some _ _ _ _ _ rfl]
    simp only [bind_assoc, letV_eval, bindV_eval, Expr.eval, Env.get_zero, Env.get_succ]
    refine PeelSim.peel_bind _ (Prod.map msgKeysToVal
        (List.map (fun x => ((sessionIdToVal x.1.1, x.1.2), x.2.1, msgKeysToVal x.2.2))))
        ?_ (fun mko => ?_)
    · rw [cpR_caseOpt_some _ _ _ _ _ rfl, cpR_iteC]
      refine PeelSim.peel_ite _ ?_ (fun _ => by simp only [cpR_ret]; exact PeelSim.peel_pure _ rfl) (fun _ => ?_)
      · simp only [Expr.eval, Env.get_zero, Env.get_succ, sameSaltKeyE_eval, iasSpqrSalt?,
          idealAuthSessionToVal]
      rw [cpR_iteC]
      refine PeelSim.peel_ite _ Iff.rfl (fun _ => ?_) (fun _ => ?_)
      · simp only [letV_eval]
        rw [caseOptV_eval]
        simp only [eFind, Expr.eval, Env.get_zero, Env.get_succ, iasSid, idealAuthSessionToVal]
        rw [cpR_mkFind K hst.mkSaltCache hB.mkSaltCache_le sM.sid salt _ (fun s' o rc mk => by
          simp only [Expr.eval, Env.get_succ, Env.get_zero, sameSaltKeyE_eval, mkSaltKeyMatch]
          rw [sidEq_eval _ _ _ s' sM.sid rfl rfl])]
        split
        · rename_i hn
          simp only [Option.map_eq_none_iff] at hn
          simp only [hn, bindV_eval, samplePrim_msgKeys80_eval, cpR_ret, Expr.eval, Env.get_zero, Env.get_succ,
            map_bind, bind_map_left, map_pure]
          rfl
        · rename_i v hv
          simp only [Option.map_eq_some_iff] at hv
          obtain ⟨⟨⟨sid', o'⟩, rc', mk'⟩, hw, rfl⟩ := hv
          simp only [hw, cpR_ret, Expr.eval, Env.get_zero, Env.get_succ, map_pure]
          rfl
      · simp only [bindV_eval, samplePrim_msgKeys80_eval, cpR_ret, Expr.eval, Env.get_zero, Env.get_succ,
          map_bind, bind_map_left, map_pure]
        rfl
    revert mko
    refine cpR_pairCases (fun mk c' => ?_)
    simp only [Prod.map]
    rw [cpR_iteC, PeelSim.ite_bind, cpR_iteMapBind]
    refine cpR_iteEq ?_ (fun hsm => ?_) (fun hsm => ?_)
    · simp only [Expr.eval, Env.get_zero, Env.get_succ, sameSaltKeyE_eval, iasSpqrSalt?,
        idealAuthSessionToVal]
    · simp only [cpR_ret, pure_bind, ↓cpR_eIte, Expr.eval, Env.get_zero, Env.get_succ]
      rw [cpR_iteMapBind]
      simp only [Expr.eval, bytesBeq_eval, Env.get_zero, Env.get_succ, firstMsgADE_eval, iasAdE,
        iasAeadCtE, idealAuthSessionToVal, pkmPqRatchetMsg, pkmAeadCt]
      cases h2 : (firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg == sM.ad &&
            msg.aeadCt == sM.aeadCt)
      · simp only [Bool.cond_false, Bool.false_eq_true, ↓reduceIte, pure_bind]
        rw [cpR_caseOpt_none _ _ _ _ rfl]
        exact PeelSim.peel_pure _ (by cpR_close)
      · simp only [Bool.cond_true, ↓reduceIte, pure_bind]
        rw [cpR_caseOpt_some _ _ _ _ _ rfl]
        simp only [bindV_eval]
        refine PeelSim.peel_bind _ (Option.map (Prod.map id principalEntryToVal))
          (findHonestC_eval S _ _ _ hst.base (by
            simp only [Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, authStateToVal,
              Prod.mk.eta, List.map_id']) hB.principals_le) (fun sP2 => ?_)
        simp only [letV_eval, cpR_ret]
        refine PeelSim.peel_pure _ ?_
        rcases sP2 with _ | ⟨i2, e2⟩ <;>
        simp only [Expr.eval, Env.get_zero, Env.get_succ, Option.map, Prod.map,
          authHybridStateFixedToVal, authHybridStateFixedWithSlotsToVal, authSlotStateToVal, authHybridStateToVal, authStateToVal, authRespToVal, authRenc,
          drKeyToVal, drKeyV, Prod.mk.eta, List.map_id', List.map_cons, recvKemRecordToVal, hTakeO,
          aRecvUnfresh, aRecvHonest, List.map_map, nat3Eq_eval, Prod.mk.injEq, true_and, and_true,
          eMap, asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
          asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asSentOPKEvents, asSentNoOPKEvents,
          asRecvdOPKEvents, asRecvdNoOPKEvents, asRoCache, asAdvKeys, oeOpkSk, oeOpkPk,
          iasDrKey, iasMsgPlainE] <;>
        exact cpR_opkMap _ _
    · rw [cpR_iteC, PeelSim.ite_bind, cpR_iteMapBind]
      refine cpR_iteEq (by rcases sP with _ | ⟨_, e⟩ <;> simp) (fun _ => ?_) (fun _ => ?_)
      · simp only [cpR_ret, pure_bind, Expr.eval]
        rw [cpR_caseOpt_none _ _ _ _ rfl]
        exact PeelSim.peel_pure _ (by cpR_close)
      simp only [bind_assoc]
      refine PeelSim.peel_bind_same _ ?_ (fun pt? => ?_)
      · simp only [queryPrim_eval, Expr.eval, Env.get_zero, Env.get_succ, firstMsgADE_eval, PTag.evalPrim]
        rfl
      refine cpR_optCases pt? (fun hn => ?_) (fun pt hpt => ?_)
      · subst hn
        rw [cpR_caseOpt_none _ _ _ _ rfl]
        simp only [pure_bind]
        exact PeelSim.peel_pure _ (by cpR_close)
      subst hpt
      rw [cpR_caseOpt_some _ _ _ _ pt rfl]
      simp only [pure_bind, bindV_eval]
      refine PeelSim.peel_bind _ (Option.map (Prod.map id principalEntryToVal))
        (findHonestC_eval S _ _ _ hst.base (by
          simp only [Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, authStateToVal,
            Prod.mk.eta, List.map_id']) hB.principals_le) (fun sP2 => ?_)
      simp only [letV_eval, cpR_ret]
      refine PeelSim.peel_pure _ ?_
      rcases sP2 with _ | ⟨i2, e2⟩ <;>
      simp only [Expr.eval, Env.get_zero, Env.get_succ, Option.map, Prod.map,
        authHybridStateFixedToVal, authHybridStateFixedWithSlotsToVal, authSlotStateToVal, authHybridStateToVal, authStateToVal, authRespToVal, authRenc,
        drKeyToVal, drKeyV, Prod.mk.eta, List.map_id', List.map_cons, recvKemRecordToVal, hTakeO,
        aRecvUnfresh, aRecvHonest, List.map_map, nat3Eq_eval, Prod.mk.injEq, true_and, and_true,
        eMap, asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
        asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asSentOPKEvents, asSentNoOPKEvents,
        asRecvdOPKEvents, asRecvdNoOPKEvents, asRoCache, asAdvKeys, oeOpkSk, oeOpkPk,
        idealAuthSessionToVal, iasDrKey] <;>
      exact cpR_opkMap _ _

theorem cpaRecvC_eval_opk (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ recvQTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (env : Env Δ) (hst : AuthHybridStateFixed S)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (hs : Env.get env (h₁.wk fhst) = authHybridStateFixedToVal hst)
    (hx : Env.get env (h₂.wk x) = (k.val, (j.val, (o.val, preKeyMsgToVal msg))))
    (hB : AuthListsBounded K hst)
    (hIdeal : hst.toAuthHybridState.idealSessions.length ≤ K) :
    (cpaRecvC S K true fhst x).eval env =
      Prod.map authRespToVal authHybridStateFixedToVal <$>
        stepAuthCpaNonSendPrim S (.recvOPK k j o msg) hst :=
  cpaRecvC_slot_eval_opk S K fhst x env hst k j o msg hs hx hB hIdeal

set_option maxHeartbeats 1000000 in
theorem cpaRecvC_slot_eval_noopk (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ recvQTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (env : Env Δ) (hst : AuthHybridStateFixed S)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (hs : Env.get env (h₁.wk fhst) = authHybridStateFixedToVal hst)
    (hx : Env.get env (h₂.wk x) = (k.val, (j.val, (l.val, preKeyMsgToVal msg))))
    (hB : AuthListsBounded K hst)
    (hIdeal : hst.toAuthHybridState.idealSessions.length ≤ K) :
    (cpaRecvC S K false fhst x).eval env =
      Prod.map authRespToVal authHybridStateFixedToVal <$>
        stepAuthCpaNonSendPrim S (.recvNoOPK k j l msg) hst := by
  have hx' : @Env.get pqSig Δ (.prod .nat (.prod .nat (.prod .nat preKeyMsgTy))) env
      (@Ext.wk Γ₂ Δ h₂ (.prod .nat (.prod .nat (.prod .nat preKeyMsgTy))) x) =
      (k.val, (j.val, (l.val, preKeyMsgToVal msg))) := hx
  have hTakeP : (hst.base.principals.map (Prod.map id principalEntryToVal)).take K =
      hst.base.principals.map (Prod.map id principalEntryToVal) := by
    apply List.take_of_length_le; simpa using hB.principals_le
  have hTakeS : (hst.base.spkBundles.map (Prod.map id spkBundleEntryToVal)).take K =
      hst.base.spkBundles.map (Prod.map id spkBundleEntryToVal) := by
    apply List.take_of_length_le; simpa using hB.spkBundles_le
  have hTakeO : (hst.base.opkEntries.map
      (Prod.map (fun x => (x.1, x.2.1, x.2.2)) opkEntryToVal)).take K =
      hst.base.opkEntries.map (Prod.map (fun x => (x.1, x.2.1, x.2.2)) opkEntryToVal) := by
    apply List.take_of_length_le; simpa using hB.opkEntries_le
  unfold cpaRecvC stepAuthCpaNonSendPrim
  simp only [letV_eval, cpR_iteC, cpR_ret, bindV_eval, v, ahsfHybrid, ahsBase, ahsfRecvCount,
    ahsfUpd, ahsfMkSlots, ahsfSlots, ahsfMkSaltCache, aNone, pkmHdr, hdrSpkId, hdrPqspkId, hdrOpkId?, hdrIkAPk,
    hdrEkAPk, pkmEphAPk, optU32Eq_eval, natEq_eval, u32Beq_eval, u32OfNat_eval, bytesLen_eval,
    ↓reduceIte, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, hs, hx,
    authHybridStateFixedToVal, authHybridStateFixedWithSlotsToVal, authSlotStateToVal, preKeyMsgToVal, preKeyMsgV, hdrV, Bool.false_eq_true]
  refine PeelSim.peel_ite _ Iff.rfl (fun _ => PeelSim.peel_pure _ rfl) (fun _ => ?_)
  refine PeelSim.peel_ite _ ?_ (fun _ => PeelSim.peel_pure _ rfl) (fun _ => ?_)
  · simp only [eAny, asUsedRecvNoOPK, nat3Eq_eval, Expr.eval, Env.get_zero, Env.get_succ,
      authHybridStateToVal, authStateToVal]
    rw [cpR_any_take3 K _ hB.usedRecvNoOPK_le]
  rw [koskSenderOkC_eval S K _ _ _ hst.base rfl hB.advKeys_le hB.principals_le]
  refine PeelSim.peel_bind_same _ (by simp only [Expr.eval, Env.get_zero, Env.get_succ]) (fun ok => ?_)
  refine PeelSim.peel_ite _ Iff.rfl (fun _ => PeelSim.peel_pure _ rfl) (fun hok => ?_)
  refine cpR_optCases2 (List.find? (fun x => x.1 == k.val) hst.base.principals)
    (fun hp => ?_) (fun kIdx kEntry hp => ?_)
  · rw [cpR_caseOpt_none _ _ _ _ (by
      simp only [eFind, asPrincipals, natEq_eval, Expr.eval, Env.get_zero, Env.get_succ,
        hx, authHybridStateToVal, authStateToVal, hTakeP, List.find?_map, Function.comp_def,
        Prod.map, id_eq, hp, Option.map_none])]
    simp only [hp]
    exact PeelSim.peel_pure _ rfl
  rw [cpR_caseOpt_some _ _ _ _ (kIdx, principalEntryToVal kEntry) (by
      simp only [eFind, asPrincipals, natEq_eval, Expr.eval, Env.get_zero, Env.get_succ,
        hx, authHybridStateToVal, authStateToVal, hTakeP, List.find?_map, Function.comp_def,
        Prod.map, id_eq, hp, Option.map_some])]
  simp only [hp]
  refine cpR_optCases2 (List.find? (fun x => x.1 == (k.val, j.val)) hst.base.spkBundles)
    (fun hb => ?_) (fun bIdx bEntry hb => ?_)
  · rw [cpR_caseOpt_none _ _ _ _ (by
      simp only [eFind, asSpkBundles, nat2Eq_eval, Expr.eval, Env.get_zero, Env.get_succ,
        hx, authHybridStateToVal, authStateToVal, hTakeS, List.find?_map, Function.comp_def,
        Prod.map, id_eq, hb, Option.map_none])]
    simp only [hb]
    exact PeelSim.peel_pure _ rfl
  rw [cpR_caseOpt_some _ _ _ _ (bIdx, spkBundleEntryToVal bEntry) (by
      simp only [eFind, asSpkBundles, nat2Eq_eval, Expr.eval, Env.get_zero, Env.get_succ,
        hx, authHybridStateToVal, authStateToVal, hTakeS, List.find?_map, Function.comp_def,
        Prod.map, id_eq, hb, Option.map_some])]
  simp only [hb, letV_eval, bindV_eval]
  simp only [cpR_ret, pure_bind, Expr.eval, Env.get_zero, Env.get_succ]
  rw [cpR_caseSum_inr _ _ _ _ none rfl]
  simp only [letV_eval]
  rw [kyberCheckE_eval K _ _ _ (by
    simp [asUsedKyberTriples, Expr.eval, authHybridStateToVal, authStateToVal,
      hB.usedKyberTriples_le])]
  simp only [bindV_eval, asUsedKyberTriples, Expr.eval, Env.get_zero, Env.get_succ, hx,
    authHybridStateToVal, authStateToVal, Prod.mk.eta, List.map_id']
  refine PeelSim.peel_bind_same _ (by rfl) (fun can => ?_)
  refine PeelSim.peel_bind_same _ (by rfl) (fun canE => ?_)
  rw [cpR_iteC]
  refine PeelSim.peel_ite _ (by simp only [boolOr_eval, Expr.eval, Env.get_zero, Env.get_succ])
    (fun _ => PeelSim.peel_pure _ (by cpR_close)) (fun hcan => ?_)
  rw [bindV_eval]
  refine PeelSim.peel_bind_same _ (by rfl) (fun ss? => ?_)
  refine cpR_optCases ss? (fun hn => ?_) (fun ss hss => ?_)
  · subst hn
    rw [cpR_caseOpt_none _ _ _ _ rfl]
    exact PeelSim.peel_pure _ (by cpR_close)
  subst hss
  rw [cpR_caseOpt_some _ _ _ _ ss rfl]
  simp only [letV_eval, bindV_eval]
  refine PeelSim.peel_bind_same _ (by rfl) (fun dh1 => ?_)
  refine PeelSim.peel_bind_same _ (by rfl) (fun dh2 => ?_)
  refine PeelSim.peel_bind_same _ (by rfl) (fun dh3 => ?_)
  refine (cpR_bindPure _ none _ (by rw [cpR_caseOpt_none _ _ _ _ rfl]; rfl)).trans ?_
  simp only [Expr.eval, Env.get_zero, Env.get_succ, hs,
    hx', authHybridStateFixedToVal, authHybridStateFixedWithSlotsToVal, authSlotStateToVal, buildSecretsE_eval, eCaseOpt,
    ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions, ahsUpd,
    sbPqspkPk, sbPqspkSk, sbSpkSk, sbSpkPk, hdrKemCt, peIkAPk,
    spkBundleEntryToVal, principalEntryToVal, preKeyMsgToVal, preKeyMsgV, hdrV]
  unfold evalAuthRecvScheduleCpaFixedPrim
  simp only [bind_assoc]
  refine PeelSim.peel_bind _ (Option.map (Prod.map id principalEntryToVal))
    (findHonestC_eval S _ _ _ hst.base (by
      simp only [Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, authStateToVal,
        Prod.mk.eta, List.map_id']) hB.principals_le) (fun sP => ?_)
  simp only [Expr.eval, Env.get_zero, peCorrupted]
  refine PeelSim.peel_bind _ (Option.map idealAuthSessionToVal) ?_ (fun mt => ?_)
  · simp only [findMV, Comp.eval, Expr.eval, Env.get_succ, Env.get_zero, findML_eq_findMPrim,
      ← List.map_take, cpR_take_min_of_le K S.N_sess_tot _ hIdeal]
    rw [findMPrim_map_congr idealAuthSessionToVal _
      (matchIdealAuthHandshakePrim kEntry.ikAPk bEntry.spkPk none bEntry.pqspkPk msg.hdr)]
    intro s
    exact matchIdealAuthHandshakeC_eval S _ _ _ _ _ .zero _ kEntry.ikAPk bEntry.spkPk none
      bEntry.pqspkPk msg.hdr s rfl rfl rfl rfl rfl rfl
  refine cpR_optCases mt (fun hn => ?_) (fun sM hsM => ?_)
  · subst hn
    simp only [Option.map_none]
    rw [cpR_caseOpt_none _ _ _ _ rfl, cpR_iteC]
    refine PeelSim.peel_bind _ (Prod.map drKeyToVal (List.map (Prod.map id drKeyToVal))) ?_ (fun dro => ?_)
    · refine PeelSim.peel_ite _ ?_ (fun hu => ?_) (fun hu => ?_)
      · rcases sP with _ | ⟨_, e⟩ <;> simp
      · simp only [bindV_eval, samplePrim_drKey96_eval, cpR_ret, Expr.eval, Env.get_zero, map_bind,
          bind_map_left, map_pure]
        rfl
      · rw [hkdfRoC_eval S K _ _ _ hst.base (by
          simp only [Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, authStateToVal,
            Prod.mk.eta, List.map_id']) hB.roCache_le]
        rfl
    revert dro
    refine cpR_pairCases (fun dk roC => ?_)
    simp only [Prod.map]
    refine PeelSim.peel_bind_same _ (by rfl) (fun dhR => ?_)
    refine PeelSim.peel_bind_same _ (by rw [cpR_caseOpt_none _ _ _ _ rfl]; rfl) (fun se => ?_)
    refine PeelSim.peel_bind_same _ (by
      rw [cpR_caseOpt_none _ _ _ _ rfl, cpR_iteC]
      refine cpR_iteEq (by rcases sP with _ | ⟨_, e⟩ <;> simp) (fun _ => rfl) (fun _ => ?_)
      rw [rootRoC_eval S K _ _ _ _ hst.base (by
          simp only [Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, authStateToVal,
            Prod.mk.eta, List.map_id']) hB.rootRoCache_le]
      rfl) (fun rko => ?_)
    refine PeelSim.peel_bind_same _ (by
      rw [cpR_caseOpt_none _ _ _ _ rfl, cpR_iteC]
      exact cpR_iteEq (by rcases sP with _ | ⟨_, e⟩ <;> simp) (fun _ => rfl) (fun _ => rfl))
      (fun mkc => ?_)
    refine PeelSim.peel_bind_same _ (by rfl) (fun sp? => ?_)
    refine cpR_optCases2 sp? (fun hn => ?_) (fun pqr salt hsp => ?_)
    · subst hn
      rw [cpR_caseOpt_none _ _ _ _ rfl]
      simp only [pure_bind]
      exact PeelSim.peel_pure _ (by cpR_close)
    subst hsp
    rw [cpR_caseOpt_some _ _ _ _ _ rfl]
    simp only [bind_assoc, letV_eval, bindV_eval, Expr.eval, Env.get_zero, Env.get_succ]
    refine PeelSim.peel_bind _ (Prod.map msgKeysToVal
        (List.map (fun x => ((sessionIdToVal x.1.1, x.1.2), x.2.1, msgKeysToVal x.2.2))))
        ?_ (fun mko => ?_)
    · rw [cpR_caseOpt_none _ _ _ _ rfl, cpR_iteC]
      refine PeelSim.peel_ite _ (by rcases sP with _ | ⟨_, e⟩ <;> simp) (fun _ => ?_) (fun _ => ?_)
      · simp only [bindV_eval, samplePrim_msgKeys80_eval, cpR_ret, Expr.eval, Env.get_zero, Env.get_succ,
          map_bind, bind_map_left, map_pure]
        rfl
      · simp only [bindV_eval, queryPrim_eval, queryPrim_deriveMsgKeys_eval, cpR_ret, Expr.eval,
          Env.get_zero, Env.get_succ, map_bind, bind_map_left, map_pure]
        rfl
    revert mko
    refine cpR_pairCases (fun mk c' => ?_)
    simp only [Prod.map, Bool.false_eq_true, ↓reduceIte]
    rw [cpR_iteC, ite_eq_right (by simp only [Expr.eval, Env.get_zero, Env.get_succ,
      Bool.false_eq_true, not_false_eq_true]), cpR_iteC, PeelSim.ite_bind, PeelSim.ite_bind]
    refine PeelSim.peel_ite _ (by rcases sP with _ | ⟨_, e⟩ <;> simp) (fun _ => ?_) (fun _ => ?_)
    · simp only [cpR_ret, pure_bind, Expr.eval]
      rw [cpR_caseOpt_none _ _ _ _ rfl]
      exact PeelSim.peel_pure _ (by cpR_close)
    simp only [bind_assoc]
    refine PeelSim.peel_bind_same _ ?_ (fun pt? => ?_)
    · simp only [queryPrim_eval, Expr.eval, Env.get_zero, Env.get_succ, firstMsgADE_eval, PTag.evalPrim]
      rfl
    refine cpR_optCases pt? (fun hn => ?_) (fun pt hpt => ?_)
    · subst hn
      rw [cpR_caseOpt_none _ _ _ _ rfl]
      simp only [pure_bind]
      exact PeelSim.peel_pure _ (by cpR_close)
    subst hpt
    rw [cpR_caseOpt_some _ _ _ _ pt rfl]
    simp only [pure_bind, bindV_eval]
    refine PeelSim.peel_bind _ (Option.map (Prod.map id principalEntryToVal))
      (findHonestC_eval S _ _ _ hst.base (by
        simp only [Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, authStateToVal,
          Prod.mk.eta, List.map_id']) hB.principals_le) (fun sP2 => ?_)
    simp only [letV_eval, cpR_ret]
    refine PeelSim.peel_pure _ ?_
    rcases sP2 with _ | ⟨i2, e2⟩ <;>
    simp only [Expr.eval, Env.get_zero, Env.get_succ, Option.map, Prod.map,
      authHybridStateFixedToVal, authHybridStateFixedWithSlotsToVal, authSlotStateToVal,
      authHybridStateToVal, authStateToVal, authRespToVal, authRenc,
      drKeyToVal, drKeyV, Prod.mk.eta, List.map_id', List.map_cons, recvKemRecordToVal,
      aRecvUnfresh, aRecvHonest, asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries,
      asSessions, asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asSentOPKEvents,
      asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents, asAdvKeys]
  · subst hsM
    simp only [Option.map_some]
    rw [cpR_caseOpt_some _ _ _ _ _ rfl]
    simp only [cpR_ret, pure_bind, Expr.eval]
    refine PeelSim.peel_bind_same _ (by rfl) (fun dhR => ?_)
    refine PeelSim.peel_bind_same _ (by
      rw [cpR_caseOpt_some _ _ _ _ _ rfl]
      simp only [bindV_eval, queryPrim_eval, cpR_ret]
      rfl) (fun se => ?_)
    refine PeelSim.peel_bind_same _ (by
      rw [cpR_caseOpt_some _ _ _ _ _ rfl, cpR_iteC]
      exact cpR_iteEq Iff.rfl (fun _ => rfl) (fun _ => rfl)) (fun rko => ?_)
    refine PeelSim.peel_bind_same _ (by
      rw [cpR_caseOpt_some _ _ _ _ _ rfl, cpR_iteC]
      exact cpR_iteEq Iff.rfl (fun _ => rfl) (fun _ => rfl)) (fun mkc => ?_)
    refine PeelSim.peel_bind_same _ (by rfl) (fun sp? => ?_)
    refine cpR_optCases2 sp? (fun hn => ?_) (fun pqr salt hsp => ?_)
    · subst hn
      rw [cpR_caseOpt_none _ _ _ _ rfl]
      simp only [pure_bind]
      exact PeelSim.peel_pure _ (by cpR_close)
    subst hsp
    rw [cpR_caseOpt_some _ _ _ _ _ rfl]
    simp only [bind_assoc, letV_eval, bindV_eval, Expr.eval, Env.get_zero, Env.get_succ]
    refine PeelSim.peel_bind _ (Prod.map msgKeysToVal
        (List.map (fun x => ((sessionIdToVal x.1.1, x.1.2), x.2.1, msgKeysToVal x.2.2))))
        ?_ (fun mko => ?_)
    · rw [cpR_caseOpt_some _ _ _ _ _ rfl, cpR_iteC]
      refine PeelSim.peel_ite _ ?_ (fun _ => by simp only [cpR_ret]; exact PeelSim.peel_pure _ rfl) (fun _ => ?_)
      · simp only [Expr.eval, Env.get_zero, Env.get_succ, sameSaltKeyE_eval, iasSpqrSalt?,
          idealAuthSessionToVal]
      rw [cpR_iteC]
      refine PeelSim.peel_ite _ Iff.rfl (fun _ => ?_) (fun _ => ?_)
      · simp only [letV_eval]
        rw [caseOptV_eval]
        simp only [eFind, Expr.eval, Env.get_zero, Env.get_succ, iasSid, idealAuthSessionToVal]
        rw [cpR_mkFind K hst.mkSaltCache hB.mkSaltCache_le sM.sid salt _ (fun s' o rc mk => by
          simp only [Expr.eval, Env.get_succ, Env.get_zero, sameSaltKeyE_eval, mkSaltKeyMatch]
          rw [sidEq_eval _ _ _ s' sM.sid rfl rfl])]
        split
        · rename_i hn
          simp only [Option.map_eq_none_iff] at hn
          simp only [hn, bindV_eval, samplePrim_msgKeys80_eval, cpR_ret, Expr.eval, Env.get_zero, Env.get_succ,
            map_bind, bind_map_left, map_pure]
          rfl
        · rename_i v hv
          simp only [Option.map_eq_some_iff] at hv
          obtain ⟨⟨⟨sid', o'⟩, rc', mk'⟩, hw, rfl⟩ := hv
          simp only [hw, cpR_ret, Expr.eval, Env.get_zero, Env.get_succ, map_pure]
          rfl
      · simp only [bindV_eval, samplePrim_msgKeys80_eval, cpR_ret, Expr.eval, Env.get_zero, Env.get_succ,
          map_bind, bind_map_left, map_pure]
        rfl
    revert mko
    refine cpR_pairCases (fun mk c' => ?_)
    simp only [Prod.map]
    rw [cpR_iteC, PeelSim.ite_bind, cpR_iteMapBind]
    refine cpR_iteEq ?_ (fun hsm => ?_) (fun hsm => ?_)
    · simp only [Expr.eval, Env.get_zero, Env.get_succ, sameSaltKeyE_eval, iasSpqrSalt?,
        idealAuthSessionToVal]
    · simp only [cpR_ret, pure_bind, ↓cpR_eIte, Expr.eval, Env.get_zero, Env.get_succ]
      rw [cpR_iteMapBind]
      simp only [Expr.eval, bytesBeq_eval, Env.get_zero, Env.get_succ, firstMsgADE_eval, iasAdE,
        iasAeadCtE, idealAuthSessionToVal, pkmPqRatchetMsg, pkmAeadCt]
      cases h2 : (firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg == sM.ad &&
            msg.aeadCt == sM.aeadCt)
      · simp only [Bool.cond_false, Bool.false_eq_true, ↓reduceIte, pure_bind]
        rw [cpR_caseOpt_none _ _ _ _ rfl]
        exact PeelSim.peel_pure _ (by cpR_close)
      · simp only [Bool.cond_true, ↓reduceIte, pure_bind]
        rw [cpR_caseOpt_some _ _ _ _ _ rfl]
        simp only [bindV_eval]
        refine PeelSim.peel_bind _ (Option.map (Prod.map id principalEntryToVal))
          (findHonestC_eval S _ _ _ hst.base (by
            simp only [Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, authStateToVal,
              Prod.mk.eta, List.map_id']) hB.principals_le) (fun sP2 => ?_)
        simp only [letV_eval, cpR_ret]
        refine PeelSim.peel_pure _ ?_
        rcases sP2 with _ | ⟨i2, e2⟩ <;>
        simp only [Expr.eval, Env.get_zero, Env.get_succ, Option.map, Prod.map,
          authHybridStateFixedToVal, authHybridStateFixedWithSlotsToVal, authSlotStateToVal, authHybridStateToVal, authStateToVal, authRespToVal, authRenc,
          drKeyToVal, drKeyV, Prod.mk.eta, List.map_id', List.map_cons, recvKemRecordToVal,
          aRecvUnfresh, aRecvHonest, asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries,
          asSessions, asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asSentOPKEvents,
          asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents, asRoCache, asAdvKeys, iasDrKey,
          iasMsgPlainE]
    · rw [cpR_iteC, PeelSim.ite_bind, cpR_iteMapBind]
      refine cpR_iteEq (by rcases sP with _ | ⟨_, e⟩ <;> simp) (fun _ => ?_) (fun _ => ?_)
      · simp only [cpR_ret, pure_bind, Expr.eval]
        rw [cpR_caseOpt_none _ _ _ _ rfl]
        exact PeelSim.peel_pure _ (by cpR_close)
      simp only [bind_assoc]
      refine PeelSim.peel_bind_same _ ?_ (fun pt? => ?_)
      · simp only [queryPrim_eval, Expr.eval, Env.get_zero, Env.get_succ, firstMsgADE_eval, PTag.evalPrim]
        rfl
      refine cpR_optCases pt? (fun hn => ?_) (fun pt hpt => ?_)
      · subst hn
        rw [cpR_caseOpt_none _ _ _ _ rfl]
        simp only [pure_bind]
        exact PeelSim.peel_pure _ (by cpR_close)
      subst hpt
      rw [cpR_caseOpt_some _ _ _ _ pt rfl]
      simp only [pure_bind, bindV_eval]
      refine PeelSim.peel_bind _ (Option.map (Prod.map id principalEntryToVal))
        (findHonestC_eval S _ _ _ hst.base (by
          simp only [Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, authStateToVal,
            Prod.mk.eta, List.map_id']) hB.principals_le) (fun sP2 => ?_)
      simp only [letV_eval, cpR_ret]
      refine PeelSim.peel_pure _ ?_
      rcases sP2 with _ | ⟨i2, e2⟩ <;>
      simp only [Expr.eval, Env.get_zero, Env.get_succ, Option.map, Prod.map,
        authHybridStateFixedToVal, authHybridStateFixedWithSlotsToVal, authSlotStateToVal, authHybridStateToVal, authStateToVal, authRespToVal, authRenc,
        drKeyToVal, drKeyV, Prod.mk.eta, List.map_id', List.map_cons, recvKemRecordToVal,
        aRecvUnfresh, aRecvHonest, asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries,
        asSessions, asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asSentOPKEvents,
        asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents, asRoCache, asAdvKeys,
        idealAuthSessionToVal, iasDrKey]

theorem cpaRecvC_eval_noopk (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ recvQTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (env : Env Δ) (hst : AuthHybridStateFixed S)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (hs : Env.get env (h₁.wk fhst) = authHybridStateFixedToVal hst)
    (hx : Env.get env (h₂.wk x) = (k.val, (j.val, (l.val, preKeyMsgToVal msg))))
    (hB : AuthListsBounded K hst)
    (hIdeal : hst.toAuthHybridState.idealSessions.length ≤ K) :
    (cpaRecvC S K false fhst x).eval env =
      Prod.map authRespToVal authHybridStateFixedToVal <$>
        stepAuthCpaNonSendPrim S (.recvNoOPK k j l msg) hst :=
  cpaRecvC_slot_eval_noopk S K fhst x env hst k j l msg hs hx hB hIdeal

end Recv

end SignalPqxdh.Security.ReductionDsl.AuthAead

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfCost
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfMkShallow
import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3H2
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfMkDecomp
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfMkLeaves
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfMkRecv
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfMkSend
import VCVio.EvalDist.Monad.Basic

/-!
# Evaluation Equivalence and Wiring for `prfMsgKeysRedProg`

Proves that `prfMsgKeysRedProg S b.q_total` evaluates to the shallow reduction
`prfMsgKeysReductionAuthFixed S b A`. Packages the DSL reduction as `prfMsgKeysDslAdv` and
establishes advantage equality and query-budget bounds.
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

/-- Encodes the `prfMsgKeysRedProg` state `(budget, core)` into `prfMkStTy.denote`. -/
def mkStToVal {S : Setup} (bud : Nat) (secb : Bool) (idx : Nat) (sc : Bool)
    (hst : AuthHybridStateFixed S) : prfMkStTy.denote :=
  (bud, mkCoreToVal secb idx sc hst)

@[simp] theorem mkStToVal_fst {S : Setup} (bud : Nat) (secb : Bool) (idx : Nat) (sc : Bool)
    (hst : AuthHybridStateFixed S) :
    (mkStToVal bud secb idx sc hst).1 = bud := rfl

@[simp] theorem mkStToVal_snd {S : Setup} (bud : Nat) (secb : Bool) (idx : Nat) (sc : Bool)
    (hst : AuthHybridStateFixed S) :
    (mkStToVal bud secb idx sc hst).2 = mkCoreToVal secb idx sc hst := rfl

/-- Identity wrapper aligning `OracleComp PrfMkSimSpec` with the syntactic `pqPrfMkIface` monad
    `OracleComp (PrimBaseSpec + msgKeyPrfOracle.spec)` at `implicit` transparency. -/
def toDslMk {α : Type} (m : OracleComp PrfMkSimSpec α) :
    OracleComp (PrimBaseSpec + msgKeyPrfOracle.spec) α :=
  m

@[simp] theorem toDslMk_pure {α : Type} (a : α) :
    toDslMk (pure a) = pure a := rfl

@[simp] theorem toDslMk_bind {α β : Type} (m : OracleComp PrfMkSimSpec α)
    (f : α → OracleComp PrfMkSimSpec β) :
    toDslMk (m >>= f) = toDslMk m >>= fun a => toDslMk (f a) := rfl

@[simp] theorem toDslMk_map {α β : Type} (f : α → β) (m : OracleComp PrfMkSimSpec α) :
    toDslMk (f <$> m) = f <$> toDslMk m := rfl

@[simp] theorem toDslMk_embedPrimMk {α : Type} (m : OracleComp PrimBaseSpec α) :
    toDslMk (embedPrimMk m) = FgGapDh.embedPrim (spec := msgKeyPrfOracle.spec) m := rfl

@[simp] theorem toDslMk_embedUnifMk {α : Type} (m : ProbComp α) :
    toDslMk (embedUnifMk m) =
      FgGapDh.embedPrim (spec := msgKeyPrfOracle.spec) (embedUnif m) := rfl

@[simp] theorem toDslMk_deriveMkQ (salt? : Option Bytes) :
    toDslMk (deriveMkQ salt?) =
      query (spec := PrimBaseSpec + msgKeyPrfOracle.spec)
        (Sum.inr (PrfMsgKeysQuery.derive (effectiveHkdfSaltBytes salt?))) := rfl

theorem AllLeaves.toDslMk {α : Type} {P : α → Prop} {m : OracleComp PrfMkSimSpec α}
    (h : AllLeaves P m) : AllLeaves P (toDslMk m) := h

@[simp] theorem queryDeriveMk_eval' {Γ : List PT}
    (salt? : Expr pqxdhOps Γ (.opt (B 32))) (env : Env Γ) :
    (queryDeriveMk salt?).eval env =
      msgKeysToVal <$> toDslMk (AuthSubHops1to3.deriveMkQ (salt?.eval env)) := by
  simp only [queryDeriveMk, Comp.eval, pqPrfMkIface, pqChalIface, msgKeyPrfOracle,
    saltKeyEnc, toDslMk_deriveMkQ, map_eq_bind_pure_comp]
  rfl

@[simp] theorem sampleChal_index_eval {Γ : List PT} (N : ℕ) (env : Env Γ) :
    (sampleChal (C := msgKeyPrfOracle) (.index N)).eval env =
      toDslMk (embedUnifMk (RoKem.sampleIndexRange N)) := by
  simp only [sampleChal_eval, samplePrim_index_eval, toDslMk_embedUnifMk]

@[simp] theorem sampleChal_bool_eval {Γ : List PT} (env : Env Γ) :
    (sampleChal (C := msgKeyPrfOracle) .bool).eval env =
      toDslMk (embedUnifMk ($ᵗ Bool)) := by
  simp only [sampleChal_eval, samplePrim_bool_eval, toDslMk_embedUnifMk]

theorem pqPrfMkIface_fwdU_eq (uq : ℕ) :
    toDslMk (embedUnifMk (liftM (OracleSpec.query (spec := unifSpec) uq))) =
      pqPrfMkIface.fwdU uq := by
  have h := pqChalIface_liftP_eq (C := msgKeyPrfOracle) (liftM (OracleSpec.query (spec := unifSpec) uq))
  change (query (spec := PrimBaseSpec + msgKeyPrfOracle.spec) (.inl (.inl uq)) >>= pure) =
    FgGapDh.embedPrim (spec := msgKeyPrfOracle.spec)
      (embedUnif (liftM (OracleSpec.query (spec := unifSpec) uq))) at h
  rw [bind_pure] at h
  exact h.symm

section Dispatch

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}

theorem wrapMkBase_eval (core : Var Γ₁ prfMkCoreTy) [h₁ : Ext Γ₁ Δ] (env : Env Δ)
    (secb : Bool) (idx : Nat) (sc : Bool) (hst : AuthHybridStateFixed S)
    (hcore : Env.get env (h₁.wk core) = mkCoreToVal secb idx sc hst)
    (m : Comp pqxdhOps pqPrimIface Δ RSF)
    (mx : OracleComp PrimBaseSpec (AuthResponse × AuthHybridStateFixed S))
    (hm : m.eval env = Prod.map authRespToVal authHybridStateFixedToVal <$> mx) :
    (wrapMkBase core m).eval env =
      mkPreToVal secb idx sc <$> (Sum.inl <$> mx : OracleComp PrimBaseSpec (MkPre S)) := by
  simp only [wrapMkBase, bindV, v, Comp.eval, Expr.eval, Ext.step_wk, Env.get_succ,
    hm, hcore, mkCoreToVal, mkcMk, mkcSecb, mkcIdx, mkcSentChal, map_eq_bind_pure_comp,
    bind_assoc, Function.comp_apply, pure_bind]
  refine bind_congr fun x => ?_
  rcases x with ⟨r, h⟩
  rfl

theorem prfMkStepPreC_eval (core : Var Γ₁ prfMkCoreTy) (q : Var Γ₂ authQueryTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (env : Env Δ)
    (secb : Bool) (idx : Nat) (sc : Bool) (hst : AuthHybridStateFixed S) (qv : AuthQuery S)
    (hcore : Env.get env (h₁.wk core) = mkCoreToVal secb idx sc hst)
    (hq : Env.get env (h₂.wk q) = authQueryToVal qv)
    (hB : AuthListsBounded K hst) :
    (prfMkStepPreC S K core q).eval env = mkPreToVal secb idx sc <$> mkPre S idx qv hst sc := by
  cases qv <;> simp only [authQueryToVal, authQenc] at hq <;>
    simp only [prfMkStepPreC, letV, eval_letC, caseSumV, v, Comp.eval, Expr.eval, Ext.step_wk,
      Ext.refl_wk, Env.get_succ, Env.get_zero, hq]
  case initPrin u =>
    refine wrapMkBase_eval S core _ secb idx sc hst ?_ _ _
      (initPrinFixedB_eval S K _ _ _ hst u ?_ ?_ hB) <;>
      first | rfl | simp [hcore, mkCoreToVal]
  case corruptIK u =>
    refine wrapMkBase_eval S core _ secb idx sc hst ?_ _ _
      (corruptFixedB_eval S K _ _ _ hst u ?_ ?_ hB) <;>
      first | rfl | simp [hcore, mkCoreToVal]
  case genSPK u j =>
    refine wrapMkBase_eval S core _ secb idx sc hst ?_ _ _
      (genSpkFixedB_eval S K _ _ _ hst u j ?_ ?_ hB) <;>
      first | rfl | simp [hcore, mkCoreToVal]
  case genOPK u j o =>
    refine wrapMkBase_eval S core _ secb idx sc hst ?_ _ _
      (genOpkFixedB_eval S K _ _ _ hst u j o ?_ ?_ hB) <;>
      first | rfl | simp [hcore, mkCoreToVal]
  case sendOPK u i b m0 m1 =>
    refine authMkSendPreB_eval_opk S K _ _ _ secb idx sc hst u i b m0 m1 ?_ ?_ hB <;>
      first | rfl | simp [hcore]
  case sendNoOPK u i b m0 m1 =>
    refine authMkSendPreB_eval_noopk S K _ _ _ secb idx sc hst u i b m0 m1 ?_ ?_ hB <;>
      first | rfl | simp [hcore]
  case recvOPK k j o msg =>
    refine authMkRecvPreB_eval_opk S K _ _ _ secb idx sc hst k j o msg ?_ ?_ hB <;>
      first | rfl | simp [hcore]
  case recvNoOPK k j l msg =>
    refine authMkRecvPreB_eval_noopk S K _ _ _ secb idx sc hst k j l msg ?_ ?_ hB <;>
      first | rfl | simp [hcore]
  case roQuery sec =>
    refine wrapMkBase_eval S core _ secb idx sc hst ?_ _ _
      (roFixedB_eval S K _ _ _ hst sec ?_ ?_ hB) <;>
      first | rfl | simp [hcore, mkCoreToVal]
  case roRootQuery rk dh =>
    refine wrapMkBase_eval S core _ secb idx sc hst ?_ _ _
      (roRootFixedB_eval S K _ _ _ hst rk dh ?_ ?_ hB) <;>
      first | rfl | simp [hcore, mkCoreToVal]
  case revealDhSecrets =>
    simp [Expr.eval, hcore, aNone, mkPre, AuthSubHops1to3.stepAuthOtherPrim, mkPreToVal, authRenc]
  case registerKey sk =>
    refine wrapMkBase_eval S core _ secb idx sc hst ?_ _ _
      (registerFixedB_eval S _ _ _ hst sk ?_ ?_) <;>
      first | rfl | simp [hcore, mkCoreToVal]

private theorem finishAuthRecvMkSlotsPrim_eq_map' {S : Setup} (msg : PreKeyMsg)
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

set_option maxRecDepth 20000 in
theorem prfMkStepPostC_eval (cont : Var Γ₁ prfMkChalContTy) (mkv : Var Γ₂ msgKeysTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (env : Env Δ)
    (secb : Bool) (idx : Nat) (sc : Bool) (c : MkCont S) (mk : MessageKeys)
    (hc : Env.get env (h₁.wk cont) = c.toVal secb idx sc)
    (hmk : Env.get env (h₂.wk mkv) = msgKeysToVal mk)
    (hB : c.Bounded K) :
    (prfMkStepPostC S K cont mkv).eval env =
      (fun p => (authRespToVal p.1, mkCoreToVal secb idx (sc || c.isSend) p.2)) <$>
        c.post mk := by
  cases c with
  | send hst sid uEntry pp bundle m0 m1 ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 ck1_1
      salt? pqMsg msgPlain =>
    simp only [prfMkStepPostC, caseSumV, v, Comp.eval, Expr.eval, hc, MkCont.toVal, letV_eval,
      bindV_eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero]
    rw [finishAuthSendMkC_eval S K (hst := hst) (sidv := sid) (uEntry := uEntry)
      (peerPrincipal? := pp) (bundle := bundle) (m0 := m0) (m1 := m1) (ekASk := ekASk)
      (ekAPk := ekAPk) (ss := ss) (kemCt := kemCt) (ephASk := ephASk) (ephAPk := ephAPk)
      (drKeyv := drKey) (rk1v := rk1) (mkSeedv := []) (ck1_1v := ck1_1) (spqrSaltv? := salt?)
      (pqMsgv := pqMsg) (msgPlainv := msgPlain) (mk := mk) (hB := hB)]
    · simp only [MkCont.post, MkCont.isSend, Bool.or_true, map_eq_bind_pure_comp, bind_assoc,
        Function.comp_apply, pure_bind]
      refine bind_congr fun x => ?_
      simp [mkCoreToVal]
    all_goals first | rfl | simp [Expr.eval, hmk, msgKeysToVal]
  | recv msg prep drKey rk1 ck1_1 rc' cache slots ci? =>
    rcases ci? with _ | ⟨⟨sid, salt?⟩, rc⟩ <;>
    simp only [prfMkStepPostC, caseSumV, letV, eval_letC, bindV, v, eCaseOpt, Comp.eval, Expr.eval,
      Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, hc, hmk, MkCont.toVal]
    · rw [MkCont.post, finishAuthRecvMkSlotsPrim_eq_map',
        finishAuthRecvMkC_eval S K _ _ _ _ _ _ _ _ _ msg prep drKey rk1 ck1_1 rc' cache mk
          rfl rfl rfl rfl rfl rfl rfl (by simp [Expr.eval, hmk]) hB.1]
      simp only [MkCont.isSend, Bool.or_false, map_eq_bind_pure_comp, bind_assoc,
        Function.comp_apply, pure_bind]
      refine bind_congr fun x => ?_
      simp [ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, mkCoreToVal, Expr.eval]
    · rw [MkCont.post, finishAuthRecvMkSlotsPrim_eq_map',
        finishAuthRecvMkC_eval S K _ _ _ _ _ _ _ _ _ msg prep drKey rk1 ck1_1 rc'
          (((sid, salt?), (rc, mk)) :: cache) mk
          rfl rfl rfl rfl rfl rfl rfl (by simp [Expr.eval, hmk]) hB.1]
      simp only [MkCont.isSend, Bool.or_false, map_eq_bind_pure_comp, bind_assoc,
        Function.comp_apply, pure_bind]
      refine bind_congr fun x => ?_
      simp [ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, mkCoreToVal, Expr.eval]

end Dispatch

theorem prfMkStepC_leaves {S : Setup} {n : Nat} (idx : Nat) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S) (sc : Bool) (hB : AuthListsBounded n hst) :
    AllLeaves (fun (x : (AuthResponse × AuthHybridStateFixed S) × Nat × Bool) =>
        AuthListsBounded (n + 1) x.1.2 ∧
        ((x.2.1 = 0 ∧ x.2.2 = sc) ∨
         (x.2.1 = 1 ∧ ((sc = false ∧ x.2.2 = true) ∨
           (isAuthRecvQuery (.inr q : Nat ⊕ AuthQuery S) ∧ x.2.2 = sc)))))
      (prfMkStepC S idx q hst sc) := by
  unfold prfMkStepC prfMkRunPre
  refine AllLeaves.bind (AllLeaves.embedPrim (mkPre_leaves idx q hst sc hB)) fun p hp => ?_
  rcases p with ⟨r, hst'⟩ | ⟨salt?, c⟩
  · exact AllLeaves.pure ⟨hp, Or.inl ⟨rfl, rfl⟩⟩
  · obtain ⟨hcB, hsend, hrecv⟩ := hp
    refine AllLeaves.bind_const _ fun mk => ?_
    refine AllLeaves.bind (AllLeaves.embedPrim (MkCont.post_leaves c mk hcB)) fun res hres => ?_
    refine AllLeaves.pure ⟨hres, Or.inr ⟨rfl, ?_⟩⟩
    cases hc : c.isSend
    · exact Or.inr ⟨hrecv hc, by simp⟩
    · exact Or.inl ⟨hsend hc, by simp⟩

theorem prfMsgKeysHandleDsl_eval (S : Setup) (K : Nat) (secb : Bool) (idx : Nat) (sc : Bool)
    (hst : AuthHybridStateFixed S) (bud : Nat) (qv : AuthQuery S)
    (hB : AuthListsBounded K hst)
    (hsc : sc = false → 0 < bud)
    (hrecv : isAuthRecvQuery (.inr qv : Nat ⊕ AuthQuery S) → 0 < bud) :
    (prfMsgKeysHandleDsl S K).eval
        (.cons (mkStToVal bud secb idx sc hst)
          (.cons (authQueryToVal qv) .nil)) =
      toDslMk ((fun x => (authRespToVal x.1.1,
        mkStToVal (bud - x.2.1) secb idx x.2.2 x.1.2)) <$> prfMkStepC S idx qv hst sc) := by
  have hpre := prfMkStepPreC_eval S K
    (env := (.cons (mkCoreToVal secb idx sc hst) (.cons bud
      (.cons (mkStToVal bud secb idx sc hst)
        (.cons (mkStToVal bud secb idx sc hst)
          (.cons (authQueryToVal qv) .nil)))) :
      Env [prfMkCoreTy, .nat, prfMkStTy, prfMkStTy, authQueryTy]))
    (core := (.zero : Var [prfMkCoreTy, .nat, prfMkStTy, prfMkStTy, authQueryTy] prfMkCoreTy))
    (q := (.succ .zero : Var [prfMkStTy, authQueryTy] authQueryTy))
    (secb := secb) (idx := idx) (sc := sc) (hst := hst) (qv := qv) (hcore := rfl) (hq := rfl)
    (hB := hB)
  simp only [prfMsgKeysHandleDsl, letV, eval_letC, bindV, caseSumV, v, Comp.eval, Expr.eval,
    Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, mkStToVal_fst, mkStToVal_snd,
    eval_liftPrimComp]
  rw [hpre]
  unfold prfMkStepC prfMkRunPre
  simp only [toDslMk_bind, toDslMk_pure, toDslMk_embedPrimMk, map_eq_bind_pure_comp,
    embedPrim_bind, embedPrim_pure, bind_assoc, Function.comp_apply, pure_bind]
  refine allLeaves_bind_congr (AllLeaves.embedPrim (mkPre_leaves idx qv hst sc hB))
    fun p hp => ?_
  rcases p with ⟨r, hst'⟩ | ⟨salt?, c⟩
  · simp [mkStToVal, mkPreToVal, mkCoreToVal]
  · obtain ⟨hcB, hsend, hrecvc⟩ := hp
    have hbud : bud ≠ 0 := by
      cases hc : c.isSend
      · exact Nat.pos_iff_ne_zero.mp (hrecv (hrecvc hc))
      · exact Nat.pos_iff_ne_zero.mp (hsc (hsend hc))
    have hb : (bud == 0) = false := by simpa using hbud
    simp only [mkPreToVal, Expr.eval, natEq_eval, Env.get_zero, Env.get_succ,
      queryDeriveMk_eval', hb, Bool.false_eq_true, ↓reduceIte, toDslMk_bind, toDslMk_pure,
      toDslMk_embedPrimMk, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
    refine bind_congr fun mk => ?_
    rw [prfMkStepPostC_eval S K
      (Γ₁ := [prfMkChalContTy, .opt (B 32), .prod (.opt (B 32)) prfMkChalContTy, prfMkStepPreTy,
        prfMkCoreTy, .nat, prfMkStTy, prfMkStTy, authQueryTy])
      (Γ₂ := [msgKeysTy, prfMkChalContTy, .opt (B 32), .prod (.opt (B 32)) prfMkChalContTy,
        prfMkStepPreTy, prfMkCoreTy, .nat, prfMkStTy, prfMkStTy, authQueryTy])
      (Δ := [msgKeysTy, prfMkChalContTy, .opt (B 32), .prod (.opt (B 32)) prfMkChalContTy,
        prfMkStepPreTy, prfMkCoreTy, .nat, prfMkStTy, prfMkStTy, authQueryTy])
      .zero .zero _ secb idx sc c mk _ _ hcB]
    rotate_left
    · rfl
    · rfl
    simp only [map_eq_bind_pure_comp, embedPrim_bind, embedPrim_pure, bind_assoc,
      Function.comp_apply, pure_bind, mkStToVal]

theorem prfMk_budget_step (r r' bud c : Nat) (sc sc' : Bool) (R : Prop) [Decidable R]
    (hr : r' = if R then r - 1 else r) (hR : R → 0 < r)
    (hbud : r + (if sc = true then 0 else 1) ≤ bud)
    (hleaf : (c = 0 ∧ sc' = sc) ∨ (c = 1 ∧ ((sc = false ∧ sc' = true) ∨ (R ∧ sc' = sc)))) :
    r' + (if sc' = true then 0 else 1) ≤ bud - c := by
  subst hr
  by_cases hR' : R
  · have := hR hR'
    cases sc <;> cases sc' <;> (try simp [hR'] at hleaf hbud ⊢) <;> omega
  · cases sc <;> cases sc' <;> (try simp [hR'] at hleaf hbud ⊢) <;> omega

/-- Simulation agreement between `prfMsgKeysHandleDsl S K` and `authMkStepReduction S idx` under
    bounded game, receive, and challenger budgets. -/
theorem prfMk_runBridge (S : Setup) (K : Nat) (secb : Bool) (idx : Nat) {α β : Type}
    (f : α × prfMkStTy.denote → OracleComp (PrimBaseSpec + msgKeyPrfOracle.spec) β)
    (g : (α × AuthHybridStateFixed S) × Bool → OracleComp PrfMkSimSpec β)
    (hfg : ∀ a hst sc bud, AuthListsBounded K hst →
      f (a, mkStToVal bud secb idx sc hst) = toDslMk (g ((a, hst), sc)))
    (mx : OracleComp (unifSpec + authSpec S) α) :
    ∀ (n r m bud : Nat) (hst : AuthHybridStateFixed S) (sc : Bool),
      IsQueryBoundP mx (fun q => SignalPqxdh.isGameQuery q = true) n →
      IsQueryBoundP mx isAuthRecvQuery r →
      AuthListsBounded m hst → m + n ≤ K →
      r + (if sc = true then 0 else 1) ≤ bud →
      ((simulateQ (handlerImpl (C := authCodec S) (prfMsgKeysHandleDsl S K)) mx).run
        (mkStToVal bud secb idx sc hst) >>= f) =
        toDslMk (runWithPrfMkStep (authMkStepReduction S idx) mx hst sc >>= g) := by
  induction mx using OracleComp.inductionOn with
  | pure a =>
    intro n r m bud hst sc _ _ hB hmK _
    simp only [simulateQ_pure, runWithPrfMkStep, OracleComp.construct_pure, pure_bind]
    exact hfg a hst sc bud (hB.mono (by omega))
  | query_bind q k ih =>
    intro n r m bud hst sc hG hR hB hmK hbud
    rw [isQueryBoundP_query_bind_iff] at hG hR
    rcases q with uq | gq
    · obtain ⟨_, hG⟩ := hG
      obtain ⟨_, hR⟩ := hR
      have hnr : ¬ isAuthRecvQuery (.inl uq : Nat ⊕ AuthQuery S) := id
      simp only [SignalPqxdh.isGameQuery, Bool.false_eq_true, ↓reduceIte, hnr] at hG hR
      change (((do let a ← pqPrfMkIface.fwdU uq; pure (a, mkStToVal bud secb idx sc hst)) >>=
          fun x =>
            (simulateQ (handlerImpl (C := authCodec S) (prfMsgKeysHandleDsl S K)) (k x.1)).run
              x.2) >>= f) =
        toDslMk ((embedUnifMk (liftM (OracleSpec.query (spec := unifSpec) uq)) >>= fun u =>
            runWithPrfMkStep (authMkStepReduction S idx) (k u) hst sc) >>= g)
      simp only [toDslMk_bind, pqPrfMkIface_fwdU_eq, bind_assoc, pure_bind]
      refine bind_congr fun u => ?_
      exact ih u n r m bud hst sc (hG u) (hR u) hB hmK hbud
    · obtain ⟨hG0, hG⟩ := hG
      obtain ⟨hR0, hR⟩ := hR
      simp only [SignalPqxdh.isGameQuery, ↓reduceIte] at hG hG0
      have hn : 0 < n := by
        rcases hG0 with h | h
        · exact absurd trivial h
        · exact h
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at hG
      change (((do
          let p ← (prfMsgKeysHandleDsl S K).eval
            (.cons (mkStToVal bud secb idx sc hst) (.cons (authQueryToVal gq) .nil))
          return (valToAuthResp p.1, p.2)) >>= fun x =>
            (simulateQ (handlerImpl (C := authCodec S) (prfMsgKeysHandleDsl S K)) (k x.1)).run
              x.2) >>= f) =
        toDslMk ((authMkStepReduction S idx gq hst sc >>= fun p =>
            runWithPrfMkStep (authMkStepReduction S idx) (k p.1.1) p.1.2 p.2) >>= g)
      have hRpos : isAuthRecvQuery (.inr gq : Nat ⊕ AuthQuery S) → 0 < r := fun h => by
        rcases hR0 with h' | h'
        · exact absurd h h'
        · exact h'
      have hB' : AuthListsBounded K hst := hB.mono (by omega)
      rw [prfMsgKeysHandleDsl_eval S K secb idx sc hst bud gq hB'
        (fun h => by subst h; simp at hbud; omega)
        (fun h => by have := hRpos h; omega),
        authMkStepReduction_eq]
      simp only [toDslMk_bind, toDslMk_pure, map_eq_bind_pure_comp, bind_assoc,
        Function.comp_apply, pure_bind]
      refine allLeaves_bind_congr (AllLeaves.toDslMk (prfMkStepC_leaves idx gq hst sc hB))
        fun x hx => ?_
      obtain ⟨hxB, hleaf⟩ := hx
      rw [valToAuthResp_authRespToVal]
      refine ih x.1.1 n' (if isAuthRecvQuery (.inr gq : Nat ⊕ AuthQuery S) then r - 1 else r)
        (m + 1) (bud - x.2.1) x.1.2 x.2.2 (hG x.1.1) (hR x.1.1) hxB (by omega) ?_
      exact prfMk_budget_step r _ bud x.2.1 sc x.2.2
        (isAuthRecvQuery (.inr gq : Nat ⊕ AuthQuery S)) rfl hRpos hbud hleaf

theorem prfMsgKeysInitDsl_eval (S : Setup) (u : Ty.denote .unit) :
    (prfMsgKeysInitDsl S).eval (.cons u .nil) =
      toDslMk (embedUnifMk (RoKem.sampleIndexRange S.N_sess_tot) >>= fun idx =>
        embedUnifMk ($ᵗ Bool) >>= fun secb =>
          pure ((), mkStToVal (S.N_recv_tot + 1) secb idx false
            (AuthHybridStateFixed.empty S secb))) := by
  simp only [prfMsgKeysInitDsl, bindV, v, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk,
    Env.get_succ, Env.get_zero, sampleChal_index_eval, sampleChal_bool_eval,
    toDslMk_bind, toDslMk_pure]
  refine bind_congr fun idx => bind_congr fun secb => ?_
  rfl

theorem prfMsgKeysFinishDsl_eval (S : Setup) (K : Nat) (secb : Bool) (idx : Nat) (sc : Bool)
    (hst : AuthHybridStateFixed S) (bud : Nat) (b' : Bool) (hB : AuthListsBounded K hst) :
    (prfMsgKeysFinishDsl S K).eval
        (.cons (mkStToVal bud secb idx sc hst) (.cons b' .nil)) =
      toDslMk (embedPrimMk (finalizeAuthFixedPrim S secb b' hst.toAuthHybridState)) := by
  simp only [prfMsgKeysFinishDsl, eval_liftPrimComp, letV_eval, mkcSecb, mkcFhst, ahsfHybrid, v,
    Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, mkStToVal_snd, mkCoreToVal,
    authHybridStateFixedToVal, toDslMk_embedPrimMk]
  exact congrArg _ (finalizeAuthFixedDsl_eval S K secb b' hst.toAuthHybridState _
    hB.toAuthHybridListsBounded)

private theorem isQueryBoundP_authRecv_of_game {S : Setup} {α : Type}
    (mx : OracleComp (unifSpec + authSpec S) α) :
    ∀ n, IsQueryBoundP mx (fun q => SignalPqxdh.isGameQuery q = true) n →
      IsQueryBoundP mx isAuthRecvQuery n := by
  induction mx using OracleComp.inductionOn with
  | pure _ => intro n _; exact isQueryBoundP_pure _ _ _
  | query_bind q k ih =>
    intro n hG
    rw [isQueryBoundP_query_bind_iff] at hG ⊢
    refine ⟨?_, fun u => ?_⟩
    · rcases hG.1 with h0 | hpos
      · left; intro hr; apply h0; cases q <;> simp_all [isAuthRecvQuery, SignalPqxdh.isGameQuery]
      · right; exact hpos
    · have hGu := hG.2 u
      by_cases hr : isAuthRecvQuery q
      · have hg : SignalPqxdh.isGameQuery q = true := by
          cases q <;> simp_all [isAuthRecvQuery, SignalPqxdh.isGameQuery]
        simp only [hr, ↓reduceIte]
        simp only [hg, ↓reduceIte] at hGu
        exact ih u (n - 1) hGu
      · simp only [hr, ↓reduceIte]
        by_cases hg : SignalPqxdh.isGameQuery q = true
        · simp only [hg, ↓reduceIte] at hGu
          exact (ih u (n - 1) hGu).mono (Nat.sub_le n 1)
        · simp only [hg] at hGu
          exact ih u n hGu

private theorem isQueryBoundP_authRecv_min {S : Setup} {α : Type}
    (mx : OracleComp (unifSpec + authSpec S) α) {rem R : Nat}
    (hG : IsQueryBoundP mx (fun q => SignalPqxdh.isGameQuery q = true) rem)
    (hR : IsQueryBoundP mx isAuthRecvQuery R) :
    IsQueryBoundP mx isAuthRecvQuery (min rem R) := by
  by_cases h : rem ≤ R
  · rw [Nat.min_eq_left h]
    exact isQueryBoundP_authRecv_of_game mx rem hG
  · rw [Nat.min_eq_right (by omega)]
    exact hR

private theorem prfMsgKeysInitDslK_eval (S : Setup) (K : Nat) (u : Ty.denote .unit) :
    (prfMsgKeysInitDslK S K).eval (.cons u .nil) =
      toDslMk (embedUnifMk (RoKem.sampleIndexRange (min K S.N_sess_tot)) >>= fun idx =>
        embedUnifMk ($ᵗ Bool) >>= fun secb =>
          pure ((), mkStToVal (min K S.N_recv_tot + 1) secb idx false
            (AuthHybridStateFixed.empty S secb))) := by
  simp only [prfMsgKeysInitDslK, bindV, v, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk,
    Env.get_succ, Env.get_zero, sampleChal_index_eval, sampleChal_bool_eval,
    toDslMk_bind, toDslMk_pure]
  refine bind_congr fun idx => bind_congr fun secb => ?_
  rfl

/-- Evaluation equivalence for `prfMsgKeysRedProg S K` on any adversary making at most `rem ≤ K`
    game queries and `S.N_recv_tot` receive queries. -/
theorem prfMsgKeysRedProg_eval_eq_of_bound (S : Setup) (K : Nat)
    (A : AuthAdversary S) (rem : Nat)
    (hG : IsQueryBoundP A.run (fun q => SignalPqxdh.isGameQuery q = true) rem)
    (hR : IsQueryBoundP A.run isAuthRecvQuery S.N_recv_tot)
    (hK : rem ≤ K) :
    (prfMsgKeysRedProg S K).eval (fun _ => A.run) () =
      (do
        let idx ← embedUnifMk (RoKem.sampleIndexRange (min K S.N_sess_tot))
        authMkReductionRun S idx A) := by
  change ((do
      let q ← (prfMsgKeysInitDslK S K).eval (.cons () .nil)
      let r ← (simulateQ (handlerImpl (C := authCodec S) (prfMsgKeysHandleDsl S K)) A.run).run q.2
      (prfMsgKeysFinishDsl S K).eval (.cons r.2 (.cons r.1 .nil))) :
      OracleComp (PrimBaseSpec + msgKeyPrfOracle.spec) Bool) =
    toDslMk (do
      let idx ← embedUnifMk (RoKem.sampleIndexRange (min K S.N_sess_tot))
      let secb ← embedUnifMk ($ᵗ Bool)
      let p ← runWithPrfMkStep (authMkStepReduction S idx) A.run
        (AuthHybridStateFixed.empty S secb) false
      embedPrimMk (finalizeAuthFixedPrim S secb p.1.1 p.1.2.toAuthHybridState))
  rw [prfMsgKeysInitDslK_eval]
  simp only [toDslMk_bind, toDslMk_pure, bind_assoc, pure_bind]
  refine bind_congr fun idx => bind_congr fun secb => ?_
  exact prfMk_runBridge S K secb idx
    (fun q => (prfMsgKeysFinishDsl S K).eval (.cons q.2 (.cons q.1 .nil)))
    (fun x => embedPrimMk (finalizeAuthFixedPrim S secb x.1.1 x.1.2.toAuthHybridState))
    (fun a hst sc bud hB => prfMsgKeysFinishDsl_eval S K secb idx sc hst bud a hB)
    A.run rem (min rem S.N_recv_tot) 0 (min K S.N_recv_tot + 1)
    (AuthHybridStateFixed.empty S secb) false
    hG (isQueryBoundP_authRecv_min A.run hG hR) (authListsBounded_empty S secb) (by omega)
    (by simp only [Bool.false_eq_true, ↓reduceIte]; omega)

/-- Evaluating `prfMsgKeysRedProg S b.q_total` agrees with `(prfMsgKeysReductionAuthFixed S b A).run`. -/
theorem prfMsgKeysRedProg_eval_eq (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (prfMsgKeysRedProg S b.q_total).eval (fun _ => A.1.run) () =
      (prfMsgKeysReductionAuthFixed S b A).run := by
  exact prfMsgKeysRedProg_eval_eq_of_bound S b.q_total A.1 b.q_total
    (SignalPqxdh.QueryBounded.auth_total A.2) (SignalPqxdh.QueryBounded.auth_recv A.2) le_rfl

/-- The `ReductionDsl` `PrfMsgKeys` adversary with the same query budgets as
    `prfMsgKeysReductionAuthFixed`. -/
def prfMsgKeysDslAdv (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) : PrfMsgKeysAdv where
  run := (prfMsgKeysRedProg S b.q_total).eval (fun _ => A.1.run) ()
  q_prf := (prfMsgKeysReductionAuthFixed S b A).q_prf
  q_prim := (prfMsgKeysReductionAuthFixed S b A).q_prim

theorem prfMsgKeysDslAdv_eq (S : Setup) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    prfMsgKeysDslAdv S b A = prfMsgKeysReductionAuthFixed S b A := by
  have h := prfMsgKeysRedProg_eval_eq S b A
  simp only [prfMsgKeysDslAdv, h]

theorem prfMsgKeysRedProg_prfMsgKeys_eq (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    PrfMsgKeys P (prfMsgKeysDslAdv S b A) = PrfMsgKeys P (prfMsgKeysReductionAuthFixed S b A) := by
  rw [prfMsgKeysDslAdv_eq]

/-- Syntactic primitive-query bound for `prfMsgKeysRedProg` against `primQueryBudget`. -/
theorem prfMsgKeysRedProg_totalPrimQueries_le_budget (S : Setup) (b : QueryBudget) :
    (prfMsgKeysRedProg S b.q_total).totalQueries mkPrimW mkWS b.q_total ≤ primQueryBudget S b := by
  have h := prfMsgKeysRedProg_totalQueries_prim_le S b.q_total b.q_total
  unfold primQueryBudget
  nlinarith

theorem prfMsgKeysDslAdv_prim_queries (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (prfMsgKeysDslAdv S b A).q_prim ≤ primQueryBudget S b :=
  prfMsgKeysReductionAuthFixed_prim_queries S b A

/-- `prfMsgKeysDslAdv` satisfies its declared query bounds. -/
theorem prfMsgKeysDslAdv_bounded (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (prfMsgKeysDslAdv S b A).Bounded := by
  rw [prfMsgKeysDslAdv_eq]
  exact prfMsgKeysReductionAuthFixed_bounded S b A

end SignalPqxdh.Security.ReductionDsl.AuthPrf
